pub mod ivl;
mod ivl_ext;

use std::vec;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr, ExprKind, Name, Op, PrefixOp, Quantifier, Type, Var};
use slang_ui::prelude::{
    slang::{ast::Op::Imp, Span},
    *,
};

pub struct App;

struct VerificationCondition {
    condition: Expr,
    span: Span,
    message: String,
}

impl slang_ui::Hook for App {
    fn analyze(&self, cx: &slang_ui::Context, file: &slang::SourceFile) -> Result<()> {
        // get reference to z3 solver
        let mut solver = cx.solver()?;

        // iterate all methods
        for m in file.methods() {
            // convert all the preconditions into smt
            let pres: Vec<smtlib::Bool<'_>> = m
                .requires()
                .map(|pre| Ok(pre.smt(cx.smt_st())?.as_bool()?))
                .collect::<Result<_>>()?;

            // get method body, convert to IVL
            let cmd = &m.body.clone().unwrap().cmd;
            let mut ivl = cmd_to_ivlcmd(cmd)?;
            for postcondition in m.ensures() {
                let assertion = IVLCmd::assert(postcondition, "Postcondition might not hold");

                ivl = ivl.seq(&assertion);
            }

            // compute verification condition
            let (_pre, vcs) = wp(&ivl, &Expr::bool(true), true)?;

            // convert each verification condition into SMT
            let mut obligations = Vec::new();

            for vc in vcs {
                let soblig = vc.condition.smt(cx.smt_st())?.as_bool()?;

                obligations.push((soblig, vc.span, vc.message));
            }

            // open a solver scope for this method
            solver.scope(|solver| {
                // assert all preconditions once per method
                for pre in pres {
                    solver.assert(pre)?;
                }

                for (soblig, span, msg) in obligations {
                    // open a solver scope for this obligation
                    solver.scope(|solver| {
                        // assert the negation of theobligation
                        solver.assert(!soblig)?;
                        // check sat of !obligation
                        match solver.check_sat()? {
                            smtlib::SatResult::Sat => {
                                cx.error(span, msg.to_string());
                            }
                            smtlib::SatResult::Unknown => {
                                cx.warning(span, format!("{msg}: unknown sat result"));
                            }
                            smtlib::SatResult::Unsat => (),
                        }

                        Ok(())
                    })?;
                }

                Ok(())
            })?;
        }

        Ok(())
    }
}

/// Encode a Cmd into IVL
fn cmd_to_ivlcmd(cmd: &Cmd) -> Result<IVLCmd> {
    match &cmd.kind {
        CmdKind::Assert { condition, message } => Ok(IVLCmd::assert(condition, message)),
        CmdKind::Assume { condition } => Ok(IVLCmd::assume(condition)),
        CmdKind::Seq(first, second) => {
            let first_ivl = cmd_to_ivlcmd(first)?;
            let second_ivl = cmd_to_ivlcmd(second)?;

            Ok(IVLCmd::seq(&first_ivl, &second_ivl))
        }
        CmdKind::Assignment { name, expr } => Ok(IVLCmd::assign(name, expr)),
        CmdKind::VarDefinition {
            name,
            ty,
            ty_span,
            expr,
        } => match expr {
            Some(value) => Ok(IVLCmd::assign(name, value)),

            None => Ok(IVLCmd::havoc(name, ty)),
        },

        CmdKind::Match { body } => {
            let mut branches = Vec::new();
            let mut earlier_failed: Option<Expr> = None;

            for case in &body.cases {
                let guard = match &earlier_failed {
                    Some(prev) => infix(&case.condition, Op::And, prev, Type::Bool),
                    None => case.condition.clone(),
                };

                let branch = IVLCmd::seq(&IVLCmd::assume(&guard), &cmd_to_ivlcmd(&case.cmd)?);
                branches.push(branch);

                let neg = not(&case.condition);
                earlier_failed = Some(match earlier_failed {
                    Some(prev) => infix(&prev, Op::And, &neg, Type::Bool),
                    None => neg,
                });
            }

            Ok(IVLCmd::nondets(&branches))
        }
        CmdKind::Return { expr } => match expr {
            Some(value) => {
                let name = Name {
                    span: cmd.span,
                    ident: "result".to_string(),
                };

                Ok(IVLCmd::assign(&name, value))
            }

            None => Ok(IVLCmd::assume(&Expr::bool(true))),
        },
        c => bail!("not yet implemented: cmd_to_ivlcmd {c:?}"),
    }
}

fn infix(left: &Expr, op: Op, right: &Expr, ty: Type) -> Expr {
    let mut result = left.clone();

    result.kind = ExprKind::Infix(Box::new(left.clone()), op, Box::new(right.clone()));

    result.ty = ty;
    result
}

fn substitute(post: &Expr, name: &Name, value: &Expr) -> Expr {
    match &post.kind {
        ExprKind::Result if name.ident == "result" => value.clone(),
        ExprKind::Ident(id) if id == &name.ident => value.clone(),

        ExprKind::Infix(left, op, right) => infix(
            &substitute(left, name, value),
            op.clone(),
            &substitute(right, name, value),
            post.ty.clone(),
        ),

        ExprKind::Prefix(op, inner) => {
            let mut result = post.clone();

            result.kind = ExprKind::Prefix(op.clone(), Box::new(substitute(inner, name, value)));

            result
        }

        _ => post.clone(),
    }
}

fn forall(name: &Name, ty: &Type, post: &Expr) -> Expr {
    let variable = Var {
        name: name.clone(),
        ty: ty.clone(),
        span: name.span,
    };

    let mut result = post.clone();

    result.kind = ExprKind::Quantifier(Quantifier::Forall, vec![variable], Box::new(post.clone()));

    result.ty = Type::Bool;

    result
}

fn not(expr: &Expr) -> Expr {
    let mut result = expr.clone();
    result.kind = ExprKind::Prefix(PrefixOp::Not, Box::new(expr.clone()));
    result.ty = Type::Bool;
    result
}

/// Compute the weakest precondition of IVL program
fn wp(
    ivl: &IVLCmd,
    post: &Expr,
    check_asserts: bool,
) -> Result<(Expr, Vec<VerificationCondition>)> {
    match &ivl.kind {
        // wp[assert H](F) = H AND F
        IVLCmdKind::Assert { condition, message } => {
            if !check_asserts {
                return Ok((post.clone(), Vec::new()));
            }
            let pre = infix(condition, Op::And, post, Type::Bool);

            let vc = VerificationCondition {
                condition: condition.clone(),
                span: condition.span,
                message: message.clone(),
            };

            Ok((pre, vec![vc]))
        }

        // wp[assume H](F) = H -> F
        IVLCmdKind::Assume { condition } => {
            let pre = infix(condition, Op::Imp, post, Type::Bool);

            Ok((pre, Vec::new()))
        }
        // wp[C1;C2](G) = wp[C1](wp[C2](G))
        IVLCmdKind::Seq(first, second) => {
            let (middle, mut second_vcs) = wp(second, post, check_asserts)?;
            let (pre, mut first_vcs) = wp(first, &middle, check_asserts)?;

            if check_asserts {
                for vc in &mut second_vcs {
                    let (condition, _) = wp(first, &vc.condition, false)?;
                    vc.condition = condition;
                }
            }

            first_vcs.append(&mut second_vcs);
            Ok((pre, first_vcs))
        }

        // wp[x := a](G) = G[x := a]
        IVLCmdKind::Assignment { name, expr } => {
            let pre = substitute(post, name, expr);
            Ok((pre, Vec::new()))
        }

        // wp[havoc x](G) = Forall x. G
        IVLCmdKind::Havoc { name, ty } => {
            let pre = forall(name, ty, post);
            Ok((pre, Vec::new()))
        }

        // wp[C1 [] C2](G) = wp[C1](G) And wp[C2](G)
        IVLCmdKind::NonDet(first, second) => {
            let (first_pre, mut first_vcs) = wp(first, post, check_asserts)?;
            let (second_pre, mut second_vcs) = wp(second, post, check_asserts)?;

            let pre = infix(&first_pre, Op::And, &second_pre, Type::Bool);
            first_vcs.append(&mut second_vcs);

            Ok((pre, first_vcs))
        }

        c => bail!("not yet implemented: wp of {:?}", c),
    }
}
