pub mod ivl;
mod ivl_ext;

use std::vec;

use ivl::{IVLCmd, IVLCmdKind};
use slang::ast::{Cmd, CmdKind, Expr, ExprKind, Name, Op, PrefixOp, Quantifier, Type, Var};
use slang_ui::prelude::{
    slang::{ast::Op::Imp, Span},
    smtlib::Bool,
    *,
};

use std::sync::atomic::{AtomicUsize, Ordering};

static FRESH_COUNTER: AtomicUsize = AtomicUsize::new(0);

pub struct App;

struct VerificationCondition {
    condition: Expr,
    span: Span,
    message: String,
}

use std::collections::HashMap;

struct Contract {
    params: Vec<Name>,
    requires: Vec<Expr>,
    ensures: Vec<Expr>,
}

impl slang_ui::Hook for App {
    fn analyze(&self, cx: &slang_ui::Context, file: &slang::SourceFile) -> Result<()> {
        // get reference to z3 solver
        let mut solver = cx.solver()?;

        let sigs: HashMap<String, Contract> = file
            .methods()
            .into_iter().map(|m| {
                (
                    m.name.ident.clone(),
                    Contract {
                        params: m.args.iter().map(|v| v.name.clone()).collect(),
                        requires: m.requires().cloned().collect(),
                        ensures: m.ensures().cloned().collect(),
                    },
                )
            })
            .collect();

        // iterate all methods
        for m in file.methods() {
            // convert all the preconditions into smt
            let pres: Vec<smtlib::Bool<'_>> = m
                .requires()
                .map(|pre| Ok(pre.smt(cx.smt_st())?.as_bool()?))
                .collect::<Result<_>>()?;

            // get method body, convert to IVL
            let cmd = &m.body.clone().unwrap().cmd;
            let ensures: Vec<Expr> = m.ensures().cloned().collect();
            let mut ivl = cmd_to_ivlcmd(cmd, &ensures, &sigs)?;
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
fn cmd_to_ivlcmd(cmd: &Cmd, ensures: &[Expr], sigs: &HashMap<String, Contract>) -> Result<IVLCmd> {
    match &cmd.kind {
        CmdKind::Assert { condition, message } => Ok(IVLCmd::assert(condition, message)),
        CmdKind::Assume { condition } => Ok(IVLCmd::assume(condition)),
        CmdKind::Seq(first, second) => {
            let first_ivl = cmd_to_ivlcmd(first, ensures, sigs)?;
            let second_ivl = cmd_to_ivlcmd(second, ensures, sigs)?;

            Ok(IVLCmd::seq(&first_ivl, &second_ivl))
        }
        CmdKind::Assignment { name, expr } => {
            let mut cmds = div_asserts(expr);
            cmds.push(IVLCmd::assign(name, expr));
            Ok(IVLCmd::seqs(&cmds))
        }
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

                let branch =
                    IVLCmd::seq(&IVLCmd::assume(&guard), &cmd_to_ivlcmd(&case.cmd, ensures, sigs)?);
                branches.push(branch);

                let neg = not(&case.condition);
                earlier_failed = Some(match earlier_failed {
                    Some(prev) => infix(&prev, Op::And, &neg, Type::Bool),
                    None => neg,
                });
            }

            Ok(IVLCmd::nondets(&branches))
        }

        CmdKind::Return { expr } => {
            let mut cmds = Vec::new();

            if let Some(value) = expr {
                let name = Name {
                    span: cmd.span,
                    ident: "result".to_string(),
                };
                cmds.extend(div_asserts(value));
                cmds.push(IVLCmd::assign(&name, value));
            }

            for post in ensures {
                cmds.push(IVLCmd::assert(post, "Postcondition might not hold"));
            }

            // Nothing after a return is executed
            cmds.push(IVLCmd::assume(&Expr::bool(false)));
            Ok(IVLCmd::seqs(&cmds))
        }

        CmdKind::Loop {
            invariants,
            variant,
            body,
        } => {
            let mut modified = Vec::new();
            let mut cmds = Vec::new();
            for inv in invariants {
                cmds.push(IVLCmd::assert(
                    inv,
                    "Loop invariant might not hold initially",
                ))
            }
            for case in &body.cases {
                collect_modified(&case.cmd, &mut modified);
            }
            for (name, ty) in &modified {
                cmds.push(IVLCmd::havoc(name, ty));
            }
            for inv in invariants {
                cmds.push(IVLCmd::assume(inv))
            }

            let mut branches = Vec::new();
            let mut none_hold: Option<Expr> = None;

            for (idx, case) in body.cases.iter().enumerate() {
                let guard = &case.condition;
                let mut b = vec![IVLCmd::assume(guard)];

                let mut old_v: Option<Expr> = None;

                if let Some(expr) = variant {
                    let old = fresh_name("variant");
                    let old_expr = name_to_expr(&old, Type::Int);

                    b.push(IVLCmd::assign(&old, expr));
                    b.push(IVLCmd::assert(
                        &infix(expr, Op::Ge, &Expr::num(0), Type::Int),
                        "Loop variant might not be non-negative",
                    ));
                    old_v = Some(old_expr);
                }

                b.push(cmd_to_ivlcmd(&case.cmd, ensures, sigs)?);

                for inv in invariants {
                    b.push(IVLCmd::assert(
                        inv,
                        &format!("Loop invariant might not be preserved in case {}", idx + 1),
                    ));
                }

                if let (Some(expr), Some(old_expr)) = (variant, old_v) {
                    b.push(IVLCmd::assert(
                        &infix(expr, Op::Lt, &old_expr, Type::Int),
                        "Loop variant might not decrease",
                    ));
                    old_v = Some(old_expr);
                }

                b.push(IVLCmd::unreachable());
                branches.push(IVLCmd::seqs(&b));

                let neg = not(guard);
                none_hold = Some(match none_hold {
                    Some(prev) => infix(&prev, Op::And, &neg, Type::Bool),
                    None => neg,
                });
            }
            branches.push(IVLCmd::assume(&none_hold.unwrap_or(Expr::bool(true))));
            cmds.push(IVLCmd::nondets(&branches));
            Ok(IVLCmd::seqs(&cmds))
        }
        CmdKind::For {
            name,
            range,
            invariants,
            variant: _,
            body,
        } => {
            let slang::ast::Range::FromTo(lower_bound, upper_bound) = range;

            // Bounded For-loops
            if let (Some(start), Some(end)) = (constant_int(lower_bound), constant_int(upper_bound))
            {
                if invariants.is_empty() {
                    return unroll_for(name, start, end, &body.cmd, ensures, sigs);
                }
            }

            // Unbounded For-loops
            //
            //   lower := L; upper := U;
            //   assert I;
            //   havoc modified; havoc lower;
            //   assume I;
            //   (  assume lower < upper;
            //      i := lower; body; lower := lower + 1;
            //      assert I; unreachable
            //   [] assume !(lower < upper) )
            let lower = fresh_name("lower");
            let upper = fresh_name("upper");

            let lower_expr = name_to_expr(&lower, Type::Int);
            let upper_expr = name_to_expr(&upper, Type::Int);

            let mut cmds = Vec::new();
            cmds.push(IVLCmd::assign(&lower, lower_bound));
            cmds.push(IVLCmd::assign(&upper, upper_bound));

            let loop_invariants: Vec<Expr> = invariants
                .iter()
                .map(|inv| substitute(inv, name, &lower_expr))
                .collect();

            for inv in &loop_invariants {
                cmds.push(IVLCmd::assert(
                    inv,
                    "For-loop invariant might not hold initially",
                ));
            }

            // Havoc loop targets, and the counter
            let mut modified = Vec::new();
            collect_modified(&body.cmd, &mut modified);
            for (modified_name, ty) in &modified {
                cmds.push(IVLCmd::havoc(modified_name, ty));
            }
            cmds.push(IVLCmd::havoc(&lower, &Type::Int));

            for inv in &loop_invariants {
                cmds.push(IVLCmd::assume(inv));
            }

            // One iteration: i := lower; body; lower := lower + 1
            let guard = infix(&lower_expr, Op::Lt, &upper_expr, Type::Bool);
            let assign_i = IVLCmd::assign(name, &lower_expr);
            let encoded_body = cmd_to_ivlcmd(&body.cmd, ensures, sigs)?;

            let increment = infix(&lower_expr, Op::Add, &Expr::num(1), Type::Int);
            let increment_lower = IVLCmd::assign(&lower, &increment);

            let mut iteration_cmds = vec![
                IVLCmd::assume(&guard),
                assign_i,
                encoded_body,
                increment_lower,
            ];

            for inv in &loop_invariants {
                iteration_cmds.push(IVLCmd::assert(
                    inv,
                    "For-loop invariant might not be preserved",
                ));
            }
            iteration_cmds.push(IVLCmd::unreachable());

            let iteration_branch = IVLCmd::seqs(&iteration_cmds);
            let exit_branch = IVLCmd::assume(&not(&guard));

            cmds.push(IVLCmd::nondets(&[iteration_branch, exit_branch]));

            Ok(IVLCmd::seqs(&cmds))
        }
        CmdKind::MethodCall {
            name,
            fun_name,
            args,
            ..
        } => {
            let Some(c) = sigs.get(&fun_name.ident) else {
                bail!("unknown method {}", fun_name.ident);
            };

            let rename = |e: &Expr| {
                c.params
                    .iter()
                    .zip(args)
                    .fold(e.clone(), |acc, (p, a)| substitute(&acc, p, a))
            };

            let mut cmds = Vec::new();

            for pre in &c.requires {
                cmds.push(IVLCmd::assert(&rename(pre), "Precondition might not hold"));
            }

            let ret = fresh_name("ret");
            let ret_expr = name_to_expr(&ret, Type::Int);
            cmds.push(IVLCmd::havoc(&ret, &Type::Int));

            let result_name = Name {
                span: cmd.span,
                ident: "result".to_string(),
            };
            for post in &c.ensures {
                cmds.push(IVLCmd::assume(&substitute(
                    &rename(post),
                    &result_name,
                    &ret_expr,
                )));
            }

            if let Some(x) = name {
                cmds.push(IVLCmd::assign(x, &ret_expr));
            }

            Ok(IVLCmd::seqs(&cmds))
        }
        c => bail!("not yet implemented: cmd_to_ivlcmd {c:?}"),
    }
}

fn collect_modified(cmd: &Cmd, out: &mut Vec<(Name, Type)>) {
    match &cmd.kind {
        CmdKind::Assignment { name, expr } => {
            if !out.iter().any(|(n, _)| n.ident == name.ident) {
                out.push((name.clone(), expr.ty.clone()));
            }
        }

        CmdKind::VarDefinition { name, ty, .. } => {
            if !out.iter().any(|(n, _)| n.ident == name.ident) {
                out.push((name.clone(), ty.clone()));
            }
        }

        CmdKind::Seq(a, b) => {
            collect_modified(a, out);
            collect_modified(b, out);
        }

        CmdKind::Match { body } | CmdKind::Loop { body, .. } => {
            for case in &body.cases {
                collect_modified(&case.cmd, out);
            }
        }

        CmdKind::For { name, body, .. } => {
            if !out.iter().any(|(n, _)| n.ident == name.ident) {
                out.push((name.clone(), Type::Int));
            }

            collect_modified(&body.cmd, out);
        }

        _ => {}
    }
}

fn constant_int(expr: &Expr) -> Option<i64> {
    match &expr.kind {
        ExprKind::Num(value) => Some(*value),

        ExprKind::Infix(left, Op::Add, right) => {
            constant_int(left)?.checked_add(constant_int(right)?)
        }

        ExprKind::Infix(left, Op::Sub, right) => {
            constant_int(left)?.checked_sub(constant_int(right)?)
        }

        ExprKind::Infix(left, Op::Mul, right) => {
            constant_int(left)?.checked_mul(constant_int(right)?)
        }

        _ => None,
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
        ExprKind::Quantifier(quantifier, vars, inner) => {
            if vars.iter().any(|v| v.name.ident == name.ident) {
                return post.clone();
            }

            let mut result = post.clone();

            result.kind = ExprKind::Quantifier(
                quantifier.clone(),
                vars.clone(),
                Box::new(substitute(inner, name, value)),
            );

            result
        }

        _ => post.clone(),
    }
}

fn unroll_for(name: &Name, start: i64, end: i64, body: &Cmd, ensures: &[Expr], sigs: &HashMap<String, Contract>) -> Result<IVLCmd> {
    let mut cmds = Vec::new();

    for i in start..end {
        cmds.push(IVLCmd::assign(name, &Expr::num(i)));
        cmds.push(cmd_to_ivlcmd(body, ensures, sigs)?);
    }

    Ok(IVLCmd::seqs(&cmds))
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

fn div_asserts(expr: &Expr) -> Vec<IVLCmd> {
    let mut out = Vec::new();
    match &expr.kind {
        ExprKind::Infix(left, op, right) => {
            out.extend(div_asserts(left));
            out.extend(div_asserts(right));

            match op {
                Op::Div | Op::Mod => {
                    let zero = Expr::num(0);
                    let nonzero = infix(right, Op::Ne, &zero, Type::Bool);
                    out.push(IVLCmd::assert(&nonzero, "Possible division or mod by zero"));
                }
                _ => {}
            }
        }
        ExprKind::Prefix(_, inner) => out.extend(div_asserts(inner)),
        _ => {}
    }
    return out;
}

fn not(expr: &Expr) -> Expr {
    let mut result = expr.clone();
    result.kind = ExprKind::Prefix(PrefixOp::Not, Box::new(expr.clone()));
    result.ty = Type::Bool;
    result
}

fn fresh_ident(base: &str) -> String {
    let n = FRESH_COUNTER.fetch_add(1, Ordering::SeqCst);
    return format!("{base}_fresh_{n}");
}

fn fresh_name(base: &str) -> Name {
    Name {
        span: Span::default(),
        ident: fresh_ident(base),
    }
}

fn name_to_expr(name: &Name, ty: Type) -> Expr {
    let mut expr = Expr::bool(true);
    expr.kind = ExprKind::Ident(name.ident.clone());
    expr.ty = ty;
    expr
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
            let fresh = fresh_name(&name.ident);
            let fresh_expr = name_to_expr(&fresh, ty.clone());
            let substituted_post = substitute(post, name, &fresh_expr);
            let pre = forall(&fresh, ty, &substituted_post);

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
