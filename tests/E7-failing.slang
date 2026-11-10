method sumn(n: Int): Int
    requires n >= 0
    ensures result >= 0
    decreases n
{
    var ret: Int;

    match {
        n == 0 =>
            ret := 0,
        true =>
            var res: Int;
            // @CheckError
            res := sumn(n);
            ret := res
    };

    return ret
} 