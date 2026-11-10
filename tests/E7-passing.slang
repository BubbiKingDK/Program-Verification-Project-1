method sumn(n: Int): Int
    requires n >= 0
    ensures result == n * (n + 1) / 2
    decreases n
{
    var ret: Int;

    match {
        n == 0 =>
            ret := 0,
        true =>
            var res: Int;
            res := sumn(n - 1);
            ret := res + n
    };

    return ret
} 