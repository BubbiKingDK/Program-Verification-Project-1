method even(n: Int): Int
    requires n >= 0
    ensures result == 1
{
    match {
        n == 0 =>
            return 1,
        true =>
            var res: Int;
            res := odd(n - 1);
            return res
    }
}

method odd(n: Int): Int
    requires n >= 0
    ensures result == 1
{
    match {
        n == 0 =>
            return 1,
        true =>
            var res: Int;
            res := even(n - 1);
            return res
    }
}
