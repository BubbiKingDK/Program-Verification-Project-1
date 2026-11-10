method count(n: Int): Int
    requires n >= 0
    ensures result >= 0
{
    match {
        n == 0 =>
            return 0,
        true =>
            var res: Int;
            // @CheckError
            res := count(n - 2);
            return res
    }
} 
