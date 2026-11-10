method absolute(n: Int): Int
    ensures result >= 0
{
    match {
        n >= 0 =>
            return n,
        true =>
            return 0 - n
    }
} 