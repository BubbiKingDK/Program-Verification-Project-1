method iter(n: Int): Int
    requires n >= 0
{
    var i: Int := 0;

    loop
        // @CheckError
        invariant i <= n
    {
        i <= n =>
            i := i + 1
    }
} 
