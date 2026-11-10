method iter(n: Int)
    requires n >= 0
{
    var i: Int := 0;

    loop
        invariant i >= 0
        invariant i <= n
        // @CheckError
        decreases n - i
    {
        i < n =>
            i := i
    }
} 
