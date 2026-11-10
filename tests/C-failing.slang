method invalid_start(n: Int)
    requires n >= 0
{
    var i: Int := 0;

    loop
        // @CheckError
        invariant i > 0
    {
        i < n =>
            i := i + 1
    }
} 