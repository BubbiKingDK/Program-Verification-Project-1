method invalid_branch(n: Int)
    requires n >= 0
{
    var i: Int := 0;

    loop
        // @CheckError
        invariant i <= n
    {
        i < n =>
            i := i + 1,
        i == n =>
            i := i + 1
    }
}