method client(n: Int)
    requires n >= 0
{
    var sum: Int := 0;

    for i in 1..(n + 1)
        invariant i >= 1
        invariant i <= n + 1
        invariant sum == (i - 1) * i / 2
    {
        sum := sum + i
    };

    assert sum == n * (n + 1) / 2
}