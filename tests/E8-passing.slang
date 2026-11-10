method sumn(n: Int)
    requires n >= 0
{
    var sum: Int := 0;
    var i: Int := 0;

    loop
        invariant i >= 0
        invariant i <= n
        invariant sum == i * (i + 1) / 2
        decreases n - i
    {
        i < n =>
            i := i + 1;
            sum := sum + i
    };

    assert i == n;
    assert sum == n * (n + 1) / 2
} 