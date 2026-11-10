method sumn(n: Int): Int
    requires n >= 0
    ensures result == n * (n + 1) / 2
{
    var acc: Int := 0;
    var i: Int := 0;

    loop
        invariant i >= 0
        invariant i <= n
        invariant acc == i * (i + 1) / 2
    {
        i < n =>
            i := i + 1;
            acc := acc + i
    };

    assert i == n;
    assert acc == n * (n + 1) / 2;

    return acc
} 