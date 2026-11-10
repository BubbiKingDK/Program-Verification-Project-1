method client() {
    var sum: Int := 0;

    for i in 0..10 {
        sum := sum + i
    };
    // @CheckError
    assert sum > 45
} 