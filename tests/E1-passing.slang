method client() {
    var sum: Int := 0;

    for i in 0..10 {
        sum := sum + i
    };

    assert sum == 45
}