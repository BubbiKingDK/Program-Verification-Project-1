method m(x: Int) {
    var y: Int := x;
    // @CheckError
    loop y < 10 {
        y := y + 1
    };

    assert y >= 10
} 
