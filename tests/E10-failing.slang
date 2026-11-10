method m(x: Int): Int
    requires x >= 0
    // @CheckError
    ensures result == x
{
    var y: Int := 0;
    match {
      x > 0 => return 0,
      true  => y := x
    };
    return y
}