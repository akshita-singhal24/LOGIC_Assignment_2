method Abs(x: int) returns (x': int)
    ensures x' >= 0
    ensures (x >= 0 ==> x' == x) && (x < 0 ==> x' == -x)
{
    if x < 0 {
        x' := -x;
    } else {
        x' := x;
    }
}

method Main()
{
    var result1 := Abs(5);
    print "Abs(5) = ", result1, "\n";

    var result2 := Abs(-12);
    print "Abs(-12) = ", result2, "\n";
}
