method Abs(x: int) returns (y: int)
    // Only a weak postcondition (not enough to specify abs correctly)
    ensures y >= 0
{
    y := 0; // Intentionally wrong to cause failure
}

method Main()
{
    var v := Abs(3);
    assert v == 3; // This will NOT VERIFY
    print "Abs(3) = ", v, "\n";
}
