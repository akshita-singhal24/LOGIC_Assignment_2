function method Fact(n: int): int
    requires n >= 0
{
    if n == 0 then 1 else n * Fact(n - 1)
}

method Factorial(n: int) returns (res: int)
    requires n >= 0
    ensures res == Fact(n)
{
    res := 1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant res >= 1 // TOO WEAK: doesn't guarantee factorial
        // the correct is: invariant res == Fact(i)
        decreases n - i
    {
        i := i + 1;
        res := res * i;
    }
}

method Main()
{
    var f := Factorial(3);
    assert f == 6; // This will NOT VERIFY
    print "Factorial(3) = ", f, "\n";
}
