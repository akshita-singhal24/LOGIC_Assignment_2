function Trib(n: int): int
    requires n >= 0
{
    if n == 0 then 0
    else if n == 1 then 1
    else if n == 2 then 1
    else Trib(n-1) + Trib(n-2) + Trib(n-3)
}

method Tribonacci(n: int) returns (result: int)
    requires n >= 0
    ensures result == Trib(n)
{
    if n == 0 { return 0; }
    if n == 1 { return 1; }
    if n == 2 { return 1; }

    var a := 0;
    var b := 1;
    var c := 1;
    var i := 2;

    while i < n
        invariant 2 <= i <= n
        // MISSING: invariants a == Trib(i-2), b == Trib(i-1), c == Trib(i)
        decreases n - i
    {
        i := i + 1;
        var next := a + b + c;
        a := b;
        b := c;
        c := next;
    }
    return c;
}

method Main()
{
    var t := Tribonacci(5);
    assert t == 7; // This will NOT VERIFY
    print "Tribonacci(5) = ", t, "\n";
}
