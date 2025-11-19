// =========================
// SPECIFICATION
// =========================

function Trib(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else if n == 2 then 1
  else Trib(n-1) + Trib(n-2) + Trib(n-3)
}

// =========================
// IMPLEMENTATION
// =========================

method Tribonacci(n: int) returns (result: int)
  requires n >= 0
  ensures result == Trib(n)
{
  if n == 0 { return 0; }
  if n == 1 { return 1; }
  if n == 2 { return 1; }

  var a := 0; // T(0)
  var b := 1; // T(1)
  var c := 1; // T(2)
  var i := 2;

  while i < n
    invariant 2 <= i <= n
    invariant a == Trib(i-2)
    invariant b == Trib(i-1)
    invariant c == Trib(i)
    decreases n - i
  {
    i := i + 1;
    var next := a + b + c;
    // help verifier
    assert next == Trib(i);
    a := b;
    b := c;
    c := next;
    assert a == Trib(i-2);
    assert b == Trib(i-1);
    assert c == Trib(i);
  }

  assert i == n;
  assert c == Trib(n);
  return c;
}

// =========================
// MAIN METHOD (call methods as statements)
// =========================

method Main()
{
  var t0 := Tribonacci(0);
  print "T(0) = ", t0, "\n";

  var t1 := Tribonacci(1);
  print "T(1) = ", t1, "\n";

  var t2 := Tribonacci(2);
  print "T(2) = ", t2, "\n";

  var t3 := Tribonacci(3);
  print "T(3) = ", t3, "\n";

  var t4 := Tribonacci(4);
  print "T(4) = ", t4, "\n";

  var t5 := Tribonacci(5);
  print "T(5) = ", t5, "\n";
}
