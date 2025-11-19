// Helper mathematical definition for verification (Specification Function)
function Fact(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else n * Fact(n - 1)
}

method Factorial(n: int) returns (res: int)
  // Precondition: Input must be non-negative
  requires n >= 0
  // Postcondition: The result equals the mathematical factorial of n
  ensures res == Fact(n)
{
  res := 1;
  var i := 0;
  
  while i < n
    // Loop Invariant (Partial Correctness):
    // 1. Loop counter is within bounds
    invariant 0 <= i <= n
    // 2. 'res' currently holds the factorial of 'i'
    invariant res == Fact(i)
    
    // Loop Variant (Total Correctness):
    // The distance to the target 'n' decreases by 1 each loop.
    decreases n - i
  {
    i := i + 1;
    res := res * i;
  }
}

// Optional: Add a Main method for execution proof
method Main()
{
  var res5 := Factorial(5);
  print "Factorial of 5 is: ", res5, "\n"; // Expected: 120

  var res0 := Factorial(0);
  print "Factorial of 0 is: ", res0, "\n"; // Expected: 1
}