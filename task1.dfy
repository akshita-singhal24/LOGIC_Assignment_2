method Abs(x: int) returns (x': int)
  // Postcondition 1: The result must be non-negative
  ensures x' >= 0
  // Postcondition 2: The result matches the input logic
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
  // Test 1: Positive input (Expected Output: 5)
  var result1 := Abs(5);
  print "Abs(5) = ", result1, "\n";

  // Test 2: Negative input (Expected Output: 12)
  var result2 := Abs(-12);
  print "Abs(-12) = ", result2, "\n";
}