method FindFirstNegative(a: array<int>) returns (index: int)
  // Precondition: The array must exist (must not be null)
  requires a != null
  
  // Postcondition 1 (If found): The index is valid and the element is negative.
  ensures index >= 0 ==> 0 <= index < a.Length && a[index] < 0
  
  // Postcondition 2 (If found): It must be the FIRST negative: all elements before it must be non-negative.
  ensures index >= 0 ==> (forall k :: 0 <= k < index ==> a[k] >= 0)
  
  // Postcondition 3 (If not found): The index is -1, and the entire array is non-negative.
  ensures index < 0 ==> index == -1 && (forall k :: 0 <= k < a.Length ==> a[k] >= 0)
{
  var i := 0;
  
  while i < a.Length
    // Loop Invariant (Partial Correctness):
    // - The loop counter is in bounds.
    invariant 0 <= i <= a.Length
    // - All elements scanned so far (from 0 up to i-1) are non-negative.
    invariant forall k :: 0 <= k < i ==> a[k] >= 0
    
    // Loop Variant (Total Correctness):
    // - The number of elements left to check strictly decreases.
    decreases a.Length - i
  {
    if a[i] < 0 {
      return i;
    }
    i := i + 1;
  }
  return -1;
}

