method FindFirstNegative(a: array<int>) returns (index: int)
    requires a != null
    ensures index >= 0 ==> 0 <= index < a.Length && a[index] < 0
    ensures index >= 0 ==> (forall k :: 0 <= k < index ==> a[k] >= 0)
    ensures index < 0 ==> index == -1 && (forall k :: 0 <= k < a.Length ==> a[k] >= 0)
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        // MISSING: correctness invariant for scanned elements!
        //invariant forall k :: 0 <= k < i ==> a[k] >= 0
        decreases a.Length - i
    {
        if a[i] < 0 {
            return i;
        }
        i := i + 1;
    }
    return -1;
}

method Main()
{
    var arr := new int[3];
    arr[0] := -5; arr[1] := 4; arr[2] := -2;
    var idx := FindFirstNegative(arr);
    assert idx == 0; // This will NOT VERIFY
    print "First negative index: ", idx, "\n";
}
