//Ex4

method copyArray(arr : array<int>) returns (r:array<int>)
ensures arr[..] == r[..]

{
    r:= new int [arr.Length](_=>0);
    var idx:= 0;
    while(idx < arr.Length)
    invariant 0<=idx<=arr.Length
    invariant arr[..idx] == r[..idx]
    decreases arr.Length - idx
    {
        r[idx] := arr[idx];
        idx:=idx+1;
    }
}