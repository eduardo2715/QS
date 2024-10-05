//Ex1

method arrIncre(arr: array<int>)
ensures forall k :: 0<=k<arr.Length ==> arr[k] == old(arr[k]) + 1
modifies arr //antiframe (tudo o que é modado)
{
    var idx:=0;
    while(idx<arr.Length)
    invariant 0<=idx<=arr.Length
    invariant forall k ::0<=k<idx ==> arr[k] == old(arr[k]) + 1
    invariant forall k ::idx<=k<arr.Length ==> arr[k] == old(arr[k])
    {
        arr[idx]:=arr[idx]+1;
        idx:=idx + 1;
    }

}