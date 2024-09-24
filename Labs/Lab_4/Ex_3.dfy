//Ex3

method partition(arr : array < int >) returns (i:int, v:int)
requires arr.Length > 0
ensures 0<=i<arr.Length
ensures forall k :: 0<=k<i ==> arr[k] <= v
ensures forall k :: i<k<arr.Length ==> arr[k] > v
ensures arr[i] == v
ensures multiset(arr[..]) == multiset(old(arr[..]))

modifies arr
{
    var j:=0;
    v:= arr[arr.Length - 1];
    i:=0;

    while(j<arr.Length - 1)
    invariant 0<= i <= j < arr.Length
    invariant forall k :: 0<=k<i ==> arr[k] <= v
    invariant forall k :: i<=k<j ==> arr[k] > v
    invariant arr[arr.Length - 1] == v
    invariant multiset(arr[..]) == multiset(old(arr[..]))

    
    {
        if(arr[j] <= v)
        {
            arr[i] , arr[j] := arr[j], arr[i];
            i:=i+1;
        }
        j:=j+1;
    }
    arr[i] , arr[j] := arr[j], arr[i];
}