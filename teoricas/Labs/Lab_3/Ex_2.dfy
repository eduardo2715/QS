//Ex2

function sortedS(s:seq<int>):bool
{
forall k1, k2 :: 0<=k1<=k2<|s| ==> s[k1]<=s[k2]
}

method BinSearch(arr:array<int>, v:int) returns (z:int)
requires sortedS(arr[..])
ensures z>=0 ==> 0<=z<arr.Length && arr[z] == v
ensures z<0 ==> forall i :: 0<=i<arr.Length ==> arr[i] != v
    
{
    var l:=0; 
    var r:= arr.Length - 1;

    while (r>=l)
    invariant 0<=l<=r+1<=arr.Length
    invariant forall i:: 0<=i<l ==> arr[i] < v
    invariant forall i:: r<i<arr.Length ==> arr[i] > v
    decreases r - l
    {
        var m :=(l+r)/2;
        var u := arr[m];
        if(u==v){z:=m;return;}
        if(u>v){r:=m-1;}
        if(u<v){l:=m + 1;}
    }
    z:=-1;return;
}