/* 

array(mutavel)        arr
sequences(imutavel)     seq

arr[..] -> squencia de valores contidos no array

*/

//Ex1

method linearsearch (arr: array<int>, v:int) returns (r:int)
ensures r >= 0 ==> 0 <= r < arr.Length && arr[r] == v
ensures r < 0 ==> forall i:: 0 <= i < arr.Length ==> arr[i] != v
{
    var idx:=0;
    while(idx<arr.Length)
    invariant 0<=idx<=arr.Length
    invariant forall i:: 0 <= i < idx ==> arr[i]!=v
    decreases arr.Length-idx
    {
        if(arr[idx]==v){
            r:=idx;
            return;
        }
        idx:=idx+1;
    }
    r:=-1;
    return;
}