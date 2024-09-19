method noRepetitionsQuadratic(arr : array<nat>) returns (b: bool) 
  requires arr.Length >= 0 
  requires forall k :: 0 <= k < arr.Length ==> arr[k] >= 0 // All elements in arr are natural numbers
  ensures b == (forall i, j :: 0 <= i < j < arr.Length ==> arr[i] != arr[j])
  
 {
  var i := 0; 
  b := true; 

  while (i < arr.Length) 
  invariant 0 <= i <= arr.Length //i is between 0 and the size of the array
  invariant forall m, n :: 0 <= m < i && 0 <= n < i && m != n ==> arr[m] != arr[n] //all elements behind i are different 
  {

    var v := arr[i];   
    var j := 0;
  
    while (j < arr.Length)
    invariant 0 <= j <= arr.Length //j is between 0 and the size of the array
    invariant forall k :: 0 <= k < j ==> k != i ==> arr[k] != arr[i] //all elements behind j are different to i
    {
      var u := arr[j]; 
      if ((j != i) && (u == v)) {
        b := false; 
        return; 
      }
      j := j+1;
    }
    i := i+1; 
  }
}


method test()
{
  var arr := new nat[3](i => i+1);/* (_ => 1); */
  var b:=noRepetitionsQuadratic(arr);
  assert b == true;
  var arr2 := new nat[3](_ => 1);/* (_ => 1); */
  var b2:=noRepetitionsQuadratic(arr2);
  assert b2 == false;
}



method noRepetitionsLinear(arr: array<nat>) returns (b: bool)
  requires arr.Length >= 0
  requires forall k :: 0 <= k < arr.Length ==> 0 <= arr[k] < 1000
  ensures b == (forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i != j ==> arr[i] != arr[j])
{
  var seen: array<nat> := new nat[1000](_ => 10000); //arbitrary big number
  var i := 0;
  b := true;

  while (i < arr.Length)
    invariant 0 <= i <= arr.Length
    invariant forall k :: 0 <= k < i ==> seen[arr[k]] == arr[k]
    invariant b == true
  {
    var v := arr[i];
    if (seen[v] != 10000) {
      b := false;
      return;
    }
    seen[v] := arr[i];
    i := i + 1;
  }
  return;
}



method test2()
{
  var arr := new nat[3](i => i+1);/* (_ => 1); */
  var b:=noRepetitionsLinear(arr);
  assert b == true;
  var arr2 := new nat[3](_ => 1);/* (_ => 1); */
  var b2:=noRepetitionsLinear(arr2);
  assert b2 == false;
}


