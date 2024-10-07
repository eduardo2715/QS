method noRepetitionsQuadratic(arr : array<nat>) returns (b: bool) 
  requires arr.Length >= 0 
  ensures b == true <==> forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i !=j ==> arr[i] != arr[j]

 {
  var i := 0; 
  b := true; 

  while (i < arr.Length) 
  invariant 0 <= i <= arr.Length 
  invariant forall m, n :: 0 <= m < i && 0 <= n < i && m != n ==> arr[m] != arr[n] 
  {

    var v := arr[i];   
    var j := 0;
  
    while (j < arr.Length)
    invariant 0 <= j <= arr.Length 
    invariant forall k :: 0 <= k < j ==> k != i ==> arr[k] != arr[i] 
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
  var arr := new nat[4];
  arr[0], arr[1], arr[2], arr[3] := 1, 2, 3, 4; 
  var b:=noRepetitionsQuadratic(arr);
  assert b == true;
  var arr2 := new nat[4]; 
  arr2[0], arr2[1], arr2[2], arr2[3] := 2, 2, 3, 4;
  var b2:=noRepetitionsQuadratic(arr2);
  assert arr2[0] == arr2[1];
  assert b2 == false;

}


method noRepetitionsLinear(arr: array<nat>) returns (b: bool)
  requires arr.Length >= 0  
  ensures b == true ==> forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i != j ==> arr[i] != arr[j]
  ensures b == false ==> exists i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i != j && arr[i] == arr[j]
{
  var i := 0;
  var p := 0;
  var max := 0;

  while (p < arr.Length)
    invariant 0 <= p <= arr.Length  
    invariant forall k :: 0 <= k < p ==> max >= arr[k]  
  {
    if (arr[p] > max) {
      max := arr[p];  
    }
    p := p + 1;
  }

  
  var seen: array<bool> := new bool[max + 1](_ => false);  
  b := true;

  
  while (i < arr.Length)
    invariant 0 <= i <= arr.Length  
    invariant forall k :: 0 <= k < i ==> 0 <= arr[k] <= max
    invariant forall j :: (exists k :: 0 <= k < arr.Length && arr[k] == j) ==> (seen[j] == true <==> exists k2 :: 0 <= k2 < i && arr[k2] == j)
    invariant forall x, y :: 0 <= x < i && 0 <= y < i && x != y ==> arr[x] != arr[y]  
  {
    var v := arr[i];
    
    
    if (seen[v]) {
      b := false;
      return;
    }
    
    
    seen[v] := true;  
    i := i + 1;
  }


  return;
}


method test2()
{
  var arr := new nat[4]; 
  arr[0], arr[1], arr[2], arr[3] := 1, 2, 3, 4; 
  var b:=noRepetitionsLinear(arr);
  assert b == true;
  var arr2 := new nat[4]; 
  arr2[0], arr2[1], arr2[2], arr2[3] := 2, 2, 3, 4; 
  var b2:=noRepetitionsLinear(arr2);
  assert arr2[0] == arr2[1];
  assert b2 == false;
}


