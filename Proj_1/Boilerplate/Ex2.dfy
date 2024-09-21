method noRepetitionsQuadratic(arr : array<nat>) returns (b: bool) 
  requires arr.Length >= 0 
  ensures b == (forall i, j :: 0 <= i < j < arr.Length ==> arr[i] != arr[j])
  //ensures b == true ==> forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length ==> arr[i] != arr[j]
  ensures b == false ==> exists i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && arr[i] == arr[j]

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


/* method test()
{
  var arr := new nat[4]; // Create an array of length 4
  arr[0], arr[1], arr[2], arr[3] := 1, 2, 3, 4; // Populate the array
  var b:=noRepetitionsQuadratic(arr);
  assert b == true;
  var arr2 := new nat[4]; // Create an array of length 4
  arr2[0], arr2[1], arr2[2], arr2[3] := 2, 2, 3, 4; // Populate the array
  var b2:=noRepetitionsQuadratic(arr2);
  assert b2 == false;
} */


method noRepetitionsLinear(arr: array<nat>) returns (b: bool)
  requires arr.Length >= 0  // The array has a non-negative length
  ensures b == true ==> forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i != j ==> arr[i] != arr[j]
  ensures b == false ==> exists i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i != j && arr[i] == arr[j]
{
  var i := 0;
  var p := 0;
  var max := 0;

  // Correct calculation of the maximum value in the array
  while (p < arr.Length)
    invariant 0 <= p <= arr.Length  // Loop variable `p` is within bounds
    invariant forall k :: 0 <= k < p ==> max >= arr[k]  // max should be greater than or equal to all seen values
  {
    if (arr[p] > max) {
      max := arr[p];  // Update max if a larger element is found
    }
    p := p + 1;
  }

  // Create a 'seen' array with size 'max + 1' 
  var seen: array<bool> := new bool[max + 1](_ => false);  // Initialize `seen` array with false for all indices
  b := true;

  // Check for repetitions
  while (i < arr.Length)
    invariant 0 <= i <= arr.Length  // Loop variable `i` is within bounds
    invariant forall k :: 0 <= k < i ==> 0 <= arr[k] <= max  // All processed values are within bounds of `seen`
    invariant forall j :: (exists k :: 0 <= k < arr.Length && arr[k] == j) ==> (seen[j] != false <==> exists k2 :: 0 <= k2 < i && arr[k2] == j)
    invariant forall x, y :: 0 <= x < i && 0 <= y < i && x != y ==> arr[x] != arr[y]  // All elements in `arr` up to `i` are distinct
  {
    var v := arr[i];
    
    // Ensure we are accessing within bounds of 'seen'
    assert 0 <= v <= max;  // `v` is within bounds of the `seen` array
    
    // Check if the value has been seen before
    if (seen[v]) {
      b := false;
      return;
    }
    
    // Mark `v` as seen
    seen[v] := true;  // Mark the value `v` as seen
    i := i + 1;
  }

  // Ensure the postcondition when b == true
  if (b) {
    assert forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i != j ==> arr[i] != arr[j];
  }

  return;
}


/* method test2()
{
  var arr := new nat[4]; // Create an array of length 4
  arr[0], arr[1], arr[2], arr[3] := 1, 2, 3, 4; // Populate the array
  var b:=noRepetitionsLinear(arr);
  assert b == true;
  var arr2 := new nat[4]; // Create an array of length 4
  arr2[0], arr2[1], arr2[2], arr2[3] := 2, 2, 3, 4; // Populate the array
  var b2:=noRepetitionsLinear(arr2);
  assert b2 == false;
} */


