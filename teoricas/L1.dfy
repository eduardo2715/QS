datatype Color = Green | Black | Red

function ColorOrder(c1 : Color, c2 : Color) : bool {
  match c1 {
    case Green => true
    case Black => c2 == Red || c2 == Black 
    case Red => c2 == Red
  }
}

method OrganizeFlag(arr : array<Color>) 
  ensures forall k1, k2 :: 0 <= k1 <= k2 < arr.Length ==> ColorOrder(arr[k1], arr[k2])
  modifies arr 
{

  var g := 0; 
  var b := 0; 
  var r := arr.Length; 

  while (b < r) 
    invariant 0 <= g <= b <= arr.Length
    invariant 0 <= r <= arr.Length 
    invariant forall k :: 0 <= k < g ==> arr[k] == Green
    invariant forall k :: g <= k < b ==> arr[k] == Black 
    invariant forall k :: r <= k < arr.Length ==> arr[k] == Red
  {
    match arr[b] {
      case Green => 
        arr[g], arr[b] := arr[b], arr[g];
        g := g+1; b := b+1; 

      case Black => b := b+1;  

      case Red =>
        arr[b], arr[r-1] := arr[r-1], arr[b];
        r := r-1;    
    }
  }

} 