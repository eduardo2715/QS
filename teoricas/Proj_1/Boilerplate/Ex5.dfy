include "Ex3.dfy"

module Ex5 {
  
  import Ex3=Ex3

  class Set {
    var tbl : array<bool>  
    var list : Ex3.Node?

    ghost var footprint : set<Ex3.Node>
    ghost var content : set<nat>

    ghost function Valid() : bool 
      reads this, footprint, this.list, this.tbl
    {
      // Invariant: If the list is non-null, it must be a valid Node list
      // The footprint of the set should match the list's footprint
      if (list == null)
      then 
        footprint == {}
        && 
        content == {}
        &&
        forall i :: 0 <= i < tbl.Length ==> tbl[i] == false
      else
        footprint == list.footprint
        &&
        content == list.content
        && 
        list.Valid()        
        &&
        forall i :: 0 <= i < tbl.Length ==> tbl[i] == (i in content)
    }
      
    constructor (size : nat) 
    ensures Valid()
    ensures Valid() && this.content == {} && this.footprint == {}
    ensures forall i :: 0 <= i < tbl.Length ==> tbl[i] == false
    {
      tbl := new bool[size] (_=>false);  // Initialize array with all false
      list := null;
      footprint := {};
      content := {};
    }


    method mem(v: nat) returns (b: bool)
      requires v < tbl.Length  // Ensure the value is within the bounds of the array
      requires Valid()
      ensures Valid()
      ensures b == (v in content)
    {
      // Check constant-time membership from the array
      b := tbl[v];
      assert b == (v in content);
    }

    
    method add(v: nat)
      requires v < tbl.Length
      requires Valid()
      ensures Valid()
      ensures content == old(content) + {v}
      modifies tbl, this
    {
      if (!tbl[v]) {
        // Update the membership array
        tbl[v] := true;

        // Add the element to the linked list
        if (list == null) {
          list := new Ex3.Node(v);
        } else {
          var newNode := list.add(v);  // Add to the front of the list
          list := newNode;
        }

        // Update ghost fields
        content := content + {v};
        footprint := if list == null then {} else list.footprint;
      }
    }

    method union(s : Set) returns (r : Set)
    {
    }

    method inter(s : Set) returns (r : Set)
    {
    }

  }

}