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
        &&
        forall i :: i in this.content ==> i < tbl.Length

    }

    constructor (size : nat)
      ensures Valid()
      ensures Valid() && this.content == {} && this.footprint == {}
      ensures forall i :: 0 <= i < tbl.Length ==> tbl[i] == false
      ensures forall i :: i in this.content ==> i < size
      ensures tbl.Length == size
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
        requires Valid()
        requires s.Valid()
        ensures r.Valid()
        ensures r.content == s.content + this.content  // Union of the two sets
    {
        var max := max(s.tbl.Length, this.tbl.Length);  // Union needs to accommodate both sets
        r := new Set(max);  // Result set initialized to the larger size

        // Reassert `Valid()` to make sure Dafny keeps track of this invariant
        assert this.Valid();
        assert s.Valid();

        // Assert that `this.content` and `s.content` are within their respective `tbl` bounds
        assert forall i :: i in this.content ==> i < this.tbl.Length;
        assert forall i :: i in s.content ==> i < s.tbl.Length;

        // First, add elements from `this` to `r`
        ghost var seen : set<int> := {};  // Keep track of processed elements
        var current := this.list;
        while current != null
          invariant r.Valid()
          invariant this.tbl.Length <= r.tbl.Length
          invariant current != null ==> forall i :: i in current.content ==> i < max
          invariant current != null ==> current.Valid()
          invariant current != null ==> this.content == seen + current.content
          invariant current == null ==> this.content == seen
          invariant r.content == seen
          invariant current != null ==> r.tbl[current.val] == (current.val in r.content)
          decreases if (current != null) then current.footprint else {}
        {
            // Check if the current value is within the bounds of `r`'s table
            if current.val < r.tbl.Length && !r.tbl[current.val] {
                r.add(current.val);  // Add the value to the result set
            }
            seen := seen + {current.val};  // Mark the value as seen
            current := current.next;  // Move to the next node
        }

        // Now, add elements from `s` to `r`
        var other := s.list;
        ghost var seen2 : set<int> := {};
        while other != null
          invariant r.Valid()
          invariant other != null ==> other.Valid()
          invariant other != null ==> s.content == seen2 + other.content
          invariant other == null ==> s.content == seen2
          invariant r.content == this.content + seen2
          invariant other != null ==> r.tbl[other.val] == (other.val in r.content)
          decreases if (other != null) then other.footprint else {}
        {
            // Check if the current value is within the bounds of `r`'s table
            if other.val < r.tbl.Length && !r.tbl[other.val] {
                r.add(other.val);  // Add the value to the result set
            }
            seen2 := seen2 + {other.val};  // Mark the value as seen
            other := other.next;  // Move to the next node
        }

        // After both loops, `r` should have the union of both sets
        assert r.content == this.content + s.content;
        assert r.Valid();  // Ensure the result set is valid
    }




    method inter(s : Set) returns (r : Set)
    {
    }

  }

  function max(a:int,b:int):int{
    if a >= b
    then a
    else b
  }
}
