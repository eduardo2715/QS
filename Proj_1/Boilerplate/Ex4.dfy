include "Ex3.dfy"

module Ex4 {
  import Ex3=Ex3

  class Set {
    var list : Ex3.Node?

    ghost var footprint : set<Ex3.Node>
    ghost var content : set<nat>

    ghost function Valid() : bool 
      reads this, footprint, this.list
    {
      if (this.list == null)
        then 
          footprint == {}
          &&
          content == {}
        else 
          footprint == list.footprint
          &&
          content == list.content
          &&
          list.Valid()
    }

    constructor () 
      ensures Valid() && this.content == {} && this.footprint == {}
    {
      list := null; 
      footprint := {}; 
      content := {};      
    }


    method mem(v: nat) returns (b: bool)
      requires Valid()
      ensures b == (v in this.content)
    {
      if this.list == null {
        b := false;
      } else {
        b := this.list.mem(v);  // Reuse the 'mem' method from the Node class
      }
    }


    method add(v: nat)
      requires Valid()
      ensures Valid()
      ensures this.content == old(this.content) + {v}
      modifies this
    {
      if this.list == null {
        // The set is empty, so create the first node
        this.list := new Ex3.Node(v);
        this.content := {v};
        this.footprint := {this.list};
      } else {
        // Use the `add` method from Node to add the value `v`
        var inside := this.mem(v);
        if !inside{
          var newNode := this.list.add(v);
          this.list := newNode;
          
          // Update ghost fields
          this.content := this.content + {v};
          this.footprint := newNode.footprint;
        }
      }
    }



    method union(s: Set) returns (r: Set)
      requires Valid() && s.Valid()
      ensures r.Valid()
      ensures r.content == this.content + s.content
    {
        r := new Set();

        // First, add elements from `this` to `r`
        var current := this.list;
        ghost var seen :set<int> := {};
        while current != null
          invariant r.Valid()
          invariant current != null ==> current.Valid()
          invariant current != null ==> this.content == seen + current.content
          invariant current == null ==> this.content == seen
          invariant r.content == seen
          decreases if (current != null) then current.footprint else {}
        {
          // Check if the current value is already in `r`
          var inside := r.mem(current.val);
          if (!inside) {
            r.add(current.val);
          }

          seen := seen + {current.val};
          current := current.next;
        }
        assert this.content == seen;

        // Now, add elements from `s` to `r`
        var other := s.list;

        ghost var seen2 :set<int> := {};
        while other != null
          invariant r.Valid()
          invariant other != null ==> other.Valid()
          invariant other != null ==> s.content == seen2 + other.content
          invariant other == null ==> s.content == seen2
          invariant r.content == this.content + seen2
          decreases if (other != null) then other.footprint else {}
        {
          // Check if the current value is already in `r`
          var inside := r.mem(other.val);
          if (!inside) {
            r.add(other.val);
          }

          seen2 := seen2 + {other.val};
          other := other.next;
        }

        //assert r.content == seen + seen2;

    }



    method inter(s: Set) returns (r: Set)
      requires Valid() && s.Valid()
      ensures r.Valid()
      ensures r.content == this.content * s.content  // Intersection of this and s
    {
      r := new Set();  // Create a new set for the intersection result

      var current := this.list;  // Start with the elements in 'this' set
      ghost var seen : set<nat> := {};  // Tracks elements we've processed from 'this'

      // Loop through each element in 'this'
      while current != null
        invariant r.Valid()
        invariant current != null ==> current.Valid()
        invariant this.content == seen + (if current != null then current.content else {})
        //invariant r.content == seen * s.content  // Ensure that r.content is the intersection
        decreases if (current != null) then current.footprint else {}
      {
        var inOther := s.mem(current.val);  // Check if current element is in set 's'
        if inOther {  
          r.add(current.val);  // Add to result if it is present in both sets

          // Update ghost fields explicitly
          r.content := r.content + {current.val};  // Track the added element
        }
        seen := seen + {current.val};  // Mark the current element as seen
        current := current.next;  // Move to the next node
      }
    }

  }
}

