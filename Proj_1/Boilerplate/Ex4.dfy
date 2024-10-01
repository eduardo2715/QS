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
      ensures v in this.content  // Ensure the set contains v after the method
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

        while current != null
          invariant r.Valid()
          invariant r.content <= this.content
          invariant current == null || current.val in this.content
          decreases current
        {
          // Check if the current value is already in `r`
          var inside := r.mem(current.val);
          if (!inside) {
            r.add(current.val);
          }
          current := current.next;
        }

        // Now, add elements from `s` to `r`
        var other := s.list;

        while other != null
          invariant r.Valid()  // `r` should remain valid
          invariant r.content <= this.content + s.content
          invariant other == null || other.val in s.content
          decreases other
        {
          
          var inside := r.mem(other.val);
          if (!inside) {
            r.add(other.val);
          }
          other := other.next;
        }
    }






/*   method inter(s : Set) returns (r : Set)
    {
      
      r := s;
    } */

    
  }

}

