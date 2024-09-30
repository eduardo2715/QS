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
  requires Valid() && s.Valid()  // Both sets must be valid before performing the union
  ensures r.Valid()  // The resulting set must be valid
  ensures r.content == this.content + s.content  // The content of the result should be the union of both sets' contents
{
    r := new Set();  // Start with an empty set

    // Add elements from the current set (this) to r
    var current := this.list;

    ghost var remaining := this.content;  // Tracks the elements that are yet to be processed
    while current != null
      invariant current == null || current.Valid()  // current should either be null or a valid node
      invariant r.Valid()  // r should remain valid during the loop
      invariant r.content == this.content - remaining  // r.content is exactly what has been processed from this set
      invariant current == null || current.val in remaining  // Every node's value must be in the remaining set
      invariant remaining <= this.content  // Remaining is always a subset of this.content
      decreases |remaining|  // The size of the remaining set decreases
    {
      // Check if the current value is already in r's content
      var inside := r.mem(current.val);
      if (!inside) {
        r.add(current.val);  // Add only if it's not already in r
      }

      // Update remaining set and move to the next node
      remaining := remaining - {current.val};
      current := current.next;  // Move to the next node
    }

    // Add elements from the input set s to r
    var other := s.list;
    while other != null
      invariant other == null || other.Valid()  // other should either be null or a valid node
      invariant r.Valid()  // r should remain valid during the loop
      invariant r.content <= this.content + s.content  // r's content should grow to include elements from both sets
      decreases other
    {
      // Check if the value is already in r's content before adding
      var inside := r.mem(other.val);
      if (!inside) {
        r.add(other.val);  // Add the current node's value to r only if it isn't already present
      }
      other := other.next;  // Move to the next node
    }
}



/*   method inter(s : Set) returns (r : Set)
    {
      
      r := s;
    } */

    
  }

}

