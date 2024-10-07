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
        b := this.list.mem(v);
      }
    }


    method add(v: nat)
      requires Valid()
      ensures Valid()
      ensures this.content == old(this.content) + {v}
      modifies this
      {
      if this.list == null {
        this.list := new Ex3.Node(v);
        this.content := {v};
        this.footprint := {this.list};
      } else {
        var inside := this.mem(v);
        if !inside{
          var newNode := this.list.add(v);
          this.list := newNode;
          
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
          var inside := r.mem(current.val);
          if (!inside) {
            r.add(current.val);
          }

          seen := seen + {current.val};
          current := current.next;
        }

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
          var inside := r.mem(other.val);
          if (!inside) {
            r.add(other.val);
          }

          seen2 := seen2 + {other.val};
          other := other.next;
        }

    }



    method inter(s: Set) returns (r: Set)
      requires Valid() && s.Valid()
      ensures r.Valid()
      ensures r.content == this.content * s.content  
    {
      r := new Set();  

      var current := this.list;  
      ghost var seen : set<nat> := {};  

      while current != null
        invariant this.Valid()
        invariant r.Valid()
        invariant current != null ==> current.Valid()
        invariant this.content == seen + (if current != null then current.content else {})
        invariant r.content == seen * s.content  
        decreases if (current != null) then current.footprint else {}
      {
        var inOther := s.mem(current.val);  
        if inOther {  
          r.add(current.val);  

          r.content := r.content + {current.val};
        }
        seen := seen + {current.val};
        current := current.next;  
      }
    }

  }
}

