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
      ensures tbl.Length == size + 1
    {
      tbl := new bool[size + 1] (_=>false);  
      list := null;
      footprint := {};
      content := {};
    }


    method mem(v: nat) returns (b: bool)
      requires v < tbl.Length  
      requires Valid()
      ensures Valid()
      ensures b == (v in content)
    {      b := tbl[v];
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
        tbl[v] := true;

        if (list == null) {
          list := new Ex3.Node(v);
        } else {
          var newNode := list.add(v);  
          list := newNode;
        }

        content := content + {v};
        footprint := if list == null then {} else list.footprint;
      }
    }

      method union(s : Set) returns (r : Set)
        requires Valid()
        requires s.Valid()
        ensures r.Valid()
        ensures r.content == s.content + this.content  
    {
        var max;
        if this.tbl.Length >= s.tbl.Length {
          max := this.tbl.Length;
        }else{ max := s.tbl.Length;
        }
        r := new Set(max); 
        assert r.tbl.Length == max + 1;
        assert this.Valid();
        assert s.Valid();


        ghost var seen : set<int> := {}; 
        var current := this.list;
        while current != null
          invariant r.Valid()
          invariant this.tbl.Length <= r.tbl.Length
          invariant current != null ==> forall i :: i in current.content ==> i <  r.tbl.Length 
          invariant current != null ==> current.Valid()
          invariant current != null ==> this.content == seen + current.content
          invariant current == null ==> this.content == seen
          invariant r.content == seen
          invariant current != null ==> r.tbl[current.val] == (current.val in r.content)
          decreases if (current != null) then current.footprint else {}
        {
            if current.val < r.tbl.Length && !r.tbl[current.val] {
                r.add(current.val); 
            }
            seen := seen + {current.val}; 
            current := current.next; 
        }

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
            if other.val < r.tbl.Length && !r.tbl[other.val] {
                r.add(other.val);  
            }
            seen2 := seen2 + {other.val};  
            other := other.next;  
        }


        assert r.content == this.content + s.content;
        assert r.Valid(); 
    }


    method inter(s: Set) returns (r: Set)
        requires Valid()
        requires s.Valid()
        ensures r.Valid()
        ensures r.content == this.content * s.content 
    {
        var max; 
        if this.tbl.Length >= s.tbl.Length {
          max := this.tbl.Length;
        } else {
          max := s.tbl.Length;
        }
        r := new Set(max);  
        assert r.tbl.Length == max + 1;

    
        assert this.Valid();
        assert s.Valid();
    
        ghost var seen : set<int> := {}; 
        var current := this.list;
        while current != null
          invariant r.Valid()
          invariant this.tbl.Length <= r.tbl.Length
          invariant s.tbl.Length <= r.tbl.Length
          invariant current != null ==> forall i:: i in current.content ==> i < r.tbl.Length
          invariant current != null ==> current.Valid()
          invariant current != null ==> this.content == seen + current.content
          invariant current == null ==> this.content == seen
          invariant r.content == seen * s.content 
          invariant current != null ==> r.tbl[current.val] == (current.val in r.content)
          decreases if (current != null) then current.footprint else {}
        {
            if current.val < r.tbl.Length && s.tbl[current.val] && !r.tbl[current.val] {
                r.add(current.val);
            }
            seen := seen + {current.val}; 
            current := current.next; 
        }

        assert r.content == this.content * s.content;
        assert r.Valid();  
    }


  }

  function max(a:int,b:int):int{
    if a >= b
    then a
    else b
  }

function maxUnion(s: array<bool>, t: array<bool>, i: int) : int
  requires 0 <= i <= max(s.Length, t.Length)  // Ensure valid index
  decreases max(s.Length, t.Length) - i
  reads s, t
{
  if i == max(s.Length, t.Length) then
    -1  // Base case: no match found, return -1
  else if i < s.Length && i < t.Length && s[i] && t[i] then
    var nextMax := maxUnion(s, t, i + 1);  // Recursively check the next index
    if nextMax == -1 then i else nextMax  // If no larger match, return current index
  else
    maxUnion(s, t, i + 1)  // Continue searching if no match at current index
}

}