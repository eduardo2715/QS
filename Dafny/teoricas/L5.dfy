function incrListF(s : seq<int>) : seq<int> 
    decreases s 
  {
    if (s == []) 
      then [] 
      else [ s[0] + 1 ] + incrListF(s[1..])
  }



class Node {
  ghost var list : seq<int>
  ghost var footprint : set<Node>

  var data : int
  var next : Node? 

  ghost function Valid() : bool 
    reads this, footprint
    decreases footprint
  {
    (this in footprint) &&
    ((next == null) ==> list == [ data ] && footprint =={this}) &&
    ((next != null) ==> 
      (next in footprint) && 
      footprint == next.footprint + { this } && 
      (this !in next.footprint) &&
      list == [ data ] + next.list &&
      next.Valid())
  }


  constructor (val : int) 
    ensures Valid() 
      && next == null && list == [ data ] 
      && footprint == { this } 
      && val == data 
  {
    this.data := val; 
    this.next := null; 
    this.list := [ val ]; 
    this.footprint := { this };
  } 

  method countRec () returns (r : int) 
    requires Valid() 
    ensures (r == |list|) 
    decreases footprint  
  {
    if (this.next == null) {
      r := 1;
    } else {
      r := this.next.countRec(); 
      r := 1 + r; 
    }

  }

   method countIter() returns (r : int)
    requires Valid()
    ensures (r == |list|) 
  {
    r := 1;
    var cur := this.next;  

    while (cur != null) 
      invariant cur != null ==> cur.Valid()
      invariant cur == null ==> |list| == r 
      invariant cur != null ==> |list| == r + |cur.list|
      decreases |list| - r
    {
      r := r + 1; 
      cur := cur.next;

    }
    return;
  }

method countIter2() returns (r : int)
    requires Valid()
    ensures (r == |list|) 
  {
    r := 1;
    var cur := this;  

    while (cur.next != null)
      invariant cur != null
      invariant cur.Valid() 
      invariant r == |this.list|-|cur.list|+1
      decreases cur.footprint
    {
      r := r + 1; 
      cur := cur.next;

    }
    return;
  }



  method copyListRec () returns (r : Node)
    requires Valid()
    ensures r.Valid() && Valid()
    ensures fresh(r.footprint)
    ensures r.list == this.list 
    decreases this.footprint 
  {
      
    r := new Node(this.data);
    if (this.next != null) {
      var aux := this.next.copyListRec(); 
      r.next := aux; 
      r.list := [ r.data ] + aux.list; 
      r.footprint := { r } + aux.footprint;
    }
  }


  method incrListIP () 
    requires Valid()
    ensures Valid() && this.footprint == old(this.footprint)
    ensures this.list == incrListF(old(this.list))
    decreases footprint
    modifies footprint
  {

    ghost var old_lst := this.list;
    if (next == null) {
      this.data := this.data + 1; 
      this.list := [ this.data ]; 
    } else {
      ghost var next_lst := next.list;
      ghost var next_footprint := next.footprint; 
      ghost var incr_next_lst := incrListF(next_lst);
  
      next.incrListIP();
      assert next.list == incr_next_lst;

      this.data := this.data + 1;   
      this.list := [ this.data ] + this.next.list;
      assert this.Valid();
    }  
  }


}