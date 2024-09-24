
module Ex3 {

  class Node {

    var val : nat
    var next : Node?

    ghost var footprint : set<Node>
    ghost var content : set<nat> 

    ghost function Valid() : bool 
      reads this, this.footprint 
      decreases footprint
    {
      this in this.footprint 
      &&
      if (this.next == null)
        then 
          this.footprint == { this }
          && 
          this.content == { this.val }
        else 
          this.next in this.footprint
          &&
          this !in this.next.footprint
          &&      
          this.footprint == { this } + this.next.footprint 
          &&
          this.content == { this.val } + this.next.content
          &&
          this.next.Valid()
    }

    constructor (v : nat) 
    ensures Valid() 
      && next == null && content == {val} 
      && footprint == { this } 
      && v == val 
    {
      this.val := v;
      this.next := null;
      this.content := {v};
      this.footprint := {this};
    }

    method add(v: nat) returns (r: Node)
    requires Valid()
    ensures r.Valid()
    ensures r.val == v
    ensures r.next == this
    ensures r.content == {v} + this.content
    ensures r.footprint == {r} + this.footprint
    {
      r := new Node(v);
      r.next := this;
      r.content := {v} + this.content;
      r.footprint := {r} + this.footprint;
    }

    method mem(v: nat) returns (b: bool)
    requires Valid()
    ensures b == (v in this.content)
    decreases this.footprint
    {
      if (this.val == v) {
        b := true;
      } else if (this.next == null) {
        b := false;
      } else {
        b := this.next.mem(v);  // Recursively check the next node
      }
    }


    method copy() returns (n : Node)
    requires Valid()
    ensures n.Valid() && Valid()
    ensures fresh(n.footprint)
    ensures n.content == this.content 
    decreases this.footprint 
    {
      n := new Node(this.val);
      if (this.next != null) {
        var aux := this.next.copy(); 
        n.next := aux; 
        n.content := { n.val } + aux.content; 
        n.footprint := { n } + aux.footprint;
      }
    }

  }
}
