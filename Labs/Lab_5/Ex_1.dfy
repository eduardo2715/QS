
class Node {

    var val : int
    var next : Node?

    ghost var footprint : set<Node>
    ghost var list : seq<int> 

    ghost function Valid() : bool 
        reads this, footprint 
        decreases footprint
    {
        if (this.next == null)
        then 
            this.list == [this.val ]
            && 
            this.footprint == { this }
        else 
            this.next in footprint
            &&           
            this.list == [this.val]  + this.next.list
            &&
            this.footprint == { this } + this.next.footprint 
            &&
            this !in this.next.footprint
            &&
            this.next.Valid()
    }

    constructor (v : int) 
    ensures Valid() 
        && next == null && list == [val] 
        && footprint == { this } 
        && v == val 
    {
        this.val := v;
        this.next := null;
        this.list := [v];
        this.footprint := {this};
    }

    method prepad(i: int) returns (r: Node)
    requires Valid()
    ensures r.Valid()
    ensures r.list == [i] + this.list
    ensures r.footprint == {r} + this.footprint
    && fresh(r)
    {
      r := new Node(i);
      r.next := this;
      r.list := [i] + this.list;
      r.footprint := {r} + this.footprint;
    }


}
