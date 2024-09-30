
//specification should not leak implementation details 

class   PVNode   {
    var   data   :   int
    var   pri   :   int
    var   next   :   PVNode?
    ghost   var   pvlist   :   seq <( int , int ) >
    ghost   var   footprint   :   set < PVNode >

    ghost function Valid() : bool
       reads this, footprint
    {
    if next == null
    then this.pvlist == [(data, pri)] && this.footprint == {this}
    else 
    next in footprint
    && pvlist == [(data, pri)] + next.pvlist
    && footprint == {this} + next.footprint
    && this !in next.footprint
    && sortedPVList(pvlist)
    && next.Valid()
    

    }

    constructor (p : int, v : int)
    ensures Valid()
        && footprint == {this}
        && pvlist == [(v,p)]
    {
        this.pri := p;
        this.data:= v;
        this.next:= null;
        this.pvlist := [(v,p)];
        this.footprint := {this};
    }

    method insertPVPair ( p :   int , v : int ) returns (r:PVNode )
    requires Valid () && p>=0
    ensures Valid () && r.Valid()
    ensures r.pvlist[0].1 <= max(p, old(this.pvlist[0].1))
    ensures fresh(r.footprint - old(this.footprint))


    modifies footprint
    decreases footprint
    {
        if(p <= this.pri){
            r:=new PVNode(p,v);
            r.next:= this;
            r.pvlist:= [(v,p)] + this.pvlist;
            r.footprint:={r} + this.footprint;
            return;
        }else{
            r:=this;
            if(this.next == null){
                var aux := new PVNode(p,v);
                this.next:=aux;
                this.pvlist:=[(this.data, this.pri), (v,p)];
                this.footprint:={this, aux};
                return;
            }else{
                assert this.pri == this.pvlist[0].1;
                assert next.pri == this.pvlist[1].1;
                var aux := this.next.insertPVPair(p,v);
                this.next:=aux;
                this.pvlist:=[(this.data, this.pri)] + aux.pvlist;
                this.footprint:={this} + aux.footprint;
                return;
            }
        }
    }

}

function sortedPVList(pvlist: seq<(int, int)>):bool{
    forall i,j :: 0<=i<=j<|pvlist| ==> pvlist[i].1 <= pvlist[j].1
}

function max(x:int, y:int):int{
    if x <= y
    then y
    else x
}




