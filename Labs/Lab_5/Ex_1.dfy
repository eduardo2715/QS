function filter(s: seq<int>):seq<int>
{
    if (s == [])
        then []
        else if s[0] < 0
                then filter(s[1..])
                else [s[0]] + filter(s[1..])
}



class Node {

    var val : int
    var next : Node?

    ghost var footprint : set<Node> //atributos
    ghost var list : seq<int>       //usados para justificação

    ghost function Valid() : bool //apenas serve para justificação
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

    method append(i:int)
    requires Valid()
    ensures this.list == old(this.list) + [i]
    && fresh(footprint - old(footprint))

    decreases footprint
    modifies footprint
    {
        if(this.next == null){
            var r:= new Node(i);
            this.next := r;
            this.footprint := {this, r};
            this.list := [this.val, i];
        }else{
            this.next.append(i);
            this.footprint := {this} + this.next.footprint;
            this.list := [this.val] + this.next.list;
        }

    }

    
    method find(i: int) returns (b: bool)
    requires Valid()
    ensures b == (i in this.list)
    
    {
      var cur := this;
      b := false;
      ghost var listaux := [];
      while(cur != null)
      invariant cur != null ==> cur.Valid()
      invariant !(i in listaux)
      invariant cur != null ==> this.list == listaux + cur.list
      invariant cur == null ==> this.list == listaux
      
      decreases if (cur != null) then cur.footprint else{}
      {
        if(cur.val == i){
            b:=true;
            return;
        }
        listaux := listaux + [cur.val];
        cur:=cur.next;
      }
      
    }

    method filter() returns (r:Node?)
    requires Valid()
    ensures r!=null ==> r.Valid()
    ensures r!=null ==> r.footprint <= old(this.footprint)
    ensures r!=null ==> r.list == filter(old(this.list))
    ensures r==null ==> filter(old(this.list)) == []
    modifies footprint
    decreases footprint
    {
        if (this.next == null) {
            if (this.val < 0){
                r:= null;
                return;
            }else{
                r:= this;
                return;
            }
        }else{
            var aux := this.next.filter();
            if (this.val < 0){
                r:= aux;
                return;
            }else{
                if (aux != null){
                    r := this;
                    r.next:=aux;
                    r.list := [r.val] + aux.list;
                    r.footprint := {r} + aux.footprint;
                    return;
                    }else{
                        r := this;
                        r.next:=null;
                        r.list := [r.val];
                        r.footprint := {r};
                        return;
                }
            }
            return;
        }
    }
}


