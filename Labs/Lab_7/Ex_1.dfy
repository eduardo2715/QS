module Ex1 {

    class KVNode { 
        var  data : int
        var key:int
        var next: KVNode?

        ghost var kv_map : map <int,int>
        ghost var footprint : set<KVNode>
        
        
        ghost function Valid():bool
            reads this, footprint
        {
            this.data >= 0
            &&
            if(this.next == null)
            then
                this.footprint == {this}
                && this.kv_map == map[this.key:=this.data]
            else
                this.next in footprint
                && this.footprint == {this} + this.next.footprint
                && this.kv_map == this.next.kv_map[this.key:=this.data]
                && this !in this.next.footprint
                && this.next.Valid()
                && this.key !in this.next.kv_map
        }

        constructor (k:int, v:int)
            requires v>=0
            ensures this.key == k 
                && this.data == v
                && this.next == null
            ensures this.footprint == {this}
                && this.kv_map == map[k:=v]
            ensures Valid()
        {
            this.key := k;
            this.data := v;
            this.next := null;
            this.footprint := {this};
            this.kv_map := map[k:=v];

        }

        method update(k:int, v:int)
            requires this.Valid() && v>=0
            ensures this.Valid() && fresh(footprint - old(footprint))
            ensures this.kv_map == old(this.kv_map)[k:=v]
            decreases footprint
            modifies footprint
        
        {
            if (this.key == k){
                this.data := v;
                this.kv_map := this.kv_map[k:=v];
            } else {
                if (this.next == null){
                    var aux := new KVNode(k,v);
                    this.next := aux;
                    this.footprint:={this,aux};
                    this.kv_map:=map[this.key:=this.data, k:=v];
                }else{
                    this.next.update(k,v);   
                    this.footprint:={this} + this.next.footprint;
                    this.kv_map:=this.next.kv_map[this.key:=this.data];             
                }
            }
        }

        method findKey(k:int) returns (v:int)
            ensures k in kv_map ==> v == kv_map[k]
            ensures k !in kv_map ==> v == -1 
        {
            var cur := this;
            ghost var seen_keys :set<int> := {};

            while(cur != null)
            
            invariant k !in seen_keys
            invariant cur != null ==> cur.Valid()
            invariant cur != null ==> this.kv_map.Keys == seen_keys + cur.kv_map.Keys
            invariant cur == null ==> this.kv_map.Keys == seen_keys
            invariant cur != null ==> forall k1:: k1 in cur.kv_map ==> cur.kv_map[k1] == this.kv_map[k1] 
            
            decreases if(cur != null) then cur.footprint else {}
            {
                if (cur.key == k){
                    v := cur.data;
                    return;
                }
                seen_keys := seen_keys + {cur.key};
                cur:=cur.next;
            }
            v:=-1;
        }

        method RemoveKey(k:int) returns (r:KVNode?)
        requires Valid()
        ensures r!=null ==> Valid() 
        ensures r!=null ==> r.footprint <= old(this.footprint)
        ensures r!=null ==> this.kv_map.Keys == old(this.kv_map.Keys) - {k}
        ensures r == null ==>  old(this.kv_map.Keys) == {k}

        modifies footprint
        decreases footprint
        {
            if (k==this.key){
                r:=this.next;return;
            }else{
                if (this.next == null){
                    r:=this; return;
                }else{
                    var aux:=this.next.RemoveKey(k);
                    this.next := aux;
                    if(this.next != null){
                    this.footprint := {this} + this.next.footprint;
                    this.kv_map := this.next.kv_map[this.key:=this.data];
                    }else{
                        this.footprint := {this};
                        this.kv_map := kv_map[this.key:=this.data];
                    }
                    r:=this; return;
                }
            }
        }
    }
}