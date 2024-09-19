datatype uop = Neg 
datatype bop = Plus | Minus 

datatype aexpr =
  | Var(seq<nat>)
  | Val(nat)
  | UnOp(uop, aexpr)
  | BinOp(bop, aexpr, aexpr)
 
datatype code = 
  | VarCode(seq<nat>)  
  | ValCode(nat)       
  | UnOpCode(uop)      
  | BinOpCode(bop)     

function Serialize(a : aexpr) : seq<code> 
{
  match a {
    case Var(s) => [ VarCode(s) ]
    case Val(i) => [ ValCode(i) ]
    case UnOp(op, a1) => Serialize(a1) + [ UnOpCode(op) ]
    case BinOp(op, a1, a2) => Serialize(a2) + Serialize(a1) + [ BinOpCode(op) ]
  }
}


/*
  Ex1.1
*/

function Deserialize(cs : seq<code>) : seq<aexpr> 
{
  DeserializeAux(cs, [])
}

function DeserializeAux(cs : seq<code>, aexprs : seq<aexpr>) : seq<aexpr> 
{
  if (|cs| == 0)
  then aexprs
  else DeserializeAux(cs[1..], DeserializeCode(cs[0], aexprs))
}

function DeserializeCode(c : code, aexprs : seq<aexpr>) : seq<aexpr> 
{
  match (c){
    case VarCode(a) => [Var(a)] + aexprs
    case ValCode(n) => [Val(n)] + aexprs
    case UnOpCode(u)  => if (|aexprs| >= 1)then[UnOp(u, aexprs[0])] + aexprs[1..] else[]
    case BinOpCode(b)  =>  if (|aexprs| >= 2)then[BinOp(b, aexprs[0], aexprs[1])] + aexprs[2..] else[]
  }
}


/*
  Ex1.2
*/

lemma DeserializeProperty(e : aexpr)
  ensures Deserialize(Serialize(e)) == [ e ]
{
  
}


lemma DeserializePropertyAux(e : aexpr, cs : seq<code>, es : seq<aexpr>)
  ensures DeserializeAux(Serialize(e) + cs, es) == DeserializeAux(cs, [e] + es)
  decreases e
{
 match (e){
  case Var(a) =>
   calc{
    DeserializeAux(Serialize(e) + cs, es);
    ==
    DeserializeAux(Serialize(Var(a)) + cs, es);
    ==
    DeserializeAux([VarCode(a)] + cs, es);
    ==
    DeserializeAux(cs, [Var(a)] + es);
    ==
    DeserializeAux(cs, [e] + es);
   }
  case Val(n) =>
    calc{
    DeserializeAux(Serialize(e) + cs, es);
    ==
    DeserializeAux(Serialize(Val(n)) + cs, es);
    ==
    DeserializeAux([ValCode(n)] + cs, es);
    ==
    DeserializeAux(cs, [Val(n)] + es);
    ==
    DeserializeAux(cs, [e] + es);

   }
  case UnOp(u, a) =>
    calc{
      DeserializeAux(Serialize(e) + cs, es);
      ==
      DeserializeAux(Serialize(UnOp(u, a)) + cs, es);
      ==
      DeserializeAux(Serialize(a) + [ UnOpCode(u) ] + cs, es);
      == {
        assert Serialize(a) + [ UnOpCode(u) ] + cs == Serialize(a) + ([ UnOpCode(u) ] + cs); 
        DeserializePropertyAux(a, [ UnOpCode(u) ] + cs, es); 
      }
      DeserializeAux([ UnOpCode(u) ] + cs, [a] + es);
      ==
      DeserializeAux(cs, [UnOp(u, a)] + es);
      ==
      DeserializeAux(cs, [e] + es);
    }
  case BinOp(b, a1, a2) => 
    calc{
      DeserializeAux(Serialize(e) + cs, es);
      ==
      DeserializeAux(Serialize(BinOp(b, a1, a2)) + cs, es);
      ==
      DeserializeAux(Serialize(a2) + Serialize(a1) + [ BinOpCode(b) ] + cs, es);
      =={
        assert Serialize(a2) + Serialize(a1) + [ BinOpCode(b) ] + cs == Serialize(a2) + (Serialize(a1) + ([ BinOpCode(b) ] + cs)); 
        DeserializePropertyAux(a2 , Serialize(a1) + [ BinOpCode(b) ] + cs, es); 
      }
      DeserializeAux(Serialize(a1) + ([ BinOpCode(b) ] + cs), [a2] + es);
      =={
        DeserializePropertyAux(a2 , [ BinOpCode(b) ] + cs, [a1] + es); 
      }
      DeserializeAux([ BinOpCode(b) ] + cs, [a1] + ([a2] + es));
      =={assert [a1] + ([a2] + es) == ([a1]+[a2]) + es;}
      DeserializeAux([ BinOpCode(b) ] + cs, [a1, a2] + es);
      == 
      DeserializeAux(cs, DeserializeCode(BinOpCode(b), [a1, a2] + es));
      ==
      DeserializeAux(cs, [BinOp(b, a1, a2)] + es);
      ==
      DeserializeAux(cs, [e] + es);
    }
  }
}

/* 
/*
  Ex1.3
*/
function SerializeCodes(cs : seq<code>) : seq<nat> 
{

}

function DeserializeCodes(ints : seq<nat>) : seq<code> {
  
}


/*
  Ex1.4
*/
lemma DeserializeCodesProperty(cs : seq<code>)
  ensures DeserializeCodes(SerializeCodes(cs)) == cs
{
}

/*
  Ex1.5
*/
function FullSerialize(e : aexpr) : seq<nat> {
 
}

function FullDeserealize(nats : seq<nat>) : seq<aexpr> {
 
}

/*
  Ex1.6
*/
lemma FullDeserealizeProperty(e : aexpr)
  ensures FullDeserealize(FullSerialize(e)) == [ e ]
{
    
} */