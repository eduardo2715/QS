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
function Deserialize(cs : seq<code>, aexprs : seq<aexpr>) : seq<aexpr> 
{
  if (|cs| == 0)
  then aexprs
  else Deserialize(cs[1..], DeserializeCode(cs[0], aexprs))
}

function DeserializeCode(c : code, aexprs : seq<aexpr>) : seq<aexpr> 
{
  match (c){
    case VarCode(a) => [Var(a)] + aexprs
    case ValCode(n) => [Val(n)] + aexprs
    case UnOpCode(u)  => if (|aexprs| >= 1)then[UnOp(u, aexprs[0])] + aexprs[1..] else[]
    case BinOpCode(b)  =>  if (|aexprs| >= 2)then[BinOp(b, aexprs[1], aexprs[0])] + aexprs[2..] else[]
  }
}


/*
  Ex1.2
*/
lemma DeserializeProperty(e : aexpr, cs : seq<code>, es : seq<aexpr>)
  ensures Deserialize(Serialize(e) + cs, es) == Deserialize(cs, [e] + es)
  decreases e
{
 match (e){
  case Var(a) =>
   calc{
    Deserialize(Serialize(e) + cs, es);
    ==
    Deserialize(Serialize(Var(a)) + cs, es);
    ==
    Deserialize([VarCode(a)] + cs, es);
    ==
    Deserialize(cs, [Var(a)] + es);
    ==
    Deserialize(cs, [e] + es);
   }
  case Val(n) =>
    calc{
    Deserialize(Serialize(e) + cs, es);
    ==
    Deserialize(Serialize(Val(n)) + cs, es);
    ==
    Deserialize([ValCode(n)] + cs, es);
    ==
    Deserialize(cs, [Val(n)] + es);
    ==
    Deserialize(cs, [e] + es);

   }
  case UnOp(u, a) =>
    calc{
      Deserialize(Serialize(e) + cs, es);
      ==
      Deserialize(Serialize(UnOp(u, a)) + cs, es);
      ==
      Deserialize(Serialize(a) + [ UnOpCode(u) ] + cs, es);
      == {
        assert Serialize(a) + [ UnOpCode(u) ] + cs == Serialize(a) + ([ UnOpCode(u) ] + cs); 
        DeserializeProperty(a, [ UnOpCode(u) ] + cs, es); 
      }
      Deserialize([ UnOpCode(u) ] + cs, [a] + es);
      ==
      Deserialize(cs, [UnOp(u, a)] + es);
      ==
      Deserialize(cs, [e] + es);
    }
  case BinOp(b, a1, a2) => 
    calc{
      Deserialize(Serialize(e) + cs, es);
      ==
      Deserialize(Serialize(BinOp(b, a1, a2)) + cs, es);
      ==
      Deserialize(Serialize(a2) + Serialize(a1) + [ BinOpCode(b) ] + cs, es);
      =={
        assert Serialize(a2) + Serialize(a1) + [ BinOpCode(b) ] + cs == Serialize(a2) + (Serialize(a1) + ([ BinOpCode(b) ] + cs)); 
        DeserializeProperty(a1 , Serialize(a2) + [ BinOpCode(b) ] + cs, es); 
      }
      Deserialize(Serialize(a1) + ([ BinOpCode(b) ] + cs), [a2] + es);
      =={
        DeserializeProperty(a1 , [ BinOpCode(b) ] + cs, [a2] + es); 
      }
      Deserialize([ BinOpCode(b) ] + cs, [a1] + ([a2] + es));
      =={assert [a1] + ([a2] + es) == ([a1]+[a2]) + es;}
      Deserialize([ BinOpCode(b) ] + cs, [a1, a2] + es);
      == 
      Deserialize(cs, DeserializeCode(BinOpCode(b), [a1, a2] + es));
      == {assert [a1, a2] + es == [a1] + [a2] + es;}//something missing here HELP
      Deserialize(cs, [BinOp(b, a1, a2)] + es);
      ==
      Deserialize(cs, [e] + es);
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