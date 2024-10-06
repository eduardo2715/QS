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




lemma DeserializePropertyAux(e : aexpr, cs : seq<code>, es : seq<aexpr>)
  ensures DeserializeAux(Serialize(e) + cs, es) == DeserializeAux(cs, [e] + es)
{
 match e{
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



lemma DeserializeProperty(e : aexpr)
  ensures Deserialize(Serialize(e)) == [e]
{
    calc{
      Deserialize(Serialize(e));
      == {assert Serialize(e) + [] == Serialize(e);}
      DeserializeAux(Serialize(e) + [], []);
      == {DeserializePropertyAux(e, [], []);}
      DeserializeAux([], [e] + []);
      == {DeserializePropertyAux(e, [], []);}
      DeserializeAux(Serialize(e) + [], []);
      == {DeserializePropertyAux(e, [], []);}
      DeserializeAux([], [e]);
      ==
     [e];
  }
}


/*
  Ex1.3
*/
function SerializeCodes(cs: seq<code>): seq<nat>
{
  if |cs| == 0 then []
  else
    match cs[0] {
      case VarCode(s) => //[Var(a)] + aexprs
        [0, |s|] + s + SerializeCodes(cs[1..])  
      case ValCode(n) => //[Val(n)] + aexprs
        [1, n] + SerializeCodes(cs[1..])
      case UnOpCode(u) => //Serialize(a1) + [ UnOpCode(op) ]
        [2, match u { case Neg => 0 }] + SerializeCodes(cs[1..]) 
      case BinOpCode(b) => //Serialize(a2) + Serialize(a1) + [ BinOpCode(op) ]
        [3, match b { case Plus => 0 case Minus => 1 }] + SerializeCodes(cs[1..])  
    }
}

function DeserializeCodes(ints: seq<nat>): seq<code>
{
  if |ints| == 0 then []
  else
    match ints[0] {
      case 0 =>
        if |ints| >= 2 && |ints| >= 2 + ints[1] then
          [VarCode(ints[2 .. 2 + ints[1]])] + DeserializeCodes(ints[2 + ints[1] ..])
        else []
      case 1 =>
        if |ints| >= 2 then
          [ValCode(ints[1])] + DeserializeCodes(ints[2..])
        else []
      case 2 =>
        if |ints| >= 2 then
          [UnOpCode(match ints[1] { case 0 => Neg 
                                    case _ => Neg 
                                    })] + DeserializeCodes(ints[2..])
        else []
      case 3 =>
        if |ints| >= 2 then
          [BinOpCode(match ints[1] {  case 0 => Plus 
                                      case 1 => Minus 
                                      case _ => Plus 
                                      })] + DeserializeCodes(ints[2..])
        else []
      case _ => []
    }
}



/*
  Ex1.4
*/
lemma DeserializeCodesProperty(cs: seq<code>)
  ensures DeserializeCodes(SerializeCodes(cs)) == cs
{
  if |cs| == 0 {
    calc {
      DeserializeCodes(SerializeCodes(cs));
      == { assert SerializeCodes(cs) == []; }
      DeserializeCodes([]);
      == 
      [];
      == 
      cs;
    }
  } else {
    
    var c := cs[0];
    var rest := cs[1..];

    
    match c {
      case VarCode(s) =>
        calc {
          DeserializeCodes(SerializeCodes(cs));
          == { assert SerializeCodes(cs) == [0, |s|] + s + SerializeCodes(rest); }
          DeserializeCodes([0, |s|] + s + SerializeCodes(rest));
          == 
          [VarCode(s)] + DeserializeCodes(SerializeCodes(rest));
          == 
          [VarCode(s)] + rest;
          == 
          cs;
        }

      case ValCode(n) =>
        calc {
          DeserializeCodes(SerializeCodes(cs));
          == { assert SerializeCodes(cs) == [1, n] + SerializeCodes(rest); }
          DeserializeCodes([1, n] + SerializeCodes(rest));
          == 
          [ValCode(n)] + DeserializeCodes(SerializeCodes(rest));
          == 
          [ValCode(n)] + rest;
          ==
          cs;
        }

      case UnOpCode(u) =>
        calc {
          DeserializeCodes(SerializeCodes(cs));
          == { assert SerializeCodes(cs) == [2, match u { case Neg => 0 }] + SerializeCodes(rest); }
          DeserializeCodes([2, match u { case Neg => 0 }] + SerializeCodes(rest));
          == 
          [UnOpCode(u)] + DeserializeCodes(SerializeCodes(rest));
          == 
          [UnOpCode(u)] + rest;
          ==
          cs;
        }

      case BinOpCode(b) =>
        calc {
          DeserializeCodes(SerializeCodes(cs));
          == { assert SerializeCodes(cs) == [3, match b { case Plus => 0 case Minus => 1 }] + SerializeCodes(rest); }
          DeserializeCodes([3, match b { case Plus => 0 case Minus => 1 }] + SerializeCodes(rest));
          == 
          [BinOpCode(b)] + DeserializeCodes(SerializeCodes(rest));
          ==
          [BinOpCode(b)] + rest;
          == 
          cs;
        }
    }
  }
}



/*
  Ex1.5
*/
function FullSerialize(e : aexpr) : seq<nat> {
 SerializeCodes(Serialize(e))
}

function FullDeserealize(nats : seq<nat>) : seq<aexpr> {
 Deserialize(DeserializeCodes(nats))
}

/*
  Ex1.6
*/
lemma FullDeserealizeProperty(e : aexpr)
  ensures FullDeserealize(FullSerialize(e)) == [ e ]
{
  calc{
    FullDeserealize(FullSerialize(e));
    ==
    FullDeserealize(SerializeCodes(Serialize(e)));
    ==
    Deserialize(DeserializeCodes(SerializeCodes(Serialize(e))));
    == {DeserializeCodesProperty(Serialize(e));}
    Deserialize(Serialize(e)); 
    == {DeserializeProperty(e);}
    [e];
  }
    
}