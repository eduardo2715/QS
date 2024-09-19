datatype Tree<T> = Leaf(T) | Node(Tree<T>, Tree<T>)

datatype Code<T> = Lf(T) | Nd


function MaxF(x : int, y : int) : int {
  if (x >= y) then x else y
}

method Max(x: int, y: int) 
  returns (z: int)
  ensures z == MaxF(x, y) {
  
  if (x >= y) {
    z := x;
  } else {
    z := y;
  }

  return;
}


function flatten<T> (t : Tree<T>) : seq<Code<T>> 
  decreases t 
{
  match t 
    case Leaf(x) => [ Lf(x) ]
    case Node(t1, t2) => flatten(t1) + flatten(t2) + [ Nd ]
}

function size<T>(t : Tree<T>) : nat 
  decreases t
{ 
  match t 
    case Leaf(x) => 1 
    case Node(t1, t2) => 1 + size(t1) + size(t2)
}

function height<T> (t : Tree<T>) : nat  
  decreases t 
{ 
  match t 
    case Leaf(x) => 0
    case Node(t1, t2) => 1 + MaxF(height(t1), height(t2))
}



function getNd<T> (t : Tree<T> ) : Code<T> {
  Nd
}



lemma sizeFlattenLemma<T>  (t : Tree<T>)  
  ensures size(t) == |flatten(t)| {

  match t {
    case Leaf(x) =>  
      calc {
        size(Leaf(x)); 
          == 
            1; 
          == 
            | [getNd(t)] |; 
          == 
            | flatten(Leaf(x)) |; 
      }
    case Node(t1, t2) => 
      calc {
        size(Node(t1, t2));
          == // def. size
            1 + size(t1) + size(t2);
          == { sizeFlattenLemma(t1); sizeFlattenLemma(t2); } 
            1 + |flatten(t1)| + |flatten(t2)|;
          == // singleton sequence 
             |flatten(t1)| + |flatten(t2)| + | [ getNd(t) ] |; 
          == // property of flatten
            | flatten(t1) + flatten(t2) + [ Nd ] |;
          == 
            | flatten (t) |;
      }
  }
}


ghost method sizeFlattenLemma1<T>  (t : Tree<T>)  
  ensures size(t) == |flatten(t)| {

  match t {
    case Leaf(x) =>  
    case Node(t1, t2) => 
  }
}


ghost method sizeFlattenLemma2<T>  (t : Tree<T>)  
  ensures size(t) == |flatten(t)| {
}



function reconstruct<T> (cds : seq<Code<T>>, trees : seq<Tree<T>>) : seq<Tree<T>> 
    decreases cds, trees {
  if (cds == []) 
    then trees
    else reconstruct(cds[1..], reconstructAux(cds[0], trees))
}


function reconstructAux<T> (cd : Code<T>, trees : seq<Tree<T>>) : seq<Tree<T>> {
  match cd {
    case Lf (v) => [ Leaf(v) ] + trees
    case Nd => 
      if |trees| < 2 then [ ] 
      else [ Node (trees[1], trees[0]) ] + trees[2..]
  }
}


lemma ReconstructAfterFlatenningLemma<T> (t : Tree<T>, cds : seq<Code<T>>, ts : seq<Tree<T>>) 
  ensures reconstruct(flatten(t)+cds, ts) == reconstruct(cds, [ t ] + ts) {

  match t {
    case Leaf(x) => 
      calc {
        reconstruct(flatten(t)+cds, ts);
          == 
            reconstruct([ Lf(x) ] + cds, ts);
          == 
            reconstruct(cds, reconstructAux(Lf(x), ts));
          ==
            reconstruct(cds, [ Leaf(x) ] + ts);
      }

    case Node(t1, t2) => 
      assert flatten(t1) + flatten(t2) + [ Nd ] + cds == flatten(t1) + (flatten(t2) + [ Nd ] + cds);
      assert flatten(t2) + [Nd] + cds == flatten(t2) + ([Nd] + cds); 
      assert  [ t2 ] + ([ t1 ] + ts) == [ t2, t1] + ts;
      calc {
        reconstruct(flatten(t) + cds, ts); 
          ==
            reconstruct(flatten(t1) + flatten(t2) + [ Nd ] + cds, ts);
          == 
            reconstruct(flatten(t1) + (flatten(t2) + [ Nd ] + cds), ts);
          == { ReconstructAfterFlatenningLemma(t1, flatten(t2) + [ Nd ] + cds, ts); }
            reconstruct(flatten(t2) + [Nd] + cds, [ t1 ] + ts);
          == 
            reconstruct(flatten(t2) + ([Nd] + cds), [ t1 ] + ts);
          == { ReconstructAfterFlatenningLemma(t2, [ Nd ] + cds, [ t1 ] + ts); }
            reconstruct([ Nd ] + cds, [ t2 ] + ([ t1 ] + ts));
          == 
            reconstruct([ Nd ] + cds, [ t2, t1] + ts);
          ==
            reconstruct(cds, reconstructAux(Nd, [ t2, t1 ] + ts));
          == 
            reconstruct(cds, [ Node(t1, t2) ] + ts); 
          == 
            reconstruct(cds, [ t ] + ts);
      }
  }
}



ghost method ReconstructAfterFlatenningCorollary<T> (t : Tree<T>) 
  ensures reconstruct(flatten(t), []) == [ t ] 
{

  assert flatten(t) + [] == flatten(t);

  calc {
    reconstruct(flatten(t), []);
      ==
        reconstruct(flatten(t) + [], []);
      == { ReconstructAfterFlatenningLemma(t, [], []); }     
        reconstruct([], [ t ] + []);
      == 
        reconstruct([], [ t ]); 
      == 
        [ t ];
  }
} 


