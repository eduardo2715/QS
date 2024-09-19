/*
 Ex 1. A function that defines the product via sum
*/

function prodF(x : nat, y : nat) : nat 
  decreases y
{
    if (y == 0)   
      then 0
      else prodF(x, y-1) + x
}

/*
 Ex 2. Prove that prodF is commutative 
*/

lemma ProdAuxiliaryLemma1 (x : nat) 
  ensures prodF(0, x) == 0
  decreases x 
{
  if (x == 0) {
    calc {
      prodF(0, x);
        == 
          0;
    }
  } else {
    calc {
      prodF(0, x); 
        == 
          prodF(0, x-1) + 0; 
        == 
          prodF(0, x-1); 
        == { ProdAuxiliaryLemma1(x-1); }
          0;
    }
  }
}

lemma ProdAuxiliaryLemma2 (x : nat, y : nat) 
  ensures prodF(x+1, y) == prodF(x, y)+y
{
  if (y == 0) {
    calc {
      prodF(x+1, y); 
        == 
          prodF(x+1, 0); 
        == 
          0; 
        == 
          prodF(x, 0) + 0;
    }
  } else {
    calc {
      prodF(x+1, y);
        ==
          prodF(x+1, y-1) + (x+1);
        == { ProdAuxiliaryLemma2(x, y-1); }
          prodF(x, y-1) + (y-1) + (x+1);
        ==
          prodF(x, y-1) + x + y;
        ==
          prodF(x, y) + y; 
    }
  }
}

lemma CommutativeProperty (x : nat, y : nat) 
  ensures prodF(x, y) == prodF(y, x)
  decreases y
{
  if (y == 0) {
    calc {
      prodF (x, y); 
        == 
          prodF(x, 0); 
        == 
          0; 
        == { ProdAuxiliaryLemma1(x); } 
          prodF(0, x);
        == 
          prodF(y, x);
    }
  } else {
    calc {
      prodF(x, y);
        == 
          prodF(x, y-1) + x; 
        ==
          prodF(y-1, x) + x; 
        == { ProdAuxiliaryLemma2(y-1, x); }
          prodF(y, x);
    }
  }
}

/*
 Example 2: Summing the elements of a sequence
*/

function sum (s : seq<int>) : int 
  decreases s 
{
  if (s == [])
    then 0
    else s[0] + sum(s[1..])
}

/*
 Proving the distributivity property
*/
lemma sumDistributivityProperty (s1 : seq<int>, s2 : seq<int>) 
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if (s1 == []) {
    calc {
      sum(s1 + s2); 
        == 
          sum([] + s2);
        == { assert [] + s2 == s2; }
          sum (s2); 
        ==
          0 + sum(s2);
        == 
          sum([]) + sum(s2);
        ==
          sum(s1) + sum(s2);
    }
  } else {
    calc {
      sum (s1 + s2); 
        == 
          s1[0] + sum((s1+s2)[1..]);
        == { assert (s1+s2)[1..] == s1[1..] + s2; }
          s1[0] + sum(s1[1..] + s2);
        == { sumDistributivityProperty(s1[1..], s2); }
          s1[0] + sum(s1[1..]) + sum(s2); 
        == 
          sum(s1) + sum(s2);
    }
  }
}

/*
  Example 3: maximum element of a sequence 
    + distributivity property of max
*/

function max (x : int, y : int) : int {
  if (x >= y) then x else y
}

function maxSeq(s : seq<int>) : int 
  requires |s| > 0
{
  if (|s| == 1) 
    then s[0]
    else max (s[0], maxSeq(s[1..]))
} 



lemma maxDistributivityProperty(s1 : seq<int>, s2 : seq<int>) 
  requires |s1| > 0 && |s2| > 0
  ensures maxSeq(s1+s2) == max(maxSeq(s1), maxSeq(s2)) 
  decreases s1
{
  if (|s1| == 1) {
    calc {
      maxSeq(s1 + s2); 
        == 
          max(s1[0], maxSeq(s2));
        ==
          max(maxSeq(s1), maxSeq(s2));
    }
  } else {
    calc {
      maxSeq(s1 + s2); 
        ==
          max((s1+s2)[0], maxSeq((s1+s2)[1..])); 
        == { assert (s1+s2)[0] == s1[0]; }
          max (s1[0], maxSeq((s1+s2)[1..]));
        == { assert (s1+s2)[1..] == s1[1..] + s2; }
          max (s1[0], maxSeq(s1[1..] + s2)); 
        == { sumDistributivityProperty(s1[1..], s2); }
          max(s1[0], max(maxSeq(s1[1..]), maxSeq(s2)));
        ==
          max(max(s1[0], maxSeq(s1[1..])), maxSeq(s2) );
        ==
          max (maxSeq(s1), maxSeq(s2));
    }
  }
}





