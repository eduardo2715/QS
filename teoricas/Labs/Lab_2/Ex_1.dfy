//ex1

function sumSeqF(s:seq<int>):int //def
{
    if(|s| == 0)
    then 0
    else s[0] + sumSeqF(s[1..])
}

lemma sumDistributiviy(s1: seq<int>, s2: seq<int>)
ensures sumSeqF(s1 + s2) == sumSeqF(s1) + sumSeqF(s2) //IH
{
    if(s1 == []){//base case
        calc{
            sumSeqF(s1 + s2);
            == 
            sumSeqF([] + s2); //case
            == {assert [] + s2 == s2;}
            sumSeqF(s2); 
            == 
            sumSeqF([]) + sumSeqF(s2); //def
            == 
            sumSeqF(s1) + sumSeqF(s2); //case
        }
    }else{
        calc{
            sumSeqF(s1 + s2);
            == {assert s1 + s2 == [s1[0]] + (s1[1..] + s2);}
            sumSeqF([s1[0]] + (s1[1..] + s2));
            == 
            s1[0] + sumSeqF(s1[1..] + s2); 
            == {sumDistributiviy(s1[1..], s2);} //def
            s1[0] + sumSeqF(s1[1..]) + sumSeqF(s2); //IH
            == 
            sumSeqF(s1) + sumSeqF(s2); //def
        }
    }
}

method SumSeqIter(s:seq<int>) returns (r:int)
ensures r == sumSeqF(s)
{
    r := 0;
    var i := 0;
    while(i < |s|)
    invariant 0 <= i <= |s|
    invariant r == sumSeqF(s[..i])
    {
        calc{
            sumSeqF(s[..i+1]); //this should be the new value of r
            == {assert s[..i+1] == s[..i] + [s[i]];}
            sumSeqF(s[..i] + [s[i]]);
            == {sumDistributiviy(s[..i], [s[i]]);} //lemma
            sumSeqF(s[..i]) + sumSeqF([s[i]]);
            ==
            sumSeqF(s[..i]) + s[i];
            ==
            r + s[i];
        }
        r := r + s[i];
        i := i + 1;
    }
    assert s == s[..|s|];
}