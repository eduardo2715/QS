//ex3
function max(v1:int, v2:int):int
{
    if(v1>=v2)
    then v1
    else v2
}

function MaxSeqF(s:seq<int>):int //def
requires |s| > 0
{
    if |s| == 1
    then s[0]
    else max(s[0], MaxSeqF(s[1..]))
}

lemma MaxDistributivity(s1:seq<int>, s2:seq<int>)
requires |s1| > 0  && |s2| > 0
ensures MaxSeqF(s1 + s2) == max(MaxSeqF(s1), MaxSeqF(s2))
decreases s1
{
    if(|s1| == 1){ //Base Case
        calc{
            MaxSeqF(s1 + s2);
            ==
            MaxSeqF([s1[0]] + s2); //case
            == {assert ([s1[0]] + s2)[0] == s1[0];
            assert ([s1[0]] + s2)[1..] == s2;}
            max(s1[0], MaxSeqF(s2)); //def
            ==
            max(MaxSeqF(s1), MaxSeqF(s2)); //def
        }
    }
     else{
        calc{
            MaxSeqF(s1 + s2);
            == {assert s1+s2 == [s1[0]]+(s1[1..]+s2);}
            MaxSeqF([s1[0]]+(s1[1..]+s2)); //case
            == /* {assert ([s1[0]]+(s1[1..]+s2))[0] == s1[0];
             assert ([s1[0]]+(s1[1..]+s2))[1..] == s2; } */
            max(s1[0], MaxSeqF(s1[1..] + s2)); //def
            == {MaxDistributivity(s1[1..], s2);}
            max(s1[0], max(MaxSeqF(s1[1..]), MaxSeqF(s2))); //IH
            ==
            max(max(s1[0], MaxSeqF(s1[1..])), MaxSeqF(s2));
            ==
            max(MaxSeqF(s1), MaxSeqF(s2));
       } 
    } 
}


