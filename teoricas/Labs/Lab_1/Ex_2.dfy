//ex2

method absM (x:int) returns (y:int)
//loose spec
//ensures y<=0; 

//more precise spec
ensures x<0 ==> y ==-x
ensures x>=0 ==> y==x

//simpler way to spec (less is more)
ensures y == absF(x)
{
    if (x<0){
    y:=-x;
    }else{
    y:=x;
    }
}

method testAbs()
{
var x:=-1;
var y:=absM (x);
assert y >= 0;
assert y == 1; //does not work because loose spec is not precise enough
}


function absF (x:int) : int{
if(x<0)
then -x
else x
}


