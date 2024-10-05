//ex4

method succ(x:int) returns (y:int)
ensures y == x+1;
{
y:=x + 1;
}

method sum1(x: int, y: int) returns (r: int)  //recursive
requires x>=0 && y>=0
ensures r == x + y;
{
    if y==0{
        r:=x;
    }else{
        var aux:=sum1(x, y-1);
        r:=succ(aux);
    }
}

method sum2(x: int, y: int) returns (r: int)  //iterative
requires x>=0 && y>=0
ensures r == x + y;
{
    r:=x;

    if (y==0){
        r:=x;return;
    }else{
        var aux:=y;
        while(aux>0)
            invariant 0<=aux<=y;
            invariant r==x+(y-aux);
            decreases aux;
            {
                r:=succ(r);
                aux:=aux-1;
            }
    }
}


method testSum()
{
var x:=1;
var y:=2;
var z1:=sum2(x, y);
var z2:=sum2(x, y);
assert z1 == 3;
assert z2 == 3;
}
