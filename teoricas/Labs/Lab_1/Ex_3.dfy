//ex3

method ProductItera (x:int, y:int) returns (z:int)              //iter|x|y||aux|z |z==x*(y-aux)
requires x>=0 && y>=0                                           // 0  |4|3|| 3 |0 |true
ensures z==x*y                                                  // 1  |4|3|| 2 |4 |true
                                                                // 2  |4|3|| 1 |8 |true
{                                                               // 3  |4|3|| 0 |12|true 
    z:=0;                                                           
    var aux:=y;
    while (aux>0)
        invariant 0<=aux<=y;
        invariant z==x*(y-aux);
        decreases aux;
    {
    z:=z+x;
    aux:=aux-1;
    }
    return;
}
