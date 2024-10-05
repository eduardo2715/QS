//ex6

function factF(n:nat):nat{
if (n<=1)
then 1
else n*factF(n-1)
}

method factM(n:nat) returns (z:nat)
ensures z==factF(n)
{
if (n<=1){
z:=1;return;
}

var cur:=1;
var fact_cur:=1;
while(cur<n)
    invariant 1<=cur<=n;
    invariant fact_cur==factF(cur);
    decreases n-cur;
    {
        cur:=cur+1;
        fact_cur:=cur*fact_cur;
    }
z:=fact_cur;
}

//reverse

/* method factMR(n:nat) returns (z:nat)
ensures z==factF(n)
{
var cur:=1;
var acc:=1;

while(cur > 0)

invariant 0<=cur<=n;
invariant factF(n) == cur*factF(cur)
{
acc:=acc * cur;
cur:=cur-1;
}
} */