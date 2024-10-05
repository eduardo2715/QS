//ex5 Fibonacci

function FibF(n: nat):nat
{
if (n<=1)
then n
else FibF(n-1)+FibF(n-2)
}

method FibM(n: nat) returns (z:nat)
ensures z==FibF(n);
{
if (n<=1){
    z:=n; return;
}
var cur:=1;
var fib_prev:=0;
var fib_cur:=1;

while(cur<n)
    invariant 0<=cur<=n
    invariant fib_prev == FibF(cur-1)
    invariant fib_cur == FibF(cur)
    {
        var aux:=fib_cur;
        fib_cur:=fib_cur+fib_prev;
        fib_prev:=aux;
        cur:=cur+1;
    }
z:=fib_cur;

}
