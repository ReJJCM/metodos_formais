method Triplo(x:int) returns (r:int)
ensures r == 3*x
{
    var y := Dobro(x);
    r := y + x;
}

method Dobro(x:int) returns (r:int)
ensures r == 2*x


method SumMax (x:int, y:int) returns (s:int, m:int)
requires x >= 0 && y >= 0
ensures s == x + y
ensures x <= m && y <= m 
ensures m == x || m == y
{
    s := x + y;
    if x < y
    {
        m := y;
    }  
    else
    {
        m := x;
    }
}

/* 0,1,1,2,3,5,8,...

FIB: N --> N
FIB(0) = 0
FIB(1) = 1
FIB(n) = FIB(n-2)+FIB(n-1), se n>=2
*/

function Fib(n:nat):nat
{   
    /*
    FIB(0) = 0
    FIB(1) = 1
    */
    if n < 2
    then n
    //FIB(n) = FIB(n-2)+FIB(n-1), se n>=2
    else Fib(n-2) + Fib(n-1)
}

// não recursiva
method ComputaFib(n:nat) returns (x:nat)
ensures x == Fib(n)
{
    x := 0;
    var i := 0;
    var y := 1;
    while i < n
    invariant 0 <= i <= n
    invariant x == Fib(i) && y == Fib(i+1)
    {
        x,y := y, x+y;
        i := i + 1;
    } 
}

method Teste()
{
    var f := ComputaFib(4);
    assert f == 3;
    
}