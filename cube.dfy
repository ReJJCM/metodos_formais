method Cube(N: int) returns (c: int)
 requires 0 <= N;
 ensures c == N*N*N;
{
 c := 0;
 var n := 0;
 var k := 1;
 var m := 6;
 while (n < N)
  invariant 0 <= n <=  N
  invariant m == 6 + 6*n
  invariant k == 1 + 3*n + 3*n*n
  invariant c == n*n*n
 {
 c := c + k;   
 k := k + m;   
 m := m + 6;  
 n := n + 1;    
 }
}
