function Sum(n: nat): nat
{
  if n == 0
  then 0
  else n + Sum(n-1)
}

method Compute_Sum(n: nat) returns (s: nat)
ensures s == Sum(n);
{
  var k :=0;
  s := 0;
  while (k < n)
    invariant 0 <= k <= n;
    invariant s == Sum(k);
  {
    k := k +1;
    s := s + k;
  }
}
