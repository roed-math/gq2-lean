# W55-SLOT3 reconnaissance: is [a^n,b]*[b^n,a] = 1 in F/lambda_{k+1}?
# lambda = lower exponent-2 central series (GAP: exponent-p central series of PQuotient).
# Repo convention: commP x y = x^-1 y^-1 x y.  n = 2^(k-2).
comm := function(x,y) return x^-1*y^-1*x*y; end;;
test := function(r, k)
  local F, q, hom, G, a, b, n, z;
  F := FreeGroup(r);
  q := PQuotient(F, 2, k);
  hom := EpimorphismQuotientSystem(q);
  G := Image(hom);
  a := Image(hom, F.1);
  b := Image(hom, F.2);
  n := 2^(k-2);
  z := comm(a^n, b) * comm(b^n, a);
  Print("rank=", r, " k=", k, " |F/lambda_", k+1, "|=2^", LogInt(Size(G),2),
        "  [a^n,b][b^n,a]=1 ? ", z = One(G), "\n");
  return z = One(G);
end;;
for r in [2,3,4] do
  for k in [3,4,5] do
    test(r,k);
  od;
od;
QUIT;
