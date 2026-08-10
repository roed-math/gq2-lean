# W55-SLOT3: the CORRECTED paired move.
# Claim: with c = commP(a,b), n = 2^(k-2), m = 2^(k-3), in F/lambda_{k+1}
#   commP(a^n * c^m, b) * commP(b^n * c^m, a) = 1
# and the exact obstruction of the UNCORRECTED move is
#   commP(a^n,b) * commP(b^n,a) = (commP(c,a) * commP(c,b))^m.
comm := function(x,y) return x^-1*y^-1*x*y; end;;
test := function(r, k)
  local F, q, hom, Q, a, b, c, n, m, lhs, obstr, pred;
  F := FreeGroup(r);
  q := PQuotient(F, 2, k);
  hom := EpimorphismQuotientSystem(q);
  Q := Image(hom);
  a := Image(hom, F.1);
  b := Image(hom, F.2);
  c := comm(a,b);
  n := 2^(k-2);
  m := 2^(k-3);
  lhs := comm(a^n * c^m, b) * comm(b^n * c^m, a);
  obstr := comm(a^n, b) * comm(b^n, a);
  pred := (comm(c,a) * comm(c,b))^m;
  Print("rank=", r, " k=", k,
        "   corrected move = 1 ? ", lhs = One(Q),
        "   |   obstruction = ([c,a][c,b])^m ? ", obstr = pred,
        "   |   obstruction trivial ? ", obstr = One(Q), "\n");
end;;
for r in [2,3,4] do
  for k in [3,4,5] do
    test(r,k);
  od;
od;
QUIT;
