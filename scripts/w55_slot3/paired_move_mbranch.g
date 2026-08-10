# W55-SLOT3: the paired-move identity on the M branch.
# M relator (repo convention commP x y = x^-1 y^-1 x y):
#   A^2 * commP(A,B) * C^(2^alpha) * commP(C,D) * prod_j commP(u_j,v_j)
# Tuple letters: generators 0,1,2,3 = A,B,C,D.  Slot-3 paired move uses
#   a = base 3 = D,  b = base 2 = C,  n = 2^(k-2),
# and asks whether commP(D^n, C) * commP(C^n, D) = 1 in G/lambda_{k+1}.
comm := function(x,y) return x^-1*y^-1*x*y; end;;
mgroup := function(alpha, h)
  local F, gens, r, j;
  F := FreeGroup(4 + 2*h);
  gens := GeneratorsOfGroup(F);
  r := gens[1]^2 * comm(gens[1],gens[2]) * gens[3]^(2^alpha) * comm(gens[3],gens[4]);
  for j in [0..h-1] do
    r := r * comm(gens[5+2*j], gens[6+2*j]);
  od;
  return F/[r];
end;;
test := function(alpha, h, k)
  local G, q, hom, Q, a, b, n, z;
  G := mgroup(alpha, h);
  q := PQuotient(G, 2, k);
  hom := EpimorphismQuotientSystem(q);
  Q := Image(hom);
  b := Image(hom, GeneratorsOfGroup(G)[3]);   # C  = base 2
  a := Image(hom, GeneratorsOfGroup(G)[4]);   # D  = base 3
  n := 2^(k-2);
  z := comm(a^n, b) * comm(b^n, a);
  Print("M  alpha=", alpha, " h=", h, " k=", k,
        "  |G/lambda_", k+1, "|=2^", LogInt(Size(Q),2),
        "  [D^n,C][C^n,D]=1 ? ", z = One(Q), "\n");
end;;
for alpha in [2,3,4] do
  for h in [0,1] do
    for k in [3,4] do
      test(alpha,h,k);
    od;
  od;
od;
QUIT;
