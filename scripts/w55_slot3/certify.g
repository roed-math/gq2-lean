# W55-SLOT3 reconnaissance, certified run.
# lambda = lower exponent-2 central series (GAP's exponent-p central series).
# Repo convention: commP x y = x^-1 y^-1 x y.  n = 2^(k-2), m = 2^(k-3), c = commP(a,b).
SizeScreen([250,60]);;
comm := function(x,y) return x^-1*y^-1*x*y; end;;
freeQ := function(r,k)
  local F,q,hom;
  F := FreeGroup(r); q := PQuotient(F,2,k); hom := EpimorphismQuotientSystem(q);
  return [Image(hom), List(GeneratorsOfGroup(F), g -> Image(hom,g))];
end;;
mQ := function(alpha,h,k)
  local F,gens,r,j,G,q,hom;
  F := FreeGroup(4+2*h); gens := GeneratorsOfGroup(F);
  r := gens[1]^2*comm(gens[1],gens[2])*gens[3]^(2^alpha)*comm(gens[3],gens[4]);
  for j in [0..h-1] do r := r*comm(gens[5+2*j],gens[6+2*j]); od;
  G := F/[r]; q := PQuotient(G,2,k); hom := EpimorphismQuotientSystem(q);
  return [Image(hom), List(GeneratorsOfGroup(G), g -> Image(hom,g))];
end;;
report := function(tag, Q, gens, k, ia, ib)
  local a,b,c,n,m,w54,pred,corr;
  a := gens[ia]; b := gens[ib]; c := comm(a,b); n := 2^(k-2); m := 2^(k-3);
  w54  := comm(a^n,b)*comm(b^n,a);
  pred := comm(c^m,a)*comm(c^m,b);
  corr := comm(a^n*c^m,b)*comm(b^n*c^m,a);
  Print(tag, "  |Q|=2^", LogInt(Size(Q),2),
        "   W54 move trivial: ", w54 = One(Q),
        "   |   W54 move = [c^m,a][c^m,b]: ", w54 = pred,
        "   |   corrected move trivial: ", corr = One(Q), "\n");
end;;
Print("=== free pro-2 groups F_r / lambda_{k+1}, a = x1, b = x2 ===\n");
for r in [2,3,4] do for k in [3,4] do
  d := freeQ(r,k); report(Concatenation("free r=",String(r)," k=",String(k)), d[1], d[2], k, 1, 2);
od; od;
d := freeQ(2,5);; report("free r=2 k=5", d[1], d[2], 5, 1, 2);
Print("\n=== M-relator Demushkin groups A^2[A,B]C^(2^alpha)[C,D]prod[u,v] ===\n");
Print("    slot-3 paired move: a = D = base 3, b = C = base 2\n");
for alpha in [2,3] do for k in [3,4] do
  d := mQ(alpha,0,k);
  report(Concatenation("M alpha=",String(alpha)," h=0 k=",String(k)), d[1], d[2], k, 4, 3);
od; od;
d := mQ(2,1,3);; report("M alpha=2 h=1 k=3", d[1], d[2], 3, 4, 3);
Print("\n=== the key power-commutator identity [a^n,b] c^n [c^m,a] = 1 ===\n");
for r in [2,3,4] do for k in [3,4] do
  d := freeQ(r,k);
  a := d[2][1]; b := d[2][2]; c := comm(a,b); n := 2^(k-2); m := 2^(k-3);
  Print("free r=", r, " k=", k, "   identity holds: ",
        comm(a^n,b)*c^n*comm(c^m,a) = One(d[1]), "\n");
od; od;
QUIT;
