SizeScreen([200,40]);;
comm := function(x,y) return x^-1*y^-1*x*y; end;;
# Identity (II):  [a^n,b] * c^n * [c^m,a] = 1  in F/lambda_{k+1},  c = commP(a,b),
#                 n = 2^(k-2), m = 2^(k-3).
# Identity (I):   [a^n c^m, b] * [b^n c^m, a] = 1   (the corrected paired move).
# Identity (III): [a^n, b] * (c^m)^2 * [c^m,b0] * [c^m,b1] * [c^m,b0] = 1 with a = b1, b = w
#                 (the slot-0/1 move, N branch shape), i.e. rows R0(c^m)*R1(c^m)*R_{i0}(a^n).
test := function(r, k)
  local F, q, hom, Q, gens, a, b, c, n, m, id2, id1, id3, b0, b1, w, e;
  F := FreeGroup(r);
  q := PQuotient(F, 2, k);
  hom := EpimorphismQuotientSystem(q);
  Q := Image(hom);
  gens := List(GeneratorsOfGroup(F), g -> Image(hom,g));
  n := 2^(k-2); m := 2^(k-3);
  a := gens[1]; b := gens[2];
  c := comm(a,b);
  id2 := comm(a^n,b) * c^n * comm(c^m,a);
  id1 := comm(a^n*c^m,b) * comm(b^n*c^m,a);
  # N-branch shape: sharp generator b1 := gens[2], slot-0 letter b0 := gens[1],
  # partner w := gens[3] (or gens[2] when r=2).
  b0 := gens[1]; b1 := gens[2];
  if r >= 3 then w := gens[3]; else w := gens[1]; fi;
  e := comm(b1,w);
  id3 := comm(b1^n, w) * ( (e^m)^2 * comm(e^m,b0) * comm(e^m,b1) ) * comm(e^m,b0);
  Print("rank=", r, " k=", k,
        "   (II) ", id2 = One(Q),
        "   (I) ", id1 = One(Q),
        "   (III) ", id3 = One(Q), "\n");
end;;
for r in [2,3,4] do for k in [3,4,5] do test(r,k); od; od;
QUIT;
