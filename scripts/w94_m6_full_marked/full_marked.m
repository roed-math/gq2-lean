SetColumns(0);
SetAutoColumns(false);
SetSeed(1);

F<a,b,c,d> := FreeGroup(4);
G := quo< F | a^2 * (a,b) * c^4 * (c,d) >;

Q, phi := pQuotient(G, 2, 5);
P := pCentralSeries(Q, 2);
A := phi(G.1); B := phi(G.2); C := phi(G.3); D := phi(G.4);

Comm := func<x,y | (x,y)>;
MWord := func<x,y,z,w | x^2 * Comm(x,y) * z^4 * Comm(z,w)>;

W := Comm(D,B);
Ut := B^4;
Un := B^4 * Comm(B^2,D);
s := W; t := W * Ut; m := Id(Q); n := Un;
letA := A * (B^4)^-1 * s;
letB := B * t;
letC := B^2 * C * m;
letD := D * n;
defect := MWord(letA, letB, letC, letD);

Incr := function(us,ut,um,un)
  return us^2 * Comm(us,A) * Comm(us,B*t) * Comm(um,D*n) *
    Comm(A,ut) * Comm(C,un);
end function;

Coord := function(x, w)
  V, q := quo< P[w] | P[w+1] >;
  return Vector(GF(2), [ GF(2)!e : e in Eltseq(q(x)) ]);
end function;

LayerBasis := function(K, w)
  V, q := quo< P[w] | P[w+1] >;
  gens := [ Q!x : x in PCGenerators(K meet P[w]) ];
  if #gens eq 0 then
    return [], ZeroMatrix(GF(2), 0, NPCgens(V));
  end if;
  A0 := Matrix(GF(2), [ [ GF(2)!e : e in Eltseq(q(x)) ] : x in gens ]);
  E, T := EchelonForm(A0);
  reps := [];
  for k in [1..Rank(A0)] do
    y := Id(Q);
    for l in [1..#gens] do
      if T[k][l] ne 0 then y := y * gens[l]; end if;
    end for;
    Append(~reps, y);
  end for;
  return reps, A0;
end function;

DQ := DerivedSubgroup(Q);
Marked := sub< Q | B^2, DQ >;
mb, mmat := LayerBasis(Marked, 4);
db, dmat := LayerBasis(DQ, 4);

print "Q order exponent", Ilog2(#Q);
print "lower-2-central layer dimensions",
  [ Ilog2(#P[i] div #P[i+1]) : i in [1..5] ];
print "defect in P5", defect in P[5], "defect trivial", IsIdentity(defect);
print "marked layer-4 dimension", #mb, "pivot-derived layer-4 dimension", #db;

rowsS := [ Coord(Incr(x,Id(Q),Id(Q),Id(Q)),5) : x in mb ];
rowsT := [ Coord(Incr(Id(Q),x,Id(Q),Id(Q)),5) : x in mb ];
rowsM := [ Coord(Incr(Id(Q),Id(Q),x,Id(Q)),5) : x in db ];
rowsN := [ Coord(Incr(Id(Q),Id(Q),Id(Q),x),5) : x in mb ];
rows := rowsS cat rowsT cat rowsM cat rowsN;
target := Coord(defect^-1,5);

print "slot ranks S,T,M,N",
  [ Rank(Matrix(x)) : x in [rowsS,rowsT,rowsM,rowsN] ];
print "cumulative ranks", [ Rank(Matrix(rowsS)), Rank(Matrix(rowsS cat rowsT)),
  Rank(Matrix(rowsS cat rowsT cat rowsM)), Rank(Matrix(rows)) ];
print "two-slot T+N rank", Rank(Matrix(rowsT cat rowsN));
print "target nonzero", not IsZero(target);
print "two-slot T+N membership", target in RowSpace(Matrix(rowsT cat rowsN));
print "full membership", target in RowSpace(Matrix(rows));
assert not (target in RowSpace(Matrix(rowsT cat rowsN)));
assert target in RowSpace(Matrix(rows));

ok, sol := IsConsistent(Matrix(rows), target);
assert ok;
us := Id(Q); ut := Id(Q); um := Id(Q); un := Id(Q);
ofs := [0, #mb, 2*#mb, 2*#mb+#db];
for i in [1..#mb] do
  if sol[ofs[1]+i] ne 0 then us *:= mb[i]; end if;
end for;
for i in [1..#mb] do
  if sol[ofs[2]+i] ne 0 then ut *:= mb[i]; end if;
end for;
for i in [1..#db] do
  if sol[ofs[3]+i] ne 0 then um *:= db[i]; end if;
end for;
for i in [1..#mb] do
  if sol[ofs[4]+i] ne 0 then un *:= mb[i]; end if;
end for;
print "solution support S,T,M,N", [
  #[i : i in [1..#mb] | sol[ofs[1]+i] ne 0],
  #[i : i in [1..#mb] | sol[ofs[2]+i] ne 0],
  #[i : i in [1..#db] | sol[ofs[3]+i] ne 0],
  #[i : i in [1..#mb] | sol[ofs[4]+i] ne 0]
];
print "solution kills", IsIdentity(defect * Incr(us,ut,um,un));
assert IsIdentity(defect * Incr(us,ut,um,un));
print "us", us;
print "ut", ut;
print "um", um;
print "un", un;

quit;
