SetColumns(0);
SetAutoColumns(false);
SetSeed(1);

F<a,b,c,d> := FreeGroup(4);
G := quo< F | a^2 * (a,b) * c^4 * (c,d) >;
Q, phi := pQuotient(G, 2, 5);
P := pCentralSeries(Q, 2);
dm := [Ilog2(#P[i] div #P[i+1]) : i in [1..5]];
ofs := [0 : i in [1..6]];
for i in [1..5] do ofs[i+1] := ofs[i] + dm[i]; end for;
A := phi(G.1); B := phi(G.2); C := phi(G.3); D := phi(G.4);
gg := [A,B,C,D]; gn := ["A","B","C","D"];
Comm := func<x,y | (x,y)>;
MWord := func<x,y,z,w | x^2 * Comm(x,y) * z^4 * Comm(z,w)>;

W := Comm(D,B); Ut := B^4; Un := B^4 * Comm(B^2,D);
s := W; t := W * Ut; m := Id(Q); n := Un;
defect := MWord(A*(B^4)^-1*s, B*t, B^2*C*m, D*n);
Incr := function(us,ut,um,un)
  return us^2 * Comm(us,A) * Comm(us,B*t) * Comm(um,D*n) *
    Comm(A,ut) * Comm(C,un);
end function;

Coord := function(x, w)
  e := Eltseq(Q!x);
  return Vector(GF(2), [GF(2)!e[i] : i in [ofs[w]+1..ofs[w+1]]]);
end function;

IndepRecords := function(cands, w)
  A0 := Matrix([Coord(z[1],w) : z in cands]);
  E := EchelonForm(Transpose(A0));
  piv := [];
  for i in [1..Nrows(E)] do
    dep := Depth(E[i]);
    if dep ne 0 then Append(~piv, dep); end if;
  end for;
  return [cands[j] : j in piv];
end function;

LayerDim := function(K,w)
  gens := [Q!x : x in PCGenerators(K meet P[w])];
  return Rank(Matrix([Coord(x,w) : x in gens]));
end function;

baseD := [<Comm(gg[i],gg[j]), "[" cat gn[i] cat "," cat gn[j] cat "]"> :
  i,j in [1..4] | i lt j];
DB := [IndepRecords(baseD,2)];
MB := [IndepRecords(baseD cat [<B^2,"B^2">],2)];
for w in [3..4] do
  prev := DB[w-2];
  cands := [<z[1]^2,"(" cat z[2] cat ")^2"> : z in prev] cat
    [<Comm(z[1],gg[i]), "[" cat z[2] cat "," cat gn[i] cat "]"> :
      z in prev, i in [1..4]];
  Append(~DB,IndepRecords(cands,w));
  prev := MB[w-2];
  cands := [<z[1]^2,"(" cat z[2] cat ")^2"> : z in prev] cat
    [<Comm(z[1],gg[i]), "[" cat z[2] cat "," cat gn[i] cat "]"> :
      z in prev, i in [1..4]];
  Append(~MB,IndepRecords(cands,w));
end for;

DQ := DerivedSubgroup(Q); Marked := sub<Q | B^2,DQ>;
print "natural D dims", [#x : x in DB],
  "exact", [LayerDim(DQ,w) : w in [2..4]];
print "natural M dims", [#x : x in MB],
  "exact", [LayerDim(Marked,w) : w in [2..4]];
assert [#x : x in DB] eq [LayerDim(DQ,w) : w in [2..4]];
assert [#x : x in MB] eq [LayerDim(Marked,w) : w in [2..4]];

mb := MB[3]; db := DB[3];
rowsS := [Coord(Incr(x[1],Id(Q),Id(Q),Id(Q)),5) : x in mb];
rowsT := [Coord(Incr(Id(Q),x[1],Id(Q),Id(Q)),5) : x in mb];
rowsM := [Coord(Incr(Id(Q),Id(Q),x[1],Id(Q)),5) : x in db];
rowsN := [Coord(Incr(Id(Q),Id(Q),Id(Q),x[1]),5) : x in mb];
rows := rowsS cat rowsT cat rowsM cat rowsN;
target := Coord(defect^-1,5);
ok, sol := IsConsistent(Matrix(rows),target); assert ok;
Ker := [Parent(sol)!k : k in Basis(Nullspace(Matrix(rows)))];
Wt := func<v | #[i : i in [1..Degree(Parent(v))] | v[i] ne 0]>;
LocalReduce := function(v)
  changed := true;
  while changed do
    changed := false;
    for k in Ker do
      if Wt(v+k) lt Wt(v) then v +:= k; changed := true; end if;
    end for;
  end while;
  return v;
end function;
best := LocalReduce(sol);
for trial in [1..4000] do
  v := sol;
  for k in Ker do
    if Random(7) eq 0 then v +:= k; end if;
  end for;
  v := LocalReduce(v);
  if Wt(v) lt Wt(best) then
    best := v;
    print "improved weight", Wt(best), "trial", trial;
  end if;
end for;
sol := best;
ofs := [0,#mb,2*#mb,2*#mb+#db];
print "kernel dimension", #Ker, "optimized total weight", Wt(sol);
print "natural solution support", [
  #[i : i in [1..#mb] | sol[ofs[1]+i] ne 0],
  #[i : i in [1..#mb] | sol[ofs[2]+i] ne 0],
  #[i : i in [1..#db] | sol[ofs[3]+i] ne 0],
  #[i : i in [1..#mb] | sol[ofs[4]+i] ne 0]
];
print "S:";
for i in [1..#mb] do
  if sol[ofs[1]+i] ne 0 then print mb[i][2]; end if;
end for;
print "T:";
for i in [1..#mb] do
  if sol[ofs[2]+i] ne 0 then print mb[i][2]; end if;
end for;
print "M:";
for i in [1..#db] do
  if sol[ofs[3]+i] ne 0 then print db[i][2]; end if;
end for;
print "N:";
for i in [1..#mb] do
  if sol[ofs[4]+i] ne 0 then print mb[i][2]; end if;
end for;

us := Id(Q); ut := Id(Q); um := Id(Q); un := Id(Q);
for i in [1..#mb] do
  if sol[ofs[1]+i] ne 0 then us *:= mb[i][1]; end if;
end for;
for i in [1..#mb] do
  if sol[ofs[2]+i] ne 0 then ut *:= mb[i][1]; end if;
end for;
for i in [1..#db] do
  if sol[ofs[3]+i] ne 0 then um *:= db[i][1]; end if;
end for;
for i in [1..#mb] do
  if sol[ofs[4]+i] ne 0 then un *:= mb[i][1]; end if;
end for;
print "kills", IsIdentity(defect*Incr(us,ut,um,un));
assert IsIdentity(defect*Incr(us,ut,um,un));
quit;
