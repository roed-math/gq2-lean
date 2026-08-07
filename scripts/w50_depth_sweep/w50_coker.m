/*  W50 -- anatomy of the corank-6 cokernel of the defect map.
 *
 *      magma -b cls:=4 out:=coker_c4.txt w50_coker.m
 *
 *  At every level and every marking the defect map delta has image of codimension exactly 6
 *  in the layer it targets.  A vector landing in a codimension-6 F_2-subspace by chance has
 *  probability 2^-6 = 1/64.  The relator's defect lands there EVERY time.  This script asks
 *  whether that is structural: is the image the SAME subspace for different markings, and
 *  where inside it does the defect sit?
 */
SetColumns(0); SetAutoColumns(false); SetSeed(1);
load "c0.m";
CLS := StringToInteger(cls);
OUT := out; System("rm -f " cat OUT);
procedure Say(str) PrintFile(OUT, str); end procedure;

F<fs,fx0,fx1,fu,fv> := FreeGroup(5);
RELW := (fx0^fs)^-1 * (fx0^3)^-1 * fx1^2 * (fx1, fx1^fs) * (fu,fv);
G := quo< F | RELW >;
Rel := function(m)
  return (m[2]^m[1])^-1 * (m[2]^3)^-1 * m[3]^2 * (m[3], m[3]^m[1]) * (m[4],m[5]);
end function;
Coord := function(q,x) return Vector(GF(2),[GF(2)!e : e in Eltseq(q(x))]); end function;

Q, phi := pQuotient(G, 2, CLS);
P  := pCentralSeries(Q, 2);
gQ := [phi(G.i) : i in [1..5]];
DQ := DerivedSubgroup(Q);
wQ := gQ[1] * (gQ[2]^(C0 mod 2^(CLS+2)))^-1;
tbQ:= (gQ[2]^2)^-1 * gQ[3];
Say(Sprintf("W50 cokernel anatomy -- class %o, Q order 2^%o", CLS, Ilog2(#Q)));

LayerBasis := function(K, Pj, Pj1)
  V, q := quo< Pj | Pj1 >;
  gens := [ x : x in PCGenerators(K meet Pj) ];
  A := Matrix(GF(2), [ [ GF(2)!e : e in Eltseq(q(x)) ] : x in gens ]);
  E, T := EchelonForm(A);
  reps := [];
  for k in [1..Rank(A)] do
    y := Id(Q);
    for l in [1..#gens] do if T[k][l] ne 0 then y := y * gens[l]; end if; end for;
    Append(~reps, y);
  end for;
  return reps;
end function;

MARKS := [[0,1],[1,0],[1,1],[1,2],[2,1],[3,5],[2,2],[0,2],[5,7],[1,4]];
IMG := AssociativeArray();
Say("");
Say("marking | level | target dim | rank | corank | defect in image? | image same as (0,1)'s?");
Say("--------+-------+------------+------+--------+------------------+-----------------------");

for e0 in MARKS do
  t := e0[1]; s := e0[2];
  UQ := (wQ^t)^-1 * gQ[4];  VQ := gQ[5] * (wQ^s)^-1;
  base := [gQ[1], gQ[2], gQ[3], UQ, VQ];
  K := sub< Q | UQ, VQ, tbQ, DQ >;
  dressQ := [ UQ^(a div 4) * VQ^((a div 2) mod 2) * tbQ^(a mod 2) : a in [0..7] ];
  fc := 4*(s mod 2) + 2*(t mod 2);            // the forced core dressing U^-s V^t mod squares
  m := [ base[1]*dressQ[fc+1], base[2]*dressQ[fc+1], base[3], base[4], base[5] ];
  r := Rel(m);
  for j in [3..CLS] do
    if r in P[j+1] then continue; end if;
    reps := LayerBasis(K, P[j-1], P[j]);
    Vt, qtar := quo< P[j] | P[j+1] >;
    dtar := NPCgens(Vt);
    rows := [];
    for i in [1..5] do for b in reps do
      mm := m; mm[i] := m[i]*b;
      Append(~rows, Coord(qtar, Rel(mm) * r^-1));
    end for; end for;
    A := Matrix(rows);
    RS := RowSpace(A);
    tar := Coord(qtar, r^-1);
    inimg := tar in RS;
    key := [j];
    same := "(reference)";
    if IsDefined(IMG, key) then
      same := (IMG[key] eq RS) select "yes" else "NO -- differs";
    else
      IMG[key] := RS;
    end if;
    Say(Sprintf("%2o %2o   |  L%o   | %10o | %4o | %6o | %-16o | %o",
        t, s, j, dtar, Dimension(RS), dtar-Dimension(RS), inimg, same));
    ok, x := IsConsistent(A, tar);
    nb := #reps;
    for i in [1..5] do for l in [1..nb] do
      if x[(i-1)*nb + l] ne 0 then m[i] := m[i] * reps[l]; end if;
    end for; end for;
    r := Rel(m);
  end for;
end for;

/* how special is "the defect lands in a codimension-6 subspace"? */
Say("");
Say("control: how often does a RANDOM element of the layer land in the image?");
t := 1; s := 1;
UQ := (wQ^t)^-1 * gQ[4];  VQ := gQ[5] * (wQ^s)^-1;
base := [gQ[1], gQ[2], gQ[3], UQ, VQ];
K := sub< Q | UQ, VQ, tbQ, DQ >;
dressQ := [ UQ^(a div 4) * VQ^((a div 2) mod 2) * tbQ^(a mod 2) : a in [0..7] ];
m := [ base[1]*dressQ[7], base[2]*dressQ[7], base[3], base[4], base[5] ];
r := Rel(m);
reps := LayerBasis(K, P[2], P[3]);
Vt, qtar := quo< P[3] | P[4] >;
rows := [];
for i in [1..5] do for b in reps do
  mm := m; mm[i] := m[i]*b;
  Append(~rows, Coord(qtar, Rel(mm) * r^-1));
end for; end for;
RS := RowSpace(Matrix(rows));
hit := 0; N := 2000;
for k in [1..N] do
  if Random(Generic(RS)) in RS then hit +:= 1; end if;
end for;
Say(Sprintf("   L3: %o / %o random layer vectors lie in the image (expected %o = N/2^6)",
    hit, N, N/64));
Say("DONE");
quit;
