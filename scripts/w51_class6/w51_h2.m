/*  W51 -- the h = 2 corank, one class deeper than W50 managed.
 *
 *      magma -b cls:=5 marks:="0,1;1,1;1,0" out:=../../data/h2_c5.txt w51_h2.m
 *
 *  D_sq 2 on sigma, x0, x1, u1, v1, u2, v2 (sqRank 2 = 7), relator
 *      sqWord(sigma, x0, x1) * [u1,v1] * [u2,v2],
 *  nu' = nuSel 2 0 t s, so the marking sits on the FIRST handle and the second handle's
 *  letters are lam- and nu'-trivial and therefore lie in K.  W50 measured corank 8 = d + 1
 *  (d = sqRank 2 = 7) at L3 and L4; this pushes the same number to L5.
 *
 *  Same generating-set method as w51_corank.m, and the same certificate: K_w contains
 *  [L_{w-1}, L_1] plus the squares of a basis of K_{w-1}, while sigma^(2^(w-1)) and
 *  x0^(2^(w-1)) span a plane meeting K_w trivially (lam(sigma) = c0 a unit, lam(x0) = 1,
 *  nu'(sigma) = 1, nu'(x0) = 0, minor a unit), so codim K_w >= 2 and the two measured
 *  conditions pin K_w exactly.
 */
SetColumns(0); SetAutoColumns(false); SetSeed(1);
load "../w50_depth_sweep/c0.m";

CLS := StringToInteger(cls);
OUT := out; System("rm -f " cat OUT);
procedure Say(str) PrintFile(OUT, str); print str; end procedure;

MARKS := [];
for chunk in Split(marks, ";") do
  ab := Split(chunk, ",");
  Append(~MARKS, [StringToInteger(ab[1]), StringToInteger(ab[2])]);
end for;

F<fs,fx0,fx1,fu1,fv1,fu2,fv2> := FreeGroup(7);
RELW := (fx0^fs)^-1 * (fx0^3)^-1 * fx1^2 * (fx1, fx1^fs) * (fu1,fv1) * (fu2,fv2);
G := quo< F | RELW >;
Rel := function(m)
  return (m[2]^m[1])^-1 * (m[2]^3)^-1 * m[3]^2 * (m[3], m[3]^m[1]) * (m[4],m[5]) * (m[6],m[7]);
end function;

Say(Sprintf("W51 h=2 corank probe -- class %o, markings %o", CLS, MARKS));
tall := Cputime();
PR := pQuotientProcess(G, 2, 1);
for c in [2..CLS] do NextClass(~PR); end for;
Q := ExtractGroup(PR);
tbuild := Cputime(tall);
P := pCentralSeries(Q, 2);
n := NPCgens(Q);
dm := [ Ilog2(#P[i] div #P[i+1]) : i in [1..#P-1] ];
ofs := [0 : w in [1..CLS+1]];
for w in [1..CLS] do ofs[w+1] := ofs[w] + dm[w]; end for;
for w in [1..CLS] do
  assert NPCgens(P[w]) eq n - ofs[w];
  assert Q.(ofs[w]+1) in P[w];
  assert not (Q.(ofs[w]+1) in P[w+1]);
end for;
Say(Sprintf("Q_%o : order 2^%o, layers %o  (build %o s, total %o s, mem %o MB)",
    CLS, Ilog2(#Q), dm, tbuild, Cputime(tall), GetMemoryUsage() div (1024*1024)));

Coord := function(x, w)
  e := Eltseq(x);
  return Vector(GF(2), [ GF(2)!e[k] : k in [ofs[w]+1 .. ofs[w+1]] ]);
end function;
IndepSubset := function(cands, w)
  E := EchelonForm(Transpose(Matrix([ Coord(x, w) : x in cands ])));
  piv := [];
  for i in [1..Nrows(E)] do
    d := Depth(E[i]);
    if d ne 0 then Append(~piv, d); end if;
  end for;
  return [ cands[j] : j in piv ];
end function;

gQ  := [Q.i : i in [1..7]];
assert Rel(gQ) eq Id(Q);
Say("cross-check: Rel(standard generators) = 1 in Q .. OK");
wQ  := gQ[1] * (gQ[2]^(C0 mod 2^(CLS+2)))^-1;
tbQ := (gQ[2]^2)^-1 * gQ[3];
pw := [ gQ[1]^(2^(w-1)) : w in [1..CLS] ];
qw := [ gQ[2]^(2^(w-1)) : w in [1..CLS] ];
LGEN := [ [ Q.k : k in [ofs[w]+1 .. ofs[w+1]] ] : w in [1..CLS] ];

COMM := [ [] : w in [1..CLS] ];
for w in [2..CLS-1] do
  cs := [];
  for x in LGEN[w-1] do for i in [1..7] do Append(~cs, (x, gQ[i])); end for; end for;
  COMM[w] := cs;
end for;

Say("");
Say("marking | level | target | domain | rank | corank | defect in im | cert | secs");
Say("--------+-------+--------+--------+------+--------+--------------+------+------");

for e0 in MARKS do
  t := e0[1]; s := e0[2];
  UQ := (wQ^t)^-1 * gQ[4];  VQ := gQ[5] * (wQ^s)^-1;
  base := [gQ[1], gQ[2], gQ[3], UQ, VQ, gQ[6], gQ[7]];

  KB := [ IndepSubset([UQ, VQ, tbQ, gQ[6], gQ[7]], 1) ];
  for w in [2..CLS-1] do
    Append(~KB, IndepSubset(COMM[w] cat [ b^2 : b in KB[w-1] ], w));
  end for;
  certs := [];
  for w in [1..CLS-1] do
    rows := [ Coord(x, w) : x in KB[w] ] cat [ Coord(pw[w], w), Coord(qw[w], w) ];
    Append(~certs, (#KB[w] eq dm[w]-2) and (Rank(Matrix(rows)) eq dm[w]));
  end for;
  Say(Sprintf("  (t,s) = (%o,%o): K-layer dims %o of %o, cert %o",
      t, s, [#b : b in KB], [dm[w] : w in [1..CLS-1]], certs));

  /* level one: the forced core dressing U^-s V^t on sigma and x0, everything else trivial */
  d0 := UQ^(s mod 2) * VQ^(t mod 2);
  m := [base[1]*d0, base[2]*d0, base[3], base[4], base[5], base[6], base[7]];
  r := Rel(m);
  for j in [3..CLS] do
    tj := Cputime();
    if r in P[j+1] then
      Say(Sprintf("%2o %2o   |  L%o   | %6o | %6o |    - |      - | (already 1)  |   -  | -", t, s, j, dm[j], 7*#KB[j-1]));
      continue;
    end if;
    reps := KB[j-1];
    rows := [];
    for i in [1..7] do for b in reps do
      mm := m; mm[i] := m[i]*b;
      Append(~rows, Coord(Rel(mm) * r^-1, j));
    end for; end for;
    A := Matrix(rows); RS := RowSpace(A); tar := Coord(r^-1, j);
    Say(Sprintf("%2o %2o   |  L%o   | %6o | %6o | %4o | %6o | %-12o | %-4o | %o",
        t, s, j, dm[j], #rows, Dimension(RS), dm[j]-Dimension(RS), tar in RS, certs[j-1], Cputime(tj)));
    ok, x := IsConsistent(A, tar);
    if not ok then Say(Sprintf("   *** INFEASIBLE at L%o for (t,s) = (%o,%o) ***", j, t, s)); break; end if;
    nb := #reps;
    for i in [1..7] do for l in [1..nb] do
      if x[(i-1)*nb + l] ne 0 then m[i] := m[i] * reps[l]; end if;
    end for; end for;
    r := Rel(m);
  end for;
  if r eq Id(Q) then Say(Sprintf("   (t,s) = (%o,%o): R(m) = 1 in Q_%o  -- solvable", t, s, CLS)); end if;
end for;
Say("DONE");
quit;
