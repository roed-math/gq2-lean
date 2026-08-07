/*  W50 -- the DISCRETE-SHADOW probe, and the per-slot anatomy of the defect.
 *
 *      magma -b cls:=4 out:=reg_c4.txt w50_regime.m
 *
 *  Runs the same lift as w50_sweep.m but with the set of DRESSABLE SLOTS restricted,
 *  at level one and at every deeper level alike:
 *
 *    regime "handle"  : only the two handle slots (u,v) may be dressed.  This is exactly
 *                       the discrete/SL_2 regime -- the mapping-class moves of the handle
 *                       pair, which in the DISCRETE group preserve the SL_2(Z)-invariant
 *                       of the nu'-row pair (t,s) and therefore cannot clear it.
 *    regime "core"    : only sigma, x0, x1 may be dressed.
 *    regime "sigmax0" : only sigma and x0.
 *    regime "x0"      : only x0 (the slot the class-two balance forces).
 *    regime "full"    : all five (= SqArbRelWord).
 *
 *  It also reports, level by level, the rank of the defect map delta restricted to each
 *  single slot -- "which slot-coordinates the defect reads".
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
Say(Sprintf("W50 regime probe -- class %o, Q order 2^%o, layers %o",
    CLS, Ilog2(#Q), [Ilog2(#P[i] div #P[i+1]) : i in [1..#P-1]]));

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
  return reps, NPCgens(V);
end function;

REGIMES := [ <"handle", {4,5}>, <"core", {1,2,3}>, <"sigmax0", {1,2}>,
             <"x0", {2}>, <"full", {1,2,3,4,5}> ];

MOD := 2^CLS;
MARKS := [];
for t in [0..7] do for s in [0..7] do
  if (t ne 0 or s ne 0) and t lt MOD and s lt MOD then Append(~MARKS, [t,s]); end if;
end for; end for;

Say("");
Say("regime      |  t   s | v2(t) v2(s) | #lvl1 | verdict");
Say("------------+--------+-------------+-------+----------");

summary := AssociativeArray();
for rg in REGIMES do summary[rg[1]] := [0,0]; end for;

for rg in REGIMES do
 nm := rg[1]; SL := rg[2];
 for e0 in MARKS do
  t := e0[1]; s := e0[2];
  UQ := (wQ^t)^-1 * gQ[4];  VQ := gQ[5] * (wQ^s)^-1;
  base := [gQ[1], gQ[2], gQ[3], UQ, VQ];
  K := sub< Q | UQ, VQ, tbQ, DQ >;
  dressQ := [ UQ^(a div 4) * VQ^((a div 2) mod 2) * tbQ^(a mod 2) : a in [0..7] ];

  // level-one enumeration restricted to the dressable slots
  codes := [ [0,0,0,0,0] ];
  for i in [1..5] do
    if i in SL then
      nc := [];
      for c in codes do for a in [0..7] do
        d := c; d[i] := a; Append(~nc, d);
      end for; end for;
      codes := nc;
    end if;
  end for;

  W1b, qq1 := quo< Q | P[2] >;
  surv := [];
  for c in codes do
    m := [ base[i] * dressQ[c[i]+1] : i in [1..5] ];
    if not (Rel(m) in P[3]) then continue; end if;
    if Rank(Matrix(GF(2),5,5,[Coord(qq1,m[i])[k] : k in [1..5], i in [1..5]])) ne 5 then
      continue; end if;
    Append(~surv, c);
  end for;

  LB := [];
  for j in [3..CLS] do LB[j] := LayerBasis(K, P[j-1], P[j]); end for;

  verdict := "INFEASIBLE";
  for c in surv do
    m := [ base[i] * dressQ[c[i]+1] : i in [1..5] ];
    r := Rel(m); good := true;
    for j in [3..CLS] do
      if r eq Id(Q) then break; end if;
      if r in P[j+1] then continue; end if;
      reps := LB[j];
      Vt, qtar := quo< P[j] | P[j+1] >;
      slotlist := Sort(SetToSequence(SL));
      rows := [];
      for i in slotlist do
        for b in reps do
          mm := m; mm[i] := m[i]*b;
          Append(~rows, Coord(qtar, Rel(mm) * r^-1));
        end for;
      end for;
      A := Matrix(rows);
      ok, x := IsConsistent(A, Coord(qtar, r^-1));
      if not ok then good := false; break; end if;
      nb := #reps;
      for k in [1..#slotlist] do
        i := slotlist[k];
        for l in [1..nb] do
          if x[(k-1)*nb + l] ne 0 then m[i] := m[i] * reps[l]; end if;
        end for;
      end for;
      r := Rel(m);
    end for;
    if good and r eq Id(Q) then verdict := "solvable"; break; end if;
  end for;

  v2t := t eq 0 select 99 else Valuation(t,2);
  v2s := s eq 0 select 99 else Valuation(s,2);
  Say(Sprintf("%-11o |%3o %3o | %3o   %3o   | %5o | %o", nm, t, s, v2t, v2s, #surv, verdict));
  u := summary[nm];
  if verdict eq "solvable" then u[1] +:= 1; else u[2] +:= 1; end if;
  summary[nm] := u;
 end for;
end for;

Say("");
Say("SUMMARY (63 uncleared markings, (t,s) in [0..7]^2 minus (0,0)):");
for rg in REGIMES do
  u := summary[rg[1]];
  Say(Sprintf("   regime %-9o : solvable %o, INFEASIBLE %o", rg[1], u[1], u[2]));
end for;

/* ---- per-slot anatomy of the defect map at the full regime ---------------- */
Say("");
Say("per-slot rank of the defect map delta_j (full regime, marking (t,s)=(1,1)):");
t := 1; s := 1;
UQ := (wQ^t)^-1 * gQ[4];  VQ := gQ[5] * (wQ^s)^-1;
base := [gQ[1], gQ[2], gQ[3], UQ, VQ];
K := sub< Q | UQ, VQ, tbQ, DQ >;
dressQ := [ UQ^(a div 4) * VQ^((a div 2) mod 2) * tbQ^(a mod 2) : a in [0..7] ];
fc := 4*(s mod 2) + 2*(t mod 2);
m := [ base[1]*dressQ[fc+1], base[2]*dressQ[fc+1], base[3], base[4], base[5] ];
r := Rel(m);
for j in [3..CLS] do
  if r in P[j+1] then Say(Sprintf("   L%o : defect already trivial", j)); continue; end if;
  reps := LayerBasis(K, P[j-1], P[j]);
  Vt, qtar := quo< P[j] | P[j+1] >;
  per := [];
  allrows := [];
  for i in [1..5] do
    rows := [];
    for b in reps do
      mm := m; mm[i] := m[i]*b;
      Append(~rows, Coord(qtar, Rel(mm) * r^-1));
    end for;
    Append(~per, Rank(Matrix(rows)));
    allrows cat:= rows;
  end for;
  A := Matrix(allrows);
  Say(Sprintf("   L%o : target dim %o, joint rank %o, per-slot ranks (s,x0,x1,u,v) = %o",
      j, NPCgens(Vt), Rank(A), per));
  ok, x := IsConsistent(A, Coord(qtar, r^-1));
  nb := #reps;
  for i in [1..5] do
    for l in [1..nb] do
      if x[(i-1)*nb + l] ne 0 then m[i] := m[i] * reps[l]; end if;
    end for;
  end for;
  r := Rel(m);
end for;
Say("DONE");
quit;
