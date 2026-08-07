/*  W50 depth sweep, v2 -- same model as w50_sweep.m, with the layer bases hoisted out
 *  of the survivor loop and a selectable marking sample (for class 5, where the full
 *  (Z/32)^2 grid is out of budget).
 *
 *      magma -b cls:=5 mode:=sample out:=res_c5.txt w50_sweep2.m
 *      magma -b cls:=4 mode:=full   out:=res_c4b.txt w50_sweep2.m
 *
 *  mode = full   : every (t,s) in (Z/2^cls)^2
 *         sample : t,s in [0..7] plus a valuation-stratified tail (see MARKS below)
 */
SetColumns(0); SetAutoColumns(false); SetSeed(1);
load "c0.m";

CLS := StringToInteger(cls);
OUT := out;
MODE := "full"; if assigned mode then MODE := mode; end if;
System("rm -f " cat OUT);
procedure Say(str) PrintFile(OUT, str); end procedure;

F<fs,fx0,fx1,fu,fv> := FreeGroup(5);
RELW := (fx0^fs)^-1 * (fx0^3)^-1 * fx1^2 * (fx1, fx1^fs) * (fu,fv);
G := quo< F | RELW >;
Rel := function(m)
  return (m[2]^m[1])^-1 * (m[2]^3)^-1 * m[3]^2 * (m[3], m[3]^m[1]) * (m[4],m[5]);
end function;
Coord := function(q,x) return Vector(GF(2),[GF(2)!e : e in Eltseq(q(x))]); end function;

Say(Sprintf("W50 depth sweep v2 -- class %o, mode %o", CLS, MODE));
Say(Sprintf("relator: %o", RELW));

tt := Cputime();
Q, phi := pQuotient(G, 2, CLS);
P  := pCentralSeries(Q, 2);
gQ := [phi(G.i) : i in [1..5]];
DQ := DerivedSubgroup(Q);
wQ := gQ[1] * (gQ[2]^(C0 mod 2^(CLS+2)))^-1;
tbQ:= (gQ[2]^2)^-1 * gQ[3];
Say(Sprintf("Q_%o : order 2^%o, layers %o, Q^ab %o  (%o s)", CLS, Ilog2(#Q),
   [Ilog2(#P[i] div #P[i+1]) : i in [1..#P-1]], AbelianQuotientInvariants(Q), Cputime(tt)));
assert Rel(gQ) eq Id(Q);
Say("cross-check: Rel(standard generators) = 1 in Q .. OK");

/* class-two quotient: the level-one gate */
Q2, phi2 := pQuotient(G, 2, 2);
P2s := pCentralSeries(Q2, 2);
g2  := [phi2(G.i) : i in [1..5]];
w2  := g2[1] * (g2[2]^(C0 mod 16))^-1;
tb2 := (g2[2]^2)^-1 * g2[3];
W1, q1 := quo< Q2 | P2s[2] >;

StageA := function(t, s)
  U2 := (w2^t)^-1 * g2[4];  V2 := g2[5] * (w2^s)^-1;
  base2 := [g2[1], g2[2], g2[3], U2, V2];
  dr := [ U2^(a div 4) * V2^((a div 2) mod 2) * tb2^(a mod 2) : a in [0..7] ];
  surv := [];
  for code in [0..8^5-1] do
    e := [ (code div 8^(i-1)) mod 8 : i in [1..5] ];
    m := [ base2[i] * dr[e[i]+1] : i in [1..5] ];
    if Rel(m) ne Id(Q2) then continue; end if;
    if Rank(Matrix(GF(2),5,5,[Coord(q1,m[i])[k] : k in [1..5], i in [1..5]])) ne 5 then
      continue; end if;
    Append(~surv, e);
  end for;
  return surv;
end function;

tt := Cputime();
Acache := AssociativeArray();
for a in [0..3] do for b in [0..3] do Acache[[a,b]] := StageA(a,b); end for; end for;
Say(Sprintf("Stage-A cache built in %o s; survivor counts %o (uniformly 6 = |GL_2(F_2)|)",
   Cputime(tt), {* #Acache[[a,b]] : a in [0..3], b in [0..3] *}));

LayerBasis := function(K, Pj, Pj1)
  V, q := quo< Pj | Pj1 >;
  gens := [ x : x in PCGenerators(K meet Pj) ];
  A := Matrix(GF(2), [ [ GF(2)!e : e in Eltseq(q(x)) ] : x in gens ]);
  E, T := EchelonForm(A);
  r := Rank(A);
  reps := [];
  for k in [1..r] do
    y := Id(Q);
    for l in [1..#gens] do if T[k][l] ne 0 then y := y * gens[l]; end if; end for;
    Append(~reps, y);
  end for;
  return reps, NPCgens(V);
end function;

/* ------------------------------------------------------------------ markings */
MOD := 2^CLS;
MARKS := [];
if MODE eq "full" then
  for t in [0..MOD-1] do for s in [0..MOD-1] do
    if t ne 0 or s ne 0 then Append(~MARKS, [t,s]); end if;
  end for; end for;
else
  if MODE ne "tail" then
    for t in [0..7] do for s in [0..7] do
      if t ne 0 or s ne 0 then Append(~MARKS, [t,s]); end if;
    end for; end for;
  end if;
  EXTRA := [[0,8],[8,0],[8,8],[0,16],[16,0],[16,16],[1,8],[8,1],[1,16],[16,1],
            [3,8],[8,3],[2,16],[16,2],[4,8],[8,4],[12,20],[20,12],[9,15],[15,9],
            [5,11],[11,5],[31,31],[31,1],[1,31],[17,17],[24,8],[8,24],[28,4],[4,28],
            [8,16],[16,8],[0,24],[24,0],[2,8],[8,2],[6,10],[10,6],[13,26],[26,13]];
  for e in EXTRA do
    if e[1] lt MOD and e[2] lt MOD then Append(~MARKS, e); end if;
  end for;
end if;
Say(Sprintf("markings: (t,s) in (Z/%o)^2, %o probed", MOD, #MARKS));
Say("");
Say("  t   s | #lvl1 | verdict    | delta ranks  [level: rank/target, dim ker] | s");
Say("--------+-------+------------+------------------------------------------------");

nsolv := 0; ninf := 0; infeasible := []; surjfail := 0; firstmark := true;

for e0 in MARKS do
  t := e0[1]; s := e0[2];
  tm := Cputime();
  UQ := (wQ^t)^-1 * gQ[4];  VQ := gQ[5] * (wQ^s)^-1;
  base := [gQ[1], gQ[2], gQ[3], UQ, VQ];
  K := sub< Q | UQ, VQ, tbQ, DQ >;
  if firstmark then
    assert Index(Q, K) eq 4^CLS;      // K = ker lam cap ker nu' exactly (constraint 2)
    Say(Sprintf("       (constraint-2 audit at the first marking: Index(Q,K) = 4^%o .. OK)", CLS));
    firstmark := false;
  end if;

  LB := []; DT := [];
  for j in [3..CLS] do
    r0, d0 := LayerBasis(K, P[j-1], P[j]);
    LB[j] := r0;
    Vt, qtar := quo< P[j] | P[j+1] >;
    DT[j] := NPCgens(Vt);
  end for;

  surv := Acache[[t mod 4, s mod 4]];
  dressQ := [ UQ^(a div 4) * VQ^((a div 2) mod 2) * tbQ^(a mod 2) : a in [0..7] ];

  verdict := "INFEASIBLE"; rankinfo := ""; witness := [];
  for e in surv do
    m := [ base[i] * dressQ[e[i]+1] : i in [1..5] ];
    r := Rel(m);
    assert r in P[3];
    good := true; info := "";
    for j in [3..CLS] do
      if r eq Id(Q) then break; end if;
      if r in P[j+1] then continue; end if;
      reps := LB[j];
      Vt, qtar := quo< P[j] | P[j+1] >;
      rows := [];
      for i in [1..5] do
        for b in reps do
          mm := m; mm[i] := m[i]*b;
          Append(~rows, Coord(qtar, Rel(mm) * r^-1));
        end for;
      end for;
      A := Matrix(rows);
      ok, x := IsConsistent(A, Coord(qtar, r^-1));
      info cat:= Sprintf(" [L%o:%o/%o,k%o]", j, Rank(A), DT[j], Nrows(A)-Rank(A));
      if Rank(A) lt DT[j] then surjfail +:= 1; end if;
      if not ok then good := false; break; end if;
      nb := #reps;
      for i in [1..5] do
        for l in [1..nb] do
          if x[(i-1)*nb + l] ne 0 then m[i] := m[i] * reps[l]; end if;
        end for;
      end for;
      r := Rel(m);
      assert r in P[j+1];
    end for;
    if good and r eq Id(Q) then
      W1b, qq1 := quo< Q | P[2] >;
      assert Rank(Matrix(GF(2),5,5,[Coord(qq1,m[i])[k] : k in [1..5], i in [1..5]])) eq 5;
      for i in [1..5] do assert (base[i]^-1 * m[i]) in K; end for;
      verdict := "solvable"; rankinfo := info; witness := e; break;
    end if;
  end for;

  if verdict eq "solvable" then nsolv +:= 1; else ninf +:= 1; Append(~infeasible,[t,s]); end if;
  Say(Sprintf("%3o %3o | %5o | %-10o |%o (lvl1 %o) | %o",
      t, s, #surv, verdict, rankinfo, witness, Cputime(tm)));
end for;

Say("");
Say(Sprintf("SUMMARY class %o : solvable %o, INFEASIBLE %o, non-surjective delta events %o",
    CLS, nsolv, ninf, surjfail));
if #infeasible gt 0 then Say(Sprintf("INFEASIBLE markings: %o", infeasible)); end if;
Say("DONE");
quit;
