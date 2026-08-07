/*  W50 depth sweep -- the arbitrary-dressing residual
 *      SqArbRelWord 1  <->  SqClearingStep 1  <->  SqLamMarkTransitivity 1
 *  probed in the class-c pro-2 quotients of D_sq 1, for c = 2,3,4,5.
 *
 *  Invocation:
 *      magma -b cls:=4 out:=res_c4.txt w50_sweep.m
 *  optional:  tstep (stride through the (t,s) grid, default 1)
 *             first:=1  (stop at the first infeasible marking)
 *
 *  ---------------------------------------------------------------------------------
 *  MODEL (extracted from the Lean sources; see docs/dyadic/w50-depth-sweep.md)
 *
 *    G  = D_sq 1 = <s,x0,x1,u,v | (x0^s)^-1 x0^-3 x1^2 [x1,x1^s] [u,v]>       (Cores.lean)
 *    lam(s,x0,x1,u,v) = (c0, 1, 2, 0, 0)                                (HandleMixFixesCore.lean)
 *    nu'(s,x0,x1,u,v) = (1, 0, 0, t, s)   = nuSel 1 0 t s                  (HandleEichler.lean)
 *    w  = s * x0^-c0     (the pivot; lam(w)=0, nu'(w)=1)                    (Certificate.lean)
 *    U  = w^-t * u ,  V = v * w^-s        (the cleared handle letters)         (LamFrames.lean)
 *    base = (s, x0, x1, U, V)                                    (sqArbBase, ArbFrames.lean)
 *    m i  = base i * a i ,   a i in K = ker lam cap ker nu'       (sqArbFrame, ArbFrames.lean)
 *
 *  The two enforced constraints:
 *    (1) SqModTwoIndep: the five slot images independent in H_1 (x) F_2      (ArbFrames S2)
 *    (2) Phi(K) = <Phi(U), Phi(V), Phi(tbar), [Im Phi, Im Phi]>, tbar = x0^-2 x1;
 *        asserted below to have index 4^c, i.e. to be exactly ker lam cap ker nu'.
 */

SetColumns(0); SetAutoColumns(false); SetSeed(1);
load "c0.m";                       // C0 := sqPivotExp mod 2^64  (from padic_c0.py)

CLS  := StringToInteger(cls);
OUT  := out;
TSTEP := 1; if assigned tstep then TSTEP := StringToInteger(tstep); end if;
FIRST := 0; if assigned first then FIRST := StringToInteger(first); end if;
System("rm -f " cat OUT);

procedure Say(str)
  PrintFile(OUT, str);
end procedure;

/* ---------------------------------------------------------------- the group */

F<fs,fx0,fx1,fu,fv> := FreeGroup(5);
RELW := (fx0^fs)^-1 * (fx0^3)^-1 * fx1^2 * (fx1, fx1^fs) * (fu,fv);
G := quo< F | RELW >;

Rel := function(m)
  return (m[2]^m[1])^-1 * (m[2]^3)^-1 * m[3]^2 * (m[3], m[3]^m[1]) * (m[4],m[5]);
end function;

Say(Sprintf("W50 depth sweep -- class %o", CLS));
Say(Sprintf("relator: %o", RELW));
Say(Sprintf("c0 = sqPivotExp = %o mod 2^64  (odd: %o)", C0, IsOdd(C0)));

/* ---------------------------------------------- the class-CLS p-quotient */

tt := Cputime();
Q,  phi  := pQuotient(G, 2, CLS);
P   := pCentralSeries(Q, 2);            // P[1]=Q, ..., P[CLS+1]=1
gQ  := [phi(G.i) : i in [1..5]];
DQ  := DerivedSubgroup(Q);
c0   := C0 mod 2^(CLS+2);
wQ   := gQ[1] * (gQ[2]^c0)^-1;
tbQ  := (gQ[2]^2)^-1 * gQ[3];
Say(Sprintf("Q_%o : order 2^%o, layers %o, built in %o s",
    CLS, Ilog2(#Q), [Ilog2(#P[i] div #P[i+1]) : i in [1..#P-1]], Cputime(tt)));
assert Rel(gQ) eq Id(Q);
Say("cross-check: Rel(standard generators) = 1 in Q .. OK");
Say(Sprintf("Q^ab = %o", AbelianQuotientInvariants(Q)));

/* the class-2 quotient, where the level-1 (class-two balance) filter lives */
Q2, phi2 := pQuotient(G, 2, 2);
P2s := pCentralSeries(Q2, 2);
g2  := [phi2(G.i) : i in [1..5]];
w2  := g2[1] * (g2[2]^(C0 mod 16))^-1;
tb2 := (g2[2]^2)^-1 * g2[3];
W1, q1 := quo< Q2 | P2s[2] >;

/* --------------------------------------------------- generic helpers */

Coord := function(q, x)
  return Vector(GF(2), [ GF(2)!e : e in Eltseq(q(x)) ]);
end function;

/* a basis of  (K meet Pj)Pj1/Pj1  inside  Pj/Pj1, with group representatives */
LayerBasis := function(K, Pj, Pj1)
  V, q := quo< Pj | Pj1 >;
  d := NPCgens(V);
  gens := [ x : x in PCGenerators(K meet Pj) ];
  if #gens eq 0 or d eq 0 then return [ Id(Pj) : i in [1..0] ], d; end if;
  A := Matrix(GF(2), [ [ GF(2)!e : e in Eltseq(q(x)) ] : x in gens ]);
  E, T := EchelonForm(A);
  r := Rank(A);
  reps := [];
  for k in [1..r] do
    y := Id(Parent(gens[1]));
    for l in [1..#gens] do
      if T[k][l] ne 0 then y := y * gens[l]; end if;
    end for;
    Append(~reps, y);
  end for;
  return reps, d;
end function;

/* ---------------------------------------------------------------------------
 *  Stage A -- the level-one enumeration (the class-two balance gate).
 *  a i is free in K; modulo K meet P_2 it is  U^al V^be tbar^ga, al,be,ga in F_2,
 *  so 8 choices per slot.  R(m) in P_3 is decided in Q_2 = Q/P_3.
 *  Depends on (t,s) only mod 4 (the exponent of Q_2), so it is cached.
 * ------------------------------------------------------------------------- */

StageA := function(t, s)
  U2 := (w2^t)^-1 * g2[4];
  V2 := g2[5] * (w2^s)^-1;
  base2 := [g2[1], g2[2], g2[3], U2, V2];
  dr := [ U2^(a div 4) * V2^((a div 2) mod 2) * tb2^(a mod 2) : a in [0..7] ];
  surv := [];
  for code in [0..8^5-1] do
    e := [ (code div 8^(i-1)) mod 8 : i in [1..5] ];
    m := [ base2[i] * dr[e[i]+1] : i in [1..5] ];
    if Rel(m) ne Id(Q2) then continue; end if;
    M := Matrix(GF(2), 5, 5, [ Coord(q1, m[i])[k] : k in [1..5], i in [1..5] ]);
    if Rank(M) ne 5 then continue; end if;     // SqModTwoIndep
    Append(~surv, e);
  end for;
  return surv;
end function;

tt := Cputime();
Acache := AssociativeArray();
for a in [0..3] do for b in [0..3] do
  Acache[[a,b]] := StageA(a, b);
end for; end for;
Say(Sprintf("Stage-A cache (16 residues mod 4) built in %o s; survivor counts %o",
   Cputime(tt), [ #Acache[[a,b]] : a in [0..3], b in [0..3] ]));

/* ---------------------------------------------------------------- main sweep */

MOD := 2^CLS;                      // (t,s) matter exactly mod 2^CLS at class CLS
Say(Sprintf("markings: (t,s) in (Z/%o)^2, stride %o", MOD, TSTEP));
Say("");
Say("  t   s | #lvl1 | verdict    | delta ranks  [level: rank/target, dim ker]");
Say("--------+-------+------------+---------------------------------------------");

nsolv := 0; ninf := 0;
infeasible := [];
surjfail := 0;

for t in [0..MOD-1 by TSTEP] do
 for s in [0..MOD-1 by TSTEP] do
  if t eq 0 and s eq 0 then continue; end if;   // already cleared: nothing to do

  UQ := (wQ^t)^-1 * gQ[4];
  VQ := gQ[5] * (wQ^s)^-1;
  base := [gQ[1], gQ[2], gQ[3], UQ, VQ];
  K := sub< Q | UQ, VQ, tbQ, DQ >;
  assert Index(Q, K) eq 4^CLS;        // == index of ker lam cap ker nu'  (constraint 2)

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
      reps, dsrc := LayerBasis(K, P[j-1], P[j]);
      Vt, qtar := quo< P[j] | P[j+1] >;
      dtar := NPCgens(Vt);
      rows := [];
      for i in [1..5] do
        for b in reps do
          mm := m; mm[i] := m[i]*b;
          Append(~rows, Coord(qtar, Rel(mm) * r^-1));
        end for;
      end for;
      A := Matrix(rows);
      ok, x := IsConsistent(A, Coord(qtar, r^-1));
      info cat:= Sprintf(" [L%o:%o/%o,k%o]", j, Rank(A), dtar, Nrows(A)-Rank(A));
      if Rank(A) lt dtar then surjfail +:= 1; end if;
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
      MM := Matrix(GF(2), 5, 5, [ Coord(qq1, m[i])[k] : k in [1..5], i in [1..5] ]);
      assert Rank(MM) eq 5;                                    // constraint (1)
      for i in [1..5] do assert (base[i]^-1 * m[i]) in K; end for;   // constraint (2)
      verdict := "solvable"; rankinfo := info; witness := e;
      break;
    end if;
  end for;

  if verdict eq "solvable" then nsolv +:= 1; else ninf +:= 1; Append(~infeasible, [t,s]); end if;
  Say(Sprintf("%3o %3o | %5o | %-10o |%o  (lvl1 %o)", t, s, #surv, verdict, rankinfo, witness));
  if FIRST eq 1 and verdict ne "solvable" then break t; end if;
 end for;
end for;

Say("");
Say(Sprintf("SUMMARY class %o : solvable %o, INFEASIBLE %o, non-surjective delta events %o",
    CLS, nsolv, ninf, surjfail));
if #infeasible gt 0 then
  Say(Sprintf("INFEASIBLE markings: %o", infeasible));
end if;
Say("DONE");
quit;
