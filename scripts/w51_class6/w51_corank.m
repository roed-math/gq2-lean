/*  W51 -- corank of the dressing-defect map, with the K-intersection replaced by a
 *  graded generating set so that class 6 is reachable.
 *
 *      magma -b cls:=5 marks:=0,1 out:=../../data/ck_c5.txt verify:=1 w51_corank.m
 *
 *  Parameters
 *      cls     nilpotency class of the quotient tower (>= 3)
 *      marks   markings, "t,s" pairs separated by ';'   e.g. "0,1;1,1;3,5"
 *      out     output file (appended line by line, so a kill leaves the data behind)
 *      verify  1 = also compute K meet P_j the W50 way and compare (only affordable c <= 5)
 *
 *  ---------------------------------------------------------------------------
 *  WHY THE GENERATING SET IS EXACT (this is a proof, not a heuristic)
 *
 *  Write L_w = P_w/P_{w+1} for the layers of the lower exponent-2 central series of Q,
 *  and K_w = (K meet P_w)P_{w+1}/P_{w+1} for the graded pieces of K = ker lam meet ker nu'.
 *
 *  (i)  [P_{w-1}, Q] is contained in [Q,Q], which is contained in K, and in P_w.  Squares of
 *       elements of K meet P_{w-1} lie in K meet P_w.  So the span
 *           S_w := [L_{w-1}, L_1] + (squares of a basis of K_{w-1})
 *       satisfies S_w subset K_w.  (Squaring is additive modulo [L_{w-1},L_1], so the span of
 *       the squares of a basis is the image of the whole square map.)
 *  (ii) lam(sigma) = c0 is a 2-adic unit, lam(x0) = 1, nu'(sigma) = 1, nu'(x0) = 0, and the
 *       minor det [[c0,1],[1,0]] is a unit.  Put p = sigma^(2^(w-1)), q = x0^(2^(w-1)), both in
 *       P_w.  Then lam(p) = c0*2^(w-1) and lam(q) = 2^(w-1) are nonzero in Z/2^c for w <= c,
 *       and nu'(pq) = 2^(w-1) is nonzero, so none of p, q, pq lies in K: the plane they span
 *       in L_w meets K_w trivially, hence codim K_w >= 2.
 *  (iii) Therefore if the computation finds dim S_w = dim L_w - 2 AND
 *        S_w + <p,q> = L_w, then dim K_w <= dim L_w - 2 = dim S_w <= dim K_w, so S_w = K_w
 *        EXACTLY.  Both conditions are checked at every level and reported as "cert".
 *
 *  A basis of S_w is extracted as a SUBSET of the candidate list (pivot columns of the
 *  transposed matrix), never as a long product of candidates -- at class 6 a product-based
 *  representative would be a word in thousands of pc elements.
 *  ---------------------------------------------------------------------------
 */
SetColumns(0); SetAutoColumns(false); SetSeed(1);
load "../w50_depth_sweep/c0.m";

CLS := StringToInteger(cls);
VERIFY := StringToInteger(verify);
OUT := out; System("rm -f " cat OUT);
procedure Say(str) PrintFile(OUT, str); print str; end procedure;

MARKS := [];
for chunk in Split(marks, ";") do
  ab := Split(chunk, ",");
  Append(~MARKS, [StringToInteger(ab[1]), StringToInteger(ab[2])]);
end for;

F<fs,fx0,fx1,fu,fv> := FreeGroup(5);
RELW := (fx0^fs)^-1 * (fx0^3)^-1 * fx1^2 * (fx1, fx1^fs) * (fu,fv);
G := quo< F | RELW >;
Rel := function(m)
  return (m[2]^m[1])^-1 * (m[2]^3)^-1 * m[3]^2 * (m[3], m[3]^m[1]) * (m[4],m[5]);
end function;

Say(Sprintf("W51 corank probe -- class %o, markings %o, verify %o", CLS, MARKS, VERIFY));

/* ---------------- the tower, built incrementally ---------------- */
tall := Cputime();
PR := pQuotientProcess(G, 2, 1);
for c in [2..CLS] do NextClass(~PR); end for;
Q := ExtractGroup(PR);
tbuild := Cputime(tall);
P := pCentralSeries(Q, 2);
n := NPCgens(Q);
dm := [ Ilog2(#P[i] div #P[i+1]) : i in [1..#P-1] ];
Say(Sprintf("Q_%o : order 2^%o, layers %o  (build %o s, extract+series %o s, mem %o MB)",
    CLS, Ilog2(#Q), dm, tbuild, Cputime(tall)-tbuild, GetMemoryUsage() div (1024*1024)));
assert #dm eq CLS;
assert &+dm eq n;

/* pc generators of a p-quotient are weight graded and P_w is the tail subgroup */
ofs := [0 : w in [1..CLS+1]];
for w in [1..CLS] do ofs[w+1] := ofs[w] + dm[w]; end for;
for w in [1..CLS] do
  assert NPCgens(P[w]) eq n - ofs[w];
  assert Q.(ofs[w]+1) in P[w];
  assert not (Q.(ofs[w]+1) in P[w+1]);
end for;
Say("pc generators are weight graded, P_w = tail subgroup .. OK");

/* cross-check the exponent-vector layer coordinate against the honest quotient-group
   coordinate that W50 used, on random elements of every layer */
if VERIFY eq 1 then
  for w in [1..CLS] do
    Vw, qw0 := quo< P[w] | P[w+1] >;
    bad := 0;
    for k in [1..25] do
      x := Random(P[w]);
      a := Vector(GF(2), [ GF(2)!e : e in Eltseq(Q!x) ][ [ofs[w]+1..ofs[w+1]] ]);
      b := Vector(GF(2), [ GF(2)!e : e in Eltseq(qw0(x)) ]);
      if a ne b then bad +:= 1; end if;
    end for;
    Say(Sprintf("   coord cross-check L%o (Eltseq vs quo map): %o mismatches in 25", w, bad));
  end for;
end if;

/* layer coordinates straight off the exponent vector (no quotient group needed) */
Coord := function(x, w)
  e := Eltseq(x);
  return Vector(GF(2), [ GF(2)!e[k] : k in [ofs[w]+1 .. ofs[w+1]] ]);
end function;
CoordChecked := function(x, w)
  e := Eltseq(x);
  for k in [1..ofs[w]] do assert e[k] eq 0; end for;
  return Vector(GF(2), [ GF(2)!e[k] : k in [ofs[w]+1 .. ofs[w+1]] ]);
end function;

/* a maximal independent SUBSET of a candidate list: pivot columns of the transpose */
IndepSubset := function(cands, w)
  A := Matrix([ Coord(x, w) : x in cands ]);
  E := EchelonForm(Transpose(A));
  piv := [];
  for i in [1..Nrows(E)] do
    d := Depth(E[i]);
    if d ne 0 then Append(~piv, d); end if;
  end for;
  return [ cands[j] : j in piv ], A;
end function;

gQ  := [Q.i : i in [1..5]];
DQ  := DerivedSubgroup(Q);
wQ  := gQ[1] * (gQ[2]^(C0 mod 2^(CLS+2)))^-1;
tbQ := (gQ[2]^2)^-1 * gQ[3];
/* the two elements that certify codim(K_w) >= 2, see the header */
pw := [ gQ[1]^(2^(w-1)) : w in [1..CLS] ];
qw := [ gQ[2]^(2^(w-1)) : w in [1..CLS] ];

/* full-layer generators: the weight-w pc generators */
LGEN := [ [ Q.k : k in [ofs[w]+1 .. ofs[w+1]] ] : w in [1..CLS] ];

/* delta_j depends on m only through m mod P_2 (W50 memo section 5.1), and m mod P_2 depends
   on (t,s) only mod 2 (U = w^-t u and V = v w^-s with w = sigma x0^-c0, c0 odd).  The graded
   K_w is likewise determined by K_1, which is span(x1bar, ubar + t*wbar, vbar + s*wbar).  So
   the whole map delta_j -- image included, not just its rank -- should depend on the marking
   ONLY through (t mod 2, s mod 2).  IMG records im delta per (level, parity) so the run can
   check that directly: markings of equal parity must give the SAME subspace, and markings of
   different parity are expected to differ.  If that holds, four parity classes exhaust the
   corank question over all markings at this class. */
IMG := AssociativeArray();
Say("");
Say("marking | level | target | domain | rank | corank | defect in im | cert | im delta vs same parity | secs");
Say("--------+-------+--------+--------+------+--------+--------------+------+-------------------------+-----");

for e0 in MARKS do
  t := e0[1]; s := e0[2];
  UQ := (wQ^t)^-1 * gQ[4];  VQ := gQ[5] * (wQ^s)^-1;
  base := [gQ[1], gQ[2], gQ[3], UQ, VQ];

  /* ---- the graded generating set for K, level by level ---- */
  KB := [];
  tK := Cputime();
  cand1 := [UQ, VQ, tbQ];
  kb, _ := IndepSubset(cand1, 1);
  Append(~KB, kb);
  for w in [2..CLS-1] do
    cands := [];
    for x in LGEN[w-1] do for i in [1..5] do
      Append(~cands, (x, gQ[i]));
    end for; end for;
    for b in KB[w-1] do Append(~cands, b^2); end for;
    kb, _ := IndepSubset(cands, w);
    Append(~KB, kb);
  end for;
  tKB := Cputime(tK);

  /* ---- certificates: dim = dim L_w - 2 and S_w + <p,q> = L_w ---- */
  certs := [];
  for w in [1..CLS-1] do
    rows := [ Coord(x, w) : x in KB[w] ] cat [ Coord(pw[w], w), Coord(qw[w], w) ];
    full := Rank(Matrix(rows));
    Append(~certs, (#KB[w] eq dm[w]-2) and (full eq dm[w]));
  end for;
  Say(Sprintf("  (t,s) = (%o,%o): K-layer dims %o of %o, cert %o, built in %o s",
      t, s, [#b : b in KB], [dm[w] : w in [1..CLS-1]], certs, tKB));

  if VERIFY eq 1 then
    K := sub< Q | UQ, VQ, tbQ, DQ >;
    Say(Sprintf("   verify: Index(Q,K) = 4^%o ? %o",
        CLS, Index(Q,K) eq 4^CLS));
    for w in [1..CLS-1] do
      tv := Cputime();
      /* NB: PCGenerators of a subgroup live in the subgroup's OWN pc presentation,
         so they must be coerced into Q before their exponent vector means anything. */
      gens := [ Q!x : x in PCGenerators(K meet P[w]) ];
      Aw := Matrix([ Coord(x, w) : x in gens ]);
      Bw := Matrix([ Coord(x, w) : x in KB[w] ]);
      Say(Sprintf("   verify L%o: dim(K meet P_%o layer) = %o, gen-set dim = %o, spans equal: %o  (%o s)",
          w, w, Rank(Aw), Rank(Bw), RowSpace(Aw) eq RowSpace(Bw), Cputime(tv)));
    end for;
  end if;

  /* ---- the lift, level by level, and the corank at each ---- */
  dressQ := [ UQ^(a div 4) * VQ^((a div 2) mod 2) * tbQ^(a mod 2) : a in [0..7] ];
  fc := 4*(s mod 2) + 2*(t mod 2);
  m := [ base[1]*dressQ[fc+1], base[2]*dressQ[fc+1], base[3], base[4], base[5] ];
  r := Rel(m);
  for j in [3..CLS] do
    tj := Cputime();
    if r in P[j+1] then
      Say(Sprintf("%2o %2o   |  L%o   | %6o | %6o |    - |      - | (already 1)  |   -  | %o",
          t, s, j, dm[j], 5*#KB[j-1], Cputime(tj)));
      continue;
    end if;
    reps := KB[j-1];
    rows := [];
    for i in [1..5] do for b in reps do
      mm := m; mm[i] := m[i]*b;
      Append(~rows, Coord(Rel(mm) * r^-1, j));
    end for; end for;
    A   := Matrix(rows);
    RS  := RowSpace(A);
    tar := CoordChecked(r^-1, j);
    rk  := Dimension(RS);
    key := [j, t mod 2, s mod 2];
    if IsDefined(IMG, key) then
      same := (IMG[key] eq RS) select "same as first (t,s) parity" else "*** DIFFERS ***";
    else
      IMG[key] := RS; same := Sprintf("(reference for parity %o%o)", t mod 2, s mod 2);
    end if;
    Say(Sprintf("%2o %2o   |  L%o   | %6o | %6o | %4o | %6o | %-12o | %-4o | %-23o | %o",
        t, s, j, dm[j], #rows, rk, dm[j]-rk, tar in RS, certs[j-1], same, Cputime(tj)));
    if j eq CLS and assigned ctrl then
      /* W50's control: a random layer vector should land in im delta with probability 2^-corank */
      NC := StringToInteger(ctrl); hit := 0;
      for k in [1..NC] do
        if Random(Generic(RS)) in RS then hit +:= 1; end if;
      end for;
      Say(Sprintf("   control L%o (t,s)=(%o,%o): %o of %o random layer vectors lie in im delta (codim %o predicts %o)",
          j, t, s, hit, NC, dm[j]-rk, RealField(4)!(NC/2^(dm[j]-rk))));
    end if;
    ok, x := IsConsistent(A, tar);
    if not ok then
      Say(Sprintf("   *** INFEASIBLE at L%o for (t,s) = (%o,%o) ***", j, t, s));
      break;
    end if;
    nb := #reps;
    for i in [1..5] do for l in [1..nb] do
      if x[(i-1)*nb + l] ne 0 then m[i] := m[i] * reps[l]; end if;
    end for; end for;
    r := Rel(m);
    assert r in P[j+1];
  end for;
  if r eq Id(Q) then
    Say(Sprintf("   (t,s) = (%o,%o): R(m) = 1 in Q_%o  -- solvable", t, s, CLS));
  end if;
end for;
Say("DONE");
quit;
