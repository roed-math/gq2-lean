/*  W52-VANISH -- the discrimination experiment: is the containment an identity about THIS
 *  relator, or about ALL words?
 *
 *      magma -b cls:=4 marks:="0,1;1,1" nw:=24 seed:=1 out:=../../data/w52rand_c4.txt w52_rand.m
 *
 *  For random words W with even exponent vector annihilated by both rows (lambda, nu'), run
 *  the SAME pipeline as for the relator R, in the same group Q (the class-cls quotient of
 *  D_sq 1), with W playing R's role both as the defect and as the source of the dressing
 *  map delta_W:
 *
 *    stage A   exhaustive over the 8^5 level-one codes (decided in Q_2, where P_3 = 1),
 *              with the same rank-5 Frattini condition on the dressed frame;
 *    stage B   greedy lift j = 3..cls: rows of delta_W by honest group collection,
 *              corank recorded, W(m)'s defect tested against im delta_W, correction applied.
 *
 *  Words: W = C1 * A * C2, where A fixes an admissible abelianization -- either R's own
 *  (0,-4,2,0,0) or 0 or the handle vector (0,0,0,2s,-2t), all killed by lambda and nu'
 *  exactly over Z -- and C1, C2 are products of conjugated commutators of random short
 *  words.  (A word whose abelianization is NOT killed by both rows has lambda(W(m))
 *  constant and nonzero along every dressing orbit, so it dies at a fixed finite level for
 *  a reason that has nothing to do with the corank structure; those are excluded as
 *  uninformative, not as inconvenient.)
 *
 *  Per word we also compute the mod-2 abelianized Fox rows beta'_i (the walker below) and
 *  the Frobenius slot pattern (e_i/2 mod 2), and validate the W52 graded formula
 *      delta_W(z) = sum_i sum_k beta'_{i,k} [z_i, m_k]  +  sum_{i : e_i/2 odd} F(z_i)
 *  against the honest rows -- so the formula is tested on arbitrary words, not just R.
 *
 *  Word 0 is R itself through the identical driver (must reproduce: 6 survivors, corank 6,
 *  containment at every level, solvable).
 */
SetColumns(0); SetAutoColumns(false);
load "../w50_depth_sweep/c0.m";

CLS := StringToInteger(cls);
NW := StringToInteger(nw);
SetSeed(StringToInteger(seed));
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

/* evaluate a free word at a 5-tuple */
Ev := function(w, m)
  r := Id(Parent(m[1]));
  for k in Eltseq(w) do
    r := r * ((k gt 0) select m[k] else m[-k]^-1);
  end for;
  return r;
end function;

/* mod-2 abelianized Fox rows of a free word: beta_i = sum over occurrences of letter i of
   the prefix exponent vector mod 2 (for an inverse occurrence, the prefix after the step);
   returned in LETTER coordinates, to be pushed through the marking */
FoxRows2 := function(w)
  V := VectorSpace(GF(2), 5);
  rowsF := [ V!0 : i in [1..5] ];
  p := [0,0,0,0,0];
  for k in Eltseq(w) do
    if k gt 0 then
      rowsF[k] +:= V![ GF(2)!e : e in p ];
      p[k] +:= 1;
    else
      p[-k] -:= 1;
      rowsF[-k] +:= V![ GF(2)!e : e in p ];
    end if;
  end for;
  return rowsF;
end function;

ExpVec := function(w)
  p := [0,0,0,0,0];
  for k in Eltseq(w) do
    if k gt 0 then p[k] +:= 1; else p[-k] -:= 1; end if;
  end for;
  return p;
end function;

/* random short word and random even admissible word */
RandWord := function(len)
  w := Id(F);
  for i in [1..len] do
    k := Random(1,5); e := Random(0,1) eq 0 select 1 else -1;
    w := w * (F.k)^e;
  end for;
  return w;
end function;
RandAdmissible := function(t, s, kind, nc)
  /* kind 1: R's abelianization; kind 2: zero; kind 3: handle vector (0,0,0,2s,-2t) */
  if kind eq 1 then A := fx0^-4 * fx1^2;
  elif kind eq 2 then A := Id(F);
  else A := fu^(2*s) * fv^(-2*t);
  end if;
  C1 := Id(F); C2 := Id(F);
  for i in [1..nc] do
    C1 := C1 * ((RandWord(3), RandWord(3))^RandWord(2));
    C2 := C2 * ((RandWord(3), RandWord(3))^RandWord(2));
  end for;
  return C1 * A * C2;
end function;

/* ---------------- towers: class 2 for stage A, class CLS for the lift ---------------- */
PR := pQuotientProcess(G, 2, 1);
NextClass(~PR);
Q2 := ExtractGroup(PR);
for c in [3..CLS] do NextClass(~PR); end for;
Q := ExtractGroup(PR);
P := pCentralSeries(Q, 2);
n := NPCgens(Q);
dm := [ Ilog2(#P[i] div #P[i+1]) : i in [1..#P-1] ];
Say(Sprintf("W52 discrimination -- class %o, layers %o, %o random words per (marking, kind), seed %o",
    CLS, dm, NW, seed));
ofs := [0 : w in [1..CLS+1]];
for w in [1..CLS] do ofs[w+1] := ofs[w] + dm[w]; end for;
for w in [1..CLS] do
  assert NPCgens(P[w]) eq n - ofs[w];
  assert Q.(ofs[w]+1) in P[w];
  assert not (Q.(ofs[w]+1) in P[w+1]);
end for;
Coord := function(x, w)
  e := Eltseq(x);
  return Vector(GF(2), [ GF(2)!e[k] : k in [ofs[w]+1 .. ofs[w+1]] ]);
end function;
CoordChecked := function(x, w)
  e := Eltseq(x);
  for k in [1..ofs[w]] do assert e[k] eq 0; end for;
  return Vector(GF(2), [ GF(2)!e[k] : k in [ofs[w]+1 .. ofs[w+1]] ]);
end function;
IndepSubset := function(cands, w)
  A := Matrix([ Coord(x, w) : x in cands ]);
  E := EchelonForm(Transpose(A));
  piv := [];
  for i in [1..Nrows(E)] do
    d := Depth(E[i]);
    if d ne 0 then Append(~piv, d); end if;
  end for;
  return [ cands[j] : j in piv ];
end function;

gQ  := [Q.i : i in [1..5]];
wQ  := gQ[1] * (gQ[2]^(C0 mod 2^(CLS+2)))^-1;
tbQ := (gQ[2]^2)^-1 * gQ[3];
pw := [ gQ[1]^(2^(w-1)) : w in [1..CLS] ];
qw := [ gQ[2]^(2^(w-1)) : w in [1..CLS] ];
LGEN := [ [ Q.k : k in [ofs[w]+1 .. ofs[w+1]] ] : w in [1..CLS] ];
g2 := [Q2.i : i in [1..5]];
w2 := g2[1] * (g2[2]^(C0 mod 2^(CLS+2)))^-1;
tb2 := (g2[2]^2)^-1 * g2[3];

/* the lambda and nu' rows on the abelianization, exact over Z on the sublattice used */
LamRow := func< t, s | [C0 mod 2^30, 1, 2, 0, 0] >;
NuRow := func< t, s | [1, 0, 0, t, s] >;

for e0 in MARKS do
  t := e0[1]; s := e0[2];
  UQ := (wQ^t)^-1 * gQ[4];  VQ := gQ[5] * (wQ^s)^-1;
  base := [gQ[1], gQ[2], gQ[3], UQ, VQ];
  U2 := (w2^t)^-1 * g2[4];  V2 := g2[5] * (w2^s)^-1;
  base2 := [g2[1], g2[2], g2[3], U2, V2];
  dress2 := [ U2^(a div 4) * V2^((a div 2) mod 2) * tb2^(a mod 2) : a in [0..7] ];
  dressQ := [ UQ^(a div 4) * VQ^((a div 2) mod 2) * tbQ^(a mod 2) : a in [0..7] ];

  KB := [ IndepSubset([UQ, VQ, tbQ], 1) ];
  for w in [2..CLS-1] do
    cands := [];
    for x in LGEN[w-1] do for i in [1..5] do Append(~cands, (x, gQ[i])); end for; end for;
    for b in KB[w-1] do Append(~cands, b^2); end for;
    Append(~KB, IndepSubset(cands, w));
  end for;
  certs := [];
  for w in [1..CLS-1] do
    rows := [ Coord(x, w) : x in KB[w] ] cat [ Coord(pw[w], w), Coord(qw[w], w) ];
    Append(~certs, (#KB[w] eq dm[w]-2) and (Rank(Matrix(rows)) eq dm[w]));
  end for;
  assert &and certs;
  Say(Sprintf("---- (t,s)=(%o,%o): K dims %o, certs ok ----", t, s, [#b : b in KB]));

  words := [* <"R", RELW> *];
  for kind in [1,2,3] do
    for i in [1..NW] do
      Append(~words, <Sprintf("k%o.%o", kind, i), RandAdmissible(t, s, kind, 2 + (i mod 3))>);
    end for;
  end for;

  for wp in words do
    tag := wp[1]; W := wp[2];
    ev := ExpVec(W);
    dotL := &+[ ev[k]*LamRow(t,s)[k] : k in [1..5] ];
    dotN := &+[ ev[k]*NuRow(t,s)[k] : k in [1..5] ];
    assert (dotL mod 2^(CLS+2)) eq 0 and (dotN mod 2^(CLS+2)) eq 0;
    assert &and[ IsEven(e) : e in ev ];
    frob := [ GF(2)!((ev[k] div 2)) : k in [1..5] ];
    rowsF := FoxRows2(W);
    rkF := Rank(Matrix(rowsF));

    /* stage A in Q_2 */
    surv := [];
    for a in [0..8^5-1] do
      code := [ (a div 8^(i-1)) mod 8 : i in [1..5] ];
      mm2 := [ base2[i] * dress2[code[i]+1] : i in [1..5] ];
      if Ev(W, mm2) eq Id(Q2) then
        M := Matrix(GF(2), 5, 5, [ [ GF(2)!e : e in Eltseq(x)[1..5] ] : x in mm2 ]);
        if Rank(M) eq 5 then Append(~surv, code); end if;
      end if;
    end for;
    if #surv eq 0 then
      Say(Sprintf("%-6o len %3o foxrank %o frob %o | stage A: GATE EMPTY (0 of 32768) -- word cannot pass class 2", tag, #Eltseq(W), rkF, frob));
      continue;
    end if;

    /* stage B on the first survivor */
    code := surv[1];
    m := [ base[i] * dressQ[code[i]+1] : i in [1..5] ];
    r := Ev(W, m);
    assert r in P[3];
    line := Sprintf("%-6o len %3o foxrank %o frob %o | survivors %o | ", tag, #Eltseq(W), rkF, frob, #surv);
    solvable := true;
    for j in [3..CLS] do
      if r in P[j+1] then line cat:= Sprintf("L%o(triv) ", j); continue; end if;
      reps := KB[j-1]; nb := #reps;
      rows := []; mism := 0;
      for i in [1..5] do for b in reps do
        mm := m; mm[i] := m[i]*b;
        honest := Coord(Ev(W, mm) * r^-1, j);
        form := Coord(Id(Q), j);
        for k in [1..5] do
          if rowsF[i][k] ne 0 then form +:= Coord((b, m[k]), j); end if;
        end for;
        if frob[i] ne 0 then form +:= Coord(b^2, j); end if;
        if honest ne form then mism +:= 1; end if;
        Append(~rows, honest);
      end for; end for;
      A := Matrix(rows); RS := RowSpace(A);
      tar := CoordChecked(r^-1, j);
      inim := tar in RS;
      line cat:= Sprintf("L%o[rk %o ck %o form-mism %o in-im %o] ", j, Dimension(RS), dm[j]-Dimension(RS), mism, inim);
      if not inim then
        solvable := false;
        line cat:= "STUCK ";
        break;
      end if;
      ok, x := IsConsistent(A, tar);
      assert ok;
      for i in [1..5] do for l in [1..nb] do
        if x[(i-1)*nb + l] ne 0 then m[i] := m[i] * reps[l]; end if;
      end for; end for;
      r := Ev(W, m);
      assert r in P[j+1];
    end for;
    if solvable then
      line cat:= (r eq Id(Q)) select "| SOLVED" else "| cleared (deeper tail nonzero)";
    end if;
    Say(line);
  end for;
end for;
Say("DONE");
