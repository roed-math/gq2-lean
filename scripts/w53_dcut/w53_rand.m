/*  W53-DCUT -- is the d-1 cut generic in the word?
 *
 *      magma -b cls:=4 marks:="0,1;1,1" nw:=40 seed:=1 out:=results/w53rand_c4.txt w53_rand.m
 *
 *  W52's discrimination experiment (w52_rand.m) showed the CORANK d + 1 is generic: every
 *  full-Fox-rank even word gave 6 at every level, while the containment of the defect is
 *  special to the relator.  This script asks the sharper question W53 is about: is the
 *  d - 1 residue, and its explicit cokernel basis, generic in the word too, and in what
 *  sense?
 *
 *  Same group Q (the class-cls 2-quotient of D_sq 1), same markings, same K-tower.  For each
 *  random even word W we take its mod-2 abelianized Fox rows by the walker of w52_rand.m,
 *  push them through the marking to get beta_i in L_1, take the Frobenius slot set
 *  S = { i : e_i / 2 odd }, and run the graded Fox form
 *
 *      Delta_j(z) = sum_i [z_i, beta_i] + sum_{i in S} F(z_i)
 *
 *  of THAT word, on the full domain (L_{j-1})^d and on (K_{j-1})^d.  Reported per word:
 *
 *    corank on the full domain (predicted d - 1 when rank(beta) = d and S is nonempty);
 *    corank on (K_{j-1})^d     (predicted d + 1 = (d-1) + codim K);
 *    the residue dim K_j / im  (predicted d - 1);
 *    when |S| = 1: the cokernel bases -- the pure powers beta_i^(2^(j-1)) modulo im(Delta_full)
 *    and the bracket powers [beta_i, beta_s]^(2^(j-2)) modulo im(Delta|K) -- each of rank
 *    d - 1 with kernel exactly the Frobenius slot;
 *    an honest-collection cross-check of the form for the words with W(m) in P_3.
 *
 *  Aggregated at the end: how many DISTINCT subspaces im(Delta_full) and im(Delta|K) occur
 *  across the words -- i.e. whether the d-1 block is literally the same subspace for every
 *  word (it is not) or only uniformly described by the word's own Fox data (it is).
 *
 *  SCORING.  Inside the relator quotient the ambient itself carries the relator's initial
 *  form, so the corank is NOT word-independent here: the free-ambient value d - 1 can drop
 *  by the part of the graded ideal that survives to the pure-power quotient.  What is scored
 *  for every full-Fox-rank word is therefore the bookkeeping that does hold universally:
 *      im(Delta|K) inside K_j,   corank(Delta|K) = corank(Delta_full) + codim K,
 *      dim K_j / im(Delta|K)    = corank(Delta_full),
 *  together with, for a single Frobenius slot, the two cokernel bases having exactly the
 *  predicted ranks and a common kernel containing the Frobenius slot.  The value of
 *  corank(Delta_full) itself is reported, with the diagnostic
 *      pdim = codim of [L_{j-1}, V] in L_j   (the dimension of the pure-power space)
 *  and whether F^(j-1)(beta_s) lies in [L_{j-1}, V]; d - 1 vs d - 2 is tallied.
 */
SetColumns(0); SetAutoColumns(false);
load "../w50_depth_sweep/c0.m";

CLS := StringToInteger(cls);
NW  := StringToInteger(nw);
SetSeed(StringToInteger(seed));
OUT := out; System("rm -f " cat OUT);
procedure Say(str) PrintFile(OUT, str); print str; end procedure;

MARKS := [];
for chunk in Split(marks, ";") do
  ab := Split(chunk, ",");
  Append(~MARKS, [StringToInteger(ab[1]), StringToInteger(ab[2])]);
end for;

D := 5;
F<fs,fx0,fx1,fu,fv> := FreeGroup(D);
RELW := (fx0^fs)^-1 * (fx0^3)^-1 * fx1^2 * (fx1, fx1^fs) * (fu,fv);
G := quo< F | RELW >;
Rel := function(m)
  return (m[2]^m[1])^-1 * (m[2]^3)^-1 * m[3]^2 * (m[3], m[3]^m[1]) * (m[4],m[5]);
end function;

Ev := function(w, m)
  r := Id(Parent(m[1]));
  for k in Eltseq(w) do r := r * ((k gt 0) select m[k] else m[-k]^-1); end for;
  return r;
end function;
/* mod-2 abelianized Fox rows in LETTER coordinates (the walker of w52_rand.m) */
FoxRows2 := function(w)
  VS := VectorSpace(GF(2), D);
  rowsF := [ VS!0 : i in [1..D] ];
  p := [ 0 : i in [1..D] ];
  for k in Eltseq(w) do
    if k gt 0 then
      rowsF[k] +:= VS![ GF(2)!e : e in p ];  p[k] +:= 1;
    else
      p[-k] -:= 1;  rowsF[-k] +:= VS![ GF(2)!e : e in p ];
    end if;
  end for;
  return rowsF;
end function;
ExpVec := function(w)
  p := [ 0 : i in [1..D] ];
  for k in Eltseq(w) do
    if k gt 0 then p[k] +:= 1; else p[-k] -:= 1; end if;
  end for;
  return p;
end function;
RandWord := function(len)
  w := Id(F);
  for i in [1..len] do
    k := Random(1, D); e := (Random(0,1) eq 0) select 1 else -1;
    w := w * (F.k)^e;
  end for;
  return w;
end function;
/*  A random word with even exponent vector, decorated with conjugated commutators (which
 *  are abelian-trivial, so they move the Fox rows but not the Frobenius pattern).
 *  kind 1: exactly one slot has e_i / 2 odd, i.e. |S| = 1 -- the relator's own shape;
 *  kind 2: an unconstrained even exponent vector, so |S| is whatever it is.
 */
RandEven := function(nc, kind)
  A := Id(F);
  if kind eq 1 then
    sl := Random(1, D);
    for k in [1..D] do A := A * (F.k)^(4*Random(-1, 1)); end for;
    A := A * (F.sl)^(2*(2*Random(-1,1) + 1));
  else
    for k in [1..D] do A := A * (F.k)^(2*Random(-2, 2)); end for;
  end if;
  C1 := Id(F); C2 := Id(F);
  for i in [1..nc] do
    C1 := C1 * ((RandWord(3), RandWord(3))^RandWord(2));
    C2 := C2 * ((RandWord(3), RandWord(3))^RandWord(2));
  end for;
  return C1 * A * C2;
end function;

tall := Cputime();
PR := pQuotientProcess(G, 2, 1);
for c in [2..CLS] do NextClass(~PR); end for;
Q := ExtractGroup(PR);
P := pCentralSeries(Q, 2);
n := NPCgens(Q);
dm := [ Ilog2(#P[i] div #P[i+1]) : i in [1..#P-1] ];
ofs := [0 : w in [1..CLS+1]];
for w in [1..CLS] do ofs[w+1] := ofs[w] + dm[w]; end for;
Say(Sprintf("W53-DCUT genericity in the word -- class %o, layers %o, %o random even words per marking, seed %o",
    CLS, dm, NW, seed));

Coord := function(x, w)
  e := Eltseq(x);
  return Vector(GF(2), [ GF(2)!e[k] : k in [ofs[w]+1 .. ofs[w+1]] ]);
end function;
IndepSubset := function(cands, w)
  E := EchelonForm(Transpose(Matrix([ Coord(x, w) : x in cands ])));
  piv := [];
  for i in [1..Nrows(E)] do z := Depth(E[i]); if z ne 0 then Append(~piv, z); end if; end for;
  return [ cands[j] : j in piv ];
end function;

gQ  := [ Q.i : i in [1..D] ];
wQ  := gQ[1] * (gQ[2]^(C0 mod 2^(CLS+2)))^-1;
tbQ := (gQ[2]^2)^-1 * gQ[3];
pw  := [ gQ[1]^(2^(w-1)) : w in [1..CLS] ];
qw  := [ gQ[2]^(2^(w-1)) : w in [1..CLS] ];
LGEN := [ [ Q.k : k in [ofs[w]+1 .. ofs[w+1]] ] : w in [1..CLS] ];
VDD := VectorSpace(GF(2), D);

NCASE := 0; NFAIL := 0;

for e0 in MARKS do
  t := e0[1]; s0 := e0[2];
  UQ := (wQ^t)^-1 * gQ[4];  VQ := gQ[5] * (wQ^s0)^-1;
  base := [gQ[1], gQ[2], gQ[3], UQ, VQ];
  KB := [ IndepSubset([UQ, VQ, tbQ], 1) ];
  for w in [2..CLS] do
    cands := [];
    for x in LGEN[w-1] do for i in [1..D] do Append(~cands, (x, gQ[i])); end for; end for;
    for b in KB[w-1] do Append(~cands, b^2); end for;
    Append(~KB, IndepSubset(cands, w));
  end for;
  certs := [ (#KB[w] eq dm[w]-2) and
             (Rank(Matrix([ Coord(x,w) : x in KB[w] ] cat [ Coord(pw[w],w), Coord(qw[w],w) ])) eq dm[w])
             : w in [1..CLS] ];
  assert &and certs;
  dressQ := [ UQ^(a div 4) * VQ^((a div 2) mod 2) * tbQ^(a mod 2) : a in [0..7] ];
  fc := 4*(s0 mod 2) + 2*(t mod 2);
  m := [ base[1]*dressQ[fc+1], base[2]*dressQ[fc+1], base[3], base[4], base[5] ];
  Say(Sprintf("---- (t,s)=(%o,%o): K dims %o, codim-2 certificates ok ----", t, s0, [#b : b in KB]));

  words := [* <"R", RELW> *];
  for i in [1..NW] do
    Append(~words, <Sprintf("w%o", i), RandEven(1 + (i mod 3), (i le (NW+1) div 2) select 1 else 2)>);
  end for;

  imsL := AssociativeArray(); imsK := AssociativeArray();
  for j in [1..CLS] do imsL[j] := {}; imsK[j] := {}; end for;
  nwd := 0;
  tally := AssociativeArray(); cktal := AssociativeArray();
  for wp in words do
    tag := wp[1]; W := wp[2];
    ev := ExpVec(W);
    assert &and [ IsEven(e) : e in ev ];
    frob := [ GF(2)!(e div 2) : e in ev ];
    SS := { i : i in [1..D] | frob[i] ne 0 };
    rowsF := FoxRows2(W);
    rkF := Rank(Matrix(rowsF));
    beta := [];
    for i in [1..D] do
      b := Id(Q);
      for k in [1..D] do if rowsF[i][k] ne 0 then b := b * m[k]; end if; end for;
      Append(~beta, b);
    end for;
    Wm := Ev(W, m);
    deep := (Wm in P[3]);
    key := <rkF, #SS>;
    if not IsDefined(tally, key) then tally[key] := 0; end if;
    tally[key] +:= 1;
    line := Sprintf("%-4o len %3o foxrank %o S=%o %o |", tag, #Eltseq(W), rkF,
                    Sort(SetToSequence(SS)), deep select "W(m) in P3" else "W(m) not in P3");
    /* the scored regime is the relator's own: full Fox rank and a single Frobenius slot */
    expect := (rkF eq D) and (#SS eq 1);
    for j in [3..CLS] do
      reps := KB[j-1]; LG := LGEN[j-1];
      rowsK := []; rowsL := []; mism := -1;
      if deep then mism := 0; end if;
      for i in [1..D] do
        for b in reps do
          rr := Coord((b, beta[i]), j);
          if i in SS then rr +:= Coord(b^2, j); end if;
          if deep then
            mm := m; mm[i] := m[i]*b;
            if Coord(Ev(W, mm) * Wm^-1, j) ne rr then mism +:= 1; end if;
          end if;
          Append(~rowsK, rr);
        end for;
        for b in LG do
          rr := Coord((b, beta[i]), j);
          if i in SS then rr +:= Coord(b^2, j); end if;
          Append(~rowsL, rr);
        end for;
      end for;
      RSK := RowSpace(Matrix(rowsK));
      RSL := RowSpace(Matrix(rowsL));
      KS  := RowSpace(Matrix([ Coord(x, j) : x in KB[j] ]));
      ckK := dm[j] - Dimension(RSK);
      ckL := dm[j] - Dimension(RSL);
      resid := Dimension(KS) - Dimension(RSK);
      imsL[j] := imsL[j] join { Sprintf("%o", EchelonForm(Matrix(Basis(RSL)))) };
      imsK[j] := imsK[j] join { Sprintf("%o", EchelonForm(Matrix(Basis(RSK)))) };
      VV := VectorSpace(GF(2), dm[j]);
      /* the pure-power space of the ambient: L_j / [L_{j-1}, V] */
      brows := [];
      for x in LG do for i in [1..D] do Append(~brows, Coord((x, gQ[i]), j)); end for; end for;
      BR := RowSpace(Matrix(brows));
      pdim := dm[j] - Dimension(BR);
      bas := "n/a";
      basok := true; hitd := "-";
      if #SS eq 1 then
        sf := Rep(SS);
        hitd := (VV!Coord(beta[sf]^(2^(j-1)), j) in BR) select "in" else "out";
        CQL, mpl := quo< VV | RSL >;
        CQK, mpk := quo< VV | RSK >;
        M4 := Matrix([ mpl(VV!Coord(beta[i]^(2^(j-1)), j)) : i in [1..D] ]);
        c2 := [ Coord((beta[i], beta[sf])^(2^(j-2)), j) : i in [1..D] ];
        Mq := Matrix([ mpk(VV!x) : x in c2 ]);
        Mall := Matrix([ mpk(VV!x) : x in c2 ]
                   cat [ mpk(VV!Coord(pw[j], j)), mpk(VV!Coord(qw[j], j)) ]);
        pk := sub< VDD | [ VDD.sf ] >;
        inK := &and [ VV!x in KS : x in c2 ];
        basok := (Rank(M4) eq ckL) and (Rank(Mq) eq resid) and (Rank(Mall) eq ckK)
                 and inK and (Kernel(M4) eq Kernel(Mq)) and (pk subset Kernel(M4));
        bas := Sprintf("purepow %o=ckFull %o, brkpow %o=resid %o inK %o, +duals %o=ckK %o, kers agree %o, e_s in ker %o",
               Rank(M4), Rank(M4) eq ckL, Rank(Mq), Rank(Mq) eq resid, inK,
               Rank(Mall), Rank(Mall) eq ckK, Kernel(M4) eq Kernel(Mq), pk subset Kernel(M4));
      end if;
      good := (ckK eq ckL + 2) and (resid eq ckL) and (RSK subset KS) and basok and (mism le 0);
      NCASE +:= 1; if expect and not good then NFAIL +:= 1; end if;
      if expect then
        kk := <j, ckL>;
        if not IsDefined(cktal, kk) then cktal[kk] := 0; end if;
        cktal[kk] +:= 1;
      end if;
      line cat:= Sprintf(" L%o[ckFull %o ckK %o (=ckFull+2 %o) resid %o im<=K %o pdim %o F(beta_s) %o mism %o | %o]",
                 j, ckL, ckK, ckK eq ckL+2, resid, RSK subset KS, pdim, hitd, mism, bas);
    end for;
    Say(line);
    nwd +:= 1;
  end for;
  Say(Sprintf("  (t,s)=(%o,%o) tally by <rank(beta), |S|> : %o", t, s0,
      [ <k, tally[k]> : k in Sort(SetToSequence(Keys(tally))) ]));
  for j in [3..CLS] do
    Say(Sprintf("  (t,s)=(%o,%o) L%o : %o words, distinct im(Delta_full) %o, distinct im(Delta|K) %o",
        t, s0, j, nwd, #imsL[j], #imsK[j]));
  end for;
  Say(Sprintf("  (t,s)=(%o,%o) corank(Delta_full) tally over full-rank single-slot words, <level, corank> : %o (d-1 = %o, d-2 = %o)",
      t, s0, [ <k, cktal[k]> : k in Sort(SetToSequence(Keys(cktal))) ], D-1, D-2));
end for;

Say(Sprintf("SUMMARY: %o scored assertions, %o failures (%o s)", NCASE, NFAIL, Cputime(tall)));
Say("DONE");
