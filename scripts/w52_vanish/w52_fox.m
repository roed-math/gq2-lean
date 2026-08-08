/*  W52-VANISH -- the graded Fox form of the dressing-defect map, validated row by row.
 *
 *      magma -b cls:=4 marks:="0,1;1,1;3,5" out:=../../data/w52fox_c4.txt w52_fox.m
 *
 *  The claim under test (derived by hand from free differential calculus; this script is
 *  the machine check that the derivation is EXACT in the layer, not just mod something):
 *
 *      delta_j(z) = sum_i [z_i, beta_i]  +  F(z_{x1})           in  L_j = P_j/P_{j+1},
 *
 *  where z_i ranges over the layer K_{j-1}, [.,.] is the group commutator read in the
 *  layer, F is the squaring (Frobenius) map L_{j-1} -> L_j, and beta_i is the mod-2
 *  abelianized Fox derivative dR/dx_i evaluated at the marking -- which for THIS relator
 *  is the permuted marking letter:
 *
 *      beta_sigma = m(x0),  beta_x0 = m(sigma),  beta_x1 = m(x1),  beta_u = m(v),  beta_v = m(u),
 *
 *  the permutation (sigma x0)(u v) with x1 fixed, and the Frobenius appears in the x1
 *  slot only (exponent vector (0,-4,2,0,0), halves mod 2 = (0,0,1,0,0)).
 *
 *  Tests, per marking, per level j = 3..cls:
 *    T1  every honest row  Coord(R(m with slot i dressed by b) R(m)^-1, j)  equals the
 *        formula row  Coord((b, beta_i) * (b^2 if x1 slot), j)   -- 0 mismatches wanted;
 *    T2  im delta and the relator's defect both lie in the layer K_j (the two canonical
 *        cokernel functionals lambda_j, nu_j annihilate both);
 *    T3  the conjugation (Jacobi/Fox) kernel family: for every c in a basis of L_{j-2},
 *        the formula's value on z_i = [m_i, c] vanishes in L_j -- this is the graded
 *        shadow of R(m^g) = R(m)^g, and its vanishing needs the class-2 relation
 *        rho(m) = 0, i.e. stage-A survival.
 *
 *  Infrastructure (tower, graded K generating set, certificates, layer coordinates) is
 *  W51's, see scripts/w51_class6/w51_corank.m; the certificate proving S_w = K_w exactly
 *  is re-checked here at every level.
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

F<fs,fx0,fx1,fu,fv> := FreeGroup(5);
RELW := (fx0^fs)^-1 * (fx0^3)^-1 * fx1^2 * (fx1, fx1^fs) * (fu,fv);
G := quo< F | RELW >;
Rel := function(m)
  return (m[2]^m[1])^-1 * (m[2]^3)^-1 * m[3]^2 * (m[3], m[3]^m[1]) * (m[4],m[5]);
end function;

Say(Sprintf("W52 fox-form validation -- class %o, markings %o", CLS, MARKS));

/* ---------------- tower ---------------- */
PR := pQuotientProcess(G, 2, 1);
for c in [2..CLS] do NextClass(~PR); end for;
Q := ExtractGroup(PR);
P := pCentralSeries(Q, 2);
n := NPCgens(Q);
dm := [ Ilog2(#P[i] div #P[i+1]) : i in [1..#P-1] ];
Say(Sprintf("Q_%o : order 2^%o, layers %o", CLS, Ilog2(#Q), dm));
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

for e0 in MARKS do
  t := e0[1]; s := e0[2];
  UQ := (wQ^t)^-1 * gQ[4];  VQ := gQ[5] * (wQ^s)^-1;
  base := [gQ[1], gQ[2], gQ[3], UQ, VQ];

  /* graded K generating sets, levels 1..CLS (one beyond W51: the top TARGET layer too) */
  KB := [ IndepSubset([UQ, VQ, tbQ], 1) ];
  for w in [2..CLS] do
    cands := [];
    for x in LGEN[w-1] do for i in [1..5] do Append(~cands, (x, gQ[i])); end for; end for;
    for b in KB[w-1] do Append(~cands, b^2); end for;
    Append(~KB, IndepSubset(cands, w));
  end for;
  certs := [];
  for w in [1..CLS] do
    rows := [ Coord(x, w) : x in KB[w] ] cat [ Coord(pw[w], w), Coord(qw[w], w) ];
    Append(~certs, (#KB[w] eq dm[w]-2) and (Rank(Matrix(rows)) eq dm[w]));
  end for;
  Say(Sprintf("(t,s)=(%o,%o): K-layer dims %o, certs %o", t, s, [#b : b in KB], certs));
  assert &and certs;

  /* stage-A dressed marking, as in W50/W51 */
  dressQ := [ UQ^(a div 4) * VQ^((a div 2) mod 2) * tbQ^(a mod 2) : a in [0..7] ];
  fc := 4*(s mod 2) + 2*(t mod 2);
  m := [ base[1]*dressQ[fc+1], base[2]*dressQ[fc+1], base[3], base[4], base[5] ];
  r := Rel(m);
  assert r in P[3];

  /* the permuted beta letters: (sigma x0)(u v), x1 fixed */
  beta := [ m[2], m[1], m[3], m[5], m[4] ];

  for j in [3..CLS] do
    tj := Cputime();
    reps := KB[j-1];
    nb := #reps;
    mism := 0;
    rows := [];
    for i in [1..5] do for b in reps do
      mm := m; mm[i] := m[i]*b;
      honest := Coord(Rel(mm) * r^-1, j);
      form := Coord((b, beta[i]), j);
      if i eq 3 then form +:= Coord(b^2, j); end if;
      if honest ne form then mism +:= 1; end if;
      Append(~rows, honest);
    end for; end for;
    A := Matrix(rows); RS := RowSpace(A);
    KS := RowSpace(Matrix([ Coord(x, j) : x in KB[j] ]));
    tar := (r in P[j+1]) select Zero(Generic(KS)) else CoordChecked(r^-1, j);
    imK := RS subset KS;
    tarK := tar in KS;
    /* T3: conjugation family, formula side only */
    cbasis := (j eq 3) select [ gQ[k] : k in [1..5] ] else LGEN[j-2];
    conjbad := 0;
    for c in cbasis do
      E := Id(Q);
      for i in [1..5] do
        z := (m[i], c);
        E := E * (z, beta[i]);
        if i eq 3 then E := E * z^2; end if;
      end for;
      assert E in P[j];
      if Coord(E, j) ne 0 then conjbad +:= 1; end if;
    end for;
    Say(Sprintf("  L%o: T1 fox-form mismatches %o of %o rows | rank %o corank %o | T2 im<=K %o, defect in K %o, defect in im %o | T3 conj-kernel fails %o of %o | %o s",
        j, mism, 5*nb, Dimension(RS), dm[j]-Dimension(RS), imK, tarK, tar in RS, conjbad, #cbasis, Cputime(tj)));
    if not (r in P[j+1]) then
      ok, x := IsConsistent(A, tar);
      assert ok;
      for i in [1..5] do for l in [1..nb] do
        if x[(i-1)*nb + l] ne 0 then m[i] := m[i] * reps[l]; end if;
      end for; end for;
      r := Rel(m);
      assert r in P[j+1];
      beta := [ m[2], m[1], m[3], m[5], m[4] ];
    end if;
  end for;
  Say(Sprintf("(t,s)=(%o,%o): R(m) = 1 in Q_%o : %o", t, s, CLS, r eq Id(Q)));
end for;
Say("DONE");
