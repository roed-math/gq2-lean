/*  W53-DCUT -- the d-1 cut inside the campaign's own group.
 *
 *      magma -b h:=1 cls:=4 marks:="0,1;1,0;1,1" out:=results/w53camp_h1c4.txt w53_camp.m
 *      magma -b h:=2 cls:=4 marks:="0,1;1,1"     out:=results/w53camp_h2c4.txt w53_camp.m
 *
 *  Same tower, same markings, same greedy lift as W52's w52_fox.m: Q = the class-cls
 *  2-quotient of D_sq h, relator
 *      R = (x0^sigma)^-1 x0^-3 x1^2 [x1, x1^sigma] prod_i [u_i, v_i],   d = 3 + 2h,
 *  graded Fox rows beta = the marking letters permuted by (sigma x0)(u_i v_i) with x1 fixed,
 *  Frobenius slot S = {x1} only, K_1 = <U, V, tb, u_2, v_2, ..>, K_w = [L_{w-1}, V] + F(K_{w-1}).
 *
 *  W52 measured corank(delta on (K_{j-1})^d) = d + 1 at every level and could not explain
 *  the d - 1 beyond the canonical pair lambda, nu.  This script measures, at every marking
 *  and every level:
 *
 *    T1  the graded Fox form against honest group collection (W52's row check, re-asserted);
 *    T2  corank of delta on the FULL domain (L_{j-1})^d  --  it is d - 1, NOT zero:
 *        the form is NOT onto, contrary to w52-vanish-note section 1.4, and the corrected
 *        bookkeeping is    corank(delta|K) = corank(delta_full) + codim K = (d-1) + 2;
 *    T3  the full-domain cokernel basis: the pure powers beta_i^(2^(j-1)) of the Fox rows
 *        span L_j / im(delta_full) with kernel exactly the Frobenius slot;
 *    T4  the K-restricted cokernel basis, explicitly:  the d-1 bracket powers
 *        [beta_i, beta_{x1}]^(2^(j-2))  (i <> x1), which lie in K_j and are a basis of the
 *        residue K_j / im, together with sigma^(2^(j-1)) and x0^(2^(j-1)), the lambda-nu
 *        duals spanning L_j / K_j;
 *    T5  rank(phi) = 2: the power dressings supply exactly the lambda-nu block;
 *    T6  witnesses in the group: the diagonal power family z_i = beta_i^(2^(j-2)) has
 *        delta(z) = beta_{x1}^(2^(j-1)) exactly (all other slots cancel by [x^(2^k), x] = 1),
 *        and the conjugation family z_i = [m_i, c] is in ker delta (W52 section 1.3);
 *    T7  the relator's own defect still lands in im(delta|K) (W52's containment), and the
 *        sweep advances, so all of the above is measured along the campaign's own orbit.
 */
SetColumns(0); SetAutoColumns(false); SetSeed(1);
load "../w50_depth_sweep/c0.m";

H   := StringToInteger(h);
CLS := StringToInteger(cls);
D   := 3 + 2*H;
OUT := out; System("rm -f " cat OUT);
procedure Say(str) PrintFile(OUT, str); print str; end procedure;

MARKS := [];
for chunk in Split(marks, ";") do
  ab := Split(chunk, ",");
  Append(~MARKS, [StringToInteger(ab[1]), StringToInteger(ab[2])]);
end for;

F := FreeGroup(D);
RELW := (F.2^F.1)^-1 * (F.2^3)^-1 * F.3^2 * (F.3, F.3^F.1);
for i in [1..H] do RELW := RELW * (F.(2+2*i), F.(3+2*i)); end for;
G := quo< F | RELW >;
Rel := function(m)
  r := (m[2]^m[1])^-1 * (m[2]^3)^-1 * m[3]^2 * (m[3], m[3]^m[1]);
  for i in [1..H] do r := r * (m[2+2*i], m[3+2*i]); end for;
  return r;
end function;
/* the permuted Fox rows: (sigma x0), x1 fixed, (u_i v_i) */
FoxPerm := function(m)
  b := [ m[2], m[1], m[3] ];
  for i in [1..H] do Append(~b, m[3+2*i]); Append(~b, m[2+2*i]); end for;
  return b;
end function;

Say(Sprintf("W53-DCUT campaign ambient -- h = %o (d = %o), class %o, markings %o", H, D, CLS, MARKS));
tall := Cputime();
PR := pQuotientProcess(G, 2, 1);
for c in [2..CLS] do NextClass(~PR); end for;
Q := ExtractGroup(PR);
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
Say(Sprintf("Q_%o : order 2^%o, layers %o (build %o s)", CLS, Ilog2(#Q), dm, Cputime(tall)));

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
  E := EchelonForm(Transpose(Matrix([ Coord(x, w) : x in cands ])));
  piv := [];
  for i in [1..Nrows(E)] do z := Depth(E[i]); if z ne 0 then Append(~piv, z); end if; end for;
  return [ cands[j] : j in piv ];
end function;

gQ  := [ Q.i : i in [1..D] ];
assert Rel(gQ) eq Id(Q);
wQ  := gQ[1] * (gQ[2]^(C0 mod 2^(CLS+2)))^-1;
tbQ := (gQ[2]^2)^-1 * gQ[3];
pw  := [ gQ[1]^(2^(w-1)) : w in [1..CLS] ];
qw  := [ gQ[2]^(2^(w-1)) : w in [1..CLS] ];
LGEN := [ [ Q.k : k in [ofs[w]+1 .. ofs[w+1]] ] : w in [1..CLS] ];

NCASE := 0; NFAIL := 0;
VDD := VectorSpace(GF(2), D);

for e0 in MARKS do
  t := e0[1]; s := e0[2];
  UQ := (wQ^t)^-1 * gQ[4];  VQ := gQ[5] * (wQ^s)^-1;
  base := [gQ[1], gQ[2], gQ[3], UQ, VQ] cat [ gQ[i] : i in [6..D] ];
  KB := [ IndepSubset([UQ, VQ, tbQ] cat [ gQ[i] : i in [6..D] ], 1) ];
  for w in [2..CLS] do
    cands := [];
    for x in LGEN[w-1] do for i in [1..D] do Append(~cands, (x, gQ[i])); end for; end for;
    for b in KB[w-1] do Append(~cands, b^2); end for;
    Append(~KB, IndepSubset(cands, w));
  end for;
  certs := [];
  for w in [1..CLS] do
    rows := [ Coord(x, w) : x in KB[w] ] cat [ Coord(pw[w], w), Coord(qw[w], w) ];
    Append(~certs, (#KB[w] eq dm[w]-2) and (Rank(Matrix(rows)) eq dm[w]));
  end for;
  NCASE +:= 1; if not &and certs then NFAIL +:= 1; end if;
  Say(Sprintf("---- (t,s)=(%o,%o): K-layer dims %o of %o, codim-2 certificates %o ----",
      t, s, [#b : b in KB], dm, certs));

  dressQ := [ UQ^(a div 4) * VQ^((a div 2) mod 2) * tbQ^(a mod 2) : a in [0..7] ];
  fc := 4*(s mod 2) + 2*(t mod 2);
  m := [ base[1]*dressQ[fc+1], base[2]*dressQ[fc+1] ] cat [ base[i] : i in [3..D] ];
  r := Rel(m);
  assert r in P[3];
  beta := FoxPerm(m);

  for j in [3..CLS] do
    tj := Cputime();
    reps := KB[j-1]; nb := #reps; LG := LGEN[j-1];
    /* T1 honest rows vs the graded Fox form, on K-dressings */
    mism := 0; rowsK := [];
    for i in [1..D] do for b in reps do
      mm := m; mm[i] := m[i]*b;
      honest := Coord(Rel(mm) * r^-1, j);
      form := Coord((b, beta[i]), j);
      if i eq 3 then form +:= Coord(b^2, j); end if;
      if honest ne form then mism +:= 1; end if;
      Append(~rowsK, honest);
    end for; end for;
    /* full-domain rows, from the form */
    rowsL := [];
    for i in [1..D] do for b in LG do
      rr := Coord((b, beta[i]), j);
      if i eq 3 then rr +:= Coord(b^2, j); end if;
      Append(~rowsL, rr);
    end for; end for;
    RSK := RowSpace(Matrix(rowsK));
    RSL := RowSpace(Matrix(rowsL));
    KS  := RowSpace(Matrix([ Coord(x, j) : x in KB[j] ]));
    ckK := dm[j] - Dimension(RSK);
    ckL := dm[j] - Dimension(RSL);
    resid := Dimension(KS) - Dimension(RSK);
    VV := VectorSpace(GF(2), dm[j]);
    CQL, mpl := quo< VV | RSL >;
    CQK, mpk := quo< VV | RSK >;

    /* T3 full-domain cokernel: pure powers of the Fox rows */
    c4 := [ Coord(beta[i]^(2^(j-1)), j) : i in [1..D] ];
    M4 := Matrix([ mpl(VV!x) : x in c4 ]);
    predk := sub< VDD | [ VDD.3 ] >;
    t3 := (Rank(M4) eq ckL) and (Kernel(M4) eq predk);

    /* T4 K-restricted cokernel basis: bracket powers inside K_j, plus the two lam-nu duals */
    c2 := [ Coord((beta[i], beta[3])^(2^(j-2)), j) : i in [1..D] ];
    inK := &and [ VV!x in KS : x in c2 ];
    Mq := Matrix([ mpk(VV!x) : x in c2 ]);
    Mall := Matrix([ mpk(VV!x) : x in c2 ] cat [ mpk(VV!Coord(pw[j], j)), mpk(VV!Coord(qw[j], j)) ]);
    t4 := inK and (Rank(Mq) eq resid) and (Kernel(Mq) eq predk) and (Rank(Mall) eq ckK);

    /* T5 rank(phi): the two power dressings modulo im(delta|K) */
    prows := [];
    for a in [1, 2] do for i in [1..D] do
      rr := Coord((gQ[a]^(2^(j-2)), beta[i]), j);
      if i eq 3 then rr +:= Coord(gQ[a]^(2^(j-1)), j); end if;
      Append(~prows, mpk(VV!rr));
    end for; end for;
    rkphi := Rank(Matrix(prows));

    /* T6 witnesses: the diagonal power family, and the conjugation family */
    E := Id(Q);
    for i in [1..D] do
      z := beta[i]^(2^(j-2));
      E := E * (z, beta[i]);
      if i eq 3 then E := E * z^2; end if;
    end for;
    w6 := Coord(E, j) eq Coord(beta[3]^(2^(j-1)), j);
    cbasis := (j eq 3) select [ gQ[k] : k in [1..D] ] else LGEN[j-2];
    conjbad := 0;
    for c in cbasis do
      E2 := Id(Q);
      for i in [1..D] do
        z := (m[i], c);
        E2 := E2 * (z, beta[i]);
        if i eq 3 then E2 := E2 * z^2; end if;
      end for;
      assert E2 in P[j];
      if Coord(E2, j) ne 0 then conjbad +:= 1; end if;
    end for;

    tar := (r in P[j+1]) select Zero(Generic(KS)) else CoordChecked(r^-1, j);
    good := (mism eq 0) and (ckK eq D+1) and (ckL eq D-1) and (resid eq D-1)
            and (RSK subset KS) and t3 and t4 and (rkphi eq 2) and w6 and (conjbad eq 0)
            and (tar in RSK);
    NCASE +:= 1; if not good then NFAIL +:= 1; end if;
    Say(Sprintf("  L%o: dimL %o dimK %o | T1 form-mism %o of %o | ckK %o (=d+1 %o) ckFull %o (=d-1 %o) resid %o | im<=K %o | T3 purepow rank %o ker=<e_x1> %o | T4 brkpow in K %o rank %o ker %o +duals rank %o (=ckK %o) | T5 rk(phi) %o | T6 diag-power witness %o conj-kernel %o of %o | T7 defect in im %o | %o s",
      j, dm[j], Dimension(KS), mism, D*nb, ckK, ckK eq D+1, ckL, ckL eq D-1, resid,
      RSK subset KS, Rank(M4), Kernel(M4) eq predk, inK, Rank(Mq), Kernel(Mq) eq predk,
      Rank(Mall), Rank(Mall) eq ckK, rkphi, w6, #cbasis - conjbad, #cbasis,
      tar in RSK, Cputime(tj)));

    if not (r in P[j+1]) then
      A := Matrix(rowsK);
      ok, x := IsConsistent(A, tar);
      assert ok;
      for i in [1..D] do for l in [1..nb] do
        if x[(i-1)*nb + l] ne 0 then m[i] := m[i] * reps[l]; end if;
      end for; end for;
      r := Rel(m);
      assert r in P[j+1];
      beta := FoxPerm(m);
    end if;
  end for;
  Say(Sprintf("(t,s)=(%o,%o): R(m) = 1 in Q_%o : %o", t, s, CLS, r eq Id(Q)));
end for;

Say(Sprintf("SUMMARY: %o scored assertions, %o failures", NCASE, NFAIL));
Say("DONE");
