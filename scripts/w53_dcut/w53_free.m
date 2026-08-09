/*  W53-DCUT -- the d-1 cut of the graded Fox form, in the universal (free) ambient.
 *
 *      magma -b ds:="2,3,4,5" cls:=4 kcs:="1,2,3" nt:=6 seed:=1 out:=results/w53free_c4.txt w53_free.m
 *
 *  W52 measured corank(delta) = d + 1 at every level and split it 2 + (d-1): the 2 is the
 *  canonical pair lambda, nu (proved), the d-1 was unexplained.  This script identifies the
 *  d-1 exactly, and shows it has nothing to do with K.
 *
 *  Setting.  L = the layers P_w/P_{w+1} of the lower exponent-2 central series of the FREE
 *  pro-2 group of rank d; V = L_1 = F_2^d; F : L_w -> L_{w+1} the squaring map (linear for
 *  w >= 2).  Fix mod-2 Fox rows beta_1..beta_d in V and a Frobenius slot set S, and let
 *
 *      Delta_j(z) = sum_i [z_i, beta_i] + sum_{i in S} F(z_i)   :  (L_{j-1})^d -> L_j
 *
 *  be the graded Fox form of W52 section 1.1.  Fix also a K-tower: K_1 a subspace of V of
 *  codimension kc, K_w = [L_{w-1}, V] + F(K_{w-1}); the campaign has kc = 2 with the two
 *  power directions sigma, x0, and the sweeps run Delta on (K_{j-1})^d only.
 *
 *  Tests, per rank d, per level j = 3..cls, per frame beta, per slot set S, per kc:
 *
 *    A  the K-tower certificate: codim(K_w) = kc at every layer, and
 *       L_w = K_w + <p_1^(2^(w-1)), .., p_kc^(2^(w-1))> for the power directions p_a;
 *    B  the exact power identity in the layer, every basis pair, every level:
 *              [x^(2^k), y]  =  F^k([x,y]) + F^(k-1)(ad(x)^2(y))          (x, y in V, k >= 1)
 *       -- the naive [F(x), y] = ad(x)^2(y) is FALSE at the bottom of the tower, and the
 *       error term F^k([x,y]) is exactly what carries the d-1 cut;
 *    C  corank of Delta on the FULL domain (L_{j-1})^d is exactly d - 1;
 *    D  a basis of that cokernel: the pure powers  q_i = beta_i^(2^(j-1)) = F^(j-1)(beta_i)
 *       of the Fox rows span L_j / im Delta, with kernel exactly the Frobenius slot,
 *       so { q_i : i <> s } is a basis and the cokernel is  F_2^slots / <e_s>.
 *       Three descriptions are checked to agree modulo the image:
 *              c1_i = [beta_i^(2^(j-2)), beta_s]     (power dressing of the Frobenius slot)
 *              c2_i = [beta_i, beta_s]^(2^(j-2))     (Frobenius power of the bracket)
 *              c4_i = beta_i^(2^(j-1))               (pure power of the Fox row)
 *       together with c3_i = ad(beta_i)^2(beta_s)^(2^(j-3)) lying IN the image, and the two
 *       explicit witnesses c1_i + c4_i in im (dress slot s by beta_i^(2^(j-2))) and
 *       c4_s in im (dress slot s by its own row's power, since [x^(2^k), x] = 1);
 *    E  the K-restricted numbers: im(Delta|K) inside K_j, corank(Delta|K) = (d-1) + kc,
 *       residue dim K_j/im = d - 1 independent of kc, rank(phi) = kc where phi is the
 *       contribution of the kc power dressings modulo im(Delta|K) -- the power dressings
 *       supply exactly the lambda-nu block and nothing else -- plus an EXPLICIT basis of
 *       the (d-1+kc)-dimensional cokernel: the d-1 bracket powers c2_i = [beta_i, beta_s]^(2^(j-2))
 *       (i <> s), which lie in K_j and are a basis of the residue K_j/im, together with the
 *       kc pure powers p_a^(2^(j-1)) spanning L_j / K_j (the lambda-nu duals);
 *    F  independence: is im(Delta_full) determined by beta_s alone?  (Recorded, not assumed.)
 *
 *  Controls, reported but not scored: |S| = 0, |S| >= 2, rank-deficient frames.
 */
SetColumns(0); SetAutoColumns(false);

DS  := [ StringToInteger(x) : x in Split(ds, ",") ];
CLS := StringToInteger(cls);
KCS := [ StringToInteger(x) : x in Split(kcs, ",") ];
NT  := StringToInteger(nt);
SetSeed(StringToInteger(seed));
OUT := out; System("rm -f " cat OUT);
procedure Say(str) PrintFile(OUT, str); print str; end procedure;

Say(Sprintf("W53-DCUT free-ambient sweep -- ranks %o, class %o, K-codims %o, %o random frames, seed %o",
    DS, CLS, KCS, NT, seed));

NCASE := 0; NFAIL := 0;

for D in DS do
  t0 := Cputime();
  Q  := pQuotient(FreeGroup(D), 2, CLS);
  P  := pCentralSeries(Q, 2);
  dm := [ Ilog2(#P[i] div #P[i+1]) : i in [1..#P-1] ];
  ofs := [0 : w in [1..CLS+1]];
  for w in [1..CLS] do ofs[w+1] := ofs[w] + dm[w]; end for;
  n := NPCgens(Q);
  for w in [1..CLS] do
    assert NPCgens(P[w]) eq n - ofs[w];
    assert Q.(ofs[w]+1) in P[w];
    assert not (Q.(ofs[w]+1) in P[w+1]);
  end for;
  Say(Sprintf("==== d = %o : free class-%o 2-quotient, order 2^%o, layers %o (%o s) ====",
      D, CLS, n, dm, Cputime(t0)));

  Coord := function(x, w)
    e := Eltseq(x);
    return Vector(GF(2), [ GF(2)!e[k] : k in [ofs[w]+1 .. ofs[w+1]] ]);
  end function;
  IndepSubset := function(cands, w)
    A := Matrix([ Coord(x, w) : x in cands ]);
    E := EchelonForm(Transpose(A)); piv := [];
    for i in [1..Nrows(E)] do z := Depth(E[i]); if z ne 0 then Append(~piv, z); end if; end for;
    return [ cands[j] : j in piv ];
  end function;
  AdIter := function(x, y, r)          /* ad(x)^r (y) by group commutators */
    z := y; for i in [1..r] do z := (x, z); end for; return z;
  end function;

  g    := [ Q.i : i in [1..D] ];
  LGEN := [ [ Q.k : k in [ofs[w]+1 .. ofs[w+1]] ] : w in [1..CLS] ];
  grpelt := function(v)
    x := Id(Q);
    for i in [1..D] do if v[i] ne 0 then x := x * g[i]; end if; end for;
    return x;
  end function;

  /* ---- A : K-towers, one per codimension; K_1 = span of the last D - kc generators ---- */
  KBs := AssociativeArray();
  for KC in KCS do
    if KC ge D then continue; end if;
    KB := [ [ g[i] : i in [KC+1..D] ] ];
    for w in [2..CLS] do
      cands := [];
      for x in LGEN[w-1] do for i in [1..D] do Append(~cands, (x, g[i])); end for; end for;
      for b in KB[w-1] do Append(~cands, b^2); end for;
      Append(~KB, IndepSubset(cands, w));
    end for;
    okc := &and [ dm[w] - #KB[w] eq KC : w in [1..CLS] ];
    okp := true;
    for w in [1..CLS] do
      rows := [ Coord(x, w) : x in KB[w] ] cat [ Coord(g[a]^(2^(w-1)), w) : a in [1..KC] ];
      okp := okp and (Rank(Matrix(rows)) eq dm[w]);
    end for;
    KBs[KC] := KB;
    NCASE +:= 1; if not (okc and okp) then NFAIL +:= 1; end if;
    Say(Sprintf("  [A] kc=%o : K dims %o, codim-%o certificate %o, powers complete it %o",
        KC, [#b : b in KB], KC, okc, okp));
  end for;
  KCU := [ k : k in KCS | k lt D ];

  /* ---- B : the exact power identity ---- */
  for j in [3..CLS] do
    k := j - 2; bad := 0; badnaive := 0; tot := 0;
    for a in [1..D] do for b in [1..D] do
      tot +:= 1;
      lhs := Coord((g[a]^(2^k), g[b]), j);
      rhs := Coord((g[a], g[b])^(2^k), j) + Coord(AdIter(g[a], g[b], 2)^(2^(k-1)), j);
      if lhs ne rhs then bad +:= 1; end if;
      if lhs ne Coord(AdIter(g[a], g[b], 2^k), j) then badnaive +:= 1; end if;
    end for; end for;
    NCASE +:= 1; if bad ne 0 then NFAIL +:= 1; end if;
    Say(Sprintf("  [B] L%o : [x^(2^%o),y] = F^%o([x,y]) + F^%o(ad(x)^2 y) : %o mismatches of %o pairs (naive ad-power form: %o mismatches)",
        j, k, k, k-1, bad, tot, badnaive));
  end for;

  VD := VectorSpace(GF(2), D);

  /* ---- C0 : the pure-power space of the ambient, P_j = L_j / [L_{j-1}, V].  In the free
     ambient pi : V -> P_j,  v |-> F^(j-1)(v),  is a linear isomorphism (linearity is the
     exact identity [B]: F^(j-1)(v+w) - F^(j-1)(v) - F^(j-1)(w) = F^(j-2)([v,w]) lies in
     [L_{j-1}, V]).  This is the space the d-1 cut lives in. ---- */
  for j in [3..CLS] do
    brows := [];
    for x in LGEN[j-1] do for i in [1..D] do Append(~brows, Coord((x, g[i]), j)); end for; end for;
    BR := RowSpace(Matrix(brows));
    pdim := dm[j] - Dimension(BR);
    VVj := VectorSpace(GF(2), dm[j]);
    CB, mb := quo< VVj | BR >;
    pib := [ mb(VVj!Coord(g[i]^(2^(j-1)), j)) : i in [1..D] ];
    Mpi := Matrix(pib);
    linbad := 0;
    for v in VD do
      lhs := mb(VVj!Coord(grpelt(v)^(2^(j-1)), j));
      rhs := Zero(CB);
      for i in [1..D] do if v[i] ne 0 then rhs +:= pib[i]; end if; end for;
      if lhs ne rhs then linbad +:= 1; end if;
    end for;
    good := (pdim eq D) and (Rank(Mpi) eq D) and (linbad eq 0);
    NCASE +:= 1; if not good then NFAIL +:= 1; end if;
    Say(Sprintf("  [C0] L%o : dim L_j / [L_{j-1},V] = %o (=d %o) | pi : V -> P_j rank %o injective %o | pi linear: %o failures of %o",
        j, pdim, pdim eq D, Rank(Mpi), Rank(Mpi) eq D, linbad, 2^D));
  end for;

  Battery := procedure(bmat, SS, tag, expect, ~NC, ~NF)
    bet := [ grpelt(bmat[i]) : i in [1..D] ];
    rkb := Rank(bmat);
    for j in [3..CLS] do
      LG := LGEN[j-1];
      rowsL := [];
      for i in [1..D] do for b in LG do
        r := Coord((b, bet[i]), j);
        if i in SS then r +:= Coord(b^2, j); end if;
        Append(~rowsL, r);
      end for; end for;
      RSL := RowSpace(Matrix(rowsL));
      ckL := dm[j] - Dimension(RSL);
      VV := VectorSpace(GF(2), dm[j]);
      CQ, mp := quo< VV | RSL >;
      NC +:= 1; if expect and ckL ne D - 1 then NF +:= 1; end if;

      /* [D] the cokernel basis, only meaningful when |S| = 1 */
      pdesc := "n/a";
      if #SS eq 1 then
        s := Rep(SS);
        c1 := [ Coord((bet[i]^(2^(j-2)), bet[s]), j)          : i in [1..D] ];
        c2 := [ Coord((bet[i], bet[s])^(2^(j-2)), j)          : i in [1..D] ];
        c3 := [ Coord(AdIter(bet[i], bet[s], 2)^(2^(j-3)), j) : i in [1..D] ];
        c4 := [ Coord(bet[i]^(2^(j-1)), j)                    : i in [1..D] ];
        M4 := Matrix([ mp(VV!x) : x in c4 ]);
        ker4 := Kernel(M4);
        predk := sub< VectorSpace(GF(2), D) | [ VectorSpace(GF(2), D).s ] >;
        agree := &and [ (VV!(c1[i] + c2[i]) in RSL) and (VV!(c1[i] + c4[i]) in RSL)
                        and (VV!c3[i] in RSL) : i in [1..D] ];
        wits  := VV!c4[s] in RSL;
        eqr := Rank(Matrix([ mp(VV!x) : x in c1 ])) eq Rank(M4)
               and Rank(Matrix([ mp(VV!x) : x in c2 ])) eq Rank(M4);
        good := (Rank(M4) eq ckL) and (ker4 eq predk) and agree and wits and eqr;
        NC +:= 1; if expect and not good then NF +:= 1; end if;
        pdesc := Sprintf("purepow rank %o (=ckFull %o) ker=<e_s> %o | c1=c2=c4 mod im, c3 in im %o | c4_s in im %o | ranks agree %o",
                 Rank(M4), Rank(M4) eq ckL, ker4 eq predk, agree, wits, eqr);
      end if;

      /* [E] K-restricted numbers, per codimension */
      edesc := "";
      for KC in KCU do
        KB := KBs[KC];
        rowsK := [];
        for i in [1..D] do for b in KB[j-1] do
          r := Coord((b, bet[i]), j);
          if i in SS then r +:= Coord(b^2, j); end if;
          Append(~rowsK, r);
        end for; end for;
        RSK := RowSpace(Matrix(rowsK));
        KS  := RowSpace(Matrix([ Coord(x, j) : x in KB[j] ]));
        ckK := dm[j] - Dimension(RSK);
        resid := Dimension(KS) - Dimension(RSK);
        CQK, mpk := quo< VV | RSK >;
        prows := [];
        for a in [1..KC] do for i in [1..D] do
          r := Coord((g[a]^(2^(j-2)), bet[i]), j);
          if i in SS then r +:= Coord(g[a]^(2^(j-1)), j); end if;
          Append(~prows, mpk(VV!r));
        end for; end for;
        rkphi := Rank(Matrix(prows));
        /* the explicit cokernel basis: the d-1 bracket powers F^{j-2}([beta_i, beta_s])
           inside K_j, plus the kc pure powers p_a^(2^(j-1)) spanning L_j / K_j */
        bdesc := "";
        if #SS eq 1 then
          s := Rep(SS);
          qc := [ Coord((bet[i], bet[s])^(2^(j-2)), j) : i in [1..D] ];
          inK := &and [ VV!x in KS : x in qc ];
          Mq := Matrix([ mpk(VV!x) : x in qc ]);
          kerq := Kernel(Mq);
          predq := sub< VectorSpace(GF(2), D) | [ VectorSpace(GF(2), D).s ] >;
          Mall := Matrix([ mpk(VV!x) : x in qc ]
                     cat [ mpk(VV!Coord(g[a]^(2^(j-1)), j)) : a in [1..KC] ]);
          bok := inK and (Rank(Mq) eq resid) and (kerq eq predq) and (Rank(Mall) eq ckK);
          bdesc := Sprintf(" | brkpow in K %o rank %o=resid %o ker=<e_s> %o | +powers rank %o=ckK %o",
            inK, Rank(Mq), Rank(Mq) eq resid, kerq eq predq, Rank(Mall), Rank(Mall) eq ckK);
        else
          bok := true;
        end if;
        good := (RSK subset KS) and (ckK eq ckL + KC) and (resid eq ckL) and (rkphi eq KC) and bok;
        NC +:= 1; if expect and not good then NF +:= 1; end if;
        edesc cat:= Sprintf(" kc%o[ckK %o=ckL+kc %o | imK<=K %o | resid %o=ckL %o | rk(phi) %o=kc %o%o]",
          KC, ckK, ckK eq ckL + KC, RSK subset KS, resid, resid eq ckL, rkphi, rkphi eq KC, bdesc);
      end for;

      Say(Sprintf("  [%o] d=%o L%o S=%o rk(beta)=%o : ckFull %o (=d-1 %o) | %o |%o",
          tag, D, j, Sort(SetToSequence(SS)), rkb, ckL, ckL eq D-1, pdesc, edesc));
    end for;
  end procedure;

  /* ---- main cases : full-rank frames, single Frobenius slot ---- */
  Battery(IdentityMatrix(GF(2), D), {Min(3, D)}, "id", true, ~NCASE, ~NFAIL);
  for tr in [1..NT] do
    repeat B := RandomMatrix(GF(2), D, D); until Rank(B) eq D;
    Battery(B, {Random(1, D)}, Sprintf("rand%o", tr), true, ~NCASE, ~NFAIL);
  end for;

  /* ---- F : is im(Delta_full) determined by beta_s alone? ---- */
  for j in [3..CLS] do
    bs := IdentityMatrix(GF(2), D)[1];
    ims := [];
    for tr in [1..Max(2, Min(NT, 4))] do
      repeat
        B := RandomMatrix(GF(2), D, D); B[1] := bs;
      until Rank(B) eq D;
      bet := [ grpelt(B[i]) : i in [1..D] ];
      rowsL := [];
      for i in [1..D] do for b in LGEN[j-1] do
        r := Coord((b, bet[i]), j);
        if i eq 1 then r +:= Coord(b^2, j); end if;
        Append(~rowsL, r);
      end for; end for;
      Append(~ims, RowSpace(Matrix(rowsL)));
    end for;
    Say(Sprintf("  [F] d=%o L%o : im(Delta_full) equal across %o frames sharing beta_s : %o | coranks %o",
        D, j, #ims, &and [ ims[k] eq ims[1] : k in [1..#ims] ],
        { dm[j] - Dimension(x) : x in ims }));
  end for;

  /* ---- controls ---- */
  Say(Sprintf("  ---- controls (d = %o), not scored ----", D));
  ID := IdentityMatrix(GF(2), D);
  for k in [0, 2, D] do
    if k eq 1 or k gt D then continue; end if;
    Battery(ID, {1..k}, Sprintf("ctl|S|=%o", k), false, ~NCASE, ~NFAIL);
  end for;
  if D ge 2 then
    B := ID; B[1] := B[2];
    Battery(B, {Min(3, D)}, "ctl-deficient", false, ~NCASE, ~NFAIL);
  end if;
end for;

Say(Sprintf("SUMMARY: %o scored assertions, %o failures", NCASE, NFAIL));
Say("DONE");
