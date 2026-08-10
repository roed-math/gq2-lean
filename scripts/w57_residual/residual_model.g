#############################################################################
##
##  W57-RESIDUAL: is `EvenClimbResidualSupply` true on the even branches?
##
##  Model.  Exactly the wave-56 model of `scripts/w56_slotzero/slotzero_model.g`:
##  for a branch (M or N), a branch depth alpha, a tower level k >= 3 and a
##  handle count h, build the honest even relator group of rank 4+2h,
##
##    M:  x1^2 * [x1,x2] * x3^(2^alpha) * [x3,x4] * prod_j [u_j,v_j]
##    N:  x1^(2+2^alpha) * [x1,x2] * [x3,x4] * prod_j [u_j,v_j]
##
##  (GAP generators 1..4 are the repo's core letters 0..3; the relator shapes
##  are `MarkedCore.mWord` / `MarkedCore.nWord` verbatim), form the level-k
##  two-quotient Q = G / lambda_{k+1} by the p-quotient algorithm, and put on
##  it the cyclotomic character chi(x_i) = v_i in (Z/2^(k+alpha))^*, with
##
##    vM = (1, -1, 1, (1-2^alpha)^-1),   vN = (1, -(1+2^alpha)^-1, 1, 1),
##
##  value 1 on every handle letter.
##
##  WHAT THIS LANE MEASURES.  The residual supply asks for ONE element -- the
##  residual of one admissible correction -- to lie in the BRACKET span
##
##    B := < R_i(p) : p neutral >        (chi(p) = 1 mod 2^(k+alpha))
##
##  rather than merely in the RAW span
##
##    R := < R_i(p) : p in Lam >,        Lam := lambda_{k-1}/lambda_{k+1},
##
##  where the row functionals are the repo's `evenRawDbarWord` coordinate rows
##
##    R_0(p) = p^2 * [p,b_0] * [p,b_1]     (the ONLY row carrying a square)
##    R_1(p) = [p,b_0]     R_2(p) = [p,b_3]     R_3(p) = [p,b_2]
##    R_{u_j}(p) = [p,b_{v_j}]             R_{v_j}(p) = [p,b_{u_j}].
##
##  Wave 56 refuted R = B (that is `Hup`).  This lane's claim is that the gap
##  R/B is ONE bit, cut out by the character digit at position k+alpha-1, and
##  that the honest stage defect always lies on the trivial side of it because
##  every exponent sum of an even relator is even.  Concretely we certify:
##
##   (1) Omega(R_0(p)) = Lambda(p)  and  Omega(R_i(p)) = 0 for i <> 0, where
##       Lambda(p) = 1 iff chi(p) is sharp at k+alpha-2  (p in Lam), and
##       Omega(z)  = 1 iff chi(z) is sharp at k+alpha-1  (z in Z_k).
##       Equivalently: chi(evenRawDbarWord(c)) = chi(c_0)^2.
##   (2) dim R - dim B = 1 and  B = R  intersect  ker Omega.
##   (3) Omega is nonzero on Z_k (the sharp central class exists) and Lambda is
##       nonzero on Lam (so nothing here is vacuous).
##   (4) For honestly sampled stage tuples T (generating markings of
##       Qbar = Q/Z_k = G/lambda_k that kill the relator and satisfy the row
##       condition), the defect d = W(lift T) satisfies Omega(d) = 0, hence
##       d^-1 lies in B as soon as it lies in R.  We also report whether
##       d^-1 lies in R at all, which is the separate `Hfam` question.
##
#############################################################################

SetPrintFormattingStatus("*stdout*", false);
LogTo("scripts/w57_residual/results/w57_residual_model.txt");

Print("### W57-RESIDUAL model: the residual supply on the even branches\n");
Print("### GAP ", GAPInfo.Version, "\n\n");

# ---------------------------------------------------------------- the group

EvenRelatorGroup := function(branch, alpha, h)
  local n, F, g, rel, j;
  n := 4 + 2*h;
  F := FreeGroup(n);
  g := GeneratorsOfGroup(F);
  if branch = "M" then
    rel := g[1]^2 * Comm(g[1],g[2]) * g[3]^(2^alpha) * Comm(g[3],g[4]);
  elif branch = "N" then
    rel := g[1]^(2+2^alpha) * Comm(g[1],g[2]) * Comm(g[3],g[4]);
  else
    Error("branch must be M or N");
  fi;
  for j in [1..h] do
    rel := rel * Comm(g[2*j+3], g[2*j+4]);
  od;
  return F/[rel];
end;

# the relator evaluated at an arbitrary tuple of a group
RelAt := function(branch, alpha, h, t)
  local w, j;
  if branch = "M" then
    w := t[1]^2 * Comm(t[1],t[2]) * t[3]^(2^alpha) * Comm(t[3],t[4]);
  else
    w := t[1]^(2+2^alpha) * Comm(t[1],t[2]) * Comm(t[3],t[4]);
  fi;
  for j in [1..h] do
    w := w * Comm(t[2*j+3], t[2*j+4]);
  od;
  return w;
end;

# --------------------------------------------------------------- the values

RowValues := function(branch, alpha, h, N)
  local m, v, j;
  m := 2^N;
  if branch = "M" then
    v := [ ZmodnZObj(1, m), ZmodnZObj(-1, m), ZmodnZObj(1, m),
           ZmodnZObj(1 - 2^alpha, m)^-1 ];
  else
    v := [ ZmodnZObj(1, m), -(ZmodnZObj(1 + 2^alpha, m)^-1), ZmodnZObj(1, m),
           ZmodnZObj(1, m) ];
  fi;
  for j in [1..2*h] do Add(v, ZmodnZObj(1, m)); od;
  return v;
end;

# ------------------------- 2-adic level of u - 1 for a unit u mod 2^N

LevelOfUnit := function(u, N)
  local x, j;
  x := (Int(u) - 1) mod 2^N;
  if x = 0 then return N; fi;
  j := 0;
  while x mod 2 = 0 do x := x/2; j := j+1; od;
  return j;
end;

F2ONE := Z(2)^0;;
F2ZERO := 0*Z(2)^0;;
B2F := function(x) if x then return F2ONE; else return F2ZERO; fi; end;;

# ------------------------------------------------------------- the main run

RunCase := function(branch, alpha, k, h, nsample)
  local n, G, q, epi, Q, ser, Lam, Zk, b, N, U, v, chi, i, j, t, w, ok,
        pcL, pcZ, n1, n2, R, Mat, dvec, ovec, lin, levels, e1, e2, x, y,
        Rsp, Bsp, P, gensR, gensB, ker1, Kx, nu, Qbar, bb, T, tl, d, dexp,
        nfound, nOmega1, nInR, nInB, tries, maxtries, chiZk, chiN1, rowok,
        z, dexp2, res, cvec, idOK, sqOK, chid, chid2, lamNZ, omNZ, dimR, dimB,
        RcapKer, dimRcap, nmark, sample, sigma, uu, ii, allmark, m, serb;

  n := 4 + 2*h;
  N := k + alpha;
  Print("=====================================================\n");
  Print("branch ", branch, "   alpha ", alpha, "   k ", k, "   h ", h,
        "   rank ", n, "   (chi mod 2^", N, ")\n");

  G := EvenRelatorGroup(branch, alpha, h);
  q := PQuotient(G, 2, k);
  epi := EpimorphismQuotientSystem(q);
  Q := Image(epi);
  Print("  |Q| = 2^", LogInt(Size(Q),2), "   (Q = G / lambda_", k+1, ")\n");

  ser := PCentralSeries(Q, 2);
  Lam := ser[k-1];                    # lambda_{k-1} / lambda_{k+1}
  Zk  := ser[k];                      # Z_k = lambda_k / lambda_{k+1}
  Print("  |lambda_", k-1, "| = 2^", LogInt(Size(Lam),2),
        "   |Z_", k, "| = 2^", LogInt(Size(Zk),2), "\n");

  b := List(GeneratorsOfGroup(G), x -> Image(epi, x));

  U := Units(ZmodnZ(2^N));
  v := RowValues(branch, alpha, h, N);
  chi := GroupHomomorphismByImages(Q, U, b, v);
  if chi = fail then
    Print("  !! chi is NOT well defined on Q\n");
    return fail;
  fi;
  Print("  chi : Q -> (Z/2^", N, ")^*  IS well defined\n");

  # ---------------- the row functionals
  R := [];
  R[1] := p -> p^2 * Comm(p, b[1]) * Comm(p, b[2]);
  R[2] := p -> Comm(p, b[1]);
  R[3] := p -> Comm(p, b[4]);
  R[4] := p -> Comm(p, b[3]);
  for j in [1..h] do
    R[2*j+3] := function(p) return Comm(p, b[2*j+4]); end;
    R[2*j+4] := function(p) return Comm(p, b[2*j+3]); end;
  od;

  pcL := Pcgs(Lam);   n1 := Length(pcL);
  pcZ := Pcgs(Zk);    n2 := Length(pcZ);
  Print("  dim lambda_", k-1, " = ", n1, "   dim Z_", k, " = ", n2, "\n");

  if not ForAll([1..n], i -> ForAll(pcL, p -> R[i](p) in Zk)) then
    Print("  !! a row functional leaves Z_", k, "\n"); return fail;
  fi;

  Mat := List([1..n], i -> List(pcL,
           p -> ExponentsOfPcElement(pcZ, R[i](p)) * F2ONE));

  lin := true;
  for i in [1..n] do
    for t in [1..20] do
      e1 := List([1..n1], y -> Random([0,1]));
      e2 := List([1..n1], y -> Random([0,1]));
      x := PcElementByExponents(pcL, e1);
      y := PcElementByExponents(pcL, e2);
      if ExponentsOfPcElement(pcZ, R[i](x*y)) * F2ONE <>
         (e1*F2ONE) * Mat[i] + (e2*F2ONE) * Mat[i] then lin := false; fi;
    od;
  od;
  Print("  row functionals GF(2)-linear on lambda_", k-1, "/Frattini : ", lin, "\n");
  if not lin then return fail; fi;

  # ---------------- the two digit functionals
  #   Lambda on Lam : sharp at k+alpha-2      (the wave-56 flip bit)
  #   Omega  on Z_k : sharp at k+alpha-1      (this lane's bit)
  dvec := List(pcL, p -> B2F(LevelOfUnit(Image(chi, p), N) < k+alpha-1));
  ovec := List(pcZ, z -> B2F(LevelOfUnit(Image(chi, z), N) < k+alpha));
  levels := List(pcL, p -> LevelOfUnit(Image(chi, p), N));
  lamNZ := not IsZero(dvec);
  omNZ  := not IsZero(ovec);
  Print("  chi-levels on a pcgs of lambda_", k-1, " : min ", Minimum(levels),
        "   (depth boundary ", k+alpha-2, ")\n");
  Print("  Lambda nonzero on lambda_", k-1, " (sharp class exists) : ", lamNZ, "\n");
  Print("  Omega  nonzero on Z_", k, " (SHARP CENTRAL CLASS exists) : ", omNZ, "\n");

  # ---------------- (1) Omega(R_i(p)) = delta_{i0} * Lambda(p)
  idOK := true;
  for i in [1..n] do
    for y in [1..n1] do
      uu := Mat[i][y] * ovec;                      # Omega(R_i(pcL[y]))
      if i = 1 then
        if uu <> dvec[y] then idOK := false; fi;
      else
        if uu <> F2ZERO then idOK := false; fi;
      fi;
    od;
  od;
  Print("  (1) Omega(R_0(p)) = Lambda(p) and Omega(R_i(p)) = 0 for i<>0 : ",
        idOK, "\n");

  # the same identity in group form: chi(dbarWord(c)) = chi(c_0)^2
  sqOK := true;
  for t in [1..30] do
    cvec := List([1..n], i -> Random(Lam));
    w := One(Q);
    for i in [1..n] do w := w * R[i](cvec[i]); od;
    if Image(chi, w) <> Image(chi, cvec[1])^2 then sqOK := false; fi;
  od;
  Print("  (1') chi(evenRawDbarWord(c)) = chi(c_0)^2 on 30 random c : ",
        sqOK, "\n");

  # ---------------- (2) the raw span, the bracket span, and the gap
  P := Kernel(RestrictedMapping(chi, Lam));        # the neutral coordinates
  Print("  |neutral subgroup P| = 2^", LogInt(Size(P),2),
        "   index in lambda_", k-1, " = ", Size(Lam)/Size(P), "\n");

  gensR := [];
  gensB := [];
  for i in [1..n] do
    for x in pcL do
      Add(gensR, ExponentsOfPcElement(pcZ, R[i](x)) * F2ONE);
    od;
    for x in GeneratorsOfGroup(P) do
      Add(gensB, ExponentsOfPcElement(pcZ, R[i](x)) * F2ONE);
    od;
  od;
  Rsp := VectorSpace(GF(2), gensR, Zero(gensR[1]));
  Bsp := VectorSpace(GF(2), gensB, Zero(gensR[1]));
  dimR := Dimension(Rsp);  dimB := Dimension(Bsp);
  Print("  dim RAW span R = ", dimR, "   dim BRACKET span B = ", dimB,
        "   gap = ", dimR - dimB, "\n");

  # R intersect ker Omega : Omega is a functional, so the codimension is 0 or 1
  if ForAll(Basis(Rsp), z -> IsZero(z * ovec)) then
    dimRcap := dimR;
  else
    dimRcap := dimR - 1;
  fi;
  Print("  dim (R cap ker Omega) = ", dimRcap,
        "   equals dim B : ", dimRcap = dimB,
        "   B <= ker Omega : ", ForAll(Basis(Bsp), z -> IsZero(z * ovec)), "\n");

  # ---------------- (4) honest stage tuples and their defects
  nu := NaturalHomomorphismByNormalSubgroup(Q, Zk);
  Qbar := Image(nu);
  bb := List(b, x -> Image(nu, x));
  Print("  |Qbar| = |G/lambda_", k, "| = 2^", LogInt(Size(Qbar),2), "\n");

  chiZk := Image(chi, Zk);
  Print("  chi(Z_", k, ") has order ", Size(chiZk), "\n");

  # the row condition is  chi(t_i) in v_i * chi(Z_k); by construction below we
  # sample T_i = bb_i * c_i with c_i in the kernel of chi mod 2^(N-1), which is
  # exactly the row condition (lifts of T_i differ by Z_k).
  Kx := PreImage(nu, Subgroup(Qbar, []));          # = Zk, placeholder
  ker1 := Kernel(GroupHomomorphismByImages(Q, Units(ZmodnZ(2^(N-1))), b,
            List(v, y -> ZmodnZObj(Int(y), 2^(N-1)))));
  Kx := Image(nu, ker1);                           # allowed perturbations
  Print("  |allowed perturbation subgroup of Qbar| = 2^",
        LogInt(Size(Kx),2), "\n");

  # The perturbations are stratified by the depth at which they act: taking
  # c_i in K cap lambda_m(Qbar) makes the relator shift land in lambda_{m+1},
  # so the marking condition W(T) = 1 gets likelier as m grows and is free at
  # m = k-1.  We sweep m from 1 (fully general perturbations) upwards, so the
  # sample is NOT confined to deep perturbations.
  serb := PCentralSeries(Qbar, 2);
  nfound := 0; nOmega1 := 0; nInR := 0; nInB := 0; tries := 0;
  allmark := true;
  res := [];
  for m in [1..k-1] do
    Kx := Intersection(Image(nu, ker1), serb[m]);
    maxtries := 60000;
    if LogInt(Size(Qbar),2) > 20 then maxtries := 4000; fi;
    nmark := 0; sample := 0;
    while nmark < nsample and sample < maxtries do
      sample := sample + 1; tries := tries + 1;
      T := List([1..n], i -> bb[i] * Random(Kx));
      if RelAt(branch, alpha, h, T) <> One(Qbar) then continue; fi;
      if Size(Subgroup(Qbar, T)) <> Size(Qbar) then continue; fi;
      # row condition, checked honestly on a lift
      tl := List(T, x -> PreImagesRepresentative(nu, x));
      rowok := ForAll([1..n], i -> Image(chi, tl[i]) * v[i]^-1 in chiZk);
      if not rowok then continue; fi;
      d := RelAt(branch, alpha, h, tl);
      if not d in Zk then Print("  !! defect left Z_k\n"); return fail; fi;
      # lift independence of the defect
      tl := List([1..n], i -> tl[i] * Random(Zk));
      if RelAt(branch, alpha, h, tl) <> d then allmark := false; fi;
      dexp := ExponentsOfPcElement(pcZ, d) * F2ONE;
      nmark := nmark + 1; nfound := nfound + 1;
      if not IsZero(dexp * ovec) then nOmega1 := nOmega1 + 1; fi;
      if dexp in Rsp then nInR := nInR + 1; fi;
      if dexp in Bsp then nInB := nInB + 1; fi;
    od;
    Add(res, [m, nmark]);
  od;
  Print("  stage tuples by perturbation depth m, [m, count] : ", res, "\n");
  Print("  honest stage tuples sampled : ", nfound, " (of ", tries, " tries)\n");
  Print("  defect independent of the chosen lift : ", allmark, "\n");
  Print("  (4) tuples with Omega(defect) = 1 : ", nOmega1,
        "      <-- 0 means the defect never sees the bit\n");
  Print("      tuples with defect in RAW span R    : ", nInR, " / ", nfound,
        "   [the Hfam question]\n");
  Print("      tuples with defect in BRACKET span B: ", nInB, " / ", nfound,
        "   [the residual supply]\n");

  Print("\n");
  return [idOK, sqOK, dimR - dimB, dimRcap = dimB, omNZ, lamNZ,
          nfound, nOmega1, nInR, nInB];
end;

# --------------------------------------------------------------- the sweep

CASES := [
  ["M", 2, 3, 0], ["M", 3, 3, 0], ["M", 4, 3, 0], ["M", 5, 3, 0],
  ["N", 2, 3, 0], ["N", 3, 3, 0], ["N", 4, 3, 0], ["N", 5, 3, 0],
  ["M", 3, 4, 0], ["N", 3, 4, 0],
  ["M", 3, 3, 1], ["N", 3, 3, 1]
];

SUMMARY := [];
for CASE in CASES do
  Add(SUMMARY, [CASE, RunCase(CASE[1], CASE[2], CASE[3], CASE[4], 60)]);
od;

Print("=====================================================\n");
Print("SUMMARY  [branch,alpha,k,h] -> [idOK, sqOK, dim R/B, B=RcapKerOmega,\n");
Print("          Omega<>0 on Z_k, Lambda<>0 on Lam, #tuples, #Omega(d)=1,\n");
Print("          #d in R, #d in B]\n");
for i in [1..Length(SUMMARY)] do
  Print("  ", SUMMARY[i][1], "  ", SUMMARY[i][2], "\n");
od;
Print("=====================================================\n");

LogTo();
QUIT;
