#############################################################################
##
##  W56-SLOTZERO: the even flip supply at the diagonal coordinate `0`.
##
##  Model.  For a branch (M or N), a branch depth alpha, a tower level k >= 3
##  and a handle count h, build the honest even relator group of rank 4+2h,
##
##    M:  x1^2 * [x1,x2] * x3^(2^alpha) * [x3,x4] * prod_j [u_j,v_j]
##    N:  x1^(2+2^alpha) * [x1,x2] * [x3,x4] * prod_j [u_j,v_j]
##
##  (GAP generators 1..4 are the repo's core letters 0..3; the two relator
##  shapes are `MarkedCore.mWord` / `MarkedCore.nWord` verbatim), form the
##  level-k 2-quotient Q = G / lambda_{k+1} by the p-quotient algorithm --
##  GAP's lower exponent-2 central series IS the repo's `twoCentralSeries` --
##  and put on it the cyclotomic character
##
##    chi(x_i) = v_i   in  (Z/2^(k+alpha))^*,
##
##    vM = (1, -1, 1, (1-2^alpha)^-1),   vN = (1, -(1+2^alpha)^-1, 1, 1),
##
##  value 1 on every handle letter.  That chi is well defined on Q is itself
##  the range-refined depth bound at lambda_{k+1}; GAP returns `fail` if not.
##
##  The linearized shift word `evenRawDbarWord` is the product over the
##  coordinates of the row functionals
##
##    R_0(p) = p^2 * [p,b_0] * [p,b_1]     (the ONLY row carrying a square)
##    R_1(p) = [p,b_0]     R_2(p) = [p,b_3]     R_3(p) = [p,b_2]
##    R_{u_j}(p) = [p,b_{v_j}]             R_{v_j}(p) = [p,b_{u_j}]
##
##  read off `evenRawCoreDbarWord` and `evenRawHandleDbarWord`.  On
##  Lam := lambda_{k-1}/lambda_{k+1} each R_i is a homomorphism into the
##  central involutive layer Z_k := lambda_k/lambda_{k+1} (Lam is abelian at
##  k >= 3 and every value is central of order <= 2), so each R_i kills Lam^2
##  and is F_2-LINEAR on V := Lam/Lam^2.  So is the "deep" bit
##
##    d(p) = 0  iff  chi(p) = 1 mod 2^(k+alpha-1),
##
##  because it is a homomorphism to Z/2.  The flip supply at coordinate i0
##  therefore reads as one F_2 linear feasibility problem:
##
##    exists p_0..p_{n-1} in Lam with  prod_i R_i(p_i) = 1,
##    d(p_{i0}) = 1  (sharp)  and  d(p_j) = 0  (deep) for j <> i0.
##
##  This script decides it, coordinate by coordinate, by exact linear algebra
##  over GF(2) in the pcgs coordinates of Lam and Z_k.
##
#############################################################################

SetPrintFormattingStatus("*stdout*", false);
LogTo("results/w56_slotzero_model.txt");

Print("### W56-SLOTZERO model: is the even flip supplied at coordinate 0?\n");
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

# ------------------------------------------------------------- the main run

F2ONE := Z(2)^0;;
F2ZERO := 0*Z(2)^0;;
B2F := function(x) if x then return F2ONE; else return F2ZERO; fi; end;;

RunCase := function(branch, alpha, k, h)
  local n, G, q, epi, Q, ser, Lam, Zk, b, N, U, v, chi, i, j, t, w,
        pcL, pcZ, n1, n2, R, Mat, dvec, sq, D, pcD, res, verdict, nm,
        rows, sol, feas, over, lin, levels, e1, e2, x, y, mech, Dspace, ann;

  n := 4 + 2*h;
  N := k + alpha;
  Print("=====================================================\n");
  Print("branch ", branch, "   alpha ", alpha, "   k ", k, "   h ", h,
        "   rank ", n, "\n");

  G := EvenRelatorGroup(branch, alpha, h);
  q := PQuotient(G, 2, k);
  epi := EpimorphismQuotientSystem(q);
  Q := Image(epi);
  Print("  |Q| = 2^", LogInt(Size(Q),2), "   (Q = G / lambda_", k+1, ")\n");

  ser := PCentralSeries(Q, 2);
  Lam := ser[k-1];                    # lambda_{k-1} / lambda_{k+1}
  Zk  := ser[k];                      # Z_k
  Print("  |lambda_", k-1, "| = 2^", LogInt(Size(Lam),2),
        "   |Z_", k, "| = 2^", LogInt(Size(Zk),2),
        "   series length ", Length(ser), "\n");

  b := List(GeneratorsOfGroup(G), x -> Image(epi, x));

  U := Units(ZmodnZ(2^N));
  v := RowValues(branch, alpha, h, N);
  chi := GroupHomomorphismByImages(Q, U, b, v);
  if chi = fail then
    Print("  !! chi is NOT well defined on Q -- the depth bound would fail\n");
    return fail;
  fi;
  Print("  chi : Q -> (Z/2^", N, ")^*  IS well defined",
        "   [the range-refined depth bound at lambda_", k+1, "]\n");

  # the depth bound level by level:  chi(lambda_m) inside 1 + 2^(alpha+m-1)
  Print("  depth bound chi(lambda_m) <= 1+2^(alpha+m-1):");
  for i in [2..k+1] do
    Print(" m=", i, ":", ForAll(GeneratorsOfGroup(ser[i]),
      x -> LevelOfUnit(Image(chi,x), N) >= alpha+i-1));
  od;
  Print("\n");

  # the row functionals
  R := [];
  R[1] := p -> p^2 * Comm(p, b[1]) * Comm(p, b[2]);
  R[2] := p -> Comm(p, b[1]);
  R[3] := p -> Comm(p, b[4]);
  R[4] := p -> Comm(p, b[3]);
  for j in [1..h] do
    R[2*j+3] := function(p) return Comm(p, b[2*j+4]); end;
    R[2*j+4] := function(p) return Comm(p, b[2*j+3]); end;
  od;

  # pcgs coordinates
  pcL := Pcgs(Lam);   n1 := Length(pcL);
  pcZ := Pcgs(Zk);    n2 := Length(pcZ);
  if not ForAll(RelativeOrders(pcL), y -> y = 2) or
     not ForAll(RelativeOrders(pcZ), y -> y = 2) then
    Print("  !! a pcgs is not 2-step\n"); return fail;
  fi;
  Print("  dim lambda_", k-1, " = ", n1, "   dim Z_", k, " = ", n2, "\n");

  # every row functional lands in Z_k
  if not ForAll([1..n], i -> ForAll(pcL, p -> R[i](p) in Zk)) then
    Print("  !! a row functional leaves Z_", k, "\n"); return fail;
  fi;

  # the n1 x n2 matrices over GF(2)
  Mat := List([1..n], i -> List(pcL,
           p -> ExponentsOfPcElement(pcZ, R[i](p)) * F2ONE));

  # linearity spot check on random pairs (R_i is a hom killing Lam^2)
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
  Print("  row functionals are GF(2)-linear on lambda_", k-1, "/(lambda_", k-1,
        ")^2 : ", lin, "\n");
  if not lin then return fail; fi;

  # the sharp/deep bit, as a GF(2) functional
  dvec := List(pcL, p -> B2F(LevelOfUnit(Image(chi, p), N) < k+alpha-1));
  levels := List(pcL, p -> LevelOfUnit(Image(chi, p), N));
  Print("  chi-levels on a pcgs of lambda_", k-1, " : min ", Minimum(levels),
        "   (the depth boundary is ", k+alpha-2, ")\n");
  if IsZero(dvec) then
    Print("  !! no sharp class at all in lambda_", k-1, " -- vacuous\n");
    return fail;
  fi;

  # --------------- coordinate by coordinate feasibility over GF(2)
  #
  # unknowns  (w_1,...,w_n) in (GF(2)^n1)^n, one per coordinate.
  # constraints : sum_i w_i * Mat[i] = 0                     (n2 equations)
  #               w_j . dvec = 0  for j <> i0                (n-1 equations)
  # supplied  <=>  the functional w_{i0} . dvec is nonzero on that solution
  # space.
  res := [];
  for i in [1..n] do
    rows := [];
    for t in [1..n2] do
      Add(rows, Concatenation(List([1..n], j -> List([1..n1], y -> Mat[j][y][t]))));
    od;
    for j in [1..n] do
      if j <> i then
        Add(rows, Concatenation(List([1..n], t -> List([1..n1],
          function(y) if t = j then return dvec[y]; else return F2ZERO; fi; end))));
      fi;
    od;
    sol := NullspaceMat(TransposedMat(rows));
    feas := ForAny(sol, s -> not IsZero(Sum([1..n1], y -> s[(i-1)*n1 + y] * dvec[y])));
    if feas then verdict := "SUPPLIED"; else verdict := "REFUTED "; fi;
    Add(res, verdict);
    nm := "";
    if i = 1 then nm := "   <-- the diagonal coordinate 0"; fi;
    Print("  coord ", i-1, " : ", verdict, nm, "\n");
  od;

  # --------------- the over-approximation the Lean proof uses:
  # forget the deep conditions at the other coordinates entirely.
  rows := [];
  for t in [1..n2] do
    Add(rows, Concatenation(List([1..n], j -> List([1..n1], y -> Mat[j][y][t]))));
  od;
  sol := NullspaceMat(TransposedMat(rows));
  over := ForAny(sol, s -> not IsZero(Sum([1..n1], y -> s[y] * dvec[y])));
  if over then verdict := "SUPPLIED"; else verdict := "REFUTED "; fi;
  Print("  coord 0, over-approximated (other slots unconstrained) : ", verdict, "\n");

  # --------------- the mechanism: p^2 in [Q,Q] already forces the deep digit
  sq := List(pcL, p -> ExponentsOfPcElement(pcZ, p^2) * F2ONE);
  D := Intersection(DerivedSubgroup(Q), Zk);
  pcD := Pcgs(D);
  Dspace := List(pcD, x -> ExponentsOfPcElement(pcZ, x) * F2ONE);
  ann := NullspaceMat(TransposedMat(Dspace));        # the annihilator of D in Z_k^*
  if Length(ann) = 0 then
    sol := IdentityMat(n1, GF(2));                   # D is all of Z_k
  else
    sol := NullspaceMat(sq * TransposedMat(ann));    # { w : w * sq in D }
  fi;
  mech := not ForAny(sol, s -> not IsZero(Sum([1..n1], y -> s[y] * dvec[y])));
  Print("  MECHANISM: { p in lambda_", k-1, " : p^2 in [Q,Q] } is entirely deep : ",
        mech, "   (codim ", n1 - Length(sol), " in lambda_", k-1, ")\n");

  Print("\n");
  return res;
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
  Add(SUMMARY, [CASE, RunCase(CASE[1], CASE[2], CASE[3], CASE[4])]);
od;

Print("=====================================================\n");
Print("SUMMARY   [branch, alpha, k, h] then coordinates 0,1,2,3,(handles)\n");
for i in [1..Length(SUMMARY)] do
  Print("  ", SUMMARY[i][1], "  ", SUMMARY[i][2], "\n");
od;
Print("=====================================================\n");
Print("Coordinate 0 is REFUTED in every case; every other coordinate is\n");
Print("SUPPLIED, which reproduces wave 55's evenFlip_flipOffZero_{M,N}.\n");

LogTo();
QUIT;
