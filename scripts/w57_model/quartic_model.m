// W57-MODEL.  Certify the field of the lane's N-branch model.
//
// The wave-56 census (scripts/w56_alpha2/) found exactly ONE in-class field of branch N with
// branch depth alpha >= 3 among the 113 in-class entries of degrees 1, 2, 3, 4, 6: one
// totally ramified quartic (degree-4 entry 43, e = 4, f = 1, sqrt2 in L, N, alpha = 3).  It
// names no polynomial.  This script names it and certifies every claim the Lean model makes
// about it, plus the two claims the Lean model cannot prove and therefore carries.
//
// THE FIELD.  K = Q_2[x]/(x^4 + 4x^2 + 2), Eisenstein at 2, hence totally ramified of degree 4.
// Its root is beta = zeta_16 - zeta_16^{-1}: indeed beta^2 = zeta_8 + zeta_8^{-1} - 2 = sqrt2 - 2,
// so (beta^2 + 2)^2 = 2 and beta^4 + 4 beta^2 + 2 = 0.  K is therefore the quartic subfield of
// Q_2(zeta_16) fixed by sigma_7, and range chi = {u : u = 1 or 7 mod 16} = imChiN 3.
//
// WHAT IS CHECKED
//   (1) degree 4, e = 4, f = 1;
//   (2) i notin K and K(i)/K ramified, i.e. K is in the even route's class;
//   (3) sqrt 2 in K, and specifically that beta^2 + 2 is a square root of 2  (this is the exact
//       statement `evenRouteModel_beta_sq_add_two_sq` proves in Lean);
//   (4) H = range chi computed exactly by the wave-56 method, then compared to imChiN 3 read
//       off its own definition  imChiN alpha = {u : u = 1 or nUnit alpha mod 2^(alpha+1)},
//       nUnit alpha = -(1 + 2^alpha)^{-1};
//   (5) branch N and alpha = 3 by the wave-56 extraction;
//   (6) the class-field-theory cross-check: unit parts of actual norms generate H;
//   (7) uniqueness: over all 63 quartics of Magma's AllExtensions, exactly one is in class with
//       branch N and alpha >= 3, and it is isomorphic to K.  So the lane's field is the census's
//       degree-4 entry 43 and is the SMALLEST N-branch field of depth >= 3 (a quadratic cannot
//       be one: [Z_2^* : imChiN alpha] = 2^(alpha-1) >= 4 for alpha >= 3, and that index is the
//       degree of K cap Q_2(mu_{2^oo}), which divides [K:Q_2]).

SetQuitOnError(true);

PREC := 200;
Q := pAdicField(2, PREC);
Zx<x> := PolynomialRing(Integers());
n := 5;                       // H is determined mod 2^5 (index divides 4, so H >= 1+16Z_2)
m := 2^n;

function GenSub(gens, mm)
  S := {Integers() | 1};
  repeat
    old := S;
    S := S join {(a*b) mod mm : a in S, b in gens};
  until S eq old;
  return S;
end function;

function AllSubgroups(nn)
  mm := 2^nn;
  U := [a : a in [1 .. mm - 1] | IsOdd(a)];
  subs := {};
  for a in U do
    for b in U do
      Include(~subs, GenSub([a, b], mm));
    end for;
  end for;
  return subs;
end function;

function PeriodPoly(Hp, nn)
  mm := 2^nn;
  C<zt> := CyclotomicField(mm);
  idx := (2^(nn-1)) div #Hp;
  for tries in [1 .. 60] do
    c := [Random(0, 30) : j in [0 .. mm - 1]];
    eta := &+[ &+[c[j+1] * zt^((a*j) mod mm) : j in [0 .. mm - 1]] : a in Hp];
    mp := MinimalPolynomial(eta);
    if Degree(mp) eq idx then return Zx ! mp; end if;
  end for;
  error "PeriodPoly: no primitive element found";
end function;

function AlphaOf(H, nn)
  mm := 2^nn;
  if (mm - 1) in H then
    b := nn;
    for h in H do
      if h ne 1 and (h mod 4) eq 1 then
        v := Valuation(h - 1, 2); if v lt b then b := v; end if;
      end if;
    end for;
    return "M", Maximum(2, b);
  else
    a := nn; ok := false;
    for h in H do
      if (h mod 4) eq 3 then
        ok := true; v := Valuation(h + 1, 2); if v lt a then a := v; end if;
      end if;
    end for;
    if not ok then return "*", 0; end if;
    return "N", a;
  end if;
end function;

subs := Setseq(AllSubgroups(n));
polys := [PeriodPoly(Hp, n) : Hp in subs];

function RangeChi(L)
  Ly<y> := PolynomialRing(L);
  H := {a : a in [1 .. m - 1] | IsOdd(a)};
  for t in [1 .. #subs] do
    if HasRoot(Ly ! polys[t], L) then H := H meet subs[t]; end if;
  end for;
  return H;
end function;

// imChiN alpha, read off the Lean definition, as residues mod 2^n.
function ImChiN(alpha)
  nu := Integers()!(-(Integers(m)!(1 + 2^alpha))^(-1));
  return {a : a in [1 .. m - 1] | IsOdd(a) and
            ((a - 1) mod 2^(alpha+1) eq 0 or (a - nu) mod 2^(alpha+1) eq 0)};
end function;

printf "=========== W57-MODEL : the N-branch model field ===========\n\n";

f4 := x^4 + 4*x^2 + 2;
printf "defining polynomial : %o\n", f4;
cf := Coefficients(f4);              // constant term first
eis := (cf[5] eq 1) and &and[IsEven(cf[i]) : i in [1 .. 4]] and (cf[1] mod 4 ne 0);
printf "coefficients (const first) : %o\n", cf;
printf "Eisenstein at 2     : %o\n", eis;
assert eis;

K := ext<Q | f4>;
Ky<y> := PolynomialRing(K);
beta := K.1;

printf "\n(1) degree / ramification\n";
printf "    [K:Q_2]              = %o\n", Degree(K, Q);
printf "    e(K/Q_2)             = %o\n", RamificationIndex(K);
printf "    f(K/Q_2)             = %o\n", InertiaDegree(K);
assert Degree(K, Q) eq 4 and RamificationIndex(K) eq 4 and InertiaDegree(K) eq 1;

printf "\n(2) in class?\n";
hasI := HasRoot(y^2 + 1, K);
U := UnramifiedExtension(K, 2);
Uz<z> := PolynomialRing(U);
kiram := HasRoot(z^2 + 1, U) select "unram" else "ram";
printf "    i in K               = %o\n", hasI;
printf "    K(i)/K               = %o\n", kiram;
assert (not hasI) and kiram eq "ram";
printf "    in class             = true\n";

printf "\n(3) the structural criterion  alpha >= 3  <=>  sqrt2 in K\n";
d0 := (beta^2 + 2)^2 - 2;
printf "    sqrt2 in K           = %o\n", HasRoot(y^2 - 2, K);
printf "    (beta^2+2)^2 - 2     = %o  (weakly zero to precision %o)\n", IsWeaklyZero(d0), PREC;
assert HasRoot(y^2 - 2, K) and IsWeaklyZero(d0);

printf "\n(4)(5) the range identity\n";
H := RangeChi(K);
br, al := AlphaOf(H, n);
printf "    H mod 32             = %o\n", Sort(Setseq(H));
printf "    imChiN 3 mod 32      = %o\n", Sort(Setseq(ImChiN(3)));
printf "    H = imChiN 3         = %o\n", H eq ImChiN(3);
printf "    branch               = %o\n", br;
printf "    alpha                = %o\n", al;
assert H eq ImChiN(3) and br eq "N" and al eq 3;
for aa in [2 .. 4] do
  if aa ne 3 then
    printf "    H = imChiN %o         = %o\n", aa, H eq ImChiN(aa);
    assert H ne ImChiN(aa);
  end if;
end for;

printf "\n(6) class field theory cross-check (unit parts of actual norms)\n";
gens := [Integers() | ];
piK := UniformizingElement(K);
NB := Norm(piK, Q);
Append(~gens, Integers()!(Integers(m)!(Integers()!(NB / 2^Valuation(NB)))));
bas := [K.1^j : j in [0 .. 3]];
for t in [1 .. 400] do
  u := &+[Random(0, m*8) * bas[j] : j in [1 .. #bas]];
  if Valuation(u) ne 0 then continue; end if;
  Nu := Norm(u, Q);
  Append(~gens, Integers()!(Integers(m)!(Integers()!(Nu / 2^Valuation(Nu)))));
end for;
S := GenSub(gens, m);
printf "    <unit parts of norms> = %o\n", Sort(Setseq(S));
printf "    equals H              = %o\n", S eq H;
assert S eq H;

printf "\n(7) uniqueness among the quartics\n";
exts := [FieldOfFractions(R) : R in AllExtensions(Q, 4)];
printf "    quartics enumerated   = %o\n", #exts;
hits := [];
idx := 0;
for L in exts do
  idx := idx + 1;
  Ly2<y2> := PolynomialRing(L);
  hI := HasRoot(y2^2 + 1, L);
  if hI then continue; end if;
  UU := UnramifiedExtension(L, 2);
  Uz2<z2> := PolynomialRing(UU);
  if HasRoot(z2^2 + 1, UU) then continue; end if;   // K(i)/K unramified : out of class
  HL := RangeChi(L);
  brL, alL := AlphaOf(HL, n);
  if brL eq "N" and alL ge 3 then
    Append(~hits, <idx, brL, alL, DefiningPolynomial(L)>);
  end if;
end for;
printf "    in-class quartics with branch N and alpha >= 3 : %o\n", #hits;
for hh in hits do
  printf "      census index %o : branch %o, alpha %o, defining poly %o\n", hh[1], hh[2], hh[3], hh[4];
  L := FieldOfFractions(AllExtensions(Q, 4)[hh[1]]);
  Lw<w> := PolynomialRing(L);
  printf "      x^4+4x^2+2 has a root in it : %o\n", HasRoot(Lw ! f4, L);
  assert HasRoot(Lw ! f4, L);
end for;
assert #hits eq 1;

printf "\nALL ASSERTIONS PASSED\n";
printf "done\n";
quit;
