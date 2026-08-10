// W56-ALPHA2 supplement: name the seven quadratic 2-adic fields and give each one's alpha.
//
// Each quadratic extension of Q_2 is Q_2(sqrt d) for exactly one nontrivial square class d in
// Q_2^*/(Q_2^*)^2 = {1,-1,2,-2,5,-5,10,-10}.  We compute, for each d:
//   * whether i lies in the field  (out of class when it does),
//   * whether K(i)/K is ramified   (the even route's binder),
//   * whether sqrt 2 lies in it    (the lane's structural criterion for alpha >= 3),
//   * the exact image H = range chi inside (Z/2^5)^*, hence the branch and alpha.
//
// H is computed exactly: H = { a : sigma_a fixes K cap Q_2(mu_32) }, obtained by intersecting
// every subgroup of (Z/32)^* whose fixed field embeds into K.  [Z_2^*:H] divides 2, so H
// contains (Z_2^*)^2 = 1+8Z_2 and is determined mod 32.

SetQuitOnError(true);

Q := pAdicField(2, 200);
Zx<x> := PolynomialRing(Integers());
n := 5;
m := 2^n;

function GenSub(gens, mm)
  S := {Integers() | 1};
  repeat
    old := S;
    S := S join {(a*b) mod mm : a in S, b in gens};
  until S eq old;
  return S;
end function;

subs := {};
for a in [b : b in [1 .. m-1] | IsOdd(b)] do
  for c in [b : b in [1 .. m-1] | IsOdd(b)] do
    Include(~subs, GenSub([a, c], m));
  end for;
end for;
subs := Setseq(subs);

function PeriodPoly(Hp)
  C<zt> := CyclotomicField(m);
  idx := (2^(n-1)) div #Hp;
  for tries in [1 .. 60] do
    c := [Random(0, 30) : j in [0 .. m - 1]];
    eta := &+[ &+[c[j+1] * zt^((a*j) mod m) : j in [0 .. m - 1]] : a in Hp];
    mp := MinimalPolynomial(eta);
    if Degree(mp) eq idx then return Zx ! mp; end if;
  end for;
  error "no primitive element";
end function;

polys := [PeriodPoly(Hp) : Hp in subs];

printf "%-10o %-8o %-9o %-8o %-8o %-6o %-10o\n",
  "K", "i in K", "K(i)/K", "sqrt2", "branch", "alpha", "in class";
// Eisenstein / inertial models of the seven quadratic extensions, one per square class.
//   d = -1 : 1+i is a uniformizer, (1+i)^2 - 2(1+i) + 2 = 0
//   d = -5 : 1+sqrt(-5) has norm 6, so x^2 - 2x + 6
//   d = 5  : unramified, x^2 + x + 1
models := [ <-1, x^2 - 2*x + 2>, <2, x^2 - 2>, <-2, x^2 + 2>, <5, x^2 + x + 1>,
            <-5, x^2 - 2*x + 6>, <10, x^2 - 10>, <-10, x^2 + 10> ];
for md in models do
  d := md[1];
  K := ext<Q | md[2]>;
  Ky<y> := PolynomialRing(K);
  assert HasRoot(y^2 - d, K);
  hasI  := HasRoot(y^2 + 1, K);
  hasS2 := HasRoot(y^2 - 2, K);
  if hasI then
    kiram := "n/a";
  else
    U := UnramifiedExtension(K, 2);
    Uz<z> := PolynomialRing(U);
    kiram := HasRoot(z^2 + 1, U) select "unram" else "ram";
  end if;
  H := {a : a in [1 .. m - 1] | IsOdd(a)};
  for t in [1 .. #subs] do
    if HasRoot(Ky ! polys[t], K) then H := H meet subs[t]; end if;
  end for;
  if (m - 1) in H then
    b := n;
    for hh in H do
      if hh ne 1 and (hh mod 4) eq 1 then
        v := Valuation(hh - 1, 2); if v lt b then b := v; end if;
      end if;
    end for;
    br := "M"; al := Maximum(2, b);
  else
    a := n; ok := false;
    for hh in H do
      if (hh mod 4) eq 3 then
        ok := true; v := Valuation(hh + 1, 2); if v lt a then a := v; end if;
      end if;
    end for;
    if ok then br := "N"; al := a; else br := "-"; al := 0; end if;
  end if;
  inclass := (not hasI) and (kiram eq "ram");
  printf "Q2(rt%-5o %-8o %-9o %-8o %-8o %-6o %-10o\n",
    IntegerToString(d) cat ")", hasI, kiram, hasS2, br, al, inclass;
  printf "     H mod 32 = %o\n", Sort(Setseq(H));
end for;

printf "\ndone\n";
quit;
