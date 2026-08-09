/*  W53-CONTAIN -- symbolic validation of the class-four translation identity for the
 *  FIVE-slot gamma3-dressing (the K-dressing at the stage the class-four solve consumes),
 *  and derivation of the tenth (j-)row of the class-four witness selLiftWit.
 *
 *      magma -b w53_shift.m            (writes results/w53shift.txt)
 *
 *  Everything here is EXACT symbolic polynomial arithmetic in the unitriangular group
 *  U5(R) over a polynomial ring, matching GQ2/Dyadic/SqCore/GradedFour.lean coordinate
 *  by coordinate (mul, inv as committed).  Tests:
 *
 *    T0  group sanity: p * p^-1 = 1 symbolically.
 *    T1  the translation identity for the all-slot gamma3-dressing at h = 1 and h = 2:
 *          R(m.z) = R(m) * G,   G = <0,..,0, -4 z1h + 2 z2h, -4 z1i + 2 z2i,
 *                                     -4 z1j + 2 z2j + Phi(m, z)>,
 *        with Phi the conjectured class-four graded Fox pairing form (slot (h,i)-parts
 *        against the PERMUTED letters' outermost abelian columns (d, a); handles
 *        crosswise; the x0-slot letter the integer combination -s + 10 x - 8 y).
 *        The conjectured integer coefficients are printed against the true ones.
 *    T2  the core-word identity at fixed slots (the exact Lean statement of the
 *        core lemma sqWord_mul_gaThree): sqWord(s z0, x z1, y z2) = sqWord(s,x,y) * G0.
 *    T3  the witness rows: substitute selLiftWit into R(m) over Z8[A..W2], confirm the
 *        committed rows a..i modulo the four parity rows, and print the raw j-row plus
 *        its reduction against the parity-row ideal (the class-four gate's closed form).
 *        NOTE the f- and h-row residuals 4*D*T*(T+S)*(...): the PLAIN polynomial ideal
 *        misses parity (Frobenius) consequences of the rows; those residuals vanish mod 8
 *        because he's parity forces D*T*(T+S) even, exactly the parity witnesses the
 *        committed Lean proofs consume (selCon_ts_even and friends).  The j-row's honest
 *        closed form and its certificate live in w53_gate.m / the Lean file.
 */

SetColumns(0); SetAutoColumns(false);
OUT := "results/w53shift.txt"; System("rm -f " cat OUT);
procedure Say(s) PrintFile(OUT, s); print s; end procedure;

/* ---------- U5 arithmetic over any commutative ring, committed coordinates ---------- */

function U5Mul(p, q)
  return [ p[1]+q[1], p[2]+q[2], p[3]+q[3], p[4]+q[4],
           p[5]+q[5]+p[1]*q[2], p[6]+q[6]+p[2]*q[3], p[7]+q[7]+p[3]*q[4],
           p[8]+q[8]+p[1]*q[6]+p[5]*q[3], p[9]+q[9]+p[2]*q[7]+p[6]*q[4],
           p[10]+q[10]+p[1]*q[9]+p[5]*q[7]+p[8]*q[4] ];
end function;

function U5Inv(p)
  return [ -p[1], -p[2], -p[3], -p[4],
           p[1]*p[2]-p[5], p[2]*p[3]-p[6], p[3]*p[4]-p[7],
           -(p[1]*p[2]*p[3]) + p[1]*p[6] + p[3]*p[5] - p[8],
           -(p[2]*p[3]*p[4]) + p[2]*p[7] + p[4]*p[6] - p[9],
           p[1]*p[2]*p[3]*p[4] - p[1]*p[2]*p[7] - p[1]*p[4]*p[6] + p[1]*p[9]
             - p[3]*p[4]*p[5] + p[4]*p[8] + p[5]*p[7] - p[10] ];
end function;

function U5One(Rng) return [ Rng!0 : k in [1..10] ]; end function;
function U5Conj(x, g) return U5Mul(U5Inv(g), U5Mul(x, g)); end function;
function U5Comm(x, y) return U5Mul(U5Inv(x), U5Mul(U5Inv(y), U5Mul(x, y))); end function;

function SqWord(s, x, y)
  x3 := U5Mul(x, U5Mul(x, x));
  return U5Mul(U5Mul(U5Mul(U5Inv(U5Conj(x, s)), U5Inv(x3)), U5Mul(y, y)),
               U5Comm(y, U5Conj(y, s)));
end function;

function RelWord(s, x, y, hu, hv)   // hu, hv: sequences of handle letters
  w := SqWord(s, x, y);
  for k in [1..#hu] do w := U5Mul(w, U5Comm(hu[k], hv[k])); end for;
  return w;
end function;

/* ---------- T0/T1/T2: generic ring, h = 2 with fully symbolic slots ---------- */

// 7 slots x 10 coords for m; 7 slots x 3 gamma3-coords for z
nm := 70; nz := 21;
Rg := PolynomialRing(Integers(), nm + nz);
mv := [ [ Rg.(10*(sl-1) + k) : k in [1..10] ] : sl in [1..7] ];
zv := [ ]; // gamma3 elements: only h, i, j nonzero
for sl in [1..7] do
  base := nm + 3*(sl-1);
  z := [ Rg!0 : k in [1..10] ];
  z[8] := Rg.(base+1); z[9] := Rg.(base+2); z[10] := Rg.(base+3);
  Append(~zv, z);
end for;

s := mv[1]; x := mv[2]; y := mv[3]; u1 := mv[4]; v1 := mv[5]; u2 := mv[6]; v2 := mv[7];
z0 := zv[1]; z1 := zv[2]; z2 := zv[3]; zu1 := zv[4]; zv1 := zv[5]; zu2 := zv[6]; zv2 := zv[7];

p := mv[1];
t0 := U5Mul(p, U5Inv(p));
Say("T0 inv sanity (all zero): " cat Sprint({* t : t in t0 *} eq {* Rg!0^^10 *}));

// conjectured Phi: slot (h,i) against permuted letter (d, a); x0-slot letter -s+10x-8y
function PairHI(z, letd, leta)  return letd*z[8] - leta*z[9]; end function;

PhiCore := PairHI(z0, x[4], x[1])
  + PairHI(z1, -s[4] + 10*x[4] - 8*y[4], -s[1] + 10*x[1] - 8*y[1])
  + PairHI(z2, y[4], y[1]);
PhiHand := (PairHI(zu1, v1[4], v1[1]) + (u1[1]*zv1[9] - u1[4]*zv1[8]))
  + (PairHI(zu2, v2[4], v2[1]) + (u2[1]*zv2[9] - u2[4]*zv2[8]));
Phi := PhiCore + PhiHand;

G := [ Rg!0 : k in [1..10] ];
G[8]  := -4*z1[8] + 2*z2[8];
G[9]  := -4*z1[9] + 2*z2[9];
G[10] := -4*z1[10] + 2*z2[10] + Phi;

R0 := RelWord(s, x, y, [u1, u2], [v1, v2]);
Rd := RelWord(U5Mul(s, z0), U5Mul(x, z1), U5Mul(y, z2),
              [U5Mul(u1, zu1), U5Mul(u2, zu2)], [U5Mul(v1, zv1), U5Mul(v2, zv2)]);
RHS := U5Mul(R0, G);
rowdif := [ Rd[k] - RHS[k] : k in [1..10] ];
Say("T1 translation identity at h = 2, row differences (want ten zeros):");
for k in [1..10] do
  if rowdif[k] eq 0 then Say(Sprintf("  row %o: 0", k));
  else Say(Sprintf("  row %o: NONZERO  %o", k, rowdif[k])); end if;
end for;

// h = 1 instance too (drop the second handle)
R0a := RelWord(s, x, y, [u1], [v1]);
Rda := RelWord(U5Mul(s, z0), U5Mul(x, z1), U5Mul(y, z2), [U5Mul(u1, zu1)], [U5Mul(v1, zv1)]);
Phi1 := PhiCore + (PairHI(zu1, v1[4], v1[1]) + (u1[1]*zv1[9] - u1[4]*zv1[8]));
G1 := [ Rg!0 : k in [1..10] ];
G1[8] := G[8]; G1[9] := G[9]; G1[10] := -4*z1[10] + 2*z2[10] + Phi1;
RHSa := U5Mul(R0a, G1);
Say("T1 at h = 1 (want ten zeros): " cat
  Sprint(&and[ Rda[k] - RHSa[k] eq 0 : k in [1..10] ]));

// T2: the core-word identity at fixed slots (the Lean core lemma verbatim)
G0 := [ Rg!0 : k in [1..10] ];
G0[8] := -4*z1[8] + 2*z2[8];
G0[9] := -4*z1[9] + 2*z2[9];
G0[10] := -4*z1[10] + 2*z2[10] + PhiCore;
W0 := SqWord(s, x, y);
Wd := SqWord(U5Mul(s, z0), U5Mul(x, z1), U5Mul(y, z2));
Say("T2 core identity at fixed slots (want ten zeros): " cat
  Sprint(&and[ Wd[k] - U5Mul(W0, G0)[k] eq 0 : k in [1..10] ]));

/* If T1/T2 fail, print the true x0-slot letter coefficients by solving linearly:
   the difference is linear in z1h, z1i; extract them. */
if not &and[ Wd[k] - U5Mul(W0, G0)[k] eq 0 : k in [1..10] ] then
  d10 := Wd[10] - U5Mul(W0, G0)[10];
  Say("T2 j-row difference (to correct the conjecture):");
  Say(Sprint(d10));
end if;

/* ---------- T3: the witness rows over Z8[A..W2] ---------- */

R8<A,B,C,D,E,F,T,S,P,Q,Rv,W2> := PolynomialRing(Integers(8), 12);
sW := [ R8!0, 1, 0, 0,  0, 0, 0,  0, 0, 0 ];
xW := [ B*T - A*S, 0, D*T - C*S, F*T - E*S,  -2*T*S*B, S*T*C + T*S*D, 0,  0, 0, 0 ];
yW := [ R8!0, 0, 0, 0,  P, Q, Rv,  -(A+B)*Q, 0, 0 ];
uW := [ A, 0, C, E,  0, -T*C, 0,  0, 0, 0 ];
vW := [ B, 0, D, F,  -B*S, 0, 0,  0, 0, 0 ];

RW := RelWord(sW, xW, yW, [uW], [vW]);

hd := 2*P + (A*S - B*T);
he := 2*Q + (T*D - S*C);
hg := 2*Rv + (C*F - D*E);
hb := 2*W2 + (E*S - F*T);
I8 := ideal< R8 | hd, he, hg, hb >;
GB := GroebnerBasis(I8);

committed := [ R8!0, 0, 0, 0, 0, 0, 0,
  4*(P*Q) - 2*((A+B)*Q) + B*C*(T+S),
  2*(2*(S*T*((C+D)*W2))) - C*F*T,
  RW[10] ];  // row 10 checked below on its own

Say("T3 witness rows a..i against committed forms, modulo the parity-row ideal:");
names := ["a","b","c","d","e","f","g","h","i"];
for k in [1..9] do
  nf := NormalForm(RW[k] - committed[k], I8);
  Say(Sprintf("  row %o: %o", names[k], nf eq 0 select "OK" else "MISMATCH " cat Sprint(nf)));
end for;

Say("T3 raw j-row (over Z8[A..W2], no reduction):");
Say(Sprint(RW[10]));
Say("T3 j-row normal form modulo the parity rows:");
Say(Sprint(NormalForm(RW[10], I8)));
Say("done");
quit;
