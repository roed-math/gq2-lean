/*  W54-GAMMA2 -- the exact class-four defect of a FIVE-slot gamma2 dressing of the relator.
 *
 *      magma -b w54_shift.m            (writes results/w54shift.txt)
 *
 *  Exact symbolic polynomial arithmetic in U5(R) over Z[m, z], matching
 *  GQ2/Dyadic/SqCore/GradedFour.lean coordinate by coordinate (mul, inv as committed).
 *  A gamma2 dressing has a = b = c = d = 0 and (e, f, g, h, i, j) free; unlike the gamma3
 *  dressing of W53-CONTAIN it moves the class-two rows, the class-three rows, and it
 *  contributes GENUINELY QUADRATIC terms to the class-four row.
 *
 *  The conjectured closed form, with
 *      pair4(z, L) = z.h*L.d - z.i*L.a + z.e*L.g - z.g*L.e + z.g*L.a*L.b - z.f*L.a*L.d
 *                  ( = u5Comm4(z, L), the class-four commutator form, for z in gamma2 )
 *      pair3L(z, L) = z.e*L.c - z.f*L.a          pair3R(z, L) = z.f*L.d - z.g*L.b
 *      sigma* = 10*x - s - 8*y   (the x0-slot Fox letter, an integer combination of columns)
 *  is, for the CORE word W = sqWord(s, x, y) and G0 = W^-1 * sqWord(s z0, x z1, y z2):
 *
 *      G0.e = -4 z1.e + 2 z2.e,  G0.f = -4 z1.f + 2 z2.f,  G0.g = -4 z1.g + 2 z2.g
 *      G0.h = -4 z1.h + 2 z2.h + pair3L(z0, x) + pair3L(z1, sigma*) + pair3L(z2, y)
 *      G0.i = -4 z1.i + 2 z2.i + pair3R(z0, x) + pair3R(z1, sigma*) + pair3R(z2, y)
 *      G0.j = -4 z1.j + 2 z2.j + pair4(z0, x) + pair4(z1, sigma*) + pair4(z2, y)
 *             + corr(m, z)                                  [linear in z, printed below]
 *             + (z0.e z1.g - z0.g z1.e) + 10 z1.e z1.g - 8 z1.e z2.g + z2.e z2.g
 *
 *  and for one HANDLE pair, gam = comm(u,v)^-1 * comm(u zu, v zv):
 *      gam.a .. gam.g = 0
 *      gam.h = pair3L(zu, v) - pair3L(zv, u)
 *      gam.i = pair3R(zu, v) - pair3R(zv, u)
 *      gam.j = pair4(zu, v) - pair4(zv, u)
 *              - cg*(zu.e + zv.e) + ce*(zu.g + zv.g) + (zu.e zv.g - zu.g zv.e)
 *      with ce = u.a*v.b - u.b*v.a, cg = u.c*v.d - u.d*v.c the commutator's class-two rows.
 *
 *  Tests:
 *    T0  group sanity.
 *    T1  the core block: extract the correction polynomials of the j-row by exact
 *        coefficient reading, print them, and re-assemble: want ten zero rows.
 *    T2  the handle block: want ten zero rows.
 *    T3  the ASSEMBLED relator identity at h = 1 and h = 2:
 *          R(m.z) = R(m) * G,  G = G0 * gamsum * liftC(Hg*G0.e - He*G0.g),
 *        with gamsum the gamma3-element summing the per-handle gam's and (He, Hg) the
 *        handle word's two outer class-two rows: want ten zero rows at both handle counts.
 *    T4  the two class-three rows against the committed class-three shift of GradedVanish
 *        transported through the two U4-quotients toU4L, toU4R: want zero.
 */

SetColumns(0); SetAutoColumns(false);
OUT := "results/w54shift.txt"; System("rm -f " cat OUT);
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

function U5Conj(x, g) return U5Mul(U5Inv(g), U5Mul(x, g)); end function;
function U5Comm(x, y) return U5Mul(U5Inv(x), U5Mul(U5Inv(y), U5Mul(x, y))); end function;

function SqWord(s, x, y)
  x3 := U5Mul(x, U5Mul(x, x));
  return U5Mul(U5Mul(U5Mul(U5Inv(U5Conj(x, s)), U5Inv(x3)), U5Mul(y, y)),
               U5Comm(y, U5Conj(y, s)));
end function;

function RelWord(s, x, y, hu, hv)
  w := SqWord(s, x, y);
  for k in [1..#hu] do w := U5Mul(w, U5Comm(hu[k], hv[k])); end for;
  return w;
end function;

/* ---------- the polynomial ring: 7 frame slots, 7 gamma2 dressings ---------- */

nslot := 7;
Rg := PolynomialRing(Integers(), 10*nslot + 6*nslot);
slotnm := ["s", "x", "y", "u", "v", "p", "q"];   // p,q = the second handle pair
crd := ["a","b","c","d","e","f","g","h","i","j"];
vnames := [];
for sl in [1..nslot] do
  for k in [1..10] do Append(~vnames, slotnm[sl] cat crd[k]); end for;
end for;
for sl in [1..nslot] do
  for k in [5..10] do Append(~vnames, "z" cat slotnm[sl] cat crd[k]); end for;
end for;
AssignNames(~Rg, vnames);

mv := [ [ Rg.(10*(sl-1) + k) : k in [1..10] ] : sl in [1..nslot] ];
zv := [];
for sl in [1..nslot] do
  base := 10*nslot + 6*(sl-1);
  z := [ Rg!0 : k in [1..10] ];
  for k in [1..6] do z[4+k] := Rg.(base+k); end for;
  Append(~zv, z);
end for;

s := mv[1]; x := mv[2]; y := mv[3]; u1 := mv[4]; v1 := mv[5]; u2 := mv[6]; v2 := mv[7];
z0 := zv[1]; z1 := zv[2]; z2 := zv[3]; zu1 := zv[4]; zv1 := zv[5]; zu2 := zv[6]; zv2 := zv[7];

Say("T0 inv sanity (want true): " cat
  Sprint(&and[ U5Mul(mv[1], U5Inv(mv[1]))[k] eq 0 : k in [1..10] ]));

/* ---------- the conjectured pairing forms ---------- */

// L is a 10-tuple of column values (a possibly formal integer combination of letters)
function Pair4(z, L)
  return z[8]*L[4] - z[9]*L[1] + z[5]*L[7] - z[7]*L[5] + z[7]*L[1]*L[2] - z[6]*L[1]*L[4];
end function;
function Pair3L(z, L) return z[5]*L[3] - z[6]*L[1]; end function;
function Pair3R(z, L) return z[6]*L[4] - z[7]*L[2]; end function;

// sigma* = 10*x - s - 8*y, columnwise
sstar := [ 10*x[k] - s[k] - 8*y[k] : k in [1..10] ];

/* ---------- T1 the core block ---------- */

W0 := SqWord(s, x, y);
Wd := SqWord(U5Mul(s, z0), U5Mul(x, z1), U5Mul(y, z2));
G0 := U5Mul(U5Inv(W0), Wd);

coreFrob := [ -4*z1[k] + 2*z2[k] : k in [1..10] ];
coreFox4 := Pair4(z0, x) + Pair4(z1, sstar) + Pair4(z2, y);
coreQuad := (z0[5]*z1[7] - z0[7]*z1[5]) + 10*z1[5]*z1[7] - 8*z1[5]*z2[7] + z2[5]*z2[7];

resid := G0[10] - (coreFrob[10] + coreFox4 + coreQuad);

// extract the coefficient of each class-two dressing variable in the residual
zvarsC := [ <"z0.e", z0[5]>, <"z0.f", z0[6]>, <"z0.g", z0[7]>,
            <"z1.e", z1[5]>, <"z1.f", z1[6]>, <"z1.g", z1[7]>,
            <"z2.e", z2[5]>, <"z2.f", z2[6]>, <"z2.g", z2[7]> ];

function CoeffOf(f, v)
  // coefficient of the degree-1 part in the variable v (f is linear in each z-variable)
  R := Parent(f); out := R!0;
  for k in [1..#Monomials(f)] do
    mo := Monomials(f)[k]; cf := Coefficients(f)[k];
    if Degree(mo, v) eq 1 then out +:= cf * (mo div v); end if;
  end for;
  return out;
end function;

Say("");
Say("T1 core j-row residual after Frobenius + Fox + quadratic, by dressing coordinate:");
rebuilt := Rg!0;
for t in zvarsC do
  cf := CoeffOf(resid, t[2]);
  Say(Sprintf("   corr coefficient of %o :  %o", t[1], cf));
  rebuilt +:= cf * t[2];
end for;
Say("T1 residual minus the rebuilt correction (want 0): " cat Sprint(resid - rebuilt));

coreJ := coreFrob[10] + coreFox4 + coreQuad + rebuilt;
coreRows := [ Rg!0, 0, 0, 0, coreFrob[5], coreFrob[6], coreFrob[7],
  coreFrob[8] + Pair3L(z0, x) + Pair3L(z1, sstar) + Pair3L(z2, y),
  coreFrob[9] + Pair3R(z0, x) + Pair3R(z1, sstar) + Pair3R(z2, y),
  coreJ ];
Say("T1 core block, ten row differences (want ten zeros):");
for k in [1..10] do
  Say(Sprintf("   row %o: %o", crd[k], G0[k] - coreRows[k] eq 0 select "0"
    else "NONZERO " cat Sprint(G0[k] - coreRows[k])));
end for;

/* ---------- T2 the handle block ---------- */

function HandleGam(u, v, zu, zvw)
  ce := u[1]*v[2] - u[2]*v[1];
  cg := u[3]*v[4] - u[4]*v[3];
  gj := Pair4(zu, v) - Pair4(zvw, u)
        - cg*(zu[5] + zvw[5]) + ce*(zu[7] + zvw[7])
        + (zu[5]*zvw[7] - zu[7]*zvw[5]);
  return [ Parent(u[1]) | 0, 0, 0, 0, 0, 0, 0,
           Pair3L(zu, v) - Pair3L(zvw, u),
           Pair3R(zu, v) - Pair3R(zvw, u), gj ];
end function;

C0 := U5Comm(u1, v1);
Cd := U5Comm(U5Mul(u1, zu1), U5Mul(v1, zv1));
GM := U5Mul(U5Inv(C0), Cd);
GMc := HandleGam(u1, v1, zu1, zv1);
Say("");
Say("T2 handle block, ten row differences (want ten zeros):");
for k in [1..10] do
  Say(Sprintf("   row %o: %o", crd[k], GM[k] - GMc[k] eq 0 select "0"
    else "NONZERO " cat Sprint(GM[k] - GMc[k])));
end for;

/* ---------- T3 the assembled relator identity at h = 1 and h = 2 ---------- */

function Assemble(us, vs, zus, zvs)
  // G = coreRows * (product of the handle gam's) * liftC(Hg*G0.e - He*G0.g)
  gam := [ Rg | 0,0,0,0,0,0,0,0,0,0 ];
  He := Rg!0; Hg := Rg!0;
  for k in [1..#us] do
    gk := HandleGam(us[k], vs[k], zus[k], zvs[k]);
    gam := [ gam[t] + gk[t] : t in [1..10] ];       // gamma3 elements add coordinatewise
    He +:= us[k][1]*vs[k][2] - us[k][2]*vs[k][1];
    Hg +:= us[k][3]*vs[k][4] - us[k][4]*vs[k][3];
  end for;
  G := [ coreRows[t] : t in [1..10] ];
  G[8] +:= gam[8]; G[9] +:= gam[9];
  G[10] +:= gam[10] + Hg*coreRows[5] - He*coreRows[7];
  return G;
end function;

for hh in [1, 2] do
  us := hh eq 1 select [u1] else [u1, u2];
  vs := hh eq 1 select [v1] else [v1, v2];
  zus := hh eq 1 select [zu1] else [zu1, zu2];
  zvs := hh eq 1 select [zv1] else [zv1, zv2];
  R0 := RelWord(s, x, y, us, vs);
  Rd := RelWord(U5Mul(s, z0), U5Mul(x, z1), U5Mul(y, z2),
                [ U5Mul(us[k], zus[k]) : k in [1..hh] ],
                [ U5Mul(vs[k], zvs[k]) : k in [1..hh] ]);
  G := Assemble(us, vs, zus, zvs);
  RHS := U5Mul(R0, G);
  Say("");
  Say(Sprintf("T3 assembled identity at h = %o, ten row differences (want ten zeros):", hh));
  for k in [1..10] do
    Say(Sprintf("   row %o: %o", crd[k], Rd[k] - RHS[k] eq 0 select "0"
      else "NONZERO " cat Sprint(Rd[k] - RHS[k])));
  end for;
end for;

/* ---------- T4 the two class-three rows through the committed U4-quotients ---------- */
/*  GradedVanish's committed class-three shift (vanShift), in U4 coordinates
 *  (a,b,c,d,e,f) with dressing coords (d,e); transported by toU4L: U5 (a,b,c,e,f,h),
 *  and by toU4R: U5 (b,c,d,f,g,i).  vanShift is the ADDITIVE change of the relator's
 *  f-row; the multiplicative G-row differs by the U4 cross term (R m).a * G.e, so the
 *  test is stated additively on the relator rows.                                     */

function VanShiftU4(mm, zz, hh)
  // mm, zz: lists of 6-tuples (a,b,c,d,e,f); returns the committed vanShift
  val := -4*zz[2][6] + 2*zz[3][6]
    + (mm[2][3]*zz[1][4] - mm[2][1]*zz[1][5])
    + ((mm[1][1] + 6*mm[2][1])*zz[2][5]
       - (mm[1][3] - 10*mm[2][3] + 8*mm[3][3])*zz[2][4])
    + ((3*mm[3][1] - 8*mm[2][1])*zz[3][5] + mm[3][3]*zz[3][4]);
  for k in [1..hh] do
    iu := 2*k + 2; iv := 2*k + 3;      // slot indices of the k-th handle pair
    val +:= (mm[iv][3]*zz[iu][4] - mm[iv][1]*zz[iu][5])
          + (mm[iu][1]*zz[iv][5] - mm[iu][3]*zz[iv][4]);
  end for;
  return val;
end function;

for hh in [1, 2] do
  slots := hh eq 1 select [1,2,3,4,5] else [1,2,3,4,5,6,7];
  zs := [ zv[t] : t in slots ];  ms := [ mv[t] : t in slots ];
  R0 := RelWord(s, x, y, hh eq 1 select [u1] else [u1,u2],
                         hh eq 1 select [v1] else [v1,v2]);
  Rd := RelWord(U5Mul(s, z0), U5Mul(x, z1), U5Mul(y, z2),
                hh eq 1 select [U5Mul(u1, zu1)] else [U5Mul(u1,zu1), U5Mul(u2,zu2)],
                hh eq 1 select [U5Mul(v1, zv1)] else [U5Mul(v1,zv1), U5Mul(v2,zv2)]);
  mL := [ [ mm[1], mm[2], mm[3], mm[5], mm[6], mm[8] ] : mm in ms ];
  zL := [ [ zz[1], zz[2], zz[3], zz[5], zz[6], zz[8] ] : zz in zs ];
  mR := [ [ mm[2], mm[3], mm[4], mm[6], mm[7], mm[9] ] : mm in ms ];
  zR := [ [ zz[2], zz[3], zz[4], zz[6], zz[7], zz[9] ] : zz in zs ];
  dh := Rd[8] - R0[8] - VanShiftU4(mL, zL, hh);
  di := Rd[9] - R0[9] - VanShiftU4(mR, zR, hh);
  Say("");
  Say(Sprintf("T4 h = %o: h-row against toU4L vanShift (want 0): %o", hh, dh));
  Say(Sprintf("T4 h = %o: i-row against toU4R vanShift (want 0): %o", hh, di));
end for;

Say("");
Say("done");
quit;
