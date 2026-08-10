/*  W54-GAMMA2 -- the three gamma2-level generators in closed form, and the concrete
 *  instances committed in GQ2/Dyadic/SqCore/GradedGammaTwo.lean.
 *
 *      magma -b w54_inst.m             (writes results/w54inst.txt)
 *
 *  (a) the closed form over Z/8[A..R] of the three honest commutators of witness frame
 *      slots that carry the new gamma3-shaped moves:
 *          [sigma, x1],  [x1, U],  [x1, V];
 *  (b) the W53 "provable dead end" corner (A..S) = (0,1,1,1,2,0,2,0), halves (1,3,1):
 *      the witness is a stage-3 survivor with odd residue 5, all eight committed Lam3
 *      pairings are even, and the CUBE of [sigma, x1] on the U-handle slot kills the
 *      relator -- honest group collection;
 *  (c) a second, independent dead-end corner and its kill.
 */
SetColumns(0); SetAutoColumns(false);
OUT := "results/w54inst.txt"; System("rm -f " cat OUT);
procedure Say(s) PrintFile(OUT, s); print s; end procedure;

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
function RelW(m) return U5Mul(SqWord(m[1], m[2], m[3]), U5Comm(m[4], m[5])); end function;

/* ---------- (a) the three generators over Z/8[A..R] ---------- */

R8<A,B,C,D,E,F,T,S,P,Q,Rv> := PolynomialRing(Integers(8), 11);
mW := [ [R8|0,1,0,0, 0,0,0, 0,0,0],
        [B*T-A*S, 0, D*T-C*S, F*T-E*S, -2*T*S*B, S*T*C+T*S*D, 0, 0,0,0],
        [R8|0,0,0,0, P,Q,Rv, -(A+B)*Q, 0,0],
        [A,0,C,E, 0,-T*C,0, 0,0,0],
        [B,0,D,F, -B*S,0,0, 0,0,0] ];
crd := ["a","b","c","d","e","f","g","h","i","j"];
nm := ["sigma","x0","x1","U","V"];
for pr in [<1,3>, <3,4>, <3,5>] do
  c := U5Comm(mW[pr[1]], mW[pr[2]]);
  Say(Sprintf("(a) [%o, %o]:", nm[pr[1]], nm[pr[2]]));
  for k in [1..10] do
    Say(Sprintf("      %o = %o", crd[k], c[k]));
  end for;
end for;

/* ---------- (b), (c) the dead-end corners ---------- */

Z8 := Integers(8);
function Wit(Av, Bv, Cv, Dv, Ev, Fv, Tv, Sv, Pv, Qv, Rvv)
  return [ [Z8|0,1,0,0, 0,0,0, 0,0,0],
           [Bv*Tv-Av*Sv, 0, Dv*Tv-Cv*Sv, Fv*Tv-Ev*Sv, -2*Tv*Sv*Bv,
            Sv*Tv*Cv+Tv*Sv*Dv, 0, 0,0,0],
           [Z8|0,0,0,0, Pv,Qv,Rvv, -(Av+Bv)*Qv, 0,0],
           [Av,0,Cv,Ev, 0,-Tv*Cv,0, 0,0,0],
           [Bv,0,Dv,Fv, -Bv*Sv,0,0, 0,0,0] ];
end function;

procedure Corner(pt, tag)
  Av,Bv,Cv,Dv,Ev,Fv,Tv,Sv,Pv,Qv,Rvv := Explode([ Z8 | c : c in pt ]);
  m := Wit(Av,Bv,Cv,Dv,Ev,Fv,Tv,Sv,Pv,Qv,Rvv);
  r := RelW(m);
  Say(Sprintf("%o corner %o: witness relator rows %o", tag, pt, r));
  po := [ (-2*Av*Cv)*Fv - (Cv*Ev)*Bv, (-(Av*Dv + Bv*Cv))*Fv - (Dv*Ev)*Bv,
          (-(Av*Dv + Bv*Cv))*Fv - (Cv*Fv)*Bv, (-2*Bv*Dv)*Fv - (Dv*Fv)*Bv,
          Av*(Cv*Ev) - Ev*(-2*Av*Cv), Av*(Dv*Ev) - Ev*(-(Av*Dv + Bv*Cv)),
          Av*(Cv*Fv) - Ev*(-(Av*Dv + Bv*Cv)), Av*(Dv*Fv) - Ev*(-2*Bv*Dv) ];
  Say(Sprintf("%o   eight committed Lam3 pairings: %o (all even: %o)", tag, po,
    &and[ IsEven(Integers()!p) : p in po ]));
  g := U5Comm(m[1], m[3]);
  Say(Sprintf("%o   [sigma, x1] = %o", tag, g));
  res := Integers()!r[10];
  // the move: (h, i) = (0, k*R) on the U-handle slot; increment is -k*R*B
  for k in [0..7] do
    zz := [Z8|0,0,0,0,0,0,0, 0, k*Rvv, 0];
    md := m; md[4] := U5Mul(m[4], zz);
    if &and[ RelW(md)[t] eq 0 : t in [1..10] ] then
      Say(Sprintf("%o   KILLED by the U-slot move (h, i) = (0, %o*R) = (0, %o)",
        tag, k, k*Rvv));
      Say(Sprintf("%o   dressed frame relator: %o", tag, RelW(md)));
      break;
    end if;
  end for;
end procedure;

Corner([0,1,1,1,2,0,2,0,1,3,1], "(b)");
Corner([0,1,1,1,2,4,2,0,1,3,3], "(c)");

Say("done");
quit;
