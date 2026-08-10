/*  W54-GAMMA2 -- the residual corners, exhaustively, under three nested dressing models.
 *
 *      magma -b w54_dead.m             (writes results/w54dead.txt)
 *
 *  Runs over EVERY binder point at which the bare class-four witness survives stage 3 with
 *  an ODD class-four residue and neither the committed Lam3 pairings nor the three new
 *  gamma2-level pairings are odd (the "leftover corners" of w54_gate.m).  For each, the
 *  exact achievable increment lattice is computed under
 *
 *    M1  Gam = gamma2(im Phi): the ten slot commutators, the fifty triple commutators, the
 *        square of the gamma2-shaped x1-letter and its five commutators -- the honest image
 *        of gamma2 of the ambient group under the test hom;
 *    M0  the FREE model: every element of gamma2(U5(Z/8)) allowed as a dressing.
 *
 *  Verdict per model: the odd residue dies iff the Z/8-span of the per-(slot, generator)
 *  increment vectors meets the last coordinate axis in the WHOLE of Z/8 (order 8); order
 *  <= 4 means every stage-preserving achievable increment is even, so an odd residue
 *  survives every move of that model.  Also recorded: the mod-2 classes of the corners.
 */

SetColumns(0); SetAutoColumns(false);
OUT := "results/w54dead.txt"; System("rm -f " cat OUT);
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
function U5Comm(x, y) return U5Mul(U5Inv(x), U5Mul(U5Inv(y), U5Mul(x, y))); end function;

Z8 := Integers(8);
function Wit(A, B, C, D, E, F, T, S, P, Q, Rv)
  return [ [Z8|0,1,0,0, 0,0,0, 0,0,0],
           [B*T-A*S, 0, D*T-C*S, F*T-E*S, -2*T*S*B, S*T*C+T*S*D, 0, 0,0,0],
           [Z8|0,0,0,0, P,Q,Rv, -(A+B)*Q, 0,0],
           [A,0,C,E, 0,-T*C,0, 0,0,0],
           [B,0,D,F, -B*S,0,0, 0,0,0] ];
end function;

function Pair4(z, L)
  return z[8]*L[4] - z[9]*L[1] + z[5]*L[7] - z[7]*L[5] + z[7]*L[1]*L[2] - z[6]*L[1]*L[4];
end function;
function Pair3L(z, L) return z[5]*L[3] - z[6]*L[1]; end function;
function Pair3R(z, L) return z[6]*L[4] - z[7]*L[2]; end function;

function Incr(m, slot, z)
  s := m[1]; x := m[2]; y := m[3]; u := m[4]; v := m[5];
  sstar := [ 10*x[k] - s[k] - 8*y[k] : k in [1..10] ];
  ce := u[1]*v[2] - u[2]*v[1];
  cg := u[3]*v[4] - u[4]*v[3];
  c0 := z[5]*(-s[3]*x[4] + s[4]*x[3] - 4*x[3]*x[4] + 2*x[3]*y[4] + y[3]*y[4])
      + z[6]*(8*x[1]*x[4] - 2*x[1]*y[4] - 2*x[4]*y[1] - 2*y[1]*y[4])
      + z[7]*(s[1]*x[2] - s[2]*x[1] - 4*x[1]*x[2] + 2*x[2]*y[1] + y[1]*y[2]);
  c1 := z[5]*(3*s[3]*x[4] - 2*s[3]*y[4] + s[4]*x[3] - 20*x[3]*x[4] + 20*x[3]*y[4]
              - 4*y[3]*y[4])
      + z[6]*(2*s[1]*s[4] - 14*s[1]*x[4] + 10*s[1]*y[4] - 14*s[4]*x[1] + 10*s[4]*y[1]
              + 130*x[1]*x[4] - 100*x[1]*y[4] - 100*x[4]*y[1] + 80*y[1]*y[4])
      + z[7]*(-2*s[1]*s[2] + 11*s[1]*x[2] - 8*s[1]*y[2] + 13*s[2]*x[1] - 10*s[2]*y[1]
              - 110*x[1]*x[2] + 80*x[1]*y[2] + 100*x[2]*y[1] - 76*y[1]*y[2]);
  c2 := z[5]*(-2*s[3]*y[4] + s[4]*y[3]) + z[6]*(s[1]*y[4] + s[4]*y[1])
      + z[7]*(s[1]*y[2] - 2*s[2]*y[1]);
  case slot:
    when 1:
      return [ Z8 | 0, 0, 0, Pair3L(z, x), Pair3R(z, x), Pair4(z, x) + c0 ];
    when 2:
      return [ Z8 | -4*z[5], -4*z[6], -4*z[7],
        -4*z[8] + Pair3L(z, sstar), -4*z[9] + Pair3R(z, sstar),
        Pair4(z, sstar) + c1 + cg*(-4*z[5]) - ce*(-4*z[7]) ];
    when 3:
      return [ Z8 | 2*z[5], 2*z[6], 2*z[7],
        2*z[8] + Pair3L(z, y), 2*z[9] + Pair3R(z, y),
        Pair4(z, y) + c2 + cg*(2*z[5]) - ce*(2*z[7]) ];
    when 4:
      return [ Z8 | 0, 0, 0, Pair3L(z, v), Pair3R(z, v),
        Pair4(z, v) - cg*z[5] + ce*z[7] ];
    else
      return [ Z8 | 0, 0, 0, -Pair3L(z, u), -Pair3R(z, u),
        -Pair4(z, u) - cg*z[5] + ce*z[7] ];
  end case;
end function;

function GamGens(m)
  base := [];
  for a in [1..5] do for b in [a+1..5] do
    Append(~base, U5Comm(m[a], m[b]));
  end for; end for;
  Append(~base, U5Mul(m[3], m[3]));
  gens := base;
  for c in base do
    for a in [1..5] do Append(~gens, U5Comm(c, m[a])); end for;
  end for;
  return gens;
end function;

FreeGens := [ [Z8|0,0,0,0] cat [ (k eq t) select Z8!1 else Z8!0 : k in [1..6] ]
              : t in [1..5] ];    // the free gamma2 basis on (e,f,g,h,i)

Ab := AbelianGroup([8, 8, 8, 8, 8, 8]);
Hlast := sub< Ab | Ab.6 >;

function Verdict(m, gens)
  vecs := [];
  for t in [1..5] do
    for g in gens do
      Append(~vecs, Ab ! [ Integers()!c : c in Incr(m, t, g) ]);
    end for;
  end for;
  K := sub< Ab | vecs > meet Hlast;
  return #K;
end function;

RZ<A,B,C,D,E,F,T,S,P,Q,Rv,W2> := PolynomialRing(Integers(), 12);
candH := 4*(P*Q) - 2*((A+B)*Q) + B*C*(T+S);
candI := 2*(2*(S*T*((C+D)*W2))) - C*F*T;
cand  := B*E*T*(C+D) + 5*(P*Rv) - 2*(A*(E*Q + T*Rv)) - 2*(C*E*P) - 2*(B*Rv*(T+S));

nlo := 0; nM1kill := 0; nM0kill := 0; evenGall := true;
kM1 := {* *}; kM0 := {* *}; classes := {};
for a0, b0, c0, d0 in Z8 do
 for e0, f0, t0, s0 in Z8 do
  Av := a0; Bv := b0; Cv := c0; Dv := d0; Ev := e0; Fv := f0; Tv := t0; Sv := s0;
  dP := Bv*Tv - Av*Sv; dQ := Sv*Cv - Tv*Dv; dR := Dv*Ev - Cv*Fv; dW := Fv*Tv - Ev*Sv;
  if IsOdd(Integers()!dP) or IsOdd(Integers()!dQ) or IsOdd(Integers()!dR)
     or IsOdd(Integers()!dW) then continue; end if;
  Pv := Z8!((Integers()!dP) div 2); Qv := Z8!((Integers()!dQ) div 2);
  Rvv := Z8!((Integers()!dR) div 2); Wv := Z8!((Integers()!dW) div 2);
  point := [Av,Bv,Cv,Dv,Ev,Fv,Tv,Sv,Pv,Qv,Rvv,Wv];
  if Z8!Evaluate(candH, point) ne 0 or Z8!Evaluate(candI, point) ne 0 then continue; end if;
  jres := Z8!Evaluate(cand, point);
  if IsEven(Integers()!jres) then continue; end if;
  po := [ (-2*Av*Cv)*Fv - (Cv*Ev)*Bv, (-(Av*Dv + Bv*Cv))*Fv - (Dv*Ev)*Bv,
          (-(Av*Dv + Bv*Cv))*Fv - (Cv*Fv)*Bv, (-2*Bv*Dv)*Fv - (Dv*Fv)*Bv,
          Av*(Cv*Ev) - Ev*(-2*Av*Cv), Av*(Dv*Ev) - Ev*(-(Av*Dv + Bv*Cv)),
          Av*(Cv*Fv) - Ev*(-(Av*Dv + Bv*Cv)), Av*(Dv*Fv) - Ev*(-2*Bv*Dv) ];
  pn := [ -Rvv*Bv, Av*Rvv,
          (Pv*Cv-Qv*Av)*Fv - (Qv*Ev)*Bv, Av*(Qv*Ev) - Ev*(Pv*Cv-Qv*Av),
          (Pv*Dv-Qv*Bv)*Fv - (Qv*Fv)*Bv, Av*(Qv*Fv) - Ev*(Pv*Dv-Qv*Bv) ];
  if &or[ IsOdd(Integers()!p) : p in po cat pn ] then continue; end if;
  nlo +:= 1;
  m := Wit(Av,Bv,Cv,Dv,Ev,Fv,Tv,Sv,Pv,Qv,Rvv);
  gens := GamGens(m);
  if not &and[ IsEven(Integers()!g[7]) : g in gens ] then evenGall := false; end if;
  k1 := Verdict(m, gens); Include(~kM1, k1);
  if k1 eq 8 then nM1kill +:= 1; end if;
  k0 := Verdict(m, FreeGens); Include(~kM0, k0);
  if k0 eq 8 then nM0kill +:= 1; end if;
  Include(~classes, [ (Integers()!c) mod 2 : c in point ]);
 end for;
end for;

Say(Sprintf("leftover corners (stage-3 odd survivors, no odd pairing old or new): %o", nlo));
Say(Sprintf("  killed by the honest gamma2 lattice gamma2(im Phi):  %o", nM1kill));
Say(Sprintf("  killed by the FREE gamma2 model:                     %o", nM0kill));
Say(Sprintf("  every generator of gamma2(im Phi) has even g:        %o", evenGall));
Say(Sprintf("  |span meet last axis| multiset, honest model: %o", kM1));
Say(Sprintf("  |span meet last axis| multiset, free model:   %o", kM0));
Say(Sprintf("  number of distinct mod-2 classes of (A..S,P,Q,R,W2) among them: %o", #classes));
Say(Sprintf("  the mod-2 classes: %o", Sort(SetToSequence(classes))));
Say("done");
quit;
