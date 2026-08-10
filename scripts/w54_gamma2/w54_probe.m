/*  W54-GAMMA2 -- probe: is the W53 "provable dead end" corner reached by a gamma2-level
 *  move of the honest achievable lattice?  Honest group collection only.
 *      magma -b w54_probe.m
 */
SetColumns(0);
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
function Pow(x, n)
  r := [ Parent(x[1]) | 0,0,0,0,0,0,0,0,0,0 ];
  for k in [1..n] do r := U5Mul(r, x); end for;
  return r;
end function;

Z8 := Integers(8);
function Wit(A, B, C, D, E, F, T, S, P, Q, Rv)
  return [ [Z8|0,1,0,0, 0,0,0, 0,0,0],
           [B*T-A*S, 0, D*T-C*S, F*T-E*S, -2*T*S*B, S*T*C+T*S*D, 0, 0,0,0],
           [Z8|0,0,0,0, P,Q,Rv, -(A+B)*Q, 0,0],
           [A,0,C,E, 0,-T*C,0, 0,0,0],
           [B,0,D,F, -B*S,0,0, 0,0,0] ];
end function;

// the W53 dead-end corner
A := Z8!0; B := Z8!1; C := Z8!1; D := Z8!1; E := Z8!2; F := Z8!0; T := Z8!2; S := Z8!0;
P := Z8!1; Q := Z8!3; Rv := Z8!1;
m := Wit(A,B,C,D,E,F,T,S,P,Q,Rv);
print "witness relator rows:", RelW(m);

// the gamma2-level element [x1-letter, sigma] = commP(m[3], m[1]) of gamma2(im Phi)
z := U5Comm(m[3], m[1]);
print "z = [x1, sigma] rows (e,f,g,h,i,j):", [z[k] : k in [5..10]];

for k in [1..7] do
  zk := Pow(z, k);
  md := [ m[1], m[2], m[3], U5Mul(m[4], zk), m[5] ];
  print "dress U-slot by z^", k, " -> relator:", RelW(md);
end for;

// all ten letter commutators: their (e,f,g,h,i) data
nm := ["sigma","x0","x1","U","V"];
print "";
print "letter commutators [L_a, L_b], coords (e,f,g,h,i):";
for a in [1..5] do for b in [a+1..5] do
  c := U5Comm(m[a], m[b]);
  print "  [", nm[a], ",", nm[b], "] =", [c[k] : k in [5..9]];
end for; end for;
print "x1-letter squared:", [Pow(m[3],2)[k] : k in [5..9]];
quit;
