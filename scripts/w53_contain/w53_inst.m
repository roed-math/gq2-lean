/*  W53-CONTAIN -- numeric validation of the concrete instances committed in
 *  GQ2/Dyadic/SqCore/GradedContainFour.lean (the showcase completion, the artefact
 *  pipeline, and the provable dead end), before transcription.
 *
 *      magma -b w53_inst.m             (writes results/w53inst.txt)
 *
 *  (a) the ADF showcase: at (A..S) = (1,0,0,1,2,1,0,2), halves (3,0,1), the witness is a
 *      stage-3 survivor with odd residue 7 (kappa4 = BDF and kappa4' = ACE both even);
 *  (b) the artefact pipeline at (2,1,0,1,2,1,0,1), halves (3,0,1): the engine instance's
 *      killed frame is a solution, its U-handle gamma3-dressing (h,i) = (1,0) has defect
 *      liftC 1, and the odd-regime move (h,i) = (2,3) kills the dressed solution;
 *  (c) the dead-end corner (0,1,1,1,2,0,2,0), halves (1,3,1): stage-3 survivor with odd
 *      residue 5 (all eight achievable generator pairings even; see w53_gate.m).
 */
SetColumns(0);
OUT := "results/w53inst.txt"; System("rm -f " cat OUT);
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
function RelW(m) // m: 5 slots
  return U5Mul(SqWord(m[1], m[2], m[3]), U5Comm(m[4], m[5]));
end function;
Z8 := Integers(8);
function Wit(A, B, C, D, E, F, T, S, P, Q, Rv)
  return [ [Z8|0,1,0,0, 0,0,0, 0,0,0],
           [B*T-A*S, 0, D*T-C*S, F*T-E*S, -2*T*S*B, S*T*C+T*S*D, 0, 0,0,0],
           [Z8|0,0,0,0, P,Q,Rv, -(A+B)*Q, 0,0],
           [A,0,C,E, 0,-T*C,0, 0,0,0],
           [B,0,D,F, -B*S,0,0, 0,0,0] ];
end function;

// (a) showcase point (1,0,0,1,2,1,0,2), halves (3,0,1)
w := Wit(Z8!1, 0, 0, 1, 2, 1, 0, 2, 3, 0, 1);
r := RelW(w);
Say(Sprintf("(a) witness relator rows: %o", r));   // want [0,0,0,0,0,0,0,0,0,7]

// (b) artefact pipeline at (2,1,0,1,2,1,0,1), halves (3,0,1)
w2 := Wit(Z8!2, 1, 0, 1, 2, 1, 0, 1, 3, 0, 1);
// selLift 0 wit 1 1 <0,...,2,7,0> 1: dress U-slot (index 4) by z3
z3 := [Z8|0,0,0,0, 0,0,0, 2,7,0];
m := [ w2[1], w2[2], w2[3], U5Mul(w2[4], z3), w2[5] ];
Say(Sprintf("(b) solution check: %o", RelW(m)));   // want all zero
// dress U-handle slot by gamma3 (h,i)=(1,0)
zg := [Z8|0,0,0,0, 0,0,0, 1,0,0];
md := [ m[1], m[2], m[3], U5Mul(m[4], zg), m[5] ];
rd := RelW(md);
Say(Sprintf("(b) dressed defect: %o", rd));        // want [0,...,0,1]
// kill move (h,i) = (2,3) on U-slot
mv := [Z8|0,0,0,0, 0,0,0, 2,3,0];
mk := [ md[1], md[2], md[3], U5Mul(md[4], mv), md[5] ];
Say(Sprintf("(b) killed: %o", RelW(mk)));          // want all zero

// (c) dead-end point (0,1,1,1,2,0,2,0), halves (1,3,1): j-row odd, h,i rows?
w3 := Wit(Z8!0, 1, 1, 1, 2, 0, 2, 0, 1, 3, 1);
Say(Sprintf("(c) uncovered-corner rows: %o", RelW(w3)));

quit;
