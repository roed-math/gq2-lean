/*  W53-CONTAIN -- the class-four gate at the witness: whole-binder coverage brute force,
 *  the j-row closed form, and linear_combination certificates for the Lean transcription.
 *
 *      magma -b w53_gate.m             (writes results/w53gate.txt)
 *
 *  Q1  (coverage): at EVERY binder point (all (A..S) in (Z/8)^8 with the four adjacency
 *      differences even, halves P,Q,R,W2 determined mod 4 -- parities forced), does an odd
 *      witness j-residue imply one of the four achievable-generator pairings
 *      {BCE, ADF, BDF | ACE} is odd?  Also measured: on the even-residue locus, how often
 *      a 2-pairing witness (some generator pairing = 2 mod 4) exists (the live locus).
 *  Q2  the j-row closed form: massage the raw j-row into the committed style
 *      (even part exhibited, odd-candidate part compact), verify equivalence modulo the
 *      parity-row ideal, and emit the exact linear_combination certificate.
 */

SetColumns(0); SetAutoColumns(false);
OUT := "results/w53gate.txt"; System("rm -f " cat OUT);
procedure Say(s) PrintFile(OUT, s); print s; end procedure;

/* ---------- U5 arithmetic (as in w53_shift.m) ---------- */
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

function WitRows(A, B, C, D, E, F, T, S, P, Q, Rv, W2, Rng)
  sW := [ Rng!0, 1, 0, 0,  0, 0, 0,  0, 0, 0 ];
  xW := [ B*T - A*S, 0, D*T - C*S, F*T - E*S,  -2*T*S*B, S*T*C + T*S*D, 0,  0, 0, 0 ];
  yW := [ Rng!0, 0, 0, 0,  P, Q, Rv,  -(A+B)*Q, 0, 0 ];
  uW := [ A, 0, C, E,  0, -T*C, 0,  0, 0, 0 ];
  vW := [ B, 0, D, F,  -B*S, 0, 0,  0, 0, 0 ];
  return RelWord(sW, xW, yW, [uW], [vW]);
end function;

/* ---------- Q1 runs after Q2 (it drives off the certified closed forms) ---------- */

/* ---------- Q2: closed form + certificates over Z[A..W2], with 8 as a generator ---------- */

RZ<A,B,C,D,E,F,T,S,P,Q,Rv,W2> := PolynomialRing(Integers(), 12);
RW := WitRows(A, B, C, D, E, F, T, S, P, Q, Rv, W2, RZ);
hd := 2*P + (A*S - B*T);
he := 2*Q + (T*D - S*C);
hg := 2*Rv + (C*F - D*E);
hb := 2*W2 + (E*S - F*T);

// candidate closed form for the j-row, committed style: guessed from the Z/8 normal form
// NF = 6AEQ + 6ATR + BCET + BDET + 6BTR + 6BSR + 6CEP + 5PR
cand := B*E*T*(C+D) + 5*(P*Rv) - 2*(A*(E*Q + T*Rv)) - 2*(C*E*P) - 2*(B*Rv*(T+S));

/* tracked division over Z: eliminate P, Q, Rv, W2 terms with even integer coefficients
   using the rows (leading 2*X), and reduce coefficients mod 8 into (-4, 4] with the
   8-generator.  Returns remainder plus the five certificate coefficients. */
function TrackedCert(f, rows, Xs)
  cert := [ Parent(f)!0 : r in rows ];
  c8 := Parent(f)!0;
  g := f;
  repeat
    progressed := false;
    mons := Monomials(g); cfs := Coefficients(g);
    for k in [1..#mons] do
      cf := Integers()!cfs[k]; mono := mons[k];
      // coefficient normalization into (-4, 4]
      if cf gt 4 or cf le -4 then
        qq := (cf + 3) div 8;   // brings cf - 8 qq into (-4, 4]
        if qq ne 0 then
          c8 +:= Parent(f)!qq * mono;
          g := g - Parent(f)!(8*qq) * mono;
          progressed := true; break;
        end if;
      end if;
      if IsEven(cf) then
        for ix in [1..#Xs] do
          if Degree(mono, Xs[ix]) ge 1 then
            q := Parent(f)!(cf div 2) * (mono div Xs[ix]);
            cert[ix] +:= q;
            g := g - q*rows[ix];
            progressed := true; break;
          end if;
        end for;
      end if;
      if progressed then break; end if;
    end for;
  until not progressed;
  return g, cert, c8;
end function;

rem, cert, c8 := TrackedCert(RW[10] - cand, [hd, he, hg, hb], [P, Q, Rv, W2]);
Say("Q2 tracked-division remainder (want 0):"); Say(Sprint(rem));
Say("Q2 certificate coefficients:");
Say(Sprintf("  cd := %o", cert[1]));
Say(Sprintf("  ce := %o", cert[2]));
Say(Sprintf("  cg := %o", cert[3]));
Say(Sprintf("  cb := %o", cert[4]));
Say(Sprintf("  c8 := %o", c8));
Say("Q2 certificate check (want true): " cat
  Sprint(RW[10] - cand eq cert[1]*hd + cert[2]*he + cert[3]*hg + cert[4]*hb + 8*c8 + rem));

/* sanity: the committed h- and i-row certificates re-derived */
candH := 4*(P*Q) - 2*((A+B)*Q) + B*C*(T+S);
remH, certH, c8H := TrackedCert(RW[8] - candH, [hd, he, hg, hb], [P, Q, Rv, W2]);
Say("Q2 h-row remainder (want 0):"); Say(Sprint(remH));
candI := 2*(2*(S*T*((C+D)*W2))) - C*F*T;
remI, certI, c8I := TrackedCert(RW[9] - candI, [hd, he, hg, hb], [P, Q, Rv, W2]);
Say("Q2 i-row remainder (want 0):"); Say(Sprint(remI));

/* ---------- Q1: whole-binder brute force over Z/8, off the certified closed forms ---------- */

Z8 := Integers(8);
// spot check: closed forms against the honest word at 400 random binder points
nspot := 0; spotOK := true;
while nspot lt 400 do
  vals := [ Random(Z8) : k in [1..8] ];
  Av,Bv,Cv,Dv,Ev,Fv,Tv,Sv := Explode(vals);
  dP := Bv*Tv - Av*Sv; dQ := Sv*Cv - Tv*Dv; dR := Dv*Ev - Cv*Fv; dW := Fv*Tv - Ev*Sv;
  if IsOdd(Integers()!dP) or IsOdd(Integers()!dQ) or IsOdd(Integers()!dR)
     or IsOdd(Integers()!dW) then continue; end if;
  Pv := Z8!((Integers()!dP) div 2); Qv := Z8!((Integers()!dQ) div 2);
  Rvv := Z8!((Integers()!dR) div 2); Wv := Z8!((Integers()!dW) div 2);
  RWn := WitRows(Av, Bv, Cv, Dv, Ev, Fv, Tv, Sv, Pv, Qv, Rvv, Wv, Z8);
  point := [Av,Bv,Cv,Dv,Ev,Fv,Tv,Sv,Pv,Qv,Rvv,Wv];
  ok := RWn[8] eq Z8!Evaluate(candH, point) and RWn[9] eq Z8!Evaluate(candI, point)
        and RWn[10] eq Z8!Evaluate(cand, point)
        and &and[ RWn[k] eq 0 : k in [1..7] ];
  if not ok then spotOK := false; Say(Sprintf("SPOT FAIL at %o", point)); end if;
  nspot +:= 1;
end while;
Say(Sprintf("Q1 spot check of closed forms at %o random binder points: %o", nspot,
  spotOK select "all OK" else "FAILURES"));

nOdd := 0; nOddCovered := 0; nEven := 0; nEvenLive := 0;
nStage3 := 0; nStage3Odd := 0; nStage3OddCov := 0; nStage3EvenLive := 0; nStage3Even := 0;
bad := [];
badStage3 := [];
exs := [];   // showcase points for the Lean decide-instances
for a0, b0, c0, d0 in Z8 do
 for e0, f0, t0, s0 in Z8 do
  Av := a0; Bv := b0; Cv := c0; Dv := d0; Ev := e0; Fv := f0; Tv := t0; Sv := s0;
  dP := Bv*Tv - Av*Sv; dQ := Sv*Cv - Tv*Dv; dR := Dv*Ev - Cv*Fv; dW := Fv*Tv - Ev*Sv;
  if IsOdd(Integers()!dP) or IsOdd(Integers()!dQ) or IsOdd(Integers()!dR)
     or IsOdd(Integers()!dW) then continue; end if;
  Pv := Z8!((Integers()!dP) div 2); Qv := Z8!((Integers()!dQ) div 2);
  Rvv := Z8!((Integers()!dR) div 2); Wv := Z8!((Integers()!dW) div 2);
  point := [Av,Bv,Cv,Dv,Ev,Fv,Tv,Sv,Pv,Qv,Rvv,Wv];
  jres := Z8!Evaluate(cand, point);
  hres := Z8!Evaluate(candH, point);
  ires := Z8!Evaluate(candI, point);
  odd := IsOdd(Integers()!jres);
  // the eight achievable-generator pairings (exact Z/8 values)
  pU1 := (-2*Av*Cv)*Fv - (Cv*Ev)*Bv;
  pU2 := (-(Av*Dv + Bv*Cv))*Fv - (Dv*Ev)*Bv;
  pU3 := (-(Av*Dv + Bv*Cv))*Fv - (Cv*Fv)*Bv;
  pU4 := (-2*Bv*Dv)*Fv - (Dv*Fv)*Bv;
  pV1 := Av*(Cv*Ev) - Ev*(-2*Av*Cv);
  pV2 := Av*(Dv*Ev) - Ev*(-(Av*Dv + Bv*Cv));
  pV3 := Av*(Cv*Fv) - Ev*(-(Av*Dv + Bv*Cv));
  pV4 := Av*(Dv*Fv) - Ev*(-2*Bv*Dv);
  pairs := [pU1, pU2, pU3, pU4, pV1, pV2, pV3, pV4];
  hasOddPair := &or[ IsOdd(Integers()!p) : p in pairs ];
  hasTwoPair := &or[ (Integers()!p) mod 4 eq 2 : p in pairs ];
  if odd then
    nOdd +:= 1;
    if hasOddPair then nOddCovered +:= 1;
    elif #bad lt 12 then Append(~bad, <point, jres, pairs>); end if;
  else
    nEven +:= 1;
    if hasTwoPair or hasOddPair then nEvenLive +:= 1; end if;
  end if;
  // stage-3 survivors of the bare witness (rows h and i vanish too)
  if hres eq 0 and ires eq 0 then
    nStage3 +:= 1;
    if odd then
      nStage3Odd +:= 1;
      if hasOddPair then
        nStage3OddCov +:= 1;
        // showcase: odd kill NOT through the committed BDF/ACE generators
        if IsEven(Integers()!(Bv*Dv*Fv)) and IsEven(Integers()!(Av*Cv*Ev))
           and #exs lt 6 then
          Append(~exs, <point, jres, pairs>);
        end if;
      elif #badStage3 lt 12 then Append(~badStage3, <point, jres, pairs>);
      end if;
    else
      nStage3Even +:= 1;
      if hasTwoPair then nStage3EvenLive +:= 1; end if;
    end if;
  end if;
 end for;
end for;

Say(Sprintf("Q1 odd-residue binder points: %o, covered by an odd pairing: %o", nOdd, nOddCovered));
Say(Sprintf("Q1 UNcovered odd points (up to 12): %o", bad));
Say(Sprintf("Q1 even-residue points: %o, live (2-pairing or odd pairing): %o", nEven, nEvenLive));
Say(Sprintf("Q1 bare-witness stage-3 survivors: %o (odd %o, covered %o; even %o, 2-live %o)",
  nStage3, nStage3Odd, nStage3OddCov, nStage3Even, nStage3EvenLive));
Say(Sprintf("Q1 uncovered odd stage-3 survivors: %o", badStage3));
Say(Sprintf("Q1 showcase points (odd survivor, BDF and ACE both even): %o", exs));

Say("done");
quit;
