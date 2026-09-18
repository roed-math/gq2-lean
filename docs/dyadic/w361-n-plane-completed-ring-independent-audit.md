# W361 — independent audit of the completed-ring and relative-boundary modules

2026-09-17. Read-only audit and current-module recompilation of the two named
sources; neither reviewed source, its cached artifact, an old hypothesis, nor a
capstone was changed. A separately authorized new mixed-Lie module is recorded
in section 4.

## Outcome and verification

`MarkedCore/NPlanePowerSeries.lean` and
`MarkedCore/NPlaneRelativeBoundary.lean` were read completely and independently
recompiled with the pinned campaign runner, without output-file options. Both
exited zero. The 24 power-series audit pins printed exactly
`[propext, Classical.choice, Quot.sound]`; the three boundary pins printed
`[propext, Quot.sound]`. Neither file adds an axiom, admission, or local option.

This checks the current modules against cached dependencies, not a fresh
source-only transitive build. No mathematical defect was found in their
statements or proofs. Their explicit disclaimers are important and accurate.

## 1. Topology and involution

`NPlaneSeries` is literally `PowerSeries Z2`. The active
`PowerSeries.WithPiTopology` scope gives coefficientwise p-adic topology,
not the X-adic topology with discrete coefficients. The local linear-topology
instance for Z2 is constructed from positive-radius norm-ball ideals; closure
under scalar multiplication uses the bound that every Z2 element has norm at
most one.

The denominator `B=1+X` is an actual power-series unit. For every
`v : Z2ˣ`, the proposed substitution point is `v/B-1`. Its constant
coefficient is `v-1`, which lies in `2 Z2` and is topologically nilpotent.
The power-series evaluation theorem therefore applies even when that constant
coefficient is nonzero. This is a genuine convergent substitution, not a
formal substitution at an inadmissible point or a fraction-field argument.

The resulting Z2-algebra map fixes constants and sends

\[
B\longmapsto vB^{-1}.
\]

Its square fixes X. The proof extends this equality from polynomials by their
density and continuity in the stated topology. Thus `nSeriesStarEquiv` is an
involutive algebra equivalence, and `nSeriesStar_continuous` supplies the
continuity of that map. Its inverse is the same continuous map.

## 2. Isometry and all-rank statement

For any coefficient unit `u`, the plane transformation

\[
(x_1,x_2)\longmapsto(u^*x_1,u^{-1}x_2)
\]

preserves the displayed skew-Hermitian pairing
`x1* y2 - x2* y1`. Its inverse replaces u by its inverse. This is a
Lambda-linear equivalence because Lambda is commutative; the star occurs in
the fixed coefficient, not as a semilinear operation on the argument.

For `u=1+aX`, its ordinary constant coefficients are
`diag(1+a(v-1),1)`. `exists_nSeriesFullPlaneScale` specializes to
`v=nUnit alpha`, uses `alpha >= 2` to choose a with
`1+a(v-1)=kappa`, and takes the product with identity on
`Fin h -> Lambda × Lambda`. Therefore every handle vector, not merely its
constant coefficient, is literally fixed, for arbitrary finite h.

The public equivalence record is a `LinearEquiv`, not a
`ContinuousLinearEquiv`. Continuity of its displayed multiplication formula
is immediate from the coefficient-ring topology, but no additional bundled
continuity theorem should be attributed to the file. This is an API scope
distinction, not a defect in the stated theorem.

Neither the source nor `w361-n-plane-strong-scaling-research.md` calls the
constructed form the actual DN Alexander/intersection form. Both explicitly
retain that identification and the nonlinear group lift as further work.

## 3. Exact relative equation and orientation convention

With `commP x y=x^-1 y^-1 x y` and `conjP a b=b^-1 a b`, the group identity is

\[
a^{2+2^\alpha}[a,b]H
=a^{1+2^\alpha}(b^{-1}ab)H.
\]

Hence the relation equals one exactly when

\[
b^{-1}ab=a^{-(1+2^\alpha)}H^{-1}.
\]

The factor order on the right is essential and is correct in the source.
Taking `H=[c,d] handleWord(u,v)` gives the all-rank statement. These identities
hold in every group and for every natural alpha, including values outside the
q=2 N range. They neither assert properness of a pro-two HNN extension nor
construct a relative automorphism.

For the **right deck convention** `B(a)=b^-1 a b`, abelianizing the orientation
kernel gives the head factor `B+(1+2^alpha)`. Its root is

\[
-(1+2^\alpha)=(nUnit\ \alpha)^{-1},
\]

not `nUnit alpha`. This is not a contradiction: the module constructs its
star for every unit v, and its final existence specialization does not claim
an identification with the actual deck convention. Switching the interpolation
parameter is also harmless at the model level: from
`1+a(v-1)=kappa`, put `a'=-v*a`; then
`1+a'(v^-1-1)=kappa`. That observation does **not** identify the actual
Alexander form, its torsion coupling, or the appropriate duality involution.

## 4. Uniform next step

A separate new note, `w361-n-plane-relative-graded-correction.md`, records the
explicit mixed-Lie kernel vector found during this audit. It addresses the
simultaneous ordinary-row constraint at every filtration degree, including
the exceptional first mixed-square term. The companion new
`MarkedCore/NPlaneMixedLieKernel.lean` is now compiled and cached, warning-free
at default limits, with ten audit pins contained in the standard three-axiom
set. Its abstract inputs and the actual-filtration seam are listed in that
note. The finite-dimensional coefficient
model and the literal group relation remain distinct from the filtered
lifting/convergence argument. No full N-plane automorphism theorem follows
merely from the two modules audited here.
