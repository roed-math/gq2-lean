# W361 — what B8 scaling does and does not prove for N

**Bounded audit and additive Lean clarification, 2026-09-17. No new axiom or premise.**
The stronger historical plane-scaling statement is not needed by the completed selected
presentation: `nMarkedCorrection_of_pair` and the field primitive-plane theorem already supply
the required marked correction. This note evaluates a possible additional discharge, without
confusing that extra result with a missing assumption of the final theorem.

## 1. The exact target is stronger than normalizing one character

In `MarkedCore/N.lean`:

* `NScalingHypothesis alpha h` asks for a chi-preserving continuous automorphism with
  `f(Psi sigma)=kappa*f(sigma)` for **every** continuous Z2 character `f`, and leaves the
  other rows unconstrained.
* `NPlaneScalingHypothesis alpha h` asks for `NPlaneRealizes ... (nPlaneDet kappa)`.
  `nCoreMat` is two `Function.update`s, at sigma and x2 only. Therefore its full requirement is

  `f(Psi sigma)=kappa*f(sigma)`, `f(Psi x2)=f(x2)`,

  and `f(Psi g)=f(g)` on **all remaining marked generators**, simultaneously for every `f`.
  In particular, both rows of every handle must be unchanged.

`nHandleMixLift` or `nMarkedCorrection_of_pair` can be chosen after one character is supplied.
Such a result has the wrong quantifier order for this target: it does not provide one
automorphism working simultaneously for all characters. Reusing it would require a new
simultaneous stabilizer theorem, not just an application of the existing correction theorem.

## 2. Weak scaling needs no B8: the exact SL2 move already supplies it

The existing `nCorePlane_sl2_lift` applied to
`planeDiag kappa = diag(kappa,kappa^-1)` realizes the desired sigma scaling while scaling
the unconstrained x2 row inversely. Its determinant is one. Consequently there is no reason
to build a new B8 automorphism for `NScalingHypothesis`.

The additive `MarkedCore/NScalingAudit.lean` packages this observation as
`nScalingHypothesis_of_sl2 alpha h`. It is uniform in both parameters and has no B8 input.
The distinction remains: `diag(kappa,kappa^-1)` does **not** prove the strong
`diag(kappa,1)` plane statement unless `kappa=1`.

For evaluating the proposed stronger construction, the relevant B8 inputs also exist.

The algebraic inputs exist. `Cores.nOuter_scaling` and `nInner_scaling` are B8 transports of

`nHead(x0,x1) * sigma^-1 * (sigma^x2 * handles)=1`

and

`x0^(1+2^alpha) * x0^x1 * nHead(x0,x1)^-1=1`.

As in `MScaling`, retain the canonical `peripheralScaleP/T/C` witnesses rather than the
bare existential triples. Their `deltaHom_mem_topologicalClosure` support is essential for
the Frattini argument. Match the inner and outer head conjugators by the existing connector
construction; replace the M head by `nHead`, its first inner factor by `x0^(1+2^alpha)`,
and its outer distinguished factor by `sigma^-1`.

`MScalingHandles.peripheralScaleList_product` then splits the transported third outer factor
over `sigma^x2` and every commutator. Its `fullMark` constructor and list bookkeeping are
group-generic and reusable. The resulting marking sends sigma to a conjugate of
`sigma^kappa`, hence has the required sigma row for every character. The N relator can be
verified by the two transported triple identities and the list product identity. The same
Frattini/Hopfian proof pattern promotes the endomorphism to a continuous automorphism.
Orientation is not a fresh obstruction: at `1 ≤ alpha`,
`Instances/NOrientationCharacteristic.nCoreOrientationCharacteristic_all` now states the
characteristic-orientation result for every automorphism.

This explains how a B8-based candidate would be built, but such a construction would be
redundant for the already proved weak scaling statement. More importantly, it does **not**
prove the stronger plane predicate.

## 3. Explicit failure of the naive positive-handle extension

The relevant existing formula is not hidden in an existence proof:
`MScalingHandles.mScaleHNewU` is

`conjP (zpowZtwo U_j kappa) (innerConjugator * connector)`.

Its N analogue in the construction above therefore satisfies

`f(U'_j)=kappa*f(U_j)`

for every continuous Z2 character, independently of all choices of conjugators. At any
positive handle rank choose the character taking value 1 on `U_j` and 0 on all other marked
generators. This character exists directly by `nLiftHom`: in the abelian target all
commutators vanish and the x0 value is zero, so the N defining relator is killed.
The new U row is then `kappa`, whereas `NPlaneRealizes ... (nPlaneDet kappa)` requires 1.
For `kappa != 1` the proposed construction fails the target literally. The new Lean module
packages the coordinate character as `nHandleUCharacter`, its value as
`nHandleUCharacter_self`, and the exact candidate obstructions as
`not_nPlaneRealizes_of_handleU_scaled` and
`not_nPlaneRealizes_of_handleU_conj_power`. The last theorem permits **any** conjugator
and **any** proposed core-plane matrix, so in particular applies to `nPlaneDet kappa`.

This is an obstruction to **that construction**, not a nonexistence theorem for all N
automorphisms. Conjugating the handle images cannot repair it, since characters kill
conjugation. The standard intra-handle rescaling does not repair both rows either:
`HandleMixFrame.planeDiag` is `diag(w,w^-1)` and has determinant one. In the B8 construction
the partner has the form `V'_j=V_j+lambda*U_j` on characters, so the handle block has
determinant `kappa`; composing determinant-one intra-handle transformations cannot make it
the identity when `kappa != 1`.

The scalar `lambda` assertion here is a consequence of the displayed canonical support:
the handle inner conjugators are images of words in `U_j^-1` and `U_j^V_j`, whose character
values are `-f(U_j)` and `f(U_j)`. The outer connector merely conjugates the partner and
cancels on characters. No uncontrolled additional handle coordinate can change the
determinant calculation.

Nor can a compact-core automorphism simply be extended by fixing all handles: the compact
head relation inside the positive-rank group equals the **inverse handle product**, not 1.
A relative boundary-preservation theorem would be needed to justify such an extension.

## 4. What would close the stronger statement

A sound continuation must prove an automorphism theorem stronger than the current list
splitting. One sufficient route is a simultaneous correction of the B8 construction's
handle determinants, fixing the sigma row and the already pinned x1 row for all characters.
Equivalently, one needs an independent-unit handle move, not merely the existing
`diag(w,w^-1)` move. Such a theorem would have to verify the full N relator and may use
the torsion/head generator nontrivially; no producer was found in `N`, `HandleMixFrame`,
`HandleMixClear`, `ClearWide`, `MScaling`, or `MScalingHandles`.

At `h=0` this particular obstruction disappears. After matching the two triples, x0 is
invisible to all characters by `nChar_dnX0`, x1 is unchanged on character rows, and the
remaining x2 error is a multiple of the sigma row. A canonical coefficient can be extracted
from the free pro-2 two-generator conjugator; an exact N2 shear can remove it without
altering the scaled sigma row. That supplies a plausible bounded rank-zero construction,
but neither its formalization nor extrapolation from it to all `h` is claimed here.

The mathematically honest current status is consequently:

* Required marked correction: already proved without either scaling binder.
* Uniform weak N row scaling: follows directly from exact SL2, now packaged independently
  of B8 as `nScalingHypothesis_of_sl2`.
* Uniform strong `NPlaneScalingHypothesis`: still conditional; the proposed B8-plus-handle
  shortcut has a specific character-row obstruction. Further simultaneous automorphism
  work is required, or the historical full-stabilizer claim must remain distinct from the
  weaker theorem actually used by the presentation.

No owner memo, historical hypothesis definition, frozen source, or final capstone was
changed. In particular this note does not turn an unproved stronger assertion into an axiom,
and does not retract the completed presentation theorem.

The seven public declarations in `MarkedCore/NScalingAudit.lean` pass default Lean checking
and print exactly `[propext, Classical.choice, Quot.sound]`. The stronger existential
`NPlaneScalingHypothesis` is neither proved nor refuted by this module.
