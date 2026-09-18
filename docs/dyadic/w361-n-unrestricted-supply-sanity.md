# W361: sanity check of the uniform N-stage supply

Audit time: 2026-09-17, approximately 16:10 UTC. This note does not change any
frozen Lean source or discharge `NUnrestrictedStageSupply`. A small separately
authorized extension was checked in `/private/tmp`; its precise status is below.

**Later scope update:** Section 7 records the now checked ambient-stage route
and its unconditional strong N-plane conclusion. The conditional-status
sentences in Sections 1-6 describe the earlier snapshot, not the latest result.
Section 8 records the subsequently checked torsion-sensitive extension and
supersedes Section 7's then-current torsion limitation.

## 1. The exact remaining proposition

`MarkedCore/NPlaneUnrestrictedReduction.lean` defines a supply for every rank
`coreRank h = 4 + 2*h`, every stage `n`, and every continuous free-group
automorphism `e` preserving the canonical orientation on generators. Write
`j = n+3`, `x` for the standard free basis, `y=e(x)`, and `r` for the literal
N relator. The input is

```
r(y) * r(x)^(-1) in lambda_j.
```

The requested output is a tuple `t_i` in
`lambda_(j-1) intersect ker(chi)` making the same relative defect lie in
`lambda_(j+1)`. No ordinary-coordinate or diagonal condition is part of this
supply. The proved consumer subsequently restores all ordinary rows and
preserves the free-basis property. Its arithmetic standing assumption is
`alpha >= 2`; this audit does not assert the supply for `alpha=0` or `1`.

This is a relative free-group problem. In particular, neither `r(x)` nor `r(y)`
is assumed to be the identity in the free group or in its stage quotient.

## 2. All orientation-preserving bases are the right scope

There is no extra basis-dependent obstruction hidden in this quantifier.
Equality of the characters on free generators implies `chi ∘ e = chi`.
Consequently `e` and its inverse preserve both the lower two-central series
and `X=ker(chi)`. Naturality of powers and commutators gives

```
delta_y(e(t)) = e(delta_x(t))
```

on the appropriate graded layers. If an error is killed by every continuous
chi-crossed derivation, its pullback by `e^(-1)` has the same property: compose
each crossed lift with `e^(-1)`. Thus a canonical-basis image theorem transports
to every basis in the stated supply. No assumption that the ordinary matrix
is already diagonal is needed for this argument.

The primary-source comparison is Labute, *Classification of Demushkin groups*,
Section 4.1, printed pages 124-126, Lemmas 1-4 and the conclusion of Theorem 5.
Those pages were visually checked, including the degree-three threshold and
the non-membership sign in Lemma 1. Labute's iterative basis congruence keeps
the graded letters fixed during his induction. It should not be confused with
a necessity for the transported standalone image statement here. The paper's
classification theorem does not itself assert our prescribed integral
ordinary-row conclusion. [Primary source](https://doi.org/10.4153/CJM-1967-007-8).

## 3. Uniform symbolic check at the mixed-square threshold

Let `a=x_0`, `b=x_1`; all remaining letters are paired. The actual derivative
already proved in `NPlaneFilteredDerivative.lean` has graded form

```
delta(t) = pi(t_a) + [t_a,a] + [t_a,b] + [t_b,a]
           + sum_pairs ([t_u,v] + [t_v,u]).
```

The coefficient field is F2. Pairing a head correction with the same correction
in the b-slot removes the additional `[t_a,a]`. The available generators of
the image are therefore the twisted terms `pi(t)+[t,b]`, together with
`[t,x_s]` for `s != b`. This holds at every paired rank.

The first mixed-power identity is essential:

```
[pi(u),b] = pi([u,b]) + [[u,b],u].
```

It is incorrect to discard the triple bracket at degree three. The checked
`MixedPowerCongruence.lean` gives its actual group counterpart, with the
correct filtration indices, and `NPlaneMixedGroupKernel.lean` uses it in the
uniform correction identity. Modulo the derivative image, a term
`pi([u,b])` can leave the non-b pure tail `pi^2(u)`; it need not vanish.
These are exactly the tails retained by the existing augmented-span engine.

For brackets not involving b, Hall-Witt/Jacobi expresses their b-bracket as
a sum whose outer letters are not b. The twisted term then supplies their
squares. Subsequent steps use square transport on correction degrees at least
two, where the relevant operation is additive. This is one mixed base identity
and one uniform successor mechanism, not a nilpotency-class enumeration.

One must not implement this argument by declaring the mixed square to be a
global additive map on the entire graded Lie algebra: on degree one it is not
additive. The already checked group-quotient identities avoid that invalid
shortcut.

## 4. Existing generic span results are stronger than the old endpoint names

The repository already contains the required rank-uniform *augmented* span
machinery, not only the older rank-three `SpanTargetR0`/`SpanTargetR2` results:

- `Instances/StageAbstractionEvenRawSpanStep.lean`:
  `evenRawAugmentedSpanBaseSupply_of_generates`,
  `evenRawAugmentedSpan_step`, and
  `evenRawAugmentedSpan_of_base_of_step` work with arbitrary paired rank and
  arbitrary topologically finitely generated profinite pro-two carrier.
- `Instances/StageAbstractionEvenDerivKer.lean`:
  `evenDeriv_zLayer_le_augmentedSpan` needs a generating marking, not a
  relator-zero hypothesis. It supplies the full ambient layer as raw shifts
  plus the non-b tails.
- The same file's
  `evenDeriv_mem_rawShiftSpan_of_forall_derivKer` removes those tails using a
  coordinate crossed-derivation family and the stated mod-four conditions.
  Raw shifts there allow arbitrary depth corrections, without an exact chi
  kernel condition.

There is a packaging trap: the last theorem takes a
`Tuple W v G chi k`. It is not legitimate to instantiate this tuple with the
N word in the free group by pretending that `r(x)` dies. The criterion itself
does not otherwise use the relation attached to `W`. A constant-one
`StageWord` can package the generating orientation marking, or a new
relation-free wrapper can expose the same proof. The actual relative error
must then be supplied separately.

The necessary error condition is already unconditional:
`MarkedCore/NPlaneCrossedDefect.lean` proves that every chi-crossed lift kills
the literal relative N defect whenever both markings have the canonical
orientation values. There is no extra cohomological datum to assume for this
specific error.

## 5. Full-domain corrections and the formerly excluded b letter

The full ambient raw span is particularly attractive because its generation
theorem is already available. Crossed-derivation separation is compatible
with this larger correction domain; it is not necessary to assume each raw
correction has character exactly one to obtain the graded vanishing.

For a correction `t in lambda_(j-1)`, `j>=3`, functoriality of the series and
`Roe/Labute/TwoCentralTower.twoCentralSeries_units_le` give

```
chi(t) - 1 is divisible by 2^j.
```

For an even-valued crossed derivation `D`, its standard depth bound is
`D(lambda_r) subset 2^r Z_2`. In the exact commutator formula, the additional
term `(chi(t)-1)D(x_s)` is therefore zero modulo `2^(j+1)`. For `s!=b` the
other term vanishes since `chi(x_s)=1`. At b, the head-square contribution
cancels the bracket coefficient modulo `2^(j+1)` because
`chi(b)^(-1) = -(1+2^alpha)` and `alpha>=2`. Thus the full derivative image is
killed on the graded layer. The existing finite-shadow criterion implements
the corresponding separation with a different coordinate normalization;
one should reuse it rather than assume a new global Lie instance.

The actual kernel tuple also extends to the b letter. Set

```
g = letter(partner(i)), q = [b,g], p = q^(2^n),
w = b^(2^(n+1)).
```

In the existing ordered five-factor tuple, its last two factors become one:
`([b,g][g,b])^(2^n)=1` and `[b,b]^(2^n)=1` exactly. The remaining three factors
are w in slot i and p in slots a and b. The checked mixed-power kernel identity
then proves that its actual derivative is one. This works also when slots
coincide; products accumulate in the original order. Only `i!=a` is required.

With separate authorization after the source freeze, this extension was
default-compiled in the temporary module
`/private/tmp/NPlaneKernelBExtension.lean`. Its olean and ilean were produced;
all three public pins use exactly `propext`, `Classical.choice`, and
`Quot.sound`, with no warnings. The public conclusions are:

```
nPlaneKernelTuple_filteredDerivative_b n letter i hi
nPlaneKernelTuple_filteredDerivative_all n letter i v hi
nPlaneKernelTuple_mem_correctionKernel_all n letter i v hi
```

This is a checked scratch result, not part of the frozen repository or its
already running source-only snapshot. Its exact ordinary-row conclusion is
the existing `nPlaneKernelTuple_character`, which had no v-exclusion.

## 6. Honest remaining integration boundary

At this audit point, the frozen final theorem is still conditional. The most
promising route is now composition of existing general results:

1. Construct coordinate crossed lifts on the free group/current free basis.
2. Apply the relation-free reading of the old full ambient image criterion to
   the actual relative defect, with every arithmetic and generation input
   discharged.
3. Lift the resulting finite-level correction to actual depth elements.
4. Remove the head ordinary row using the relator's coefficient
   `2+2^alpha`, and remove all other rows using the actual closed correction
   kernel and the all-v tuple extension. The maintained diagonal branch has
   the exact target-row equality used by the existing refinement proof.
5. Reuse basis persistence, the stage induction, and the limiting transfer.

For the all-bases orientation-only supply, head b-coordinate cleanup needs
only the exact b-coordinate equality forced by orientation, rather than a
complete prescribed ordinary matrix. That adapter should be proved explicitly
if the original all-bases supply is retained. Alternatively a fully raw stage
supply can feed a directly row-refined induction. These formulations are not
silently interchangeable in Lean.

No contradiction was found. The uniform image claim is mathematically
plausible and supported by the symbolic base check and existing span engine.
Plausibility, a primary-source comparison, and a scratch kernel extension do
not by themselves constitute a producer of the frozen supply.

## 7. Downstream scope after the ambient-stage theorem compiled

Update at approximately 16:15 UTC. The new `NPlaneAmbientScaling` module was
inspected together with its consumers in `MarkedCore/N.lean`, `ClearWide.lean`,
`NScalingAudit.lean`, `Certificate.lean`, `CompactCoV.lean`, and `GeneralMain.lean`.
The parent reports the complete scratch chain green and independently audited;
the independent `NPlaneAmbientScaling.log` was also read. All seven displayed
pins in that log use only the standard three axioms. This scope audit is not
the final source-only integrated-build verification, which the parent owns.

The new route proves the fully ambient supply, then restores exact ordinary
rows on the diagonal bases maintained by its induction. It does not need to
prove the older, stronger intermediate `NUnrestrictedStageSupply` first.
Leaving that unused definition without a producer is not a remaining premise
of the new scaling endpoint.

### What is now closed

- `nPlaneScalingHypothesis_general halpha` produces
  `NPlaneScalingHypothesis alpha h` for every natural `alpha>=2` and every
  `h>=0`, including rank four. Every two-adic unit determinant is allowed.
  There is no residual stage, scaling, cohomological, or arithmetic premise.
- This is genuinely **simultaneous integral** plane scaling: one continuous
  automorphism preserves `chiN` and realizes `diag(kappa,1)` on slots 2 and 3
  for **every** continuous Z2-valued character, with every other character row,
  including all handle rows, unchanged. It is stronger than scaling one chosen
  marking and stronger than the old weak sigma-row predicate.
- `nCorePlane_gl2_lift_general halpha hT` consequently realizes every
  `T : Matrix (Fin 2) (Fin 2) Z2` with unit determinant, in the exact predicate
  `NPlaneRealizes`. The old exact SL2 families supply the determinant-one part.
- `nStabParam_lift_general halpha hP` discharges the last hypothesis of
  `ClearWide.nStabParam_lift_of_scaling`. The core-mixing pair was already
  unconditional. Therefore every admissible `NStabParam` has its entire
  prescribed **ordinary nu-frame action** realized by one chi-preserving
  continuous automorphism. Its action is literally
  `nCoreMat P.g.transpose (nFrameMix P.p P.q m)`; the transpose is intentional.
- No peripheral-scaling axiom B8 is used by these new endpoints. Older comments
  prescribing a B8-based discharge route do not describe the new proof.

### Exact limitations of the conclusion

`NPlaneRealizes` quantifies characters to the torsion-free group Z2, not all
finite characters and not the full abelianization. Likewise
`NStabParam.nuAction` ignores the three torsion fields `tau`, `tauSigma`, and
`tauX2`. Thus `nStabParam_lift_general` is **not, as stated, a literal lift of
the entire torsion-sensitive matrix `P.rows`**. In particular, two admissible
parameters differing only in `tau` have identical conclusions. A theorem
identifying the automorphism's actual torsion-sensitive abelianization with
`P.rows` would require its own bridge; it is not supplied merely by the
all-Z2-character equation. This audit makes no nonexistence claim about that
further bridge.

The parameter family describes the rank-four core stabilizer action extended
with unchanged ordinary handle rows. It is not a classification or realization
of every possible all-rank stabilizer mixing arbitrary handles with the core.
Nor does the theorem say that the individual nonabelian handle generators are
fixed literally, or that the chosen automorphism belongs to `dnClearAuts` or
`dnClearAutsWide`. The narrower historical `NCoreMixHypothesis` cannot be
recovered this way: `nCoreMixHypothesis_not_of_mix` already proves that narrow
subgroup requirement false for genuine mixing strata.

The bound `alpha>=2` is load-bearing. This is the finite-alpha N family; it is
not an extension to `alpha=1`, whose diagonal parity and abelianized torsion
differ, nor a theorem about an infinite-alpha/N0 presentation obtained by
silently substituting a natural-number parameter.

### Effect on the overall campaign

This closes the optional stronger MC-N **plane and ordinary-frame stabilizer**
claim that had remained after the field-facing marked-correction theorem was
already complete. The weak `NScalingHypothesis` was independently available
from `NScalingAudit.nScalingHypothesis_of_sl2`; the required primitive-marking
correction already used `nCorePlane_sl2_lift`, `nMarkedCorrection_of_pair`, and
the proved mix families. The new result is therefore a genuine strengthening,
not a repair of a missing premise in the completed selected field theorem.

It does not change the selected-word family, the standing `RamifiedIData K`
scope, the field theorem's inherited arithmetic axioms, or the explicit
existential calibration of its maximal-pro-two realization. In particular,
this small-plane theorem alone does not turn the `GeneralMain` endpoint into
preservation of an arbitrary previously fixed core realization, and it does
not identify a changed M splice word with the old frozen M word. Publication
acceptance of the staged certificate artifacts remains a separate issue.

Recommended completion wording is: **strong N-plane GL2 and all admissible
NStabParam ordinary-character actions are proved, uniformly in alpha>=2 and
all handle ranks**. Avoid the unqualified phrase "the full torsion-sensitive
all-rank Smith-Witt stabilizer is lifted" unless that separately stronger
statement is actually supplied.

## 8. The separate torsion-sensitive bridge is now supplied

Update at approximately 16:44 UTC. The bounded follow-up has now compiled
`/private/tmp/NStabilizerFullLift.lean`, using the banked
`NPlaneGeneralScaling` and the checked scratch modules `DNAutomorphismCup`,
`NStabilizerFullRows`, and `NTorsionAdjust`. Its sole public pin is exactly
standard-three, and default compilation is warning-free. Repository integration
and final independent verification remain owned by the parent/audit lane.

`nStabParam_fullFrame_lift_general ha P hP` takes only `alpha>=2` and
`P.Admissible`. It returns one continuous automorphism of `DN alpha h`
preserving chi, satisfying the simultaneous ordinary nu-action, and satisfying
for **every marked generator** the literal equality

```
nPhiHom ha h (abMk (Psi (dnGen alpha h i))) = fullFrameMark P h i.
```

Here `fullFrameMark` contains all three torsion parameters, the prescribed
core free-coordinate columns, and the identity handle columns. Cup preservation
forces the coupled sigma/x2 torsion coordinates and zero handle torsion; the
exact N1 precomposition sets the remaining x1 torsion coordinate without
changing any ordinary row. The final theorem has no torsion-value, cup-form,
stage, or scaling premise.

Consequently the torsion-sensitive **core** `NStabParam` lift, extended by
identity on all handle abelianization columns, is now proved as well. The
earlier observation that ordinary characters alone do not imply this conclusion
remains valid: the new proof adds precisely the missing cup/N1 bridge. This is
still not an assertion about arbitrary all-rank handle-mixing stabilizers or
literal fixation of nonabelian handle generators. The alpha bound, narrow
subgroup caveat, and distinctions from the field endpoint's prescribed-original-
realization question remain unchanged.
