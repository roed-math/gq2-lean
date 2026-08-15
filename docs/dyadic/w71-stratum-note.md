# W71: the even stage layer on the third stratum

Lane W71-STRATUM.  New module `GQ2/Dyadic/Instances/EvenStratumPoint.lean`; no edits to existing
files.  Prefix `evenStratum`.  **18** declarations (17 theorems and the model head vector
`evenStratumHeadVec`), of which the 17 theorems carry an axiom pin, all inside the committed
even axiom sets: the standard three, plus `tateDualityAt` and
`hilbertSymbol_normCriterion_finiteDyadic` on the cup-form line, plus
`Foundations.absGalQ2_localEulerCharacteristic` on
`evenStratum_orientedEquivN_one_of_forwardGeneratorData`.  The file also carries five comparison
pins on declarations from other modules, which is why it has 23 `#print axioms` lines.  (Count
corrected from "19 declarations, all pinning" by W72-HOUSE, watch round 9, machine-checked with
`scripts/mirror.sh check`.)

## 0.  Headline

The ticket's two priced replacements are **both mis-priced**, and the ticket's fourth option is
the true one, in a precise and limited sense.

> **`evenStratum_no_adaptedModelEquiv`**: at every field whose cyclotomic range lies in
> `evenRangePrin 2`, and at every handle count, there is no linear isomorphism carrying the field
> cup form to `evenFrameGramModel h`.

That is the conclusion of `evenFrameAdaptedModelEquiv`, the shared step of **all three** even
frame producers in the tree.  So the even stage layer's frame step is refuted on the whole third
stratum, not merely unproved, and not merely at the surviving point.

The classification at the surviving point is **neither proved nor refuted**.  What is refuted is
one route's frame step.  I was careful to state nothing about
`Nonempty (OrientedContinuousMulEquiv (chiN 1 h) chiCycKTwo)` in either direction, and nothing in
the module does.

## 1.  Which replacement is binding: neither

**(a) The `q = 4` stage-level frame is a non-item.**  No file under
`GQ2/Dyadic/Instances/StageAbstractionEven*.lean` consumes a `MarkedCore.NFrame`.  I checked this
exhaustively: `NFrame` is taken as a *term* by exactly three declarations tree-wide
(`NFrame.toNDecomposition`, `demushkinQ_DN_nFrame`, `nonempty_equiv_DN_self_of_nLabHypothesis`),
all in the abelianization layer, and every other mention is inside `Nonempty`/`IsEmpty`.  The
stage layer's frame is `StageGeneric.Frame` (`StageAbstraction.lean:793`), whose three fields are
generators in the target group, their character rows, and level-two generation.  It has no
torsion slot at all, so there is nothing for a `ℤ/2 ⇝ ℤ/4` change to act on.

Wave 69's cost estimate conflated the two objects: it read the emptiness of `NFrame 1 h` as a
stage-level obstruction and priced a lane against it.  Wave 70's `NFrame4` is correct and is what
the `q`-invariant needs; it simply has no stage-level consumer to lift to.  **The stage layer at
`α = 1` never wanted an `NFrame`.**

**(b) The relator-shift factorization is not reached.**  `evenRawStageShift_n` is genuinely false
at `α = 1` and its own file says so twice, but it sits downstream of the frame, and the frame is
where the route stops.  The substitute is not the next thing to build.

**(c) What is actually binding** is one arithmetical fact, upstream of both:

    evenStratum_four_dvd_nUnit_add_one_iff :  4 ∣ nUnit α + 1  <->  2 <= α  (for α >= 1).

At `α = 1`, `nUnit 1 · 3 = -1` gives `nUnit 1 ≡ 1 (mod 4)`, not `≡ -1`.  Every `2 ≤ α` binder in
the `N` stage layer is carrying exactly this: the parity table
(`evenDegreeN_parity_nUnit`), the `κ ≠ 0` binder (`evenEndpoint_kappa_of_rangeN`), the shadow
determination, the deep row supply, and the derivation-kernel diagonal row
(`evenKernel_vN_diagonal_add_one_dvd_four`, which the residual supply consumes).  Wave 69's note
listed several of these as separate leaves; they are one fact seen five times.

Consequence worth recording: **the `α = 1` `N` parity table is the zero table**
(`evenStratum_parity_nUnit_one`), where for `α ≥ 2` it has a single mark at the twisted index.

## 2.  Why it is a refutation and not a gap

Three committed steps, composed:

1. On the third stratum the range lies in `evenRangePrin 2`, which is by definition the kernel of
   the mod-four reduction, so the mod-four cyclotomic character is trivial and
   `cyclotomicModFourClassKTwo = 0` (`evenStratum_kappa_eq_zero`).
2. `frattiniFrameCup_kappa` is committed **with no hypothesis**: the diagonal of the field cup
   form is cupping with `κ`.  With `κ = 0` the form is therefore alternating
   (`evenStratum_cup_self_eq_zero`).
3. `evenFrameGramModel_self` is committed and its own docstring reads "the model Gram is not
   alternating: its diagonal is the `x₀` coordinate".  So the model has a vector of self-pairing
   `1`.

An alternating form and a form with a nonzero diagonal vector are not isomorphic.  The proof is
four lines and uses no new arithmetic.

This also explains, after the fact, why `evenEndpoint_kappa_of_rangeN` needs `2 ≤ α`: it derives
`κ ≠ 0` from the parity of `nUnit α`, and at `α = 1` that parity is `0`.  The same hypothesis
shape gives the opposite conclusion at the surviving point
(`evenStratum_kappa_eq_zero_of_rangeN_one`), which is the sharpest way to state the boundary.

## 3.  What the surviving point now costs

The positive half.  Tracing the classification chain at the `N` row, `2 ≤ α` is consumed in
exactly three places above the model: the stage base, the climb, and the residual supply.  The
model layer itself is **fully paid at `α = 1`** by wave 70, and both the rigidity step and the
orientation step were already stated at `1 ≤ α`.  So:

> **`evenStratum_orientedEquivN_one_of_forwardGeneratorData`**: given
> `Nonempty (NForwardGeneratorData 1 h χ_cyc)` and `[K : ℚ₂] = 2 + 2h`, the oriented equivalence
> `chiN 1 h ≃ χ_cyc` follows.

That is the whole remaining price: **one `Prop`**.  Read against §2 it also says where a future
lane must attack.  The datum has to be produced by some route other than the committed
frame-and-climb, because that route's frame step is provably unavailable on this stratum.  A lane
that tries to repair the frame at `α = 1` is spending itself against a refutation.

## 4.  Model field

`ℚ₂(i)`, wave 69's `evenUnramKNegOne`.  Over the standing profinite binders and **no reciprocity
bundle** (the range bound comes from the square root of `-1` directly):
`evenStratum_kappa_eq_zero_KNegOne` and `evenStratum_no_adaptedModelEquiv_KNegOne`.  This is the
tree's first named field at which the even frame step is known to be unavailable rather than
unproved.

## 5.  Stale prose found, for the orchestrator

I edited nothing.

> **[W72-HOUSE, watch round 9.]  This section is discharged.**  The orchestrator applied the
> repair later in the same wave, at `e6d10612`, and the paragraph now carries a correction
> notice.  Two points for whoever reads the applied text: it is broader than the repair suggested
> here (it also records `demushkinQ (DN 1 h) = 4` against `= 2` on the `M` row), and its notice
> is headed "⚠ **Corrected at wave 70**", whereas the correction was applied at **wave 71**
> against wave 70's landings.  Left as a finding rather than edited, because that file may be in
> flight this wave.

**`EvenForwardRouteSkeleton.lean:77-80`** is now false.  It reads that at `α = 1` the `N`
relator's "mod-2 quadratic initial form vanishes, and the `N` core is not Demushkin".  Wave 70's
`evenAlphaOne_isDemushkin_DN` proves the `N` core **is** Demushkin at every handle count, and
`evenAlphaOne_residualN_false` records the refutation of the residual that said otherwise.  The
form does not vanish; it is alternating.  Suggested repair: keep the two thresholds sentence, and
replace the parenthetical with "at `α = 1` the two rows no longer share one Gram, and `2 ≤ α` in
the committed `isDemushkin_D{N,M}` is a convenience of uniformity (`EvenAlphaOne.lean` §10.2)".

This is the wave-64 pattern again (docstrings outrunning their proofs), and it is a *statement*
docstring rather than a headline, so it is in the class the era traps say to watch.

## 6.  Queue items this lane produces

1. **Refute `IsCupAdapted` outright, not only the model equivalence.**  I proved the model
   equivalence unavailable; the stronger statement is that no cup-adapted `StageGeneric.Frame`
   exists on the stratum.  The route is: `IsCupAdapted` forces `P c c = c₀`, the alternating
   property forces `c₀ = 0` for every character, and nondegeneracy of the cup form makes the
   coordinate map injective, so `|H¹| ≤ 2^(coreRank h - 1)`, contradicting
   `card_H1_zmodTwo_maxProTwoGalK`.  That is one lane; the pieces are all committed.
2. **Wave 69 queue item 2 (the `demushkinQ`-parametrised frame) should be closed as a
   non-item**, per §1
   above, and item 1 is already discharged by wave 70's `evenAlphaOne_residualN_false`.
3. **Decide what the even route's status prose should now say.**  Wave 69 proposed a sentence
   ending "at `α = 2` the only candidate is `DN 1 h`, for which the frame layer is empty".  That
   sentence is about the wrong frame.  It should read that the stage layer's frame step is
   refuted on the stratum, and that the classification there reduces to a forward-generator datum
   that the committed route cannot supply.
4. **`q ≥ 8` is unchanged**: no `2 + 2^a` is a power of two above `4`, so the boundary theorem
   still says the present families cannot be stretched there.
