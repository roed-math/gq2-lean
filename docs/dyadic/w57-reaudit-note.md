# W57-REAUDIT: an adversarial re-audit of the even route after wave 56

Wave 57, lane REAUDIT, against `e86d253c`.  Working tree `claude/w57-reaudit`.  Everything below
was measured, not recalled: every axiom print was re-elaborated at the tip, every claim about a
Lean statement was read off the statement, and every finding that could be made into Lean was
made into Lean and elaborated clean.

## Headline verdict

**The third instance exists, and it is in the artefact the campaign tells the paper to quote.**
W56-RECUT published `EvenRouteCarriedDeep{N,M}` as the corrected carried-input list, retracting
the wave-54 bundles on the `alpha = 2` stratum and stating the corrected ones at `alpha >= 3`
with two fields, one of which is the slot-`0` flip demand.  W56-SLOTZERO, merged two commits
later in the same wave, refuted that demand at **every** `alpha >= 2`.  Nobody composed them.
The composition is committed here (`evenRouteAudit_not_carriedDeep{N,M}`): **the corrected
bundle is false at every field of branch depth `alpha >= 3`**, so `evenRouteCarried_orientedEquiv{N,M}`
are vacuous outright and the `_dichotomy` forms retain content only on the depth-`2` stratum
where their conclusion is empty.  The wave-56 owner memo's sentence "the paper-facing structures
are also corrected and minimal now" is the one that must be withdrawn.

**Second: the sharpest-bound doctrine has not been applied to the object it was written for.**
The campaign's single decisive input, `EvenClimbResidualSupply`, is asserted in six places to be
unrefuted, with one justification: `EvenAlphaTwo.lean` §6.1, that neutral corrections satisfy the
slot-`0` digit bound rather than colliding with it.  That justification survives its own sharpest
bound (`evenRouteAudit_neutral_meets_refined_digit`), but the conclusion drawn from it is too
strong.  The slot-`0` mechanism **does** reach the residual supply, once its trivial-shift-word
hypothesis is dropped, which it can be: `evenRouteAudit_residual_digit_necessary` proves that the
supply forces the residual's own character to be trivial to `k + alpha` digits, while
`evenRouteAudit_residual_digit_automatic` proves the tower already gives `k + alpha - 1`.  **The
residual supply is a one-digit character demand at coordinate `0`** - the same coordinate, the
same one digit and the same square as the two refutations the campaign has already met.  This is
**not** a refutation, and I do not claim one; it is where the decisive question actually sits.

Everything else holds.  The census is exactly 11, no wave-56 file consumes an unflagged census
axiom, the five wave-56 modules are pairwise independent in the import graph so no circularity is
possible, and the class-four obstruction really does quantify over the census's own object.  Two
further overstatements are recorded, both about coverage.

---

## (a) THE SHARPEST-BOUND SWEEP: **FAIL**

The sweep enumerated every place the current tree concludes that something survives, is
consistent, is not refuted, is unobstructed, or is non-vacuous: about thirty such sentences in
the even route's Lean, about forty in `SqCore`, and about twenty in the campaign log's sections
65 and 66 together with the owner memo's wave-56 block.  Each was checked against the sharpest
bound the tree owns on its object.  Three fail.

### a.1 The corrected carried-input list, refuted by its own wave (**the third instance**)

`EvenRouteCarried.lean` §4 publishes

```
structure EvenRouteCarriedDeepN … where
  family : EvenRouteDeepFamilyN h K          -- Hfam, guarded, at alpha >= 3
  flip   : EvenRouteDeepFlipN h K            -- EvenDigitFlipSupplySlotZero alpha, guarded
```

and its §6 says of the pair: *"the corrected artefact is true where the published one is false,
and says nothing there rather than something unsatisfiable."*  That sentence is about the
depth-`2` stratum and is correct there.  Above it, the sharpest bound the tree owns on
`EvenDigitFlipSupplySlotZero` is not the wave-55 one the file was cut against but
`evenSlotZero_not_slotZeroSupply_{N,M}` (W56-SLOTZERO), which refutes it at **every** `alpha >= 2`
as soon as one stage tuple exists.  At a field of depth `alpha` a stage tuple is not an
assumption: `evenEndpoint_nStageBase` and `evenDeepIsotropy_mStageBase` build one from `hev` and
the range identity alone, at every `alpha >= 2`.  Committed here:

| statement | content |
| --- | --- |
| `evenRouteAudit_not_deepFlip{N,M}` | `¬ EvenRouteDeepFlip{N,M} h K` at any field of branch depth `alpha >= 3` |
| `evenRouteAudit_not_carriedDeep{N,M}` | `¬ EvenRouteCarriedDeep{N,M} h K` there |
| `evenRouteAudit_orientedEquiv{N,M}_vacuous` | the exact binders of `evenRouteCarried_orientedEquiv{N,M}`, including their `hnotTwo`, already refute the bundle those theorems consume |
| `evenRouteAudit_dichotomy{N,M}_forces_two` | holding the corrected bundle forces the produced branch depth to be `2`, where the dichotomy's conclusion is the empty implication |

So of the two strata, the corrected artefact is false on one and vacuous on the other.  No
committed statement is wrong: `evenRouteCarried_orientedEquivN` is a true implication with an
unsatisfiable hypothesis, exactly as `evenRoute_orientedEquivN` was after wave 55.  What is wrong
is the description of it, in three places (see (e)).

The mechanism of the miss is structural and is the wave-55 pattern at wave-56 scale.  The five
wave-56 modules `EvenRouteCarried`, `EvenSlotZero`, `EvenAlphaTwo`, `GradedFourMirror`,
`GradedLatticeWide` are **pairwise independent in the import graph** (verified: all twenty ordered
pairs, by mechanical transitive closure, closure sizes 619 to 709 modules).  No lane could see any
sibling's result, and the merges went RECUT (`3e5ee28e`), ALPHA2 (`9c22bdca`), SLOTZERO
(`51861947`), MIRROR (`a657ea44`), WIDEN (`84fa2e5f`) with no pass back over the earlier ones.

### a.2 The residual supply: the mechanism reaches it, one digit short

Six places assert that nothing in the tree refutes `EvenClimbResidualSupply`
(`EvenAlphaTwo.lean` lines 45, 66, 453-454; campaign log 11119 and 11193; owner memo 33-34), and
all six rest on one argument, `EvenAlphaTwo.lean` §6.1: *"neutral corrections satisfy the
coordinate-`0` digit bound rather than colliding with it … the mechanism that kills the flips is
satisfied, not violated, by everything the climb actually asks for."*

Two things had to be checked, and they come out differently.

**The argument does survive its own sharpest bound.**  §6.1's committed lemma
`evenAlphaTwo_neutral_slotZero_digit` concludes only `2 ^ (k + 1) ∣ chi g - 1`, which is the
*generic* wave-55 form of the bound - the same generic-versus-refined slip wave 56 diagnosed.
`EvenAlphaTwo.lean` does not import `EvenSlotZero.lean`, so it could not have used the refined
form.  Redone at the refined bound: neutrality gives `2 ^ (k + 1 + s)`, so at `s = alpha - 1`
every coordinate meets `evenSlotZero_digit`'s `2 ^ (k + (alpha - 1))` with a digit to spare
(`evenRouteAudit_neutral_digit_sharp`, `evenRouteAudit_neutral_meets_refined_digit`).  §6.1's
conclusion is right.

**But the conclusion drawn from it is too strong.**  The refutation is not confined to supplies
that demand a sharp digit at a trivial-shift-word correction.  The hypothesis `hrow : dbar = 1`
of `evenFlip_slotZero_sq_mem_commutator` is removable: the shift word of *any* depth correction is
its slot-`0` square modulo commutators (`evenRouteAudit_dbar_slotZero_sq`).  Applied to the
neutral correction the residual supply produces, that gives

* `evenRouteAudit_residual_digit_necessary`: `EvenSharpNeutralResidualReachable Wc` at
  `s = alpha - 1` forces `2 ^ (k + alpha) ∣ chi r - 1` for any representative `r` of the residual;
* `evenRouteAudit_residual_digit_automatic`: the residual lies in `zLayer G k = lambdaImage G k
  (k+1)` (`evenRouteAudit_residual_mem_zLayer`), so `evenSharp_map_le_deep` already gives
  `2 ^ (k + alpha - 1) ∣ chi r - 1`.

**One digit.**  The residual supply is exactly the demand that the residual's own character be one
digit deeper than the tower forces, at coordinate `0`, and the digit is the one a square costs.
That is the shape of `evenSlotZero_not_slotZeroSupply` and of `evenSharp_not_imageRelLe_imChiM`
before it.

I want to be exact about what this does and does not establish.  It does **not** refute the
supply: nothing in the tree pins the residual's own character level, and if the residual is
deeper than `k + alpha - 1` the demand is met with room.  What it does is falsify the *reason*
the campaign gives for the supply's survival, and locate the decisive computation: **what is the
exact two-adic level of `chi` on `evenSharpNeutralResidualElement Wc`?**  A lane that computes
that in the GAP model of W56-SLOTZERO settles the campaign's top question in either direction.
The sister lane attacking the supply should be told this; it is the difference between an open
question and a one-line feasibility problem.

### a.3 The class-four soundness is stated over less than the tree's own `γ₂(im Φ)`

`GradedLatticeWide` (WIDEN, merged last) fixes the campaign's meaning of the achievable object:
`γ₂(im Φ) = ⟨⁅im Φ, im Φ⁆, Φ(x₁)²⟩`, the `x₁`-square being *"the only non-commutator generator"*,
and `selGaTwoIm` adjoins it explicitly.  `GradedFourRow` and `GradedFourMirror` (MIRROR, merged one
commit earlier) state their model-independent soundness over `rowGaTwoOf (…)` alone - the
commutator subgroup **without** the square - while describing it as *"the whole commutator
subgroup `γ₂(im Φ)` … the sigma-slot dressing needs no constraint whatsoever"*
(`rowFour_commutator_le`, `mirFour_commutator_le`, `dblFour_commutator_le`,
`rowWide_commutator_le`, and the six `…_gaTwo` forcings that consume them).  Two committed files
disagree about what `γ₂(im Φ)` is, and the later one is the sharper.

The gap is real as a matter of statement and empty as a matter of substance.  All four markings
carry `sigFourY` in the `x₁` slot and `evenRouteAudit_sigFourY_sq_mem` puts its square in
`rowGaTwoSub`, so the four soundness statements extend to the WIDEN-shaped object at no cost
(`evenRouteAudit_{rowFour,mirFour,dblFour,rowWide}_gaTwoIm_le`).  Consumers should cite those.

### What the sweep cleared

For completeness, because an audit that only lists faults is not an audit.  Checked against their
sharpest bounds and **passing**: the `alpha = 2` fibre inhabitation (`evenAlphaTwo_top_admissible`,
`evenAlphaTwo_{top,imChiN_two}_forces_two`) - the criterion is an iff and the classification
hypotheses are met exactly, so no group-theoretic strengthening can empty the stratum; the
doubly-uncleared row's two odd dressings (`dblFour_forcing_nonvacuous`), which are consistent with
`sqArbFrame_sigma_forced_double` because the forcing constrains only *killed* dressings, and whose
soundness survives a.3's widening; `rowFour_forcing_nonvacuous`, `mirFour_forcing_nonvacuous`,
`rowWide_forcing_nonvacuous` likewise; and the wave-55 `N`-bundle collapse
(`evenRouteWitness_carriedN_of_atDepth`), which W56-RECUT correctly re-reads as delivering falsity
rather than preventing it.

---

## (b) NON-VACUITY OF THE NEW ROUTE: **PASS-WITH-RISK**

The question here is whether the statements *around* `EvenClimbResidualSupply` are vacuous,
over-quantified or mis-binder'd, not whether the supply is true.

**The supply's own quantifier shape is clean, and this is now a theorem.**  The definition
quantifies over every level `k >= 3`, every stage tuple and **every** depth-`s` admissible
correction.  A `∀` over corrections where one would do is exactly the wave-52 and wave-56 binder
shape, so it had to be checked rather than noted.  `evenRouteAudit_residual_iff_actualDefect`
proves the supply **equivalent** to "an actual-defect supply exists at every level `k >= 3`",
which is precisely what `evenClimb_defectReachable` consumes: by the torsor criterion
`nonempty_evenSharpActualDefectSupply_iff_residual` the choice of correction is immaterial in both
directions.  So the supply neither over-quantifies nor under-quantifies, and it is not vacuous in
its correction binder either (`evenRouteAudit_residual_correction_nonempty`: depth-`s` admissible
corrections always exist, `evenSharpDeepAdmissible_nonempty`).

**The re-cut endpoints are `alpha = 2` only, and the frontier does not say so.**  The two per-field
endpoints off the supply are `evenAlphaTwo_orientedEquiv{N,M}_two_of_residual`, both at `alpha = 2`
with `hrange` fixed at `imChiN 2` / `imChiM 2`.  At `alpha >= 3` the only endpoints off the supply
are `evenAssembly_orientedEquiv{N,M}` and `ev1eFinal_orientedEquiv{N,M}`, all four of which carry
the **uniform-in-`K`** `Hrange` that wave 52 refuted and that the tree itself records as
inconsistent (`StageAbstractionEvenClimbFinal.lean` §, `StageAbstractionEvenPerK.lean` §).  So, as
committed, **no per-field endpoint above the depth-`2` stratum runs off `EvenClimbResidualSupply`**;
the `alpha >= 3` per-field endpoints are `EvenRouteCarried`'s, and (a.1) refutes their input.  The
repair is cheap and should be a wave-57 build item, not an audit item:
`evenAlphaTwo_forwardGeneratorData{N,M}_of_residual` are already stated at general `alpha >= 2`
and per field, so composing them with `evenEndpoint_nStageBase` / `evenDeepIsotropy_mStageBase`
and `nonempty_orientedEquiv{N,M}_evenDegree_of_forwardGeneratorData` gives the general-depth
per-field endpoint in about six lines.

**No concrete field instantiates the re-cut endpoints.**  `EvenAlphaTwo.lean` §4 exhibits `alpha =
2` fields inside Lean only at **odd** degree (`evenAlphaTwo_eq_two_of_odd_finrank`), and the
endpoints' `hev : finrank = 2 + 2h` excludes odd degree; the even-degree `alpha = 2` witnesses
(`ℚ₂(√5)`, `ℚ₂(√−2)`) are Magma measurements.  Meanwhile wave 55's committed field-level model
`evenRouteWitness_orientedEquivN_sqrtNegTwo` is now believed vacuous - on the same measured basis.
So the campaign currently has **no** Lean-checked field model on either branch for the live route,
and wave-57 queue item (2) is the right response.

**`EvenAlphaTwo.lean`'s own summary overstates.**  Its closing paragraph reads *"its endpoints are
**no longer vacuous**: they carry `EvenClimbResidualSupply 1`"*, and the next sentence admits the
input is unproved.  Carrying an unproved input is not non-vacuity; the accurate form is "no longer
**known** to be vacuous".  Recorded as defect 6.

**Verdict (b): PASS-WITH-RISK.**  The supply's binders are provably the right ones, which is more
than the previous audit could say for any wrapper.  The risk is that the re-cut reaches only the
`alpha = 2` stratum while the frontier reports it at every depth, and that no concrete field model
exists for it.

---

## (c) THE CLASS-FOUR RESULTS: **PASS-WITH-RISK**

### c.1 Does the obstruction's quantifier match the census's object?  **Yes.**

The wave-54 census (`docs/dyadic/w54-gamma2-note.md` §5.1) computed, at each of the `33792`
residual corners, the `Z/8`-span of the increments of *"the ten frame-slot commutators, the fifty
triple commutators, the `x1`-square and its five commutators"*.  `sqRelWord_selGaTwoIm_ne_one`
quantifies over `selGaTwoIm = rowGaTwoOf (closure (range selLiftWit)) ⊔ closure {x₁-square}`,
which is a **subgroup containing that whole generating set** (all ten frame-slot commutators and
all fifty triple commutators lie in the commutator subgroup of the closure; the square is adjoined;
its five commutators follow because the square lies in the closure).  The theorem therefore
quantifies over at least the census's object and over group elements rather than lattice spans, so
it is strictly stronger.  There is no residual mismatch of the kind wave 55 left - that one was
`selLamThreePlus` under-approximating in the `(h, i)` direction, and WIDEN both proves the gap real
(`selLamThreePlus_not_commP_zero_handleV`) and discharges the lattice.  `selGaTwoIm` is general in
the handle count `h`, so the certification is not confined to `h = 1`.

One residual, and it is small.  The theorem applies at a corner only if that corner satisfies its
four consumed pairings `h₅`, `h₇`, `h₅'`, `h₆'`.  The census's ten mod-2 classes all have
`A = B = 0` and `P = R = 1`, which gives `h₅` and `h₅'` immediately, and gives `h₇` and `h₆'`
because every class also has `P·D·F = 0` and `E·P·C = 0` mod 2 - which I checked by hand off the
note's own table, and which is **not** a committed statement.  `GradedLatticeWide` §6 runs exactly
one corner end to end.  A one-line `decide` over the ten classes would close this; until then the
sentence "the residual-corner census is certified in the census's own terms" is certified at one
corner and inferred at the rest.

### c.2 The four selected rows' coverage: **the claim overshoots by one row**

| row `(t, s)` | committed statement | handle count |
| --- | --- | --- |
| `(0,0)` cleared | `sqArbFrame_sigma_forced_nuSel` | **`DSq 1` only** |
| `(0,1)` uncleared `v` | `sqArbFrame_sigma_forced_row`, `…_row_wide` | `DSq h`, every `j` |
| `(1,0)` mirror | `sqArbFrame_sigma_forced_mirror` | `DSq h`, every `j` |
| `(1,1)` doubly uncleared | `sqArbFrame_sigma_forced_double` | `DSq h`, every `j` |

`GradedFourMirror.lean`'s headline says *"every selected row is now covered, at every handle
count"*, and the table two lines below it says the cleared row is *"unchanged"* at `h = 1`.  The
campaign log §66 repeats the headline twice (the W56-MIRROR section title and body, and the Live
frontier) and the owner memo repeats it once, while §66's own wave-57 queue item (4) asks for
"the cleared row at general handle count".  Section 66 contradicts itself.  The mathematics is
untouched - the missing case is, as the queue says, a fourth instantiation with no new content -
but three published sentences claim a coverage the tree does not have.

### c.3 Handle-count generality elsewhere: **holds**

`sqRelWord_mirTuple` and `EichRefutation.handleWord_eq_single` really do make the row solves,
verdicts, bit, increment, pivot anchor and frame identifications `h`-generic at the three new
points, and `selGaTwoIm` and `sqRelWord_selGaTwoIm_ne_one` are `h`-generic too.  Only the cleared
row is stuck.

**Verdict (c): PASS-WITH-RISK.**  The quantifier matches and the certification is honest at the
level of the theorem; the risks are the un-committed ten-class check (c.1) and the coverage
overstatement (c.2).

---

## (d) CIRCULARITY AND AXIOM DISCIPLINE: **PASS**

**Census.**  Exactly **11 committed axioms**, all in `GQ2/Foundations/Axioms.lean` (lines 104, 124,
165, 178, 204, 231, 259, 300, 359, 388, 433).  A repository-wide grep with modifier-aware patterns
finds no `axiom` declaration anywhere else; the other hits are docstring prose that begins a
wrapped line with the word.  `scripts/check_axioms.sh` expects 11 and matches.

**Sorries.**  Zero real `sorry` under `GQ2/` or in `GQ2.lean`.  The 137 raw hits are prose or the
`sorryAx` name literals inside `GQ2/AxiomLedger.lean`, which is the auditing machinery itself.  Two
real sorries exist in `Challenge.lean`, by design (the comparator challenge statements, discharged
in `Solution.lean`); noted only because `scripts/check_axioms.sh` scans `GQ2` and `GQ2.lean` and
therefore cannot see drift in those two files.  No `native_decide` and no `Lean.ofReduceBool`
anywhere in `GQ2/`.

**Does any wave-56 file consume a census axiom its report did not flag?  No.**  Re-elaborated at
the tip:

| file | prints | reaching a census axiom | file's own claim |
| --- | --- | --- | --- |
| `EvenAlphaTwo.lean` | 23 | 7 | "the ambient three plus … the committed census axioms the endpoint chain already consumes" - true, but names none |
| `EvenSlotZero.lean` | 19 | **0** | makes no claim; needs none |
| `EvenRouteCarried.lean` | 58 | 23 | names exactly the four; correct |
| `GradedLatticeWide.lean` | 23 | **0** | "all std-3 or a subset; no census axiom is reachable"; correct |
| `GradedFourMirror.lean` | 230 | - | "all 230 committed prints are std-3 or a subset"; count matches |

The only axioms reached anywhere in the wave-56 even files are the four the endpoint chain already
carries: `hilbertSymbol_normCriterion_finiteDyadic`, `tateDualityAt`,
`absGalQ2_isTopologicallyFinitelyGenerated`, `absGalQ2_localEulerCharacteristic`.  Nothing new.
The one hygiene gap is that `EvenSlotZero.lean`'s §5 states no expected pin set at all, so its
prints are unfalsifiable as documentation; it happens to be clean.

**Circularity.**  None, and this time it is mechanical rather than argued: the five wave-56
modules are pairwise non-reaching in the import graph (twenty ordered pairs, all negative), so no
lane's conclusion can be an input to another's.  The carried inputs `EvenKernelDerivationFamily`,
`EvenKernelRelatorKill`, `EvenDigitFlipSupplySlotZero` and `EvenClimbResidualSupply` mention no
`chiN`, `chiM`, `DN`, `DM` or `OrientedContinuousMulEquiv`; the last of them is a statement about
corrections and residuals in `maxProPQuotient 2 (GalK K)` alone.  The new file here is a leaf and
adds no cycle.

**Verdict (d): PASS.**

---

## (e) CLAIM VERSUS PROOF, sections 65 and 66 and the owner memo: **FAIL**

Two waves running found claims outrunning proofs; the instruction was to assume a third.  There
are four, and the first is the one that matters.

### Overstatement 1 (the third instance): "the paper-facing structures are also corrected and minimal now"

> Owner memo, "Status at wave 56", paragraph on the `h >= 1` route, final sentence.
> Campaign log §66, W56-RECUT: *"The paper-facing structures are re-cut to two fields each with
> identical binders, guarded by the range hypothesis, and proved EQUIVALENT to the single-depth
> data the endpoints consume, which is more than the audit asked for."*

Both sentences are true of the *shape* of the structures and silent about their *satisfiability*.
`EvenRouteCarriedDeep{N,M}` are false at every field of branch depth `alpha >= 3` (a.1) and hold
only vacuously at depth `2`.  A reader who does what the memo says - quotes the corrected
machine-checked list - quotes a list no field satisfies.

**Repair:** withdraw "corrected and minimal now"; say that the re-cut fixed the binders and the
isotropy field, and that the flip field it retained was refuted later in the same wave, so the
artefact needs a further re-cut onto `EvenClimbResidualSupply` before the paper quotes it.  The
Lean for the retraction is `evenRouteAudit_not_carriedDeep{N,M}` and
`evenRouteAudit_orientedEquiv{N,M}_vacuous`.

### Overstatement 2: "the endpoints are re-cut onto it" at every depth

> Campaign log §66 Live frontier: *"What is live is one supply per branch,
> `EvenClimbResidualSupply`, together with `Hfam`, at every depth including `alpha = 2`; the
> endpoints are re-cut onto it and nothing refutes it."*
> Owner memo: *"Both endpoints are re-cut onto that weaker supply."*

§66's body is accurate - *"Both `alpha = 2` endpoints are therefore re-cut"* - and the frontier and
the memo drop the qualifier.  Only the `alpha = 2` endpoints are re-cut; above the stratum the
per-field endpoints still carry the refuted flip, and the general-depth endpoints off the supply
carry the wave-52 uniform `Hrange` and are vacuous for that reason (b).

**Repair:** "the `alpha = 2` endpoints are re-cut onto it, and the general-depth per-field
endpoint is one composition away".

### Overstatement 3: all four class-four rows at every handle count

> Campaign log §66, section title *"W56-MIRROR: all four rows, at every handle count"* and body
> *"so all four selected rows at class four are covered at every handle count and every handle
> index"*; Live frontier *"extended to all four selected rows at every handle count"*; owner memo
> *"All four selected rows at class four are now covered at every handle count"*;
> `GradedFourMirror.lean` headline *"every selected row is now covered, at every handle count"*.

False for the cleared row `(0,0)`, which is `DSq 1` only, as the same file's table and the same
section's queue item (4) both say (c.2).

**Repair:** "the three rows wave 55 left open are covered at every handle count; the cleared row
remains at `h = 1`".  One sentence in `GradedFourMirror.lean`'s headline, one in §66, one in the
memo.

### Overstatement 4: the vacuity of the wave-55 `N` witness is measured, not proved

> Campaign log §66: *"the other is at `alpha = 2`, which makes the wave-55 audit's own
> non-vacuity witness on that branch a vacuous theorem."*

`EvenAlphaTwo.lean` §5 is careful here (*"`hrange` is what the census measures"*); the log states
it flatly.  The tree contains no proof that `ℚ₂(√−2)` has branch depth `2`, only a Magma
measurement, and the witness also carries an unproved classical sign condition.  Low, but it is
the same class of slip: a measurement reported as a theorem.

**Repair:** "which the census measures to be at `alpha = 2`, making the wave-55 witness vacuous on
that measurement".

### What the prose gets right

The `alpha = 2` criterion and its census, the flip refutation and its one-digit mechanism, the
statement that `Hup` was only sufficient for what the climb consumes, the retraction of the
wave-54 bundles on the depth-`2` stratum, the scope-gap diagnosis and its discharge by WIDEN, the
`A`- and `B`-evenness theorem, the sidedness and interaction corrections to wave 55's displacement
forecast, the "four of fourteen hypotheses consumed" claim, the axiom and sorry accounting, and
the process note itself are all accurately stated and all check out.  The doctrine sentence -
*"whenever a bound is used to conclude that a possibility survives, verify it is the sharpest
bound the tree already owns"* - is exactly right, and (a.2) is what it looks like when applied to
the campaign's own top object.

**Verdict (e): FAIL**, four overstatements, one of which reaches the paper.

---

## Ranked defects and risks

| # | Severity | What | Where | Repair |
| --- | --- | --- | --- | --- |
| 1 | **HIGH** | `EvenRouteCarriedDeep{N,M}`, the published corrected carried-input list, is FALSE at every field of branch depth `alpha >= 3`; `evenRouteCarried_orientedEquiv{N,M}` are vacuous and the `_dichotomy` forms keep content only where their conclusion is empty | `EvenRouteCarried.lean` §§3-5 and the header table; log §66 W56-RECUT; owner memo "corrected and minimal now" | retraction committed (`evenRouteAudit_not_carriedDeep{N,M}` etc.); re-cut the bundle's `flip` field onto `EvenClimbResidualSupply` in a build lane |
| 2 | **HIGH (open question, re-framed)** | the residual supply is a **one-digit** character demand on the residual at coordinate `0`, not an unreached hypothesis; the campaign's stated reason for its survival does not cover the mechanism | `EvenAlphaTwo.lean` §6.1; log 11119, 11193; memo 33-34 | committed: `evenRouteAudit_residual_digit_{necessary,automatic}`; hand the level computation to the lane attacking the supply |
| 3 | **MEDIUM** | "all four selected rows at every handle count" is false for the cleared row `(0,0)`, which is `DSq 1` only | `GradedFourMirror.lean` headline; log §66 twice; owner memo | one sentence in each; the missing case is a fourth instantiation |
| 4 | **MEDIUM** | "the endpoints are re-cut onto `EvenClimbResidualSupply`" holds only at `alpha = 2`; the general-depth endpoints off it carry the refuted uniform `Hrange` | log §66 Live frontier; owner memo | say "the `alpha = 2` endpoints"; the general one is ~6 lines of composition |
| 5 | **MEDIUM (Lean, scope)** | `rowFour_/mirFour_/dblFour_/rowWide_commutator_le` and the six `…_gaTwo` forcings are stated over `⁅im Φ, im Φ⁆` while `GradedLatticeWide` defines `γ₂(im Φ)` to include the `x₁`-square | `GradedFourRow.lean` §6, `GradedFourMirror.lean` §§6,7,8 | closed here: `evenRouteAudit_{rowFour,mirFour,dblFour,rowWide}_gaTwoIm_le`; cite those |
| 6 | **LOW (Lean, doc)** | "its endpoints are **no longer vacuous**" - carrying an unproved supply is not non-vacuity | `EvenAlphaTwo.lean` header, "What the even route's status is after this file" | "no longer *known* to be vacuous" |
| 7 | **LOW (Lean, stale)** | wave-55 survival sentences refuted by a wave-56 sibling remain in committed headers: *"only its deep form survives"*, *"What survives is the same supply asked only at `α ≥ 3`"* | `StageAbstractionEvenFlip.lean` lines 1341-1346, 1408, 1415 | one pointer sentence to `EvenSlotZero.lean`; no statement changes |
| 8 | **LOW (Lean, stale)** | *"So the `N` endpoint is not empty for any reason visible at the field layer"*, and the layer non-vacuity witnesses, now believed vacuous | `EvenRouteWitness.lean` §4; `StageAbstractionEvenPerK.lean` §§ | one pointer sentence to `EvenAlphaTwo.lean` §5 |
| 9 | **LOW** | the wave-54 census's ten mod-2 classes are not checked in Lean against `sqRelWord_selGaTwoIm_ne_one`'s four consumed pairings; the certification runs one corner and infers the rest | `GradedLatticeWide.lean` §6 | a `decide` over the ten classes |
| 10 | **INFO** | `EvenSlotZero.lean` states no expected axiom pin set; it happens to be std-3 throughout | `EvenSlotZero.lean` §5 | one sentence |
| 11 | **INFO** | `Challenge.lean` / `Solution.lean` carry two by-design sorries and lie outside `check_axioms.sh`'s scan | `scripts/check_axioms.sh:132` | widen the scan or note the exemption |
| 12 | **INFO** | no Lean-checked concrete field model exists for the live route on either branch: the in-Lean `alpha = 2` fields are odd degree, which the endpoints' `hev` excludes | `EvenAlphaTwo.lean` §4 | wave-57 queue item (2), already scoped |

Defects 1 and 2 require no correction to a committed **statement**: every theorem is a true
implication.  Defects 1, 3 and 4 require corrections to the campaign log, the owner memo and two
Lean headers.  Defect 5 is a statement-scope weakness now discharged.

## What this lane committed

`GQ2/Dyadic/Instances/EvenRouteAudit.lean`, 555 lines, 21 public theorems plus two local
instances and two private lemmas, zero `sorry`, no new axiom, no `native_decide`.  Prints
measured at the tip: §1's eight field-level statements print the endpoint chain's set
`[propext, Classical.choice, hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt, Quot.sound,
absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic]`, which is exactly
what `evenRouteCarried_orientedEquivN` prints; §2's eight and §3's five print std-3 or a subset
(`evenRouteAudit_sigFourY_sq_mem` prints `[propext, Quot.sound]`).  The file elaborates clean with
`-DautoImplicit=false -DrelaxedAutoImplicit=false`, zero errors and zero warnings.

Registration line for `GQ2.lean`, to be added by the orchestrator after line 780
(`import GQ2.Dyadic.Instances.EvenSlotZero`) and before `import GQ2.Dyadic.Main`:

```
import GQ2.Dyadic.Instances.EvenRouteAudit
```
