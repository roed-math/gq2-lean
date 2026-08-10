# W55-AUDIT: an adversarial audit of the even route's endpoint chain

Wave 55, lane AUDIT, against `7286d76c`.  Working tree `claude/w55-audit`.  Everything below
was measured, not recalled: every axiom print was re-elaborated at the tip, and every claim
about a Lean statement was read off the statement.

## Headline verdict

**The even route's endpoint chain holds.**  No endpoint is vacuous for the wave-52 reason, no
link of the composition is missing, no proof is circular, and the axiom census is exactly what
the campaign says it is.  Both branches' field-level hypothesis sets are satisfiable, and this
audit exhibits Lean-checked models at literal fields.

**The campaign's prose overstates what the Lean says, in three places, and one of them matters
for the paper.**  The wave-54 live frontier and the owner memo both say the even route now
carries two inputs on both branches with the reciprocity bundle, the ramified-`i` binder and the
`M`-side isotropy all discharged.  The committed per-field endpoints carry the bundle on both
branches and the ramification datum on `N`; and the published artefact `EvenRouteCarriedM`,
which the same paragraph tells the paper to quote, still carries the isotropy as a third field,
because the two wave-54 lanes that would compose to remove it never met.  The mathematics is
right in every case; the sentences are not.  `GQ2/Dyadic/Instances/EvenRouteWitness.lean`
supplies the missing composition, so the claim can now be made true by import rather than by
correction.

---

## (a) NON-VACUITY: **PASS-WITH-RISK**

### What was checked

For each of the four published bundles `EvenRouteCarried{N,M,NTwo,MTwo}` and each of the six
endpoints (`evenEndpoint_orientedEquiv{N,M}`, `evenEndpoint_orientedEquiv{N,M}_two`,
`evenEndpoint_orientedEquiv{N,M}_atDepth`), whether the hypothesis set has a model.

### Finding 1: the field-level hypotheses are satisfiable, with Lean-checked models

The wave-52 disaster was a hypothesis with no model at all
(`rangeFinal_uniform_Hrange_imChiN_absurd`: a `Hrange` uniform in `K` applies to odd-degree `K`,
where the range is `⊤`, and `-1 ∉ imChiN alpha`).  Nothing of that shape survives: every
hypothesis of every even endpoint is per-`K`, and the branch identification is produced rather
than assumed.

Positively, both branches have literal models.  `GQ2/Dyadic/Instances/EvenRouteWitness.lean` §4
instantiates the two per-field endpoints at the pilot rows of `Instances/Fields.lean`:

* `evenRouteWitness_orientedEquivN_sqrtNegTwo` runs `evenEndpoint_orientedEquivN` at
  `KSqrtNegTwo = ℚ₂(√−2)` with `h = 0`.  The degree binder is `finrank_KSqrtNegTwo`, the
  ramification binder is `not_hasEqualNormValueGroups_KSqrtNegTwo`, the square root of `−1` is
  chosen in the fixed algebraic closure, and the bundle binder is the B5-K axiom
  `markedRecipAt`.
* `evenRouteWitness_orientedEquivM_sqrtTwo` runs the `M` endpoint at `KSqrtTwo = ℚ₂(√2)` with
  `h = 0`.  The `M` branch carries no ramification datum at all, so only the degree binder and
  the bundle binder are needed.

What is left in each statement is the branch sign condition (`−1 ∉ range χ` on the first,
`−1 ∈ range χ` on the second) and the two named supplies.  The sign conditions are true and
classical: `√−2 = ζ₈ − ζ₈⁻¹` is negated by complex conjugation, so `−1 ∉ range χ` on `ℚ₂(√−2)`;
`√2 = ζ₈ + ζ₈⁻¹` is fixed by it, so `−1 ∈ range χ` on `ℚ₂(√2)`.  Neither is in the tree and
neither is claimed here.  This is the honest limit of what could be proved: the residue of the
field layer is one classical sign per branch, and nothing else.

The bundle binder deserves a separate word.  `MarkedRecip R K` is never constructed anywhere in
the repository; its only inhabitant is the axiom `GQ2.markedRecipAt` (B5-K), and
`LocalReciprocity`'s only inhabitant is `GQ2.localReciprocity` (B5).  So `B` is satisfiable
exactly as far as the census is, which is the same footing the odd route stands on.  The two
literal-field statements pay for it in their prints, which is why they are stated separately
from the general ones.

### Finding 2: the `N` bundle's depth binder is harmless, and that is now a theorem

`EvenEndpointNFamily`, `EvenEndpointNFlip`, `EvenEndpointMFamily` and `EvenEndpointMFlipOffTwo`
quantify over **every** `alpha ≥ 2`, unguarded by `hrange`, while the range identity produces
exactly one `alpha` per field.  That is the wave-52 shape transposed from `K` to `alpha`, and it
had to be checked rather than noted.

On the `N` branch it is harmless.  `evenRouteWitness_nUnit_mem_imChiN` proves that
`nUnit alpha ∈ imChiN beta` forces `alpha = beta` for `alpha, beta ≥ 2`: the mod-four class
kills the `≡ 1` branch of `evenRange_mem_imChiN_dvd`, and `nUnit alpha` and `nUnit beta` are
exactly `2 ^ min (alpha, beta)` apart, which `2 ^ (beta + 1)` never divides.  Row `1` of the `N`
table is `nUnit alpha` and a stage tuple demands a character value there, so
`evenRouteWitness_nTuple_isEmpty` gives `IsEmpty (Tuple (nStageWord alpha h _) (vN alpha) …)` at
every `alpha ≠ alpha₀`.  Hence `evenRouteWitness_carriedN_of_atDepth`: given the branch
identification, the single-depth pair of inputs already produces `EvenRouteCarriedN h K`.  The
`N` bundle is therefore **equivalent** to what `evenEndpoint_orientedEquivN_atDepth` consumes,
and asks for nothing extra.

### Finding 3: the `M` bundle's depth binder does not collapse, and this is the ranked risk

The same argument fails on `M`, provably.  `mUnit alpha − 1 = 2 ^ alpha · mUnit alpha`, so
`evenRouteWitness_mUnit_mem_imChiM` gives `mUnit alpha ∈ imChiM beta` for every
`2 ≤ beta ≤ alpha`; and the rest of the `M` table is `1` and `−1`, which lie in every `imChiM
beta`.  So `evenRouteWitness_vM_mem_range`: a field identified at depth `beta` has **all** row
values of the `M` table at **every** deeper `alpha` inside its character image.  The emptiness
route is unavailable, and `EvenRouteCarriedM` may demand strictly more than
`evenEndpoint_orientedEquivM_atDepth` consumes.

Nothing shows those extra instances false.  Evidence that they are not pathological:
`evenDigit_flipSlotTwo_M` discharges the slot-`2` demand at every `alpha ≥ 2` **generically** in
the group, the character and the tuple, without using the range identity at all, so a wrong-depth
demand is the same kind of demand as a right-depth one.  The risk is that `EvenRouteCarriedM`
is an unnecessary strengthening whose consistency is unestablished, not that it is known bad.
`EvenDeepMIsotropicSupply` shows the correct pattern: it quantifies over `alpha` **and** over
`hrange`, so only the produced depth can ever be reached, and it is a single equation in
disguise.  The four `EvenEndpoint*` supplies should be re-cut the same way.

### Finding 4: the supplies themselves are not shown consistent, and cannot be here

`Hfam` (`EvenKernelDerivationFamily` with `EvenKernelRelatorKill`) and the flip supplies are the
campaign's named inputs.  No model is exhibited for either, at any field, and none can be short
of proving them.  This is not a defect of the chain; it is the frontier.  What §4 of the witness
file establishes is that they are the **only** residue: everything else in the two per-field
endpoints is either discharged from committed statements, discharged from the census, or one
classical sign condition.

**Verdict (a): PASS-WITH-RISK.**  No hypothesis set is inconsistent, both branches have
field-level models, and the `N` bundle is proved to be exactly its single-depth instance.  The
risk is the `M` bundle's unguarded depth binder (Finding 3), which recreates the wave-52 shape
without the wave-52 consequence.

---

## (b) COMPOSITION: **PASS-WITH-RISK**

### The chain, link by link, `N` branch

Every link below exists as a committed statement, and the binders match: the whole file
`StageAbstractionEvenEndpoint.lean` re-elaborated clean at the tip with
`-DautoImplicit=false -DrelaxedAutoImplicit=false`, which is the type-level check, and each
quantifier was read off the statement, which is the shape check.

1. `evenRange_range_eq_imChiN B deltaI hdeltaI hram hneg` produces `⟨alpha, 2 ≤ alpha, hrange⟩`.
   Existential in `alpha`, per `K`.  Correct shape: this is exactly what wave 52 established and
   what the refuted uniform form got wrong.
2. `evenEndpoint_kappa_of_rangeN hα hrange : cyclotomicModFourClassKTwo ≠ 0`, at the produced
   `alpha`.
3. `evenEndpoint_nShadow` then `evenEndpoint_nFrame_of_range hα hdeg hrange`, giving a cup-adapted
   `N`-row Frattini frame at the produced `alpha`, with no supply.
4. `evenEndpoint_nStageBase hα hev hrange`, the level-three base, via
   `evenTransgression.nLevelThreeRelationRealization_fieldCup` and `Frame.toLevelThree`.
5. `evenDigit_perKRawToBracketN halpha hrange Hflip : EvenKernelRawToBracketSupply (alpha − 1) …`.
   `Hflip` is consumed **at the same `alpha`** as `hrange`; there is no uniform-in-`alpha` step.
6. `evenPerK_forwardGeneratorDataN halpha hrange base Hfam Hup :
   Nonempty (NForwardGeneratorData alpha h chiCycKTwo)`.  `Hfam` likewise at the produced `alpha`.
7. `nonempty_orientedEquivN_evenDegree_of_forwardGeneratorData alpha h (1 ≤ alpha) hev
   (evenDem_nModelDemushkin alpha h halpha) hdata :
   Nonempty (OrientedContinuousMulEquiv (chiN alpha h) chiCycKTwo)`.

Links 2 to 7 are assembled by `evenEndpoint_orientedEquivN_atDepth` at a fixed `alpha`; link 1 is
where `alpha` is produced, in `evenEndpoint_orientedEquivN`.  That ordering is the structural
repair the file's §5.1 says it is: the at-depth statement carries nothing quantified over
`alpha`, and the per-field statement quantifies only the two supplies.

### The chain, `M` branch

Identical except at links 2 to 4: `evenEndpoint_kappa_of_rangeM hrange`, then
`evenFrameDeep_mStageBase hα hev hkappa hrange hiso` (W53-KAPPA), with `hiso` the depth-class
isotropy; and link 5 goes through `evenEndpoint_mFlip_of_offTwo halpha Hflip` first, which
re-inflates the slot-`2`-free supply using `evenDigit_flipSlotTwo_M`.  On the `α = 2` stratum
`hiso` is discharged by `evenFrameDeep_isotropic_two`.

### Quantifier shape: no wave-52 defect anywhere in the chain

Every hypothesis actually consumed by the composition is consumed at the `alpha` the identity
produced.  The over-quantification is confined to the published bundles and to the four
`EvenEndpoint*` supply `Prop`s, which are wrappers, not links: the endpoints instantiate them
immediately at the produced `alpha` (`Hfam alpha halpha`, `Hflip alpha halpha` in §6).  See (a)
Findings 2 and 3 for what that costs on each branch.

### The one gap: the two wave-54 lanes never met

`GQ2/Dyadic/Instances/EvenDeepIsotropy.lean` (W54-BOCK) proves
`evenDeepMIsotropicSupply_holds : EvenDeepMIsotropicSupply K` outright.
`GQ2/Dyadic/Instances/StageAbstractionEvenEndpoint.lean` (W54-COMPOSE) publishes
`EvenRouteCarriedM` with `isotropy : EvenDeepMIsotropicSupply K` as its third field.  Both files
import `StageAbstractionEvenFrameDeep.lean`; **neither imports the other**.  So as committed:

* `evenRoute_orientedEquivM` demands a three-field bundle;
* `evenDeepIsotropy_orientedEquivM` discharges the isotropy but carries `Hup`
  (`EvenPerKMRawToBracket`, the raw-to-bracket span equality), not the flip supply, and carries
  `Hfam` in the wave-53 `∀ alpha ≥ 1` form;
* **no committed statement carries the two-input `M` endpoint the campaign claims.**

This is not a soundness defect: the composition is one import wide, and it is now committed as
`evenRouteWitness_carriedM_of_two` and `evenRouteWitness_orientedEquivM` in the witness file.  It
is a claim-versus-proof defect, and it is reported again under (d).

### Target shape

The even endpoints conclude
`Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K)))`, an
orientation-preserving continuous isomorphism between the presented core `DN alpha h =
presPro2 (nRelator alpha h)` and `maxProPQuotient 2 (GalK K)`.  That is the declared even-route
target and the file docstrings state it correctly ("its maximal pro-`2` Galois group is
oriented-isomorphic to the presented `N` core").  It is one level short of the odd route's
literal capstone `Nonempty (ContinuousMulEquiv (candidateGroup …) (GalK KSqrtNegTwo))`, which
reaches the full Galois group.  No claim confuses the two; recorded so the paper does not.

**Verdict (b): PASS-WITH-RISK.**  Every link exists with matching binders and correct quantifier
shape, and the composition is what the endpoints say it is.  The risk is the uncomposed
wave-54 pair, now discharged by the witness file.

---

## (c) CIRCULARITY AND AXIOM DISCIPLINE: **PASS**

### Circularity

No endpoint's proof consumes a statement assuming the endpoint's conclusion.  Checked three ways:

1. **Syntactically.**  Neither carried input mentions the model.  `EvenKernelDerivationFamily`,
   `EvenKernelRelatorKill`, `EvenDigitFlipSupply` and `EvenDigitFlipSupplyOffTwo` are statements
   about tuples, corrections and character digits in `maxProPQuotient 2 (GalK K)` alone; none
   mentions `chiN`, `chiM`, `DN`, `DM` or `OrientedContinuousMulEquiv`.
2. **Structurally.**  The forward datum `NForwardGeneratorData alpha h chiG` is
   generator-level: a rank-`coreRank h` tuple in `G`, the relator dying on it, topological
   generation, and the six prescribed character rows.  It is the data for a surjection out of
   the presented core, not the isomorphism in disguise; the isomorphism is produced from it by
   `D.orientedEquiv` together with the Demushkin invariants.
3. **By import.**  `Instances/EvenForwardRouteSkeleton.lean` and the per-`K` layer sit strictly
   below the endpoint file; Lean's acyclic import discipline forbids the literal cycle, and no
   hypothesis is a restatement of a downstream conclusion.

The `M` isotropy is worth naming, because it is the one place an equivalence appears:
`evenEndpoint_mIso_iff_frame` says the isotropy **is** the existence of the `M`-row cup-adapted
frame.  That is an honest sharpness statement, not a circularity: the frame is an intermediate
object of the `M` chain, not its conclusion, and the isotropy is now proved independently by
the Bockstein route in `EvenDeepIsotropy.lean` §§1 to 4, which never mentions a frame.

### Axiom census

**11 committed axioms, all in `GQ2/Foundations/Axioms.lean`** (lines 104, 124, 165, 178, 204,
231, 259, 300, 359, 388, 433).  A repository-wide grep for `axiom` at line start returns 25
hits; the other 14 are docstring prose that happens to begin a line with the word.  No axiom is
declared anywhere else, and none is declared in the audited files or in the witness file.
Census matches the campaign's claim exactly.

### Terminal prints, re-measured at the tip

Every endpoint of `StageAbstractionEvenEndpoint.lean` prints exactly

`[propext, Classical.choice, hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt, Quot.sound,
absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic]`

which is the file's `S`; `evenPerK_orientedEquiv{N,M}` and `evenDigit_orientedEquiv{N,M}` print
`S` without the norm criterion; `evenFrameDeep_orientedEquivM` and all four committed `α = 2`
endpoints print `S`; `EvenRouteCarriedM` and `evenRoute_carriedM_of_perK` print std-3 plus
`tateDualityAt`; `evenEndpoint_nIso` prints `S` minus
`absGalQ2_isTopologicallyFinitelyGenerated`.  **Every one of the file's §9 claims is exactly
right**, including the honest admission that the `N` per-field endpoint exceeds the
base-carrying committed statements by the norm criterion because it builds the base instead of
carrying it.

### The wave-54 pin shrink

The rewire is commit `d52894ae`, "rewire the ContCoh handle-index copies onto SqHandleIdx".  Its
claim is that four leaf lemmas drop `Classical.choice` and that the reduction does not
propagate.  Re-measured directly:

* `GQ2.ContCoh.sqHandleIdxU_eq_iff`, `…V_eq_iff`, `…U_ne_handleV`, `…V_ne_handleU`:
  `[propext, Quot.sound]`.  The shrink is real.
* `GQ2.ContCoh.eq_sqInitialPartner_iff` and
  `GQ2.ContCoh.modTwoFoxDerivative_sqDiscreteRelator_linearMoment`:
  `[propext, Classical.choice, Quot.sound]`.  The file's terminal statements are unperturbed.

No statement of the even chain could have been perturbed in any case: a dropped axiom can only
shrink a print, the shrink is confined to the `SqCore` handle-index family, and every even
endpoint prints `Classical.choice` anyway.  The even prints measured above are the direct
confirmation.

**Verdict (c): PASS.**  No circularity, census 11, no new axioms, every claimed print correct,
pin shrink confirmed non-propagating.

---

## (d) CLAIM VERSUS PROOF: **FAIL**

The Lean is sound; the prose is not.  Three statements in the campaign log's wave-54 live
frontier (`§64`, "Live frontier (supersedes the wave-53 frontier)") and in the owner memo
(`docs/dyadic/owner-items-2026-08-05.md`, "Status at wave 54", paragraph "The even route is now
symmetric and minimal") are not what the Lean says.

### Overstatement 1: the marked reciprocity bundle

> "Everything else is discharged: the stage base on both branches, the ramified-`i` binder, **the
> marked reciprocity bundle**, and the M-side isotropy."

`evenEndpoint_orientedEquivN` and `evenEndpoint_orientedEquivM`, and therefore
`evenRoute_orientedEquivN` and `evenRoute_orientedEquivM`, all carry
`{R : LocalReciprocity} (B : MarkedRecip R K)`.  The bundle is dropped only from the at-depth
endpoints of §5.2 and the `α = 2` strata of §7, where `hrange` is given rather than produced.
The endpoint file states this correctly and says why ("the bundle exists on this route only to
produce `α`, and §6 pays for it once, there"); the frontier and the memo drop the qualification.

**Repair:** in both passages, "the marked reciprocity bundle **on the strata**".

### Overstatement 2: the ramified-`i` binder

Same sentence.  `evenEndpoint_orientedEquivN` carries
`hram : ¬ HasEqualNormValueGroups K deltaI`, together with `deltaI` and `hdeltaI`, because
`evenRange_range_eq_imChiN` needs it to produce `alpha`.  What wave 54 discharged is the **frame
form** `cyclotomicModFourClassKTwo ≠ 0`, on both branches (§1,
`evenEndpoint_kappa_of_range{N,M}`), which is a different statement.  The endpoint file's §6
docstring makes exactly this distinction; the frontier and the memo lose it.

**Repair:** "the frame form of the ramified-`i` binder".

### Overstatement 3: the `M`-side isotropy and the published artefact

> "Both branches carry exactly two inputs at every `alpha >= 2` … the carried inputs are now
> published as Lean structures (`EvenRouteCarried{N,M,NTwo,MTwo}`) … so the even sections can
> quote a machine-checked list rather than a narrative one."

`EvenRouteCarriedM` has three fields, and the third is `isotropy : EvenDeepMIsotropicSupply K`.
A reader who does what the memo says, and quotes the machine-checked list, quotes a three-input
`M` branch.  The isotropy **is** a theorem, W54-BOCK's `evenDeepMIsotropicSupply_holds`, but the
two lanes are siblings in the import graph and no committed statement composed them.  The same
holds for the endpoint: `evenRoute_orientedEquivM` demands the three-field bundle, and
`evenDeepIsotropy_orientedEquivM` carries `Hup` rather than the flips.

This is the one overstatement that reaches the paper, because it is about the artefact the paper
is instructed to quote.

**Repair:** committed this wave.  `evenRouteWitness_carriedM_of_two` builds `EvenRouteCarriedM`
from the two inputs and `evenRouteWitness_orientedEquivM` is the two-input `M` endpoint.  Either
cite those, or re-cut `EvenRouteCarriedM` to two fields in a later wave and let
`evenDeepMIsotropicSupply_holds` supply the third at the point of use.

### A stale header inside the audited file

`StageAbstractionEvenEndpoint.lean`'s own header says "**Refused: the isotropy on `M`.**
`EvenDeepMIsotropicSupply` is not removable, and this is a theorem, not a judgement", and its
carried-input table gives `evenEndpoint_orientedEquivM` the inputs "`Hiso`, `Hfam`, flips off
slot `2`", and its headline says "The only input the `M` branch owes above `α = 2` that the `N`
branch does not is the isotropy".  All three were true of that lane's imports and all three were
falsified in the same wave by the sibling lane.  The campaign log's §64 W54-COMPOSE paragraph
does say "W54-BOCK proved it, in the same wave", so the log is honest at that spot; the file is
not, and the file is what a reader opens.

**Repair:** one sentence in the header pointing at `Instances/EvenDeepIsotropy.lean`.  No
statement changes.

### What the prose gets right

For completeness, because an audit that only lists faults is not an audit.  The stage-base
discharges on both branches, the slot-`2` shave, the slot-`3` reduction to
`[a^n, b] · [b^n, a] = 1`, the `α ≥ 2` binder tightening, the refusal record, the sharpness
statement `evenEndpoint_mIso_iff_frame`, the `μ = ω` identification, the axiom-print comparison
in §9, and the Bockstein cost claim (`tateDualityAt` only, no norm criterion) are all stated
accurately and all check out against the Lean.  Nothing measured is described as proved.
`Hfam` and the flip supplies are named as carried in every relevant passage.

**Verdict (d): FAIL**, on the prose, in three places, with no consequence for the mathematics.

---

## Ranked defects and risks

| # | Severity | What | Where | Repair |
| --- | --- | --- | --- | --- |
| 1 | **HIGH (prose)** | `EvenRouteCarriedM` published with three fields while its third is a theorem of the same wave; the memo tells the paper to quote it | `StageAbstractionEvenEndpoint.lean` §8; owner memo "Status at wave 54"; log §64 frontier | done in Lean (`evenRouteWitness_carriedM_of_two`, `evenRouteWitness_orientedEquivM`); re-cut the structure to two fields in a later wave |
| 2 | **MEDIUM (prose)** | "the marked reciprocity bundle … discharged" is false for the two per-field endpoints, which carry `B` | log §64 frontier; owner memo | add "on the strata" |
| 3 | **MEDIUM (prose)** | "the ramified-`i` binder … discharged" is false for `evenEndpoint_orientedEquivN`, which carries `hram`; only the frame form fell | log §64 frontier; owner memo | say "the frame form" |
| 4 | **MEDIUM (Lean, latent)** | `EvenEndpointMFamily` / `EvenEndpointMFlipOffTwo` / `EvenRouteCarriedM` quantify over every `alpha ≥ 2` unguarded by `hrange`, and on `M` the extra instances provably cannot be dismissed as vacuous | `StageAbstractionEvenEndpoint.lean` §5.1, §8 | guard by `hrange` as `EvenDeepMIsotropicSupply` does, or state the bundle at a depth; evidence in witness file §3 |
| 5 | **LOW (Lean, doc)** | the endpoint file's header refuses an input that was discharged in the same wave | `StageAbstractionEvenEndpoint.lean` header, three passages | one sentence |
| 6 | **LOW (Lean, cosmetic)** | `EvenRouteCarriedN` lacks the `[FiniteDimensional ℚ_[2] K]` binder its `M` twin carries | `StageAbstractionEvenEndpoint.lean` §8 | harmless; note only |
| 7 | **INFO** | the sign conditions `−1 ∈ / ∉ range χ` are unproved for every concrete field, so the two literal-field witnesses stop one classical fact short of unconditional | `EvenRouteWitness.lean` §4 | a lane could prove `−1 ∉ range χ` for `ℚ₂(√−2)` from `√−2 = ζ₈ − ζ₈⁻¹` |
| 8 | **INFO** | the even target is `maxProPQuotient 2 (GalK K)`; the odd route's literal capstone reaches `GalK K` | file docstrings, correct as written | keep the distinction in the paper |

Nothing in this table requires a correction to a committed **statement**.  Items 1 to 3 and 5
are prose; item 4 is a design weakness that should be re-cut before the artefact is quoted, not
a falsehood.

## What this lane committed

`GQ2/Dyadic/Instances/EvenRouteWitness.lean`, 419 lines, 12 public theorems plus two local
instances, zero `sorry`, no new axiom, all prints measured and recorded in its §5.  Its four
sections are the four probes above that produced reusable Lean: the `M` composition (§1), the
`N` depth rigidity and bundle collapse (§2), the `M` non-collapse (§3), and the literal-field
instantiations together with `imChiM 2 = ⊤` (§4).

Registration line for `GQ2.lean`, to be added by the orchestrator after line 771
(`import GQ2.Dyadic.Instances.EvenDeepIsotropy`):

```
import GQ2.Dyadic.Instances.EvenRouteWitness
```
