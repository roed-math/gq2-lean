# W70: the general-k relator base, and the class-five map

Lane W70-FIVE.  New modules `GQ2/Dyadic/SqCore/GradedRelatorBase.lean` and
`GQ2/Dyadic/SqCore/GradedClassFive.lean`; no edits to existing files.  Prefixes `relBase` /
`cfive`.

## 0.  Headline

**The general-`k` relator base landed at NO hypothesis.**  Wave 69 asked whether
`cfour_relator_base` replays at every class, and expected the general form to need a named
hypothesis that happens to hold at `k = 4`.  It needs none.  `cfour_relator_base` is not a
class-four fact and not a level-quotient fact: it is an identity in `D_sq h` itself.

> ⭐⭐ **`relBase_relator_base`**: there is a `t` with
> `sqRelWord (sqArbBase h nu' j) = conjP (relBaseEichDefect nu' j) t`.

The conjugator is the tail of the handle word past the twisted handle, and it is the whole
residue of wave 68's centrality hypothesis and wave 69's `Commute` hypothesis.  Those were never
needed for the identity; they were needed only to place the defect at the right-hand end of the
product instead of conjugated into it.  Since every `twoCentralSeries` layer is normal, the
conjugation is invisible to everything the residual consumes.

The hypothesis is recorded anyway, as `RelBaseCommuting`, because it is what wave 69 actually
verified and it is the exact shape that fails at class five.  The `k = 4` instance is re-derived
through it (`relBase_relator_base_four`) as an independent check.

## 1.  The schema (module `GradedRelatorBase`, §4)

* ⭐ `relBase_relator_base_mem_iff`: `sqRelWord (sqArbBase h nu' j) ∈ N ↔ relBaseEichDefect nu' j ∈ N`
  for every normal `N`.  No class, no hypothesis.
* ⭐ `relBase_relator_base_levelMk`: at every `k`, the undressed frame's class-`k` relator vanishes
  in `Q_k` iff the upstairs defect does.
* ⭐⭐ `relBase_supply_of_eichDefect`: **at every `k`**, if the upstairs Eichler defect lies in
  `γ_k` at every selected marking and handle, then `SqClassClearingSupply h k`.
* `relBase_residual_of_defectDies` / `relBase_transitivity_of_defectDies`: if it lies in `γ_k` for
  every `k ≥ 4`, then `BridgeFinalResidual h`, hence `SqLamMarkTransitivity h`.

**The payoff, as a schema.**  Each class-`k` step is no longer a fresh relator analysis.  It is
"kill the Eichler defect in the class-`k` layer", and the reduction to that is now proved once,
uniformly, rather than once per class.

**The scope is stated, not implied.**  `relBase_defectDies_iff_trivial` proves that the clause is
*equivalent* to "the trivial dressing clears class `k`", and it is only *sufficient* for
`SqClassClearingSupply h k`, which quantifies over every admissible dressing.  Wave 68's
class-three witness is a nontrivial dressing, so the gap is real and is not an artefact.

## 2.  The class-five map (module `GradedClassFive`)

### (a) `⁅γ₂, γ₃⁆ ≤ γ₅` is TRUE, and the wave-69 argument proves it after an index shift only

Nothing in wave 69's closed-annihilator argument was about the number two, so it is carried out
here once, at every layer at once:

> ⭐⭐ **`cfive_commutator_lambdaTwo`**: for every `k`, `v ∈ γ_k` and `w ∈ γ₂` give
> `commP v w ∈ γ_{k+2}`.  That is `⁅γ_k, γ₂⁆ ≤ γ_{k+2}`.

The annihilator `{g | commP v g ∈ γ_{k+2}}` of a `γ_k`-element is closed for wave 69's reason; is
a subgroup because the correction term of `cfour_commP_mul_right` is a *double* bracket against
`γ_k` and so is already two layers down; contains every square because `commP v g ∈ γ_{k+1}` and
`γ_{k+1}² ≤ γ_{k+2}`; and contains every commutator because `cfiveCommHom` is a homomorphism into
the central layer `Z_{k+1}`.  Hence it contains `twoCentralSucc ⊤ = γ₂`.

`⁅γ₂, γ₃⁆ ≤ γ₅` is the instance `k = 3` (`cfive_commutator_two_three`); wave 69's
`cfour_commutator_lambdaTwo` is the instance `k = 2`, re-derived as `cfive_commutator_four_of_two`
to check the uniform argument lost nothing.

### (b) What replaces `γ₂`-abelianness: a class-two nilpotent layer, and it is linear

In `Q₅` the layer `Y = lambdaImage G 2 5` is not abelian, but by (a) at `k = 2` its commutators
land in `zLayer G 4`, which is **central** in `Q₅` and of **exponent two**:

* `cfive_swap_free`: `y · y' = y' · y · commP y y'`, free, in any group;
* ⭐ `cfive_commP_lambdaTwo_mem_zLayer`, `_central`, `_sq`: the correction is central and squares
  to `1`;
* ⭐ `cfive_commP_lambdaTwo_hom_left` / `_right`: `commP` is **bimultiplicative** on `Y × Y`.

So the class-five reordering device is: **reorder freely and collect an `F₂`-bilinear central
correction**.  That is strictly more bookkeeping than class four, but it is a *linear* amount, not
a bracket jungle, and it is the honest replacement for `cfour_commP_lambdaTwo`.  This is the
"nilpotency-class-2 bookkeeping layer" the ticket guessed at, confirmed.

### (c) The surviving-lemma table

Three buckets, as asked.  **"Class-four-only" means the wave-69 proof delivers nothing modulo
`γ₅`, not that the statement is refuted** - no negative result is claimed anywhere in this lane.

| wave-69 declaration | verdict | replacement in W70-FIVE |
| --- | --- | --- |
| `cfour_commP_mul_left`, `_mul_right`, `cfour_sq_mul` | verbatim (free identities) | - |
| `cfour_comm_one`, `_one_comm`, `_comm_self`, `_commute_of_comm` | verbatim | - |
| `cfour_lambda_two/three/four`, `cfour_commP_mem_two` | verbatim (index arithmetic) | - |
| `cfour_commP_mem_three`, `_mem_four` | subsumed, every `k` | `cfive_commP_mem_succ` |
| `cfour_commP_mem_lambdaTwo`, `cfour_sq_mem_lambdaTwo` | verbatim, every class | - |
| `cfour_commP_zLayer_left`, `_right` | verbatim (`Z` central at every class) | `cfive_commP_zLayer_left` |
| `cfour_commP_mem_zLayer_left`, `_right` | **λ-image side condition** | `cfive_commP_mem_zLayer_left/right`: slot in `lambdaImage G k (k+2)`, so `γ₃` at class five |
| ⭐ `cfour_commP_left_hom`, `_right_hom` | **λ-image side condition** | `cfive_commP_left_hom` / `_right_hom` (every `k`); class five: `cfive_commP_left_hom_five` |
| `cfour_commP_sq_left` | λ-image side condition (same reason) | not restated |
| `cfour_sq_mem_zLayer` | class-four-only | not restated; the class-five analogue is `y² ∈ lambdaImage G 3 5`, one layer short of central, the same degradation `cfive_commP_lambdaTwo_mem_lambdaThree` records for brackets |
| `cfourAnnih`, `cfour_mem_annih`, `_isClosed_annih`, `cfourCommHom`, `_commHom_apply`, `_commHom_mem` | subsumed, every `k` | `cfiveAnnih`, `cfive_mem_annih`, `cfive_isClosed_annih`, `cfiveCommHom`, `cfive_commHom_apply`, `cfive_commHom_mem` |
| ⭐ `cfour_commutator_lambdaTwo` | subsumed, every `k` | `cfive_commutator_lambdaTwo` |
| ⭐ `cfour_commP_lambdaTwo` (`Y` abelian) | **class-four-only** | `cfive_commP_lambdaTwo_mem_zLayer` + `_central` + `_sq` + `_hom_left/right` |
| `cfour_pow_four_mem_zLayer` | **class-four-only** | `cfive_pow_four_mem_lambdaThree`, `cfive_pow_eight_mem_zLayer` |
| `cfour_pow_four_inv` | **class-four-only**, no class-five reading (it is `p⁸ ∈ γ₄`) | none |
| `cfour_sq_mul_lambdaTwo`, `cfour_pow_four_mul` | class-four-only (need `Y` abelian) | none |
| ⭐⭐ `cfour_sqWord`, `cfour_sqRelWord` | **class-four-only** | `relBase_sqWord_free` is the general form; the two simplifications are exactly the class-four content |
| `cfour_zLayer_le_lambdaTwo` | verbatim in shape | not restated |
| `cfour_commute_lambdaTwo` | class-four-only | see `cfour_commP_lambdaTwo` row |
| `cfour_handleWord_mem_lambdaTwo`, `cfour_sqRelWord_mem_lambdaTwo` | verbatim, every class | - |
| `cfour_prod_map_update`, `cfour_handleWord_update` | verbatim (already stated for any group), and superseded | `relBase_prod_map_update`, `relBase_handleWord_update`: hypothesis-free |
| `cfourEichDefect`, `cfour_eichDefect_mem`, `cfour_base_eq_gen` | verbatim / subsumed | `relBaseEichDefect`, `relBase_eichDefect_four` |
| ⭐⭐ `cfour_relator_base` | **subsumed at no hypothesis, upstairs** | `relBase_relator_base`, `relBase_relator_base_mem_iff`; on-the-nose form needs `RelBaseCommuting` |
| `cfour_zLayer_comm`, `cfour_shuffle`, `cfour_shuffle_mid` | verbatim (only centrality used) | not restated |
| `cfour_pow_four_dress`, `cfour_triple_dress_zero`, `cfour_dress_zero/one/two` | class-four-only | none; a class-five knob inventory must be redone from `relBase_sqWord_free` |
| `cfour_supply_iff` | verbatim, every `k` | - |
| ⭐⭐ `cfour_supply_of_eichDefect` | subsumed, every `k` | `relBase_supply_of_eichDefect` |
| `ClassFourResidual`, `cfour_residual_of_classFour` | verbatim (index bookkeeping) | - |

### The one thing class five genuinely loses

The relator itself.  `cfour_pow_four_inv` is `p⁸ ∈ γ₄`, which says nothing modulo `γ₅`, so the
`((b²)²)⁻¹` factor of `relBase_sqWord_free` may **not** be simplified to `b⁴` in `Q₅`, and the
`conjP c a` factor does not collapse either.  The class-five relator is therefore strictly larger
than the class-four one, and this is where a class-five run's real work begins.  What it does
*not* have to redo is §4 of wave 69: `relBase_relator_base` already covers it.

## 3.  Verification record

* Harness: `scripts/mirror.sh sweep`, then `gen GQ2.Dyadic.SqCore.GradedRelatorBase`, then
  `gen GQ2.Dyadic.SqCore.GradedClassFive`, then `check` on each source file.  Both clean.
* Axiom pins: 21 + 27 = 48 `#print axioms`, one per declaration.  Every declaration is
  `[propext, Classical.choice, Quot.sound]` or a strict subset: `relBase_map_commP` and
  `cfive_swap_free` are `[propext]` only, and `relBase_prod_map_update` /
  `relBase_handleWord_update` are `[propext, Quot.sound]`.
* No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.
* Imports added: `GQ2.Dyadic.SqCore.GradedClassFour` (by `GradedRelatorBase`) and
  `GQ2.Dyadic.SqCore.GradedRelatorBase` (by `GradedClassFive`) only.
* Everything is written in `commP`.  The **subgroup** bracket `⁅H, K⁆` does elaborate inside
  `GQ2.Dyadic.SqCore`, which is what let the restatement check below state `⁅γ₂, γ₃⁆ ≤ γ₅` in
  mathlib's own terms.  **[Corrected W72-HOUSE.]**  This bullet originally opened "Wave 69's
  notation finding reconfirmed: the **element** bracket `⁅ , ⁆` does not elaborate inside
  `GQ2.Dyadic.SqCore`".  That is **false**, and it was contradicted by a *concurrent landing of
  this same wave*, `f82cb316` (W70-HOUSE, 11:26:18), two minutes before this note was written at
  11:28:07.  The element bracket needs `open scoped commutatorElement`, which mathlib requires
  everywhere, at every namespace, because `commutatorElement` is a deliberately scoped instance;
  17 files under `GQ2/Dyadic/SqCore/` already write it.  The contrast this bullet draws between
  the subgroup and element brackets is real, but its cause is `Subgroup.commutator` being a
  *global* instance while `commutatorElement` is a *scoped* one, not anything about `SqCore`.
* Independent restatement check (scratch, not committed), six items, all typecheck:
  `⁅γ₂, γ₃⁆ ≤ γ₅` and `⁅γ_k, γ₂⁆ ≤ γ_{k+2}` as raw mathlib subgroup containments and at the raw
  element level `v⁻¹w⁻¹vw`; `relBase_relator_base` with `sqRelWord`, `conjP`, `commP` and
  `relBaseEichDefect` all written out; wave 69's `cfour_relator_base` statement discharged twice,
  once by wave 69's theorem and once by `relBase_relator_base_four`; a fully spelled-out
  `SqClassClearingSupply h k` discharged by `relBase_supply_of_eichDefect` at an arbitrary `k`;
  and the class-five bookkeeping with no `commP` and no `zLayer`.
* Base `c85f80de`; lane branch `claude/w70-five`; commits `8803d706`, `a88bcb74`.
