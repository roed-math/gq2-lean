/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedRowResidue
import GQ2.Dyadic.SqCore.GradedUniformGen

/-!
# W88-UNIFORM: the uniform-in-class supply on the row-move ladder

⚠⚠ **[MERGE-TIME NOTICE, W88 close: THIS MODULE IS A PARTIAL SALVAGE, and the plan narrated
below is the lane's INTENT, not this file's contents.**  The lane was cut off mid-increment
by a usage limit, not by any mathematical or build failure.  **Present and verified: items 1
and 2 only** (§1 to §3, through `gUni_defect_reach` and `gUni_defect_knob`).  **Absent: items
3, 4 and 5** (§4 onward), so there is no `gUni_cost_slot*`, no `gUni_knob_cost`, no
`gUni_step`, no `gUni_nonempty`, no `gUni_pair`, and in particular **no `gUni_clearing`: the
odd classification's last input did NOT land in this wave**, and the standing statement of
record remains wave 87's `gRsd_clearing_of_forall_class_five`, whose per-class hypothesis is
still open.  The "Axiom hygiene" paragraph below likewise describes the intended file; the
pins actually verified are in the merge-time pins section at the end.  The lane's further
369 lines, UNVERIFIED, are preserved as commit `f9753d3d` on branch `claude/w88-uniform`,
which is deliberately not deleted; resume there with `mirror.sh sweep` then `gen`.]

Wave 87 (`GradedRowResidue.lean`) proved rung 4 of the row-move ladder on the whole unit
locus and left the rungs `k ≥ 5` as the odd route's last input: each was priced by the
wave-86 engine as one linear-algebra question in `λ_{k-1}/λ_k`, apparently fresh at every
class.  This module closes ALL of them at once, by the supply route (ticket T2(c)): the
class-`k` defect of ANY carrier solution is invisible to both rows and to EVERY
`gDelta`-functional, uniformly in the class, so wave 80's kill ladder `gGen_killAt` places
it in the tower reach at every depth, wave 79's separation strips the tower part, and the
knob span that remains is exactly the engine-cost image of the row carrier on the unit
locus.  The rungs climb by induction from wave 87's rung 4, and the odd-degree
classification's last input lands.

## The chain

1. **The class-uniform defect** (section 2, ticket T1).  For corrections in the row carrier
   the marked letters are chi-standard: the pivot is chi-trivial (`chiSq_sqPivot`), its
   `ℤ₂`-powers stay chi-trivial (`gJoin_chiSq_zpow`), and a `γ₂`-correction with trivial
   `λ`-row is chi-trivial (`gJoin_chiSq_of_gammaTwo`).  So wave 74's master kill
   `gDelta_relWord_of_chiFrame_eq_zero` applies verbatim: `gUni_delta_zero` reads EVERY
   functional to zero on the relator value of EVERY row frame, at every class at once.
   Both rows vanish by the degree bookkeeping `gDelta_row_reading` and the exponent row
   `(A - 1, B, 2B)`: the `x₀`-degree `-4` and the `x₁`-degree `2` cancel against `B` and
   `2B` exactly (`gUni_nuLam_relWord`, `gUni_nuSq_relWord`).  This is the row analogue of
   what `SqClassClearingSupply` gave the marking side, in closed form uniform in `k`: the
   defect never carries a row or a functional bit, at any class.

2. **The defect reaches, and its tower part dies** (section 3).  `nuSq` is itself a
   selected marking, and the row carrier is exactly the admissible-correction space at
   `nu' = nuSq`.  So the kill ladder applies to the defect of any rung-`(j+1)` solution:
   `gUni_defect_reach` puts it in `gTowerReach h (nuSq h) j`, and `gJoin_reach_sep` with
   wave 79's `gExt_separationAll` and the zero readings of item 1 strips the handle towers:
   `gUni_defect_knob` lands the defect in the KNOB span, `Subgroup.closure
   (gTowerKnobSet h (nuSq h) j)`, at every depth `j ≥ 3`.

3. **The knob span is the engine-cost image, on the unit locus** (sections 4 to 6).  The
   engine cost of a single-slot carrier tuple evaluates to one marked-letter bracket or the
   `x₁`-bundle (`gUni_cost_slot*`), and on the unit locus the marked brackets recover the
   LETTER brackets exactly: `2 ∣ A - 1 - B` makes exactly one of the two core exponents
   odd, and the odd twist swaps the `σ`- and `x₀`-legs while the even one is invisible
   (`gUni_t_slot*`).  The far-slot letter reduction (`gTower_commHom_span`'s pattern on the
   `x₁`-free span) decomposes every far knob into letter brackets, the bundle knob is the
   `x₁`-slot cost on the nose, and the cost is multiplicative in the tuple
   (`gUni_cost_mul`), so `gUni_knob_cost` realizes every knob-span class as ONE engine
   cost.

4. **The rungs, uniformly** (section 7, ticket T2).  `gUni_step` turns a rung-`(j+1)`
   solution into a rung-`(j+2)` solution through items 2 and 3 and `gLad_step`, and
   `gUni_nonempty` climbs from wave 87's rung 4: `(gRowSet h A B k).Nonempty` at EVERY
   class `k` and every `(A, B)` on the unit locus.

5. **The composites** (section 8, ticket T3).  `gUni_pair` realizes every row pair on the
   unit locus, `gUni_clearing` discharges `SqNuOrientedClearAtUnitPivot h`
   unconditionally at every `h`, and the seam composites carry the odd-degree
   classification with the per-class hypothesis GONE.

## Honesty

The knob-span containment is proved on the unit locus and nowhere else: off it the parity
argument of item 3 loses the second core letter, and nothing here decides those rungs.
The negative directions of the graded campaign are untouched: the unrestricted layer
statement stays false (`gDeep_not_layerReach`), and the defect restriction of the kill
ladder remains essential; item 1 is exactly what pays it for the row frames.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`.  Everything through section 8's clearing
prints **std-3** (`propext`, `Classical.choice`, `Quot.sound`) or a subset; the two seam
composites of section 8b add the four census members the wave-83 seam always costs.  Pins
in section 10 with the honest split.
-/

open Multiplicative

namespace GQ2

open Roe Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore
open scoped commutatorElement

/-! ## §1 Level calculus at the uniform depth

Small general-level facts the wave-86 engine file states only at level 4: squares land in
the `λ₂`-image, `levelMk` distributes over brackets, and the `ℤ₂`-power calculus of a
`λ_j`-bracket sees only the parity of the exponent. -/

section LevelCalculus

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {j : ℕ}

/-- Squares lie in the `λ₂`-image, at every level. -/
theorem gUni_sq_mem_two (p : levelQuot G (j + 2)) : p ^ 2 ∈ lambdaImage G 2 (j + 2) := by
  obtain ⟨v, rfl⟩ := levelMk_surjective G (j + 2) p
  exact ⟨v ^ 2, sq_mem_twoCentralSeries_succ G (Subgroup.mem_top v), by rw [map_pow]⟩

/-- `levelMk` distributes over the bracket. -/
theorem gUni_mk_commP (k : ℕ) (a b : G) :
    levelMk G k (commP a b) = commP (levelMk G k a) (levelMk G k b) := by
  simp only [commP, map_mul, map_inv]

/-- Brackets out of a `λ_j`-image pair split exactly, in `Q_{j+2}`. -/
theorem gUni_commP_mul_left_lam {a : levelQuot G (j + 2)}
    (ha : a ∈ lambdaImage G j (j + 2)) (b g : levelQuot G (j + 2)) :
    commP (a * b) g = commP a g * commP b g := by
  rw [cfour_commP_mul_left,
    cfive_commP_zLayer_left (cfive_commP_mem_zLayer_left ha g) b, mul_one]

/-- Brackets into a `λ_j`-image pair split exactly, in `Q_{j+2}`. -/
theorem gUni_commP_mul_right_lam (p : levelQuot G (j + 2)) {q : levelQuot G (j + 2)}
    (hq : q ∈ lambdaImage G j (j + 2)) (r : levelQuot G (j + 2)) :
    commP p (q * r) = commP p q * commP p r := by
  have hz : commP p q ∈ zLayer G (j + 1) := cfive_commP_mem_zLayer_right p hq
  rw [cfour_commP_mul_right, cfive_commP_zLayer_left hz r, mul_one,
    (zLayer_commute hz (commP p r)).eq]

/-- Squares of `λ_j`-image pairs split at depth `j ≥ 2`, in `Q_{j+2}`. -/
theorem gUni_sq_mul_lam (hj : 2 ≤ j) {a b : levelQuot G (j + 2)}
    (ha : a ∈ lambdaImage G j (j + 2)) (hb : b ∈ lambdaImage G j (j + 2)) :
    (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
  rw [cfour_sq_mul, gLad_vanish (gLad_le_two hj hb) ha, cfour_one_comm, mul_one, mul_one]

/-- The central interchange: one central factor lets two products braid. -/
theorem gUni_central_interchange {z : levelQuot G (j + 2)} (hz : z ∈ zLayer G (j + 1))
    (a b w : levelQuot G (j + 2)) : a * z * (b * w) = a * b * (z * w) := by
  calc a * z * (b * w) = a * (z * b) * w := by group
    _ = a * (b * z) * w := by rw [(zLayer_commute hz b).eq]
    _ = a * b * (z * w) := by group

end LevelCalculus

/-! ## §2 The class-uniform defect: rows and functionals vanish at every class

The T1 payload.  The row frame is chi-standard for every carrier correction tuple, so wave
74's master kill reads every functional to zero on its relator value, and the degree
bookkeeping kills both rows: the class-`k` defect of the row ladder carries no row bit and
no functional bit, at ANY class, in closed form uniform in `k`. -/

section UniformDefect

variable {h : ℕ}

/-- **The row frame is chi-standard** for carrier corrections: the pivot is chi-trivial,
its `ℤ₂`-powers stay chi-trivial, and a `γ₂`-correction with trivial `λ`-row is
chi-trivial. -/
theorem gUni_chi_mark (A B : ℤ_[2]) {c : Fin (sqRank h) → (DSq h : Type)}
    (hc : ∀ i, c i ∈ gRowCorr h) (i : Fin (sqRank h)) :
    chiSq h (gRowMark h A B c i) = sqMark SvalUnit rootXUnit YvalUnit i := by
  rw [gRowMark_apply, map_mul, map_mul, gDelta_chiSq_gen,
    gJoin_chiSq_zpow (chiSq_sqPivot h) (gRowExp A B i), mul_one,
    gJoin_chiSq_of_gammaTwo (gRow_mem_corr.mp (hc i)).1.1 (gRow_mem_corr.mp (hc i)).1.2,
    mul_one]

/-- ⭐⭐⭐ **EVERY functional reads zero on EVERY row-frame relator value**: the master kill
of wave 74 applies to the row ansatz at every `(A, B)` and every carrier correction tuple.
This is the class-uniform form of the wave-87 observation that every rung-4 atom had
layer-bit reading zero, and it is what pays the kill ladder's defect restriction for the
row ladder at every class at once. -/
theorem gUni_delta_zero (A B : ℤ_[2]) {c : Fin (sqRank h) → (DSq h : Type)}
    (hc : ∀ i, c i ∈ gRowCorr h) (r : Fin (sqRank h) → ℤ_[2]) :
    gDelta h r (sqRelWord (gRowMark h A B c)) = 0 :=
  gDelta_relWord_of_chiFrame_eq_zero r (gUni_chi_mark A B hc)

/-- **The `λ`-row of the row-frame relator value is trivial**: degrees `-4` and `2` against
the letter rows `1` and `2`, with the chi-trivial pivot contributing nothing. -/
theorem gUni_nuLam_relWord (A B : ℤ_[2]) {c : Fin (sqRank h) → (DSq h : Type)}
    (hc : ∀ i, c i ∈ gRowCorr h) : nuLam h (sqRelWord (gRowMark h A B c)) = 1 := by
  refine Multiplicative.toAdd.injective ?_
  rw [gDelta_row_reading (nuLam h) (gRowMark h A B c), gRowMark_one, gRowMark_two]
  simp only [map_mul, toAdd_mul, toAdd_inv, toAdd_pow, toAdd_one, nuLam_x0, nuLam_x1,
    toAdd_map_zpowZtwo (isProP_DSq h) (nuLam h), toAdd_nuLam_sqPivot,
    (gRow_mem_corr.mp (hc 1)).1.2, (gRow_mem_corr.mp (hc 2)).1.2, toAdd_ofAdd]
  ring

/-- **The `ν_sq`-row of the row-frame relator value is trivial**: the exponent row
`(A - 1, B, 2B)` is the unique one whose degree-weighted sum vanishes, and it does. -/
theorem gUni_nuSq_relWord (A B : ℤ_[2]) {c : Fin (sqRank h) → (DSq h : Type)}
    (hc : ∀ i, c i ∈ gRowCorr h) : nuSq h (sqRelWord (gRowMark h A B c)) = 1 := by
  refine Multiplicative.toAdd.injective ?_
  rw [gDelta_row_reading (nuSq h) (gRowMark h A B c), gRowMark_one, gRowMark_two]
  simp only [map_mul, toAdd_mul, toAdd_inv, toAdd_pow, toAdd_one, nuSq_x0, nuSq_x1,
    toAdd_map_zpowZtwo (isProP_DSq h) (nuSq h), nuSq_sqPivot,
    (gRow_mem_corr.mp (hc 1)).2, (gRow_mem_corr.mp (hc 2)).2, toAdd_ofAdd]
  ring

/-! ## §3 The defect reaches, and its tower part dies

`nuSq` is a selected marking and the row carrier is the admissible-correction space at
`nu' = nuSq`, so the kill ladder applies to the row defect at every depth; the separation
plus §2's zero readings strip the handle towers, leaving the knob span. -/

/-- ⭐⭐ **The kill ladder applies to the row defect**: the class of the relator value of a
rung-`(j+1)` solution lies in the tower reach at depth `j`, for every `j ≥ 2`.  Rows vanish
by §2, functionals vanish by §2, and `gGen_killAt` does the rest. -/
theorem gUni_defect_reach {A B : ℤ_[2]} {j : ℕ} (hj : 2 ≤ j)
    {c : Fin (sqRank h) → (DSq h : Type)} (hc : c ∈ gRowSet h A B (j + 1)) :
    levelMk (DSq h : Type) (j + 2) (sqRelWord (gRowMark h A B c))
      ∈ gTowerReach h (nuSq h) j :=
  gGen_killAt j hj (nuSq h) (nuSq_sigma h) (nuSq_x0 h) _ hc.2
    (gUni_nuLam_relWord A B hc.1) (gUni_nuSq_relWord A B hc.1)
    (gUni_delta_zero A B hc.1)

/-- ⭐⭐⭐ **The row defect lands in the KNOB span**: at every depth `j ≥ 3` the separation
strips the handle towers from the reach, because §2 makes every handle-row reading zero.
What remains is exactly the part of the layer the row engine can spend. -/
theorem gUni_defect_knob {A B : ℤ_[2]} {j : ℕ} (hj : 3 ≤ j)
    {c : Fin (sqRank h) → (DSq h : Type)} (hc : c ∈ gRowSet h A B (j + 1)) :
    levelMk (DSq h : Type) (j + 2) (sqRelWord (gRowMark h A B c))
      ∈ Subgroup.closure (gTowerKnobSet h (nuSq h) j) := by
  obtain ⟨k', rfl⟩ : ∃ k', j = k' + 2 := ⟨j - 2, by omega⟩
  exact gJoin_reach_sep (nuSq_x0 h) (gExt_separationAll h (nuSq h) (k' + 2) (by omega))
    (gUni_defect_reach (by omega) hc)
    (fun jj => gJoin_mem_layerDvd.2 (by
      rw [gUni_delta_zero A B hc.1 (gJoinRowU jj)]; exact dvd_zero _))
    (fun jj => gJoin_mem_layerDvd.2 (by
      rw [gUni_delta_zero A B hc.1 (gJoinRowV jj)]; exact dvd_zero _))

end UniformDefect

end SqCore

end Dyadic

end GQ2

/-! ## §4 Axiom pins (added at merge; the lane was cut off before writing them)

Every declaration of this file, in order.  **All twelve print exactly the standard three**
(`propext`, `Classical.choice`, `Quot.sound`), verified at the W88 close.  This section
replaces the "section 10" the module docstring promises, which the lane never reached. -/

#print axioms GQ2.Dyadic.SqCore.gUni_sq_mem_two
#print axioms GQ2.Dyadic.SqCore.gUni_mk_commP
#print axioms GQ2.Dyadic.SqCore.gUni_commP_mul_left_lam
#print axioms GQ2.Dyadic.SqCore.gUni_commP_mul_right_lam
#print axioms GQ2.Dyadic.SqCore.gUni_sq_mul_lam
#print axioms GQ2.Dyadic.SqCore.gUni_central_interchange
#print axioms GQ2.Dyadic.SqCore.gUni_chi_mark
#print axioms GQ2.Dyadic.SqCore.gUni_delta_zero
#print axioms GQ2.Dyadic.SqCore.gUni_nuLam_relWord
#print axioms GQ2.Dyadic.SqCore.gUni_nuSq_relWord
#print axioms GQ2.Dyadic.SqCore.gUni_defect_reach
#print axioms GQ2.Dyadic.SqCore.gUni_defect_knob
