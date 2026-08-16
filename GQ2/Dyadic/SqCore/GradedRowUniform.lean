/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.SqCore.GradedRowResidue
import GQ2.Dyadic.SqCore.GradedUniformGen

/-!
# W88-UNIFORM: the uniform-in-class supply on the row-move ladder

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

/-! ## §4 Single-slot tuples and their engine costs

The engine cost of a carrier tuple supported on one slot is one marked-letter bracket, or
the `x₁`-bundle: the five cases of `gLadCost`, evaluated. -/

section SlotTuples

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {j : ℕ}

private theorem gUni_listProd_succ {M : Type*} [Monoid M] {n : ℕ} (f : Fin (n + 1) → M) :
    ((List.finRange (n + 1)).map f).prod
      = f 0 * ((List.finRange n).map fun i => f i.succ).prod := by
  rw [List.finRange_succ, List.map_cons, List.prod_cons, List.map_map]
  rfl

private theorem gUni_listProd_one {M : Type*} [Monoid M] {n : ℕ} {f : Fin n → M}
    (hf : ∀ i, f i = 1) : ((List.finRange n).map f).prod = 1 :=
  List.prod_eq_one (by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact hf i)

private theorem gUni_listProd_single {M : Type*} [Monoid M] :
    ∀ {n : ℕ} (f : Fin n → M) (j₀ : Fin n), (∀ i, i ≠ j₀ → f i = 1) →
      ((List.finRange n).map f).prod = f j₀ := by
  intro n
  induction n with
  | zero => exact fun _ j₀ _ => j₀.elim0
  | succ n ih =>
    intro f j₀ hf
    rw [gUni_listProd_succ]
    rcases Fin.eq_zero_or_eq_succ j₀ with rfl | ⟨j', rfl⟩
    · rw [gUni_listProd_one (f := fun i => f i.succ)
        (fun i => hf i.succ (Fin.succ_ne_zero i)), mul_one]
    · rw [hf 0 (Fin.succ_ne_zero j').symm, one_mul]
      exact ih (fun i => f i.succ) j'
        (fun i hi => hf i.succ (fun hcon => hi (Fin.succ_inj.mp hcon)))

/-- The all-but-one-trivial handle product collapses onto the `U`-bracket of the marked
slot. -/
private theorem gUni_handleProd_singleU {n : ℕ} (m εq : Fin (sqRank n) → levelQuot G (j + 2))
    (j₀ : Fin n) (hU : ∀ i, i ≠ j₀ → εq (sqHandleIdxU i) = 1)
    (hV : ∀ i, εq (sqHandleIdxV i) = 1) :
    ((List.finRange n).map fun i => commP (εq (sqHandleIdxU i)) (m (sqHandleIdxV i))
        * commP (m (sqHandleIdxU i)) (εq (sqHandleIdxV i))).prod
      = commP (εq (sqHandleIdxU j₀)) (m (sqHandleIdxV j₀)) := by
  rw [gUni_listProd_single _ j₀ (fun i hi => by
    rw [hU i hi, hV i, cfour_one_comm, cfour_comm_one, one_mul])]
  show commP (εq (sqHandleIdxU j₀)) (m (sqHandleIdxV j₀))
      * commP (m (sqHandleIdxU j₀)) (εq (sqHandleIdxV j₀)) = _
  rw [hV j₀, cfour_comm_one, mul_one]

/-- The all-but-one-trivial handle product collapses onto the `V`-bracket of the marked
slot. -/
private theorem gUni_handleProd_singleV {n : ℕ} (m εq : Fin (sqRank n) → levelQuot G (j + 2))
    (j₀ : Fin n) (hU : ∀ i, εq (sqHandleIdxU i) = 1)
    (hV : ∀ i, i ≠ j₀ → εq (sqHandleIdxV i) = 1) :
    ((List.finRange n).map fun i => commP (εq (sqHandleIdxU i)) (m (sqHandleIdxV i))
        * commP (m (sqHandleIdxU i)) (εq (sqHandleIdxV i))).prod
      = commP (m (sqHandleIdxU j₀)) (εq (sqHandleIdxV j₀)) := by
  rw [gUni_listProd_single _ j₀ (fun i hi => by
    rw [hU i, hV i hi, cfour_one_comm, cfour_comm_one, one_mul])]
  show commP (εq (sqHandleIdxU j₀)) (m (sqHandleIdxV j₀))
      * commP (m (sqHandleIdxU j₀)) (εq (sqHandleIdxV j₀)) = _
  rw [hU j₀, cfour_one_comm, one_mul]

end SlotTuples

section SlotTuplesD

variable {h : ℕ}

/-- **The single-slot tuple**: the carrier word `t` on slot `i₀`, `1` everywhere else. -/
noncomputable def gUniSlot (i₀ : Fin (sqRank h)) (t : (DSq h : Type)) :
    Fin (sqRank h) → (DSq h : Type) :=
  fun i => if (i : ℕ) = (i₀ : ℕ) then t else 1

theorem gUniSlot_same (i₀ : Fin (sqRank h)) (t : (DSq h : Type)) : gUniSlot i₀ t i₀ = t :=
  if_pos rfl

theorem gUniSlot_ne {i i₀ : Fin (sqRank h)} (hne : (i : ℕ) ≠ (i₀ : ℕ)) (t : (DSq h : Type)) :
    gUniSlot i₀ t i = 1 :=
  if_neg hne

theorem gUniSlot_mem {j : ℕ} {t : (DSq h : Type)}
    (ht : t ∈ twoCentralSeries (DSq h : Type) j) (i₀ : Fin (sqRank h)) :
    ∀ i, gUniSlot i₀ t i ∈ twoCentralSeries (DSq h : Type) j := by
  intro i
  simp only [gUniSlot]
  split
  · exact ht
  · exact one_mem _

theorem gUniSlot_nuLam {t : (DSq h : Type)} (ht : nuLam h t = 1) (i₀ : Fin (sqRank h)) :
    ∀ i, nuLam h (gUniSlot i₀ t i) = 1 := by
  intro i
  simp only [gUniSlot]
  split
  · exact ht
  · exact map_one _

theorem gUniSlot_nuSq {t : (DSq h : Type)} (ht : nuSq h t = 1) (i₀ : Fin (sqRank h)) :
    ∀ i, nuSq h (gUniSlot i₀ t i) = 1 := by
  intro i
  simp only [gUniSlot]
  split
  · exact ht
  · exact map_one _

variable {j : ℕ}

/-- The `σ`-slot cost: the bracket against the marked `x₀`-letter. -/
theorem gUni_cost_slot0 (m : Fin (sqRank h) → levelQuot (DSq h : Type) (j + 2))
    (t : (DSq h : Type)) :
    gLadCost m (fun i => levelMk (DSq h : Type) (j + 2) (gUniSlot 0 t i))
      = commP (levelMk (DSq h : Type) (j + 2) t) (m 1) := by
  have h0 : gUniSlot (0 : Fin (sqRank h)) t 0 = t := gUniSlot_same _ _
  have h1 : gUniSlot (0 : Fin (sqRank h)) t 1 = 1 :=
    gUniSlot_ne (by rw [sqVal_one, sqVal_zero]; omega) t
  have h2 : gUniSlot (0 : Fin (sqRank h)) t 2 = 1 :=
    gUniSlot_ne (by rw [sqVal_two, sqVal_zero]; omega) t
  have hU : ∀ i : Fin h, gUniSlot (0 : Fin (sqRank h)) t (sqHandleIdxU i) = 1 :=
    fun i => gUniSlot_ne (by rw [sqHandleIdxU_val, sqVal_zero]; omega) t
  have hV : ∀ i : Fin h, gUniSlot (0 : Fin (sqRank h)) t (sqHandleIdxV i) = 1 :=
    fun i => gUniSlot_ne (by rw [sqHandleIdxV_val, sqVal_zero]; omega) t
  simp only [gLadCost, h0, h1, h2, hU, hV, map_one, cfour_one_comm, cfour_comm_one,
    one_pow, one_mul, mul_one]
  rw [gUni_listProd_one (fun i => by rw [one_mul]), mul_one]

/-- The `x₀`-slot cost: the bracket of the marked `σ`-letter. -/
theorem gUni_cost_slot1 (m : Fin (sqRank h) → levelQuot (DSq h : Type) (j + 2))
    (t : (DSq h : Type)) :
    gLadCost m (fun i => levelMk (DSq h : Type) (j + 2) (gUniSlot 1 t i))
      = commP (m 0) (levelMk (DSq h : Type) (j + 2) t) := by
  have h0 : gUniSlot (1 : Fin (sqRank h)) t 0 = 1 :=
    gUniSlot_ne (by rw [sqVal_one, sqVal_zero]; omega) t
  have h1 : gUniSlot (1 : Fin (sqRank h)) t 1 = t := gUniSlot_same _ _
  have h2 : gUniSlot (1 : Fin (sqRank h)) t 2 = 1 :=
    gUniSlot_ne (by rw [sqVal_two, sqVal_one]; omega) t
  have hU : ∀ i : Fin h, gUniSlot (1 : Fin (sqRank h)) t (sqHandleIdxU i) = 1 :=
    fun i => gUniSlot_ne (by rw [sqHandleIdxU_val, sqVal_one]; omega) t
  have hV : ∀ i : Fin h, gUniSlot (1 : Fin (sqRank h)) t (sqHandleIdxV i) = 1 :=
    fun i => gUniSlot_ne (by rw [sqHandleIdxV_val, sqVal_one]; omega) t
  simp only [gLadCost, h0, h1, h2, hU, hV, map_one, cfour_one_comm, cfour_comm_one,
    one_pow, one_mul, mul_one]
  rw [gUni_listProd_one (fun i => by rw [one_mul]), mul_one]

/-- The `x₁`-slot cost: the bundle against the marked `x₁`-letter. -/
theorem gUni_cost_slot2 (m : Fin (sqRank h) → levelQuot (DSq h : Type) (j + 2))
    (t : (DSq h : Type)) :
    gLadCost m (fun i => levelMk (DSq h : Type) (j + 2) (gUniSlot 2 t i))
      = levelMk (DSq h : Type) (j + 2) t ^ 2
        * commP (levelMk (DSq h : Type) (j + 2) t) (m 2) := by
  have h0 : gUniSlot (2 : Fin (sqRank h)) t 0 = 1 :=
    gUniSlot_ne (by rw [sqVal_two, sqVal_zero]; omega) t
  have h1 : gUniSlot (2 : Fin (sqRank h)) t 1 = 1 :=
    gUniSlot_ne (by rw [sqVal_two, sqVal_one]; omega) t
  have h2 : gUniSlot (2 : Fin (sqRank h)) t 2 = t := gUniSlot_same _ _
  have hU : ∀ i : Fin h, gUniSlot (2 : Fin (sqRank h)) t (sqHandleIdxU i) = 1 :=
    fun i => gUniSlot_ne (by rw [sqHandleIdxU_val, sqVal_two]; omega) t
  have hV : ∀ i : Fin h, gUniSlot (2 : Fin (sqRank h)) t (sqHandleIdxV i) = 1 :=
    fun i => gUniSlot_ne (by rw [sqHandleIdxV_val, sqVal_two]; omega) t
  simp only [gLadCost, h0, h1, h2, hU, hV, map_one, cfour_one_comm, cfour_comm_one,
    one_pow, one_mul, mul_one]
  rw [gUni_listProd_one (fun i => by rw [one_mul]), mul_one]

/-- The `u`-handle cost: the bracket against the marked partner `v`-letter. -/
theorem gUni_cost_slotU (m : Fin (sqRank h) → levelQuot (DSq h : Type) (j + 2))
    (t : (DSq h : Type)) (j₀ : Fin h) :
    gLadCost m (fun i => levelMk (DSq h : Type) (j + 2) (gUniSlot (sqHandleIdxU j₀) t i))
      = commP (levelMk (DSq h : Type) (j + 2) t) (m (sqHandleIdxV j₀)) := by
  have h0 : gUniSlot (sqHandleIdxU j₀) t 0 = 1 :=
    gUniSlot_ne (by rw [sqVal_zero, sqHandleIdxU_val]; omega) t
  have h1 : gUniSlot (sqHandleIdxU j₀) t 1 = 1 :=
    gUniSlot_ne (by rw [sqVal_one, sqHandleIdxU_val]; omega) t
  have h2 : gUniSlot (sqHandleIdxU j₀) t 2 = 1 :=
    gUniSlot_ne (by rw [sqVal_two, sqHandleIdxU_val]; omega) t
  have hV : ∀ i : Fin h,
      levelMk (DSq h : Type) (j + 2) (gUniSlot (sqHandleIdxU j₀) t (sqHandleIdxV i)) = 1 :=
    fun i => by
      rw [gUniSlot_ne (by rw [sqHandleIdxV_val, sqHandleIdxU_val]; omega) t, map_one]
  have hU : ∀ i : Fin h, i ≠ j₀ →
      levelMk (DSq h : Type) (j + 2) (gUniSlot (sqHandleIdxU j₀) t (sqHandleIdxU i)) = 1 :=
    fun i hi => by
      rw [gUniSlot_ne (by
        rw [sqHandleIdxU_val, sqHandleIdxU_val]
        intro hcon
        exact hi (Fin.ext (by omega))) t, map_one]
  simp only [gLadCost, h0, h1, h2, map_one, cfour_one_comm, cfour_comm_one,
    one_pow, one_mul, mul_one]
  rw [gUni_handleProd_singleU m _ j₀ hU hV, gUniSlot_same]

/-- The `v`-handle cost: the bracket of the marked partner `u`-letter. -/
theorem gUni_cost_slotV (m : Fin (sqRank h) → levelQuot (DSq h : Type) (j + 2))
    (t : (DSq h : Type)) (j₀ : Fin h) :
    gLadCost m (fun i => levelMk (DSq h : Type) (j + 2) (gUniSlot (sqHandleIdxV j₀) t i))
      = commP (m (sqHandleIdxU j₀)) (levelMk (DSq h : Type) (j + 2) t) := by
  have h0 : gUniSlot (sqHandleIdxV j₀) t 0 = 1 :=
    gUniSlot_ne (by rw [sqVal_zero, sqHandleIdxV_val]; omega) t
  have h1 : gUniSlot (sqHandleIdxV j₀) t 1 = 1 :=
    gUniSlot_ne (by rw [sqVal_one, sqHandleIdxV_val]; omega) t
  have h2 : gUniSlot (sqHandleIdxV j₀) t 2 = 1 :=
    gUniSlot_ne (by rw [sqVal_two, sqHandleIdxV_val]; omega) t
  have hU : ∀ i : Fin h,
      levelMk (DSq h : Type) (j + 2) (gUniSlot (sqHandleIdxV j₀) t (sqHandleIdxU i)) = 1 :=
    fun i => by
      rw [gUniSlot_ne (by rw [sqHandleIdxU_val, sqHandleIdxV_val]; omega) t, map_one]
  have hV : ∀ i : Fin h, i ≠ j₀ →
      levelMk (DSq h : Type) (j + 2) (gUniSlot (sqHandleIdxV j₀) t (sqHandleIdxV i)) = 1 :=
    fun i hi => by
      rw [gUniSlot_ne (by
        rw [sqHandleIdxV_val, sqHandleIdxV_val]
        intro hcon
        exact hi (Fin.ext (by omega))) t, map_one]
  simp only [gLadCost, h0, h1, h2, map_one, cfour_one_comm, cfour_comm_one,
    one_pow, one_mul, mul_one]
  rw [gUni_handleProd_singleV m _ j₀ hU hV, gUniSlot_same]

end SlotTuplesD

/-! ## §5 The letter brackets of the marked slots, on the unit locus

For an admissible correction `t` at depth `j`, the bracket of `t` against a marked letter
reads only the letter and the PARITY of the pivot exponent, and on the unit locus exactly
one of the two core exponents is odd: the odd twist swaps the `σ`- and `x₀`-legs, so both
letter brackets are marked-slot brackets. -/

section LetterBrackets

variable {h : ℕ} {j : ℕ}

/-- Corrections are invisible to admissible brackets. -/
theorem gUni_t_corr {t x : (DSq h : Type)} (ht : t ∈ twoCentralSeries (DSq h : Type) j)
    (hx : x ∈ gRowCorr h) :
    commP (levelMk (DSq h : Type) (j + 2) t) (levelMk (DSq h : Type) (j + 2) x) = 1 :=
  gLad_vanish' ⟨x, (gRow_mem_corr.mp hx).1.1, rfl⟩ ⟨t, ht, rfl⟩

/-- Even `ℤ₂`-powers are invisible to admissible brackets. -/
theorem gUni_t_zpow_even {t : (DSq h : Type)} (ht : t ∈ twoCentralSeries (DSq h : Type) j)
    (g : (DSq h : Type)) {e : ℤ_[2]} (he : (2 : ℤ_[2]) ∣ e) :
    commP (levelMk (DSq h : Type) (j + 2) t)
      (levelMk (DSq h : Type) (j + 2) (zpowZtwo (isProP_DSq h) g e)) = 1 := by
  obtain ⟨s, rfl⟩ := he
  rw [zpowZtwo_two_mul, map_pow]
  exact gLad_vanish' (gUni_sq_mem_two _) ⟨t, ht, rfl⟩

/-- Odd `ℤ₂`-powers bracket like their base against admissible corrections. -/
theorem gUni_t_zpow_odd {t : (DSq h : Type)} (ht : t ∈ twoCentralSeries (DSq h : Type) j)
    (g : (DSq h : Type)) {e : ℤ_[2]} (he : ¬ (2 : ℤ_[2]) ∣ e) :
    commP (levelMk (DSq h : Type) (j + 2) t)
        (levelMk (DSq h : Type) (j + 2) (zpowZtwo (isProP_DSq h) g e))
      = commP (levelMk (DSq h : Type) (j + 2) t) (levelMk (DSq h : Type) (j + 2) g) := by
  obtain ⟨s, hs⟩ := two_dvd_sub_of_isUnit (isUnit_iff_not_two_dvd.mpr he) isUnit_one
  have hsplit : zpowZtwo (isProP_DSq h) g e
      = zpowZtwo (isProP_DSq h) g 1 * zpowZtwo (isProP_DSq h) g (2 * s) := by
    rw [← zpowZtwo_add]
    congr 1
    linear_combination hs
  rw [hsplit, zpowZtwo_one_exp, zpowZtwo_two_mul, map_mul, map_pow,
    cfive_commP_right_hom ⟨t, ht, rfl⟩,
    gLad_vanish' (gUni_sq_mem_two _) ⟨t, ht, rfl⟩, one_mul]

/-- **The pivot bracket splits over the two core letters**: `[t, w] = [t, x₀] [t, σ]` for
every admissible `t` (the `x₀`-leg keeps its inverse only up to the layer involution). -/
theorem gUni_t_pivot {t : (DSq h : Type)} (ht : t ∈ twoCentralSeries (DSq h : Type) j) :
    commP (levelMk (DSq h : Type) (j + 2) t) (levelMk (DSq h : Type) (j + 2) (sqPivot h))
      = commP (levelMk (DSq h : Type) (j + 2) t)
          (levelMk (DSq h : Type) (j + 2) (dsqX0 h))
        * commP (levelMk (DSq h : Type) (j + 2) t)
            (levelMk (DSq h : Type) (j + 2) (dsqSigma h)) := by
  have hX : commP (levelMk (DSq h : Type) (j + 2) t)
      (levelMk (DSq h : Type) (j + 2) (dsqX0 h)) ∈ zLayer (DSq h : Type) (j + 1) :=
    cfive_commP_mem_zLayer_left ⟨t, ht, rfl⟩ _
  rw [sqPivot, sqMixPivotElem, map_mul, map_inv,
    cfive_commP_right_hom ⟨t, ht, rfl⟩,
    gLad_commP_inv_right ⟨t, ht, rfl⟩,
    gUni_t_zpow_odd ht (dsqX0 h) (isUnit_iff_not_two_dvd.mp isUnit_sqPivotExp),
    zLayer_inv_self hX]

variable {A B : ℤ_[2]} {c : Fin (sqRank h) → (DSq h : Type)}

/-- The marked `x₀`-slot at even `B`: the bare `x₀`-bracket. -/
theorem gUni_t_slot1_even (hc : ∀ i, c i ∈ gRowCorr h) {t : (DSq h : Type)}
    (ht : t ∈ twoCentralSeries (DSq h : Type) j) (hB : (2 : ℤ_[2]) ∣ B) :
    commP (levelMk (DSq h : Type) (j + 2) t)
        (levelMk (DSq h : Type) (j + 2) (gRowMark h A B c 1))
      = commP (levelMk (DSq h : Type) (j + 2) t)
          (levelMk (DSq h : Type) (j + 2) (dsqX0 h)) := by
  rw [gRowMark_one, map_mul, map_mul, cfive_commP_right_hom ⟨t, ht, rfl⟩,
    gUni_t_corr ht (hc 1), one_mul, cfive_commP_right_hom ⟨t, ht, rfl⟩,
    gUni_t_zpow_even ht (sqPivot h) hB, one_mul]

/-- The marked `x₀`-slot at odd `B`: the legs swap onto the `σ`-bracket. -/
theorem gUni_t_slot1_odd (hc : ∀ i, c i ∈ gRowCorr h) {t : (DSq h : Type)}
    (ht : t ∈ twoCentralSeries (DSq h : Type) j) (hB : ¬ (2 : ℤ_[2]) ∣ B) :
    commP (levelMk (DSq h : Type) (j + 2) t)
        (levelMk (DSq h : Type) (j + 2) (gRowMark h A B c 1))
      = commP (levelMk (DSq h : Type) (j + 2) t)
          (levelMk (DSq h : Type) (j + 2) (dsqSigma h)) := by
  have hX : commP (levelMk (DSq h : Type) (j + 2) t)
      (levelMk (DSq h : Type) (j + 2) (dsqX0 h)) ∈ zLayer (DSq h : Type) (j + 1) :=
    cfive_commP_mem_zLayer_left ⟨t, ht, rfl⟩ _
  rw [gRowMark_one, map_mul, map_mul, cfive_commP_right_hom ⟨t, ht, rfl⟩,
    gUni_t_corr ht (hc 1), one_mul, cfive_commP_right_hom ⟨t, ht, rfl⟩,
    gUni_t_zpow_odd ht (sqPivot h) hB, gUni_t_pivot ht,
    (zLayer_commute hX (commP (levelMk (DSq h : Type) (j + 2) t)
      (levelMk (DSq h : Type) (j + 2) (dsqSigma h)))).eq,
    mul_assoc, ← pow_two, zLayer_sq (DSq h : Type) hX, mul_one]

/-- The marked `σ`-slot at even `A - 1`: the bare `σ`-bracket. -/
theorem gUni_t_slot0_even (hc : ∀ i, c i ∈ gRowCorr h) {t : (DSq h : Type)}
    (ht : t ∈ twoCentralSeries (DSq h : Type) j) (hA : (2 : ℤ_[2]) ∣ A - 1) :
    commP (levelMk (DSq h : Type) (j + 2) t)
        (levelMk (DSq h : Type) (j + 2) (gRowMark h A B c 0))
      = commP (levelMk (DSq h : Type) (j + 2) t)
          (levelMk (DSq h : Type) (j + 2) (dsqSigma h)) := by
  rw [gRowMark_zero, map_mul, map_mul, cfive_commP_right_hom ⟨t, ht, rfl⟩,
    gUni_t_corr ht (hc 0), one_mul, cfive_commP_right_hom ⟨t, ht, rfl⟩,
    gUni_t_zpow_even ht (sqPivot h) hA, one_mul]

/-- The marked `σ`-slot at odd `A - 1`: the legs swap onto the `x₀`-bracket. -/
theorem gUni_t_slot0_odd (hc : ∀ i, c i ∈ gRowCorr h) {t : (DSq h : Type)}
    (ht : t ∈ twoCentralSeries (DSq h : Type) j) (hA : ¬ (2 : ℤ_[2]) ∣ A - 1) :
    commP (levelMk (DSq h : Type) (j + 2) t)
        (levelMk (DSq h : Type) (j + 2) (gRowMark h A B c 0))
      = commP (levelMk (DSq h : Type) (j + 2) t)
          (levelMk (DSq h : Type) (j + 2) (dsqX0 h)) := by
  have hS : commP (levelMk (DSq h : Type) (j + 2) t)
      (levelMk (DSq h : Type) (j + 2) (dsqSigma h)) ∈ zLayer (DSq h : Type) (j + 1) :=
    cfive_commP_mem_zLayer_left ⟨t, ht, rfl⟩ _
  rw [gRowMark_zero, map_mul, map_mul, cfive_commP_right_hom ⟨t, ht, rfl⟩,
    gUni_t_corr ht (hc 0), one_mul, cfive_commP_right_hom ⟨t, ht, rfl⟩,
    gUni_t_zpow_odd ht (sqPivot h) hA, gUni_t_pivot ht,
    mul_assoc, ← pow_two, zLayer_sq (DSq h : Type) hS, mul_one]

/-- The marked `x₁`-slot: always the bare `x₁`-bracket (its exponent `2B` is even). -/
theorem gUni_t_slot2 (hc : ∀ i, c i ∈ gRowCorr h) {t : (DSq h : Type)}
    (ht : t ∈ twoCentralSeries (DSq h : Type) j) :
    commP (levelMk (DSq h : Type) (j + 2) t)
        (levelMk (DSq h : Type) (j + 2) (gRowMark h A B c 2))
      = commP (levelMk (DSq h : Type) (j + 2) t)
          (levelMk (DSq h : Type) (j + 2) (dsqX1 h)) := by
  rw [gRowMark_two, map_mul, map_mul, cfive_commP_right_hom ⟨t, ht, rfl⟩,
    gUni_t_corr ht (hc 2), one_mul, cfive_commP_right_hom ⟨t, ht, rfl⟩,
    gUni_t_zpow_even ht (sqPivot h) ⟨B, rfl⟩, one_mul]

/-- The marked `u`-handle slots: the bare handle brackets. -/
theorem gUni_t_slotU (hc : ∀ i, c i ∈ gRowCorr h) {t : (DSq h : Type)}
    (ht : t ∈ twoCentralSeries (DSq h : Type) j) (j₀ : Fin h) :
    commP (levelMk (DSq h : Type) (j + 2) t)
        (levelMk (DSq h : Type) (j + 2) (gRowMark h A B c (sqHandleIdxU j₀)))
      = commP (levelMk (DSq h : Type) (j + 2) t)
          (levelMk (DSq h : Type) (j + 2) (sqGen h (sqHandleIdxU j₀))) := by
  rw [gRowMark_handleU, map_mul, cfive_commP_right_hom ⟨t, ht, rfl⟩,
    gUni_t_corr ht (hc _), one_mul]

/-- The marked `v`-handle slots: the bare handle brackets. -/
theorem gUni_t_slotV (hc : ∀ i, c i ∈ gRowCorr h) {t : (DSq h : Type)}
    (ht : t ∈ twoCentralSeries (DSq h : Type) j) (j₀ : Fin h) :
    commP (levelMk (DSq h : Type) (j + 2) t)
        (levelMk (DSq h : Type) (j + 2) (gRowMark h A B c (sqHandleIdxV j₀)))
      = commP (levelMk (DSq h : Type) (j + 2) t)
          (levelMk (DSq h : Type) (j + 2) (sqGen h (sqHandleIdxV j₀))) := by
  rw [gRowMark_handleV, map_mul, cfive_commP_right_hom ⟨t, ht, rfl⟩,
    gUni_t_corr ht (hc _), one_mul]

end LetterBrackets

end SqCore

end Dyadic

end GQ2
