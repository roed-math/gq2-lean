/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.LamFrames

/-!
# W44 — ⚠ the Eichler ansatz is **refuted**

`SqCore/LamFrames.lean` §3 cut the whole `h ≥ 1` residual down to one word equation,
`SqEichRelWord h`: at every selected marking and every handle, some `V`-dressing weights
`(e, e', d)` kill the relator on `sqEichFrame`.  **That equation is false.**

## The witness

Take the selected marking `ν' = nuSel h j 0 1` — rows `ν'(σ) = 1`, `ν'(x₀) = 0`, `ν'(u_j) = 0`,
`ν'(v_j) = 1`.  Then `sqRelWord (sqEichFrame h ν' j e e' d) ≠ 1` for **every** `(e, e', d)`
(`not_sqRelWord_sqEichFrame_nuSel`), hence `¬ SqEichRelWord h` at every `h ≥ 1`
(`not_sqEichRelWord`).

## The obstruction, in one line

The frame's `v`-slot is `V = v_j·w^{−s}`, and `s = ν'(v_j) = 1`, so **`V` is the one letter the
frame *changes* in order to clear the `v_j`-row** — and every other moved slot is dressed by a
power of that same `V`.  Send `D_sq h` to a group where `V` dies: the dressings all die with it,
the four dressed slots fall back to their undressed values, and the `j`-th handle commutator
`[U·V^d, V]` becomes `[U, 1] = 1`.  What is left is the bare core word — which the relator says
is the *inverse* of that very commutator, so it is `≠ 1` exactly when the commutator was.

Concretely, in the order-8 group `D₄ ≅ Heis(𝔽₂)` (marking `refMark`: `σ ↦ sr 0`, `x₀ ↦ 1`,
`x₁ ↦ r 1`, `u_j ↦ sr 1`, `v_j ↦ sr 0`, every other letter `↦ 1`) the pivot `w = σ·x₀^{−c₀}`
goes to `sr 0` (no fact about `c₀` is used: `x₀ ↦ 1` and `1^{c₀} = 1`), so `V ↦ sr 0·(sr 0)⁻¹ = 1`
and `U ↦ sr 1`.  The relator holds because `C ↦ (r 1)² = r 2` and `[sr 1, sr 0] = r 2` cancel;
the frame's relator keeps the `r 2` and loses the cancelling commutator.

## ⚠ What died, and what did **not**

* **Dead**: the five-word Eichler frame `sqEichFrame` as an ansatz for the residual — not merely
  "at the class-two-forced parameters", but at *every* `(e, e', d)`, and already at a marking with
  `ν'(u_j) = 0`.  So the failure is not a near miss to be fixed by a correction term.
* **Not dead**: `SqLamMarkTransitivity h` itself.  `sqLamMarkTransitivity_iff_frames` quantifies
  over **all** five-word frames; this file kills one explicitly parametrised family of them.
* **Not dead**: the Eichler *idea*.  The diagnosis is that `sqEichFrame` is **asymmetric** — it
  offers `V`-dressings only, i.e. it is built to clear a `u_j`-row by subtracting pivot from
  `u_j`, and it has no `U`-dressing with which to clear a `v_j`-row.  The `v_j`-row is what
  breaks it.  A transposed family (dress by `U`-powers, move `v_j`) plus a composition of the two
  is the obvious repair, and §3 of `LamFrames` already supplies the composition machinery: a
  clearing step only has to leave the *other* handles alone.

## Contents

* **§1** the target `D₄` as a pro-2 group, and `handleWord_eq_single`;
* **§2** the refuting marking `refMark`, its relator, and the hom `refHom`;
* **§3** the images of the pivot, `V`, `U` and the frame, and the refutation;
* **§4** stress pins, **§5** committed axiom prints.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide` (the `decide` calls are all on the order-8 group
`D₄`).  Every declaration prints **std-3**.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The target, and a handle-block evaluation

The refutation needs one nonabelian pro-2 group in which everything is decidable.  The smallest
one that works is `D₄ ≅ Heis(𝔽₂)`, order 8, with the discrete topology: a finite 2-group is
pro-2 (`isProP_of_isPGroup`), and every other instance the lift needs is automatic for a finite
discrete group. -/

section Target

local instance instTopologicalSpaceD4 : TopologicalSpace (DihedralGroup 4) := ⊥
local instance instDiscreteTopologyD4 : DiscreteTopology (DihedralGroup 4) := ⟨rfl⟩

/-- `D₄` is pro-2: every element has order dividing `4`. -/
theorem isProP_two_dihedral4 : IsProP 2 (DihedralGroup 4) :=
  isProP_of_isPGroup fun g => ⟨2, by revert g; decide⟩

/-- A handle block in which only the `j`-th commutator survives **is** that commutator. -/
theorem handleWord_eq_single {G : Type*} [Group G] {h : ℕ} (u v : Fin h → G) (j : Fin h)
    (hne : ∀ i : Fin h, i ≠ j → commP (u i) (v i) = 1) :
    handleWord u v = commP (u j) (v j) := by
  have hpre : handlePrefix u v (j : ℕ) = 1 := by
    rw [handlePrefix, List.prod_eq_one]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hne i fun hc => absurd (mem_take_finRange hi) (by rw [hc]; omega)
  have hsuf : handleSuffix u v ((j : ℕ) + 1) = 1 := by
    rw [handleSuffix, List.prod_eq_one]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hne i fun hc => absurd (mem_drop_finRange hi) (by rw [hc]; omega)
  rw [handleWord_split u v j, hpre, hsuf, one_mul, mul_one]

/-! ## §2 The refuting marking -/

/-- `σ`'s value, and `v_j`'s: a reflection. -/
private abbrev refS : DihedralGroup 4 := DihedralGroup.sr 0

/-- `u_j`'s value: the other reflection.  `[refQ, refS] = r 2 ≠ 1`. -/
private abbrev refQ : DihedralGroup 4 := DihedralGroup.sr 1

/-- `x₁`'s value: a rotation of order four, so `refY ^ 2 = r 2` is the same central element. -/
private abbrev refY : DihedralGroup 4 := DihedralGroup.r 1

variable {h : ℕ} {j : Fin h}

/-- **The refuting marking**: `σ ↦ refS`, `x₀ ↦ 1`, `x₁ ↦ refY`, `u_j ↦ refQ`, `v_j ↦ refS`, and
`1` on every other letter. -/
private def refMark (h : ℕ) (j : Fin h) : Fin (sqRank h) → DihedralGroup 4 :=
  fun i =>
    if (i : ℕ) = 0 then refS else
    if (i : ℕ) = 2 then refY else
    if (i : ℕ) = (sqHandleIdxU j : ℕ) then refQ else
    if (i : ℕ) = (sqHandleIdxV j : ℕ) then refS else 1

@[simp] private theorem refMark_zero : refMark h j 0 = refS := by
  simp only [refMark, sqVal_zero]
  norm_num

@[simp] private theorem refMark_one : refMark h j 1 = 1 := by
  simp only [refMark, sqVal_one, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

@[simp] private theorem refMark_two : refMark h j 2 = refY := by
  simp only [refMark, sqVal_two]
  rw [if_neg (by omega)]
  norm_num

@[simp] private theorem refMark_handleU : refMark h j (sqHandleIdxU j) = refQ := by
  simp only [refMark, sqHandleIdxU_val]
  rw [if_neg (by omega), if_neg (by omega)]
  simp

@[simp] private theorem refMark_handleV : refMark h j (sqHandleIdxV j) = refS := by
  simp only [refMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

private theorem refMark_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    refMark h j (sqHandleIdxU j') = 1 := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [refMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem refMark_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    refMark h j (sqHandleIdxV j') = 1 := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [refMark, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- Every handle but the `j`-th contributes nothing. -/
private theorem commP_refMark_ne {j' : Fin h} (hne : j' ≠ j) :
    commP (refMark h j (sqHandleIdxU j')) (refMark h j (sqHandleIdxV j')) = 1 := by
  rw [refMark_handleU_ne hne, refMark_handleV_ne hne, commP, inv_one, one_mul, one_mul, one_mul]

/-- **The refuting marking kills the relator**: `C ↦ r 2` and `[refQ, refS] = r 2` cancel. -/
private theorem sqRelWord_refMark (h : ℕ) (j : Fin h) : sqRelWord (refMark h j) = 1 := by
  rw [sqRelWord, handleWord_eq_single _ _ j fun i hi => commP_refMark_ne hi, refMark_zero,
    refMark_one, refMark_two, refMark_handleU, refMark_handleV]
  decide

/-- The refuting hom `D_sq h → D₄`. -/
private noncomputable def refHom (h : ℕ) (j : Fin h) :
    ContinuousMonoidHom (DSq h : Type) (DihedralGroup 4) :=
  sqLiftHom h isProP_two_dihedral4 (refMark h j) (sqRelWord_refMark h j)

@[simp] private theorem refHom_gen (i : Fin (sqRank h)) :
    refHom h j (sqGen h i) = refMark h j i :=
  sqLiftHom_gen _ _ _ _ i

/-! ## §3 The frame dies

`x₀ ↦ 1` makes the pivot's `x₀`-leg vanish for *any* exponent (`zpowZtwo_one_base`), so
`w ↦ refS` with no fact about `c₀`; then `v_j ↦ refS` makes `V ↦ 1`, which kills every dressing
and the `j`-th handle commutator at once. -/

/-- The pivot goes to `refS`. -/
private theorem refHom_sqPivot : refHom h j (sqPivot h) = refS := by
  rw [sqPivot, sqMixPivotElem, map_mul, map_inv,
    map_zpowZtwo (isProP_DSq h) isProP_two_dihedral4, dsqX0, refHom_gen, refMark_one,
    zpowZtwo_one_base, inv_one, mul_one, dsqSigma, refHom_gen, refMark_zero]

/-- **`V` dies.**  This is the whole refutation: the frame's `v`-slot is the letter it moved. -/
private theorem refHom_sqEichV : refHom h j (sqEichV h (nuSel h j 0 1) j) = 1 := by
  rw [sqEichV, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_dihedral4,
    refHom_sqPivot, nuSel_handleV, toAdd_ofAdd, zpowZtwo_one_exp, refHom_gen, refMark_handleV,
    mul_inv_cancel]

/-- `U` goes to `refQ`: the `u_j`-row of the marking is `0`, so no pivot power is subtracted. -/
private theorem refHom_sqEichU : refHom h j (sqEichU h (nuSel h j 0 1) j) = refQ := by
  rw [sqEichU, map_mul, map_inv, map_zpowZtwo (isProP_DSq h) isProP_two_dihedral4,
    refHom_sqPivot, nuSel_handleU, toAdd_ofAdd, SectionThree.zpowZtwo_zero, inv_one, one_mul,
    refHom_gen, refMark_handleU]

variable {e e' d : ℤ_[2]}

/-- Every `V`-dressing dies with `V`. -/
private theorem refHom_dress (x : (DSq h : Type)) (k : ℤ_[2]) :
    refHom h j (x * zpowZtwo (isProP_DSq h) (sqEichV h (nuSel h j 0 1) j) k) = refHom h j x := by
  rw [map_mul, map_zpowZtwo (isProP_DSq h) isProP_two_dihedral4, refHom_sqEichV,
    zpowZtwo_one_base, mul_one]

/-- **The frame's relator does not die**: it lands on the central `r 2`. -/
private theorem refHom_sqRelWord_sqEichFrame :
    refHom h j (sqRelWord (sqEichFrame h (nuSel h j 0 1) j e e' d)) = DihedralGroup.r 2 := by
  have hzero : refHom h j (sqEichFrame h (nuSel h j 0 1) j e e' d 0) = refS := by
    rw [sqEichFrame_zero, refHom_dress, dsqSigma, refHom_gen, refMark_zero]
  have hone : refHom h j (sqEichFrame h (nuSel h j 0 1) j e e' d 1) = 1 := by
    rw [sqEichFrame_one, refHom_dress, dsqX0, refHom_gen, refMark_one]
  have htwo : refHom h j (sqEichFrame h (nuSel h j 0 1) j e e' d 2) = refY := by
    rw [sqEichFrame_two, refHom_dress, dsqX1, refHom_gen, refMark_two]
  have hU : refHom h j (sqEichFrame h (nuSel h j 0 1) j e e' d (sqHandleIdxU j)) = refQ := by
    rw [sqEichFrame_handleU, refHom_dress, refHom_sqEichU]
  have hV : refHom h j (sqEichFrame h (nuSel h j 0 1) j e e' d (sqHandleIdxV j)) = 1 := by
    rw [sqEichFrame_handleV, refHom_sqEichV]
  have hne : ∀ i : Fin h, i ≠ j →
      commP (refHom h j (sqEichFrame h (nuSel h j 0 1) j e e' d (sqHandleIdxU i)))
        (refHom h j (sqEichFrame h (nuSel h j 0 1) j e e' d (sqHandleIdxV i))) = 1 := by
    intro i hi
    rw [sqEichFrame_handleU_ne hi, sqEichFrame_handleV_ne hi, refHom_gen, refHom_gen,
      refMark_handleU_ne hi, refMark_handleV_ne hi, commP, inv_one, one_mul, one_mul, one_mul]
  rw [map_sqRelWord, sqRelWord, handleWord_eq_single _ _ j hne, hzero, hone, htwo, hU, hV]
  decide

/-- ⚠ **The refutation.**  At the selected marking `nuSel h j 0 1` the Eichler frame kills the
relator for **no** `(e, e', d)`. -/
theorem not_sqRelWord_sqEichFrame_nuSel (h : ℕ) (j : Fin h) (e e' d : ℤ_[2]) :
    sqRelWord (sqEichFrame h (nuSel h j 0 1) j e e' d) ≠ 1 := by
  intro hone
  have h1 : refHom h j (sqRelWord (sqEichFrame h (nuSel h j 0 1) j e e' d)) = 1 := by
    rw [hone, map_one]
  rw [refHom_sqRelWord_sqEichFrame] at h1
  exact absurd h1 (by decide)

/-- ⚠ **`SqEichRelWord h` is false at every `h ≥ 1`.**  The five-word Eichler ansatz of
`LamFrames` §2 does not discharge the residual. -/
theorem not_sqEichRelWord {h : ℕ} (hh : 0 < h) : ¬ SqEichRelWord h := by
  intro H
  obtain ⟨e, e', d, hrel⟩ := H (nuSel h ⟨0, hh⟩ 0 1) ⟨0, hh⟩ nuSel_sigma nuSel_x0
  exact not_sqRelWord_sqEichFrame_nuSel h ⟨0, hh⟩ e e' d hrel

/-! ## §4 Stress pins -/

section StressTests

/-- Stress: the refuting marking really is a marking — the relator dies in `D₄`. -/
example (h : ℕ) (j : Fin h) : sqRelWord (refMark h j) = 1 := sqRelWord_refMark h j

/-- Stress: the target is genuinely nonabelian, so the refutation is not an artefact of an
abelian shadow — the two handle values do not commute. -/
example : commP refQ refS ≠ 1 := by decide

/-- Stress: the marking used is **selected**, so it is inside `SqEichRelWord`'s binder. -/
example (h : ℕ) (j : Fin h) :
    nuSel h j 0 1 (dsqSigma h) = ofAdd (1 : ℤ_[2]) ∧
      nuSel h j 0 1 (dsqX0 h) = ofAdd (0 : ℤ_[2]) := ⟨nuSel_sigma, nuSel_x0⟩

/-- Stress: the refuted marking is *not* the standard one — its `v_j`-row is `1`, and at the
standard marking the ansatz does work (`sqEichFrame_nuSq_zero`). -/
example (h : ℕ) (j : Fin h) : nuSel h j 0 1 (sqGen h (sqHandleIdxV j)) = ofAdd (1 : ℤ_[2]) :=
  nuSel_handleV

/-- Stress: the frame form of the residual is untouched — it is a characterization over *all*
frames, and this file refutes one family. -/
example (h : ℕ) : SqLamMarkTransitivity h ↔
    ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
        ∃ (m : Fin (sqRank h) → (DSq h : Type)) (hrel : sqRelWord m = 1),
          Function.Surjective (sqLiftHom h (isProP_DSq h) m hrel) ∧
            (∀ i, nuLam h (m i) = nuLam h (sqGen h i)) ∧
              ∀ i, nu' (m i) = nuSq h (sqGen h i) := sqLamMarkTransitivity_iff_frames

/-- Stress: `h = 0` is untouched — there is no handle to refute at. -/
example : SqEichRelWord 0 := fun _ j _ _ => absurd j.isLt (by omega)

end StressTests

/-! ## §5 Axiom pins

Committed prints: the whole file is **std-3** (`propext`, `Classical.choice`, `Quot.sound`); no
census axiom is reachable, and no `native_decide`. -/

section AxiomPins

#print axioms isProP_two_dihedral4
#print axioms handleWord_eq_single
#print axioms not_sqRelWord_sqEichFrame_nuSel
#print axioms not_sqEichRelWord

end AxiomPins

end Target

end SqCore

end Dyadic

end GQ2
