/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Roe.Labute.TwoCentralTower
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Additive characters on the lower two-central filtration

In a compact Hausdorff abelian group the closed lower two-central series is
exactly the sequence of power images. Consequently an arbitrary continuous
additive `ℤ₂` character on a topological group sends `λ_(k+1)` into `2^k ℤ₂`.
The source group need not be compact, pro-two, or finitely generated.

The last corollary extracts one digit from an explicitly supplied identity
`f(δ) = 2u·a`, where `u` is a unit and `δ ∈ λ_(k+2)`. It does not assert that
a particular relator defect satisfies this identity, that a filtered class has
a commutator-subgroup representative, or that any relative stage is solvable.
-/

namespace GQ2.Roe.Labute
open Multiplicative
open scoped commutatorElement

section CompactAbelian
variable {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
  [CompactSpace A] [T2Space A]

/-- Compactness makes every power image closed, so the commutative lower
two-central filtration is the exact power filtration. -/
theorem twoCentralSeries_eq_powRange (k : ℕ) :
    twoCentralSeries A (k + 1) = (powMonoidHom (2 ^ k) : A →* A).range := by
  apply le_antisymm
  · induction k with
    | zero =>
        intro x _
        exact ⟨x, by simp [powMonoidHom]⟩
    | succ k ih =>
        rw [twoCentralSeries_succ A (Nat.le_add_left 1 k)]
        have hclosed : IsClosed (((powMonoidHom (2 ^ (k + 1)) : A →* A).range) : Set A) := by
          exact (isCompact_range (continuous_pow (2 ^ (k + 1)))).isClosed
        refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hclosed
        · refine (Subgroup.closure_le _).2 ?_
          rintro _ ⟨v, hv, rfl⟩
          obtain ⟨x, rfl⟩ := ih hv
          refine ⟨x, ?_⟩
          change x ^ 2 ^ (k + 1) = (x ^ 2 ^ k) ^ 2
          rw [← pow_mul, ← pow_succ]
        · refine Subgroup.commutator_le.2 fun g _ x _ ↦ ?_
          rw [commutatorElement_eq_one_iff_mul_comm.2 (mul_comm g x)]
          exact one_mem _
  · rintro x ⟨y, rfl⟩
    exact pow_two_pow_mem_twoCentralSeries_succ A y k

end CompactAbelian

section Characters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A continuous additive character maps `λ_(k+1)` into `2^k ℤ₂`. -/
theorem twoCentralSeries_z2_character_dvd_succ
    (f : ContinuousMonoidHom G (Multiplicative ℤ_[2])) {k : ℕ} {g : G}
    (hg : g ∈ twoCentralSeries G (k + 1)) :
    (2 : ℤ_[2]) ^ k ∣ (f g).toAdd := by
  have him : f g ∈ twoCentralSeries (Multiplicative ℤ_[2]) (k + 1) :=
    map_twoCentralSeries_le f.toMonoidHom f.continuous_toFun (k + 1) ⟨g, hg, rfl⟩
  rw [twoCentralSeries_eq_powRange] at him
  obtain ⟨x, hx⟩ := him
  refine ⟨x.toAdd, ?_⟩
  have h := congrArg Multiplicative.toAdd hx
  simpa only [powMonoidHom_apply, toAdd_pow, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] using h.symm

/-- The same bound using the one-based tower index `j`. -/
theorem twoCentralSeries_z2_character_dvd
    (f : ContinuousMonoidHom G (Multiplicative ℤ_[2])) {j : ℕ} (hj : 1 ≤ j) {g : G}
    (hg : g ∈ twoCentralSeries G j) :
    (2 : ℤ_[2]) ^ (j - 1) ∣ (f g).toAdd := by
  apply twoCentralSeries_z2_character_dvd_succ f
  simpa only [Nat.sub_add_cancel hj] using hg

/-- Cancellation of the exact single factor of two in `2u`. -/
theorem z2_dvd_of_two_unit_mul (u : ℤ_[2]ˣ) {k : ℕ} {a : ℤ_[2]}
    (h : (2 : ℤ_[2]) ^ (k + 1) ∣ 2 * (u : ℤ_[2]) * a) :
    (2 : ℤ_[2]) ^ k ∣ a := by
  obtain ⟨b, hb⟩ := h
  have hcancel : (u : ℤ_[2]) * a = 2 ^ k * b := by
    apply mul_left_cancel₀ (by norm_num : (2 : ℤ_[2]) ≠ 0)
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hb
  refine ⟨(↑(u⁻¹) : ℤ_[2]) * b, ?_⟩
  calc
    a = (↑(u⁻¹) : ℤ_[2]) * ((u : ℤ_[2]) * a) := by simp
    _ = (2 : ℤ_[2]) ^ k * ((↑(u⁻¹) : ℤ_[2]) * b) := by rw [hcancel]; ring

/-- A one-digit strengthening from an actual `2u` head-row identity.
The exact identity is a premise, not inferred from a graded shadow. -/
theorem twoCentralSeries_z2_character_dvd_of_two_unit
    (f : ContinuousMonoidHom G (Multiplicative ℤ_[2])) (u : ℤ_[2]ˣ)
    {k : ℕ} {g : G} {a : ℤ_[2]}
    (hg : g ∈ twoCentralSeries G (k + 2))
    (hrow : (f g).toAdd = 2 * (u : ℤ_[2]) * a) :
    (2 : ℤ_[2]) ^ k ∣ a := by
  apply z2_dvd_of_two_unit_mul u
  rw [← hrow]
  exact twoCentralSeries_z2_character_dvd_succ f hg

end Characters

#print axioms twoCentralSeries_eq_powRange
#print axioms twoCentralSeries_z2_character_dvd_succ
#print axioms twoCentralSeries_z2_character_dvd
#print axioms z2_dvd_of_two_unit_mul
#print axioms twoCentralSeries_z2_character_dvd_of_two_unit
end GQ2.Roe.Labute
