/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcOrbit

/-!
# W84-WORD: the `M6` identity, stripped to one equation

Wave 83 (`GQ2/Dyadic/Instances/MpcOrbit.lean`) reduced the `ℚ₂(√−10)` row to the single move
`MpcPivShift 2` and proved it equivalent to the existence of a four-letter marking of `D_M 2 0`
with four clauses: the core-word relation, topological generation, the four χ-values, and the
`C̄₀`-row shift.  This module removes three of the four.

Declaration prefix `mpcWord` (namespace `GQ2.Dyadic.Instances.MpcWord`).  No `sorry`, no new
axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.
-/

namespace GQ2.Dyadic.Instances.MpcWord

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcPiv GQ2.Dyadic.Instances.MpcOrb

noncomputable section

/-! ## §1 The Frattini carrier of `D_M 2 0` -/

/-- The intersection of the index-two open normal subgroups of `D_M 2 0`: the carrier in which
the four corrections of the `M6` ansatz have to sit for the marking to generate. -/
def mpcWordFrat : Subgroup (DM 2 0 : Type) :=
  ⨅ M : OpenNormalSubgroup (DM 2 0 : Type), ⨅ _ : M.toSubgroup.index = 2, M.toSubgroup

theorem mpcWord_mem_frat_iff {x : (DM 2 0 : Type)} :
    x ∈ mpcWordFrat ↔ ∀ M : OpenNormalSubgroup (DM 2 0 : Type),
      M.toSubgroup.index = 2 → x ∈ M.toSubgroup := by
  simp [mpcWordFrat, Subgroup.mem_iInf]

/-- In an index-two quotient every element is its own inverse. -/
private theorem mpcWord_quot_sq (M : OpenNormalSubgroup (DM 2 0 : Type))
    (hM : M.toSubgroup.index = 2) (z : (DM 2 0 : Type) ⧸ M.toSubgroup) : z ^ 2 = 1 := by
  haveI : Finite ((DM 2 0 : Type) ⧸ M.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hcard : Nat.card ((DM 2 0 : Type) ⧸ M.toSubgroup) = 2 := by
    rw [← Subgroup.index_eq_card]; exact hM
  have h : z ^ Nat.card ((DM 2 0 : Type) ⧸ M.toSubgroup) = 1 := pow_card_eq_one'
  rwa [hcard] at h

/-- **Squares are Frattini.** -/
theorem mpcWord_sq_mem (x : (DM 2 0 : Type)) : x ^ 2 ∈ mpcWordFrat := by
  rw [mpcWord_mem_frat_iff]
  intro M hM
  have h := mpcWord_quot_sq M hM (QuotientGroup.mk' M.toSubgroup x)
  rw [← map_pow] at h
  exact (QuotientGroup.eq_one_iff _).mp h

/-- **Commutators are Frattini.** -/
theorem mpcWord_commP_mem (x y : (DM 2 0 : Type)) : commP x y ∈ mpcWordFrat := by
  rw [mpcWord_mem_frat_iff]
  intro M hM
  have hsq := mpcWord_quot_sq M hM
  have hinv : ∀ z : (DM 2 0 : Type) ⧸ M.toSubgroup, z⁻¹ = z := by
    intro z
    have := hsq z
    rw [sq] at this
    exact inv_eq_of_mul_eq_one_left this
  have h : QuotientGroup.mk' M.toSubgroup (commP x y) = 1 := by
    rw [commP, map_mul, map_mul, map_mul, map_inv, map_inv, hinv, hinv]
    have hxy := hsq (QuotientGroup.mk' M.toSubgroup x * QuotientGroup.mk' M.toSubgroup y)
    rw [sq] at hxy
    simpa [mul_assoc] using hxy
  exact (QuotientGroup.eq_one_iff _).mp h

/-! ## §2 The four letters of the `M6` ansatz -/

/-- The `Ā`-letter of the `M6` ansatz: `Ā·B̄⁻⁴·s`. -/
def mpcWordLetA (s : (DM 2 0 : Type)) : (DM 2 0 : Type) := dmA 2 0 * (dmB 2 0 ^ 4)⁻¹ * s

/-- The `B̄`-letter of the `M6` ansatz: `B̄·t`. -/
def mpcWordLetB (t : (DM 2 0 : Type)) : (DM 2 0 : Type) := dmB 2 0 * t

/-- The `C̄₀`-letter of the `M6` ansatz: `B̄²·C̄₀·m`, the shifted row. -/
def mpcWordLetC (m : (DM 2 0 : Type)) : (DM 2 0 : Type) := dmB 2 0 ^ 2 * dmC 2 0 * m

/-- The `D̄`-letter of the `M6` ansatz: `D̄·n`. -/
def mpcWordLetD (n : (DM 2 0 : Type)) : (DM 2 0 : Type) := dmD 2 0 * n

/-! ## §3 The reduction: three of the four clauses are free -/

/-- **The `M6` ansatz generates.**  All four corrections are Frattini, so the four letters are
congruent to the marked generators modulo every index-two open normal subgroup, and the pro-2
Frattini criterion promotes that to topological generation. -/
theorem mpcWord_gen (s t m n : (DM 2 0 : Type))
    (hs : s ∈ mpcWordFrat) (ht : t ∈ mpcWordFrat) (hm : m ∈ mpcWordFrat)
    (hn : n ∈ mpcWordFrat) :
    (Subgroup.closure ({mpcWordLetA s, mpcWordLetB t, mpcWordLetC m, mpcWordLetD n} :
      Set (DM 2 0 : Type))).topologicalClosure = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine eq_top_of_forall_not_le_index_p (p := 2) (isProP_DM 2 0)
    (Subgroup.isClosed_topologicalClosure _) ?_
  intro M hM hle
  have hsub : Subgroup.closure ({mpcWordLetA s, mpcWordLetB t, mpcWordLetC m, mpcWordLetD n} :
      Set (DM 2 0 : Type)) ≤ M.toSubgroup :=
    le_trans (Subgroup.le_topologicalClosure _) hle
  have hmemA : mpcWordLetA s ∈ M.toSubgroup :=
    hsub (Subgroup.subset_closure (Or.inl rfl))
  have hmemB : mpcWordLetB t ∈ M.toSubgroup :=
    hsub (Subgroup.subset_closure (Or.inr (Or.inl rfl)))
  have hmemC : mpcWordLetC m ∈ M.toSubgroup :=
    hsub (Subgroup.subset_closure (Or.inr (Or.inr (Or.inl rfl))))
  have hmemD : mpcWordLetD n ∈ M.toSubgroup :=
    hsub (Subgroup.subset_closure (Or.inr (Or.inr (Or.inr rfl))))
  have hsM : s ∈ M.toSubgroup := (mpcWord_mem_frat_iff.mp hs) M hM
  have htM : t ∈ M.toSubgroup := (mpcWord_mem_frat_iff.mp ht) M hM
  have hmM : m ∈ M.toSubgroup := (mpcWord_mem_frat_iff.mp hm) M hM
  have hnM : n ∈ M.toSubgroup := (mpcWord_mem_frat_iff.mp hn) M hM
  have hB2 : dmB 2 0 ^ 2 ∈ M.toSubgroup :=
    (mpcWord_mem_frat_iff.mp (mpcWord_sq_mem (dmB 2 0))) M hM
  have hB4 : dmB 2 0 ^ 4 ∈ M.toSubgroup := by
    have : dmB 2 0 ^ 4 = (dmB 2 0 ^ 2) ^ 2 := by
      rw [← pow_mul]
    rw [this]
    exact (mpcWord_mem_frat_iff.mp (mpcWord_sq_mem (dmB 2 0 ^ 2))) M hM
  have hA : dmA 2 0 ∈ M.toSubgroup := by
    have : dmA 2 0 = mpcWordLetA s * s⁻¹ * dmB 2 0 ^ 4 := by
      rw [mpcWordLetA]; group
    rw [this]
    exact M.toSubgroup.mul_mem (M.toSubgroup.mul_mem hmemA (M.toSubgroup.inv_mem hsM)) hB4
  have hB : dmB 2 0 ∈ M.toSubgroup := by
    have : dmB 2 0 = mpcWordLetB t * t⁻¹ := by rw [mpcWordLetB]; group
    rw [this]
    exact M.toSubgroup.mul_mem hmemB (M.toSubgroup.inv_mem htM)
  have hC : dmC 2 0 ∈ M.toSubgroup := by
    have : dmC 2 0 = (dmB 2 0 ^ 2)⁻¹ * mpcWordLetC m * m⁻¹ := by
      rw [mpcWordLetC]; group
    rw [this]
    exact M.toSubgroup.mul_mem
      (M.toSubgroup.mul_mem (M.toSubgroup.inv_mem hB2) hmemC) (M.toSubgroup.inv_mem hmM)
  have hD : dmD 2 0 ∈ M.toSubgroup := by
    have : dmD 2 0 = mpcWordLetD n * n⁻¹ := by rw [mpcWordLetD]; group
    rw [this]
    exact M.toSubgroup.mul_mem hmemD (M.toSubgroup.inv_mem hnM)
  have hgens : Subgroup.closure (Set.range (dmGen 2 0)) ≤ M.toSubgroup := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    exacts [hA, hB, hC, hD]
  have htop : (⊤ : Subgroup (DM 2 0 : Type)) ≤ M.toSubgroup := by
    rw [← dm_topGen 2 0]
    exact Subgroup.topologicalClosure_minimal _ hgens M.toOpenSubgroup.isClosed
  have : M.toSubgroup = ⊤ := top_le_iff.mp htop
  rw [this, Subgroup.index_top] at hM
  exact absurd hM (by norm_num)

/-- **THE `M6` WORD IDENTITY IS THE WHOLE RESIDUE.**  Given four Frattini corrections in
`ker χ_M`, with the `C̄₀`-correction invisible to every `ℤ₂`-character, the single identity

    mWord 2 (Ā·B̄⁻⁴·s) (B̄·t) (B̄²·C̄₀·m) (D̄·n) = 1

yields `MpcPivShift 2`, hence the tied `√−10` branch datum with no clause.  Generation, the four
χ-values and the row shift are all discharged here, so a builder owes exactly one equation. -/
theorem mpcWord_shift_of_word (s t m n : (DM 2 0 : Type))
    (hs : s ∈ mpcWordFrat) (ht : t ∈ mpcWordFrat) (hm : m ∈ mpcWordFrat)
    (hn : n ∈ mpcWordFrat)
    (hchis : chiM 2 0 s = 1) (hchit : chiM 2 0 t = 1) (hchim : chiM 2 0 m = 1)
    (hchin : chiM 2 0 n = 1)
    (hmrow : ∀ f : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]), f m = 1)
    (hrel : mWord 2 (mpcWordLetA s) (mpcWordLetB t) (mpcWordLetC m) (mpcWordLetD n) = 1) :
    MpcPivShift 2 := by
  have h4 : ((-1 : ℤ_[2]ˣ)) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, neg_one_sq, one_pow]
  refine mpcOrb_shift_of_marking hrel (mpcWord_gen s t m n hs ht hm hn) ?_ ?_ ?_ ?_ ?_
  · rw [mpcWordLetA, map_mul, map_mul, map_inv, map_pow, chiM_dmA, chiM_dmB, hchis, h4]
    simp
  · rw [mpcWordLetB, map_mul, chiM_dmB, hchit, mul_one]
  · rw [mpcWordLetC, map_mul, map_mul, map_pow, chiM_dmB, chiM_dmC, hchim, neg_one_sq]
    simp
  · rw [mpcWordLetD, map_mul, chiM_dmD, hchin, mul_one]
  · intro f
    have hC : mpcWordLetC m = dmB 2 0 * dmB 2 0 * dmC 2 0 * m := by
      rw [mpcWordLetC, sq]
    have hfC : f (mpcWordLetC m) = f (dmB 2 0) * f (dmB 2 0) * f (dmC 2 0) := by
      rw [hC, map_mul, map_mul, map_mul, hmrow f, mul_one]
    rw [hfC, toAdd_mul, toAdd_mul]
    ring

/-! ## §9 Axiom pins

One line per declaration, measured against the mirror. -/

section AxiomPins

#print axioms mpcWordFrat
#print axioms mpcWord_mem_frat_iff
#print axioms mpcWord_sq_mem
#print axioms mpcWord_commP_mem
#print axioms mpcWordLetA
#print axioms mpcWordLetB
#print axioms mpcWordLetC
#print axioms mpcWordLetD
#print axioms mpcWord_gen
#print axioms mpcWord_shift_of_word

end AxiomPins

end

end GQ2.Dyadic.Instances.MpcWord
