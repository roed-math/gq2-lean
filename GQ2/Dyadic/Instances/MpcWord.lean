/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcOrbit
import GQ2.Dyadic.SqCore.GradedClassFive

/-!
# W84-WORD: the `M6` identity, stripped to one equation

Wave 83 (`GQ2/Dyadic/Instances/MpcOrbit.lean`) reduced the `ℚ₂(√−10)` row to the single move
`MpcPivShift 2` and proved it equivalent to the existence of a four-letter marking of `D_M 2 0`
with four clauses: the core-word relation, topological generation, the four χ-values, and the
`C̄₀`-row shift.  This module removes three of the four, and puts the fourth on a ladder.

## What lands

1. **The residue is one word identity** (§1 to §3).  For the ansatz shape
   `(Ā·B̄⁻⁴·s, B̄·t, B̄²·C̄₀·m, D̄·n)` with the four corrections in `mpcWordFrat` (the
   intersection of the index-two open normal subgroups) and in `ker χ_M`, and with `m`
   invisible to every `ℤ₂`-character, the identity

       mWord 2 (Ā·B̄⁻⁴·s) (B̄·t) (B̄²·C̄₀·m) (D̄·n) = 1

   already gives `MpcPivShift 2` (`mpcWord_shift_of_word`).  Generation is the pro-2 Frattini
   criterion (`mpcWord_gen`), the χ-values and the row shift are the shape.  `λ₂` feeds the
   carrier (`mpcWord_lambdaTwo_le_frat`), so a builder may work in the two-central tower and
   never mention index-two subgroups.

2. **The identity is decided at a finite class** (§5, §6).  The class-`k` solution sets
   `mpcWordSet k` are nested, closed, and live in a compact space, and the tower separates
   points, so class-`k` solvability for every `k` gives the identity outright
   (`mpcWord_shift_of_forall_class`).  Contrapositively: **if `M6` is false it fails at a
   finite class, in a finite 2-group**, with no inverse-limit step to hide in.

3. **Classes at most three are free** (§7).  Every quadruple of `λ₂`-corrections already
   solves the identity to class three (`mpcWord_mem_three`): modulo `λ₃` the letters are the
   marked generators times central involutions and the word collapses onto `mpcOrb_relation`.
   Hence the residue is the class-`k` solvability for `k ≥ 4` alone
   (`mpcWord_shift_of_forall_class_four`).

**[W86-HOUSE, as of `f0de6ad5`: read every "class four" in this module as THIS MODULE'S
residue, not the campaign's.**  Wave 85's `Instances/MpcBuild.lean` (which imports this one, so
nothing here can name it) proves `mpcBld_nonempty_four : (mpcWordSet 4).Nonempty`, on this very
set, with the witness the off-tree walk below predicted.  The campaign's `M6` residue therefore
starts at CLASS FIVE now (`mpcBld_shift_of_forall_class_five`), and each sentence below saying
"the first class that can obstruct is class four" describes the state before that theorem.  No
theorem here is affected and all are still consumed: `mpcBld_shift_of_forall_class_five` runs
through `mpcWord_shift_of_forall_class_four`, and `mpcWord_mem_three` is what makes the low
rungs free on both ladders.]

## What does not land

**The decision.**  `MpcPivShift 2` is neither proved nor refuted here.  Off-tree exact `𝔽₂`
computation in the Magnus model climbs the ladder through class six without meeting an
obstruction (class four is killed by `s = t = commP D̄ B̄`), and the class-by-class walk is
shown to produce false stalls on `M5`, which is a theorem of the tree.  The lane note
(`docs/dyadic/w84-word-note.md`) records both, and draws no conclusion in either direction.

[W86-HOUSE, as of `f0de6ad5`: the parenthetical is no longer off-tree.  That exact class-four
witness is `MpcBuild.mpcBld_mem_four_witness` and `mpcBld_nonempty_four` is its conclusion.
Classes five and six remain off-tree, so the qualifier still holds for the rest of the walk.]

Declaration prefix `mpcWord` (namespace `GQ2.Dyadic.Instances.MpcWord`).  No `sorry`, no new
axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.
-/

namespace GQ2.Dyadic.Instances.MpcWord

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcPiv GQ2.Dyadic.Instances.MpcOrb
open GQ2.Roe.Labute GQ2.Dyadic.SqCore

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

/-! ## §4 The tower carrier: `λ₂` feeds the ansatz -/

/-- The second level of the two-central tower lands in the Frattini carrier: `λ₂` is generated
by squares and commutators, and an index-two quotient kills both. -/
theorem mpcWord_lambdaTwo_le_frat :
    twoCentralSeries (DM 2 0 : Type) 2 ≤ mpcWordFrat := by
  intro x hx
  rw [mpcWord_mem_frat_iff]
  intro M hM
  have hsq := mpcWord_quot_sq M hM
  have hcomm : ∀ z w : (DM 2 0 : Type) ⧸ M.toSubgroup, z * w = w * z := by
    intro z w
    have hinv : ∀ y : (DM 2 0 : Type) ⧸ M.toSubgroup, y⁻¹ = y := by
      intro y
      have := hsq y
      rw [sq] at this
      exact inv_eq_of_mul_eq_one_left this
    calc z * w = (z * w)⁻¹ := (hinv _).symm
      _ = w⁻¹ * z⁻¹ := mul_inv_rev z w
      _ = w * z := by rw [hinv, hinv]
  have hle : twoCentralSeries (DM 2 0 : Type) 2 ≤ M.toSubgroup := by
    rw [twoCentralSeries_succ (G := (DM 2 0 : Type)) (k := 1) le_rfl]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) M.toOpenSubgroup.isClosed
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨v, -, rfl⟩
      have h := hsq (QuotientGroup.mk' M.toSubgroup v)
      rw [← map_pow] at h
      exact (QuotientGroup.eq_one_iff _).mp h
    · rw [Subgroup.commutator_le]
      intro g _ h _
      rw [commutatorElement_def]
      refine (QuotientGroup.eq_one_iff _).mp ?_
      show (QuotientGroup.mk' M.toSubgroup) (g * h * g⁻¹ * h⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv,
        hcomm (QuotientGroup.mk' M.toSubgroup g) (QuotientGroup.mk' M.toSubgroup h)]
      group
  exact hle hx

/-! ## §5 The per-class solution sets -/

/-- The correction carrier for the three free slots: `λ₂ ∩ ker χ_M`. -/
def mpcWordCorr : Subgroup (DM 2 0 : Type) :=
  twoCentralSeries (DM 2 0 : Type) 2 ⊓ (chiM 2 0).toMonoidHom.ker

/-- The row-invisible subgroup: the elements no `ℤ₂`-character sees. -/
def mpcWordRowKer : Subgroup (DM 2 0 : Type) :=
  ⨅ f : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]), f.toMonoidHom.ker

/-- The correction carrier for the pivot slot: `λ₂ ∩ ker χ_M` and row-invisible. -/
def mpcWordCorrC : Subgroup (DM 2 0 : Type) := mpcWordCorr ⊓ mpcWordRowKer

theorem mpcWord_mem_corr {x : (DM 2 0 : Type)} :
    x ∈ mpcWordCorr ↔ x ∈ twoCentralSeries (DM 2 0 : Type) 2 ∧ chiM 2 0 x = 1 :=
  Iff.rfl

theorem mpcWord_mem_rowKer {x : (DM 2 0 : Type)} :
    x ∈ mpcWordRowKer ↔
      ∀ f : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]), f x = 1 := by
  simp [mpcWordRowKer, Subgroup.mem_iInf, MonoidHom.mem_ker]

/-- **The class-`k` solution set of the `M6` ansatz**: quadruples of corrections in the two
carriers whose core-word value has died to class `k` of the two-central tower.  Only the last
clause depends on `k`. -/
def mpcWordSet (k : ℕ) :
    Set ((DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type)) :=
  {p | p.1 ∈ mpcWordCorr ∧ p.2.1 ∈ mpcWordCorr ∧ p.2.2.1 ∈ mpcWordCorrC ∧
    p.2.2.2 ∈ mpcWordCorr ∧
      mWord 2 (mpcWordLetA p.1) (mpcWordLetB p.2.1) (mpcWordLetC p.2.2.1)
          (mpcWordLetD p.2.2.2) ∈ twoCentralSeries (DM 2 0 : Type) k}

theorem mpcWordSet_antitone {k k' : ℕ} (hkk : k' ≤ k) : mpcWordSet k ⊆ mpcWordSet k' :=
  fun _ ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨h1, h2, h3, h4, twoCentralSeries_antitone (G := (DM 2 0 : Type)) hkk h5⟩

/-- The core word of the ansatz varies continuously in the four corrections. -/
theorem mpcWord_continuous :
    Continuous fun p : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) =>
      mWord 2 (mpcWordLetA p.1) (mpcWordLetB p.2.1) (mpcWordLetC p.2.2.1)
        (mpcWordLetD p.2.2.2) := by
  simp only [mWord, commP, mpcWordLetA, mpcWordLetB, mpcWordLetC, mpcWordLetD]
  fun_prop

theorem mpcWord_isClosed_corr : IsClosed ((mpcWordCorr : Subgroup (DM 2 0 : Type)) :
    Set (DM 2 0 : Type)) := by
  have h1 : IsClosed ((twoCentralSeries (DM 2 0 : Type) 2 : Subgroup (DM 2 0 : Type)) :
      Set (DM 2 0 : Type)) := isClosed_twoCentralSeries _ 2
  have h2 : IsClosed (((chiM 2 0).toMonoidHom.ker : Subgroup (DM 2 0 : Type)) :
      Set (DM 2 0 : Type)) := by
    have : (((chiM 2 0).toMonoidHom.ker : Subgroup (DM 2 0 : Type)) : Set (DM 2 0 : Type))
        = {x | chiM 2 0 x = 1} := rfl
    rw [this]
    exact isClosed_eq (chiM 2 0).continuous_toFun continuous_const
  exact h1.inter h2

theorem mpcWord_isClosed_rowKer : IsClosed ((mpcWordRowKer : Subgroup (DM 2 0 : Type)) :
    Set (DM 2 0 : Type)) := by
  have hset : ((mpcWordRowKer : Subgroup (DM 2 0 : Type)) : Set (DM 2 0 : Type))
      = ⋂ f : ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]), {x | f x = 1} := by
    ext x
    simp [mpcWord_mem_rowKer]
  rw [hset]
  exact isClosed_iInter fun f => isClosed_eq f.continuous_toFun continuous_const

theorem mpcWord_isClosed_corrC : IsClosed ((mpcWordCorrC : Subgroup (DM 2 0 : Type)) :
    Set (DM 2 0 : Type)) := by
  have hset : ((mpcWordCorrC : Subgroup (DM 2 0 : Type)) : Set (DM 2 0 : Type))
      = ((mpcWordCorr : Subgroup (DM 2 0 : Type)) : Set (DM 2 0 : Type)) ∩
        ((mpcWordRowKer : Subgroup (DM 2 0 : Type)) : Set (DM 2 0 : Type)) := rfl
  rw [hset]
  exact mpcWord_isClosed_corr.inter mpcWord_isClosed_rowKer

/-- **The class-`k` solution set is closed** - all five clauses are. -/
theorem mpcWord_isClosed_set (k : ℕ) : IsClosed (mpcWordSet k) := by
  have hA : IsClosed {p : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) ×
      (DM 2 0 : Type) | p.1 ∈ mpcWordCorr} :=
    mpcWord_isClosed_corr.preimage continuous_fst
  have hB : IsClosed {p : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) ×
      (DM 2 0 : Type) | p.2.1 ∈ mpcWordCorr} :=
    mpcWord_isClosed_corr.preimage (continuous_fst.comp continuous_snd)
  have hC : IsClosed {p : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) ×
      (DM 2 0 : Type) | p.2.2.1 ∈ mpcWordCorrC} :=
    mpcWord_isClosed_corrC.preimage (continuous_fst.comp (continuous_snd.comp continuous_snd))
  have hD : IsClosed {p : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) ×
      (DM 2 0 : Type) | p.2.2.2 ∈ mpcWordCorr} :=
    mpcWord_isClosed_corr.preimage (continuous_snd.comp (continuous_snd.comp continuous_snd))
  exact hA.inter (hB.inter (hC.inter (hD.inter
    ((isClosed_twoCentralSeries (G := (DM 2 0 : Type)) k).preimage mpcWord_continuous))))

/-! ## §6 The compactness assembly -/

/-- **The compactness core**: the nested nonempty closed solution sets meet, by the
finite-intersection property in the compact space of corrections. -/
theorem mpcWord_iInter_nonempty (hne : ∀ k, (mpcWordSet k).Nonempty) :
    (⋂ k, mpcWordSet k).Nonempty := by
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
  · intro k k'
    exact ⟨max k k', mpcWordSet_antitone (le_max_left k k'),
      mpcWordSet_antitone (le_max_right k k')⟩
  · exact hne
  · exact fun k => (mpcWord_isClosed_set k).isCompact
  · exact fun k => mpcWord_isClosed_set k

/-- The tower separates points on `D_M 2 0`. -/
theorem mpcWord_iInf_twoCentralSeries :
    ⨅ k, twoCentralSeries (DM 2 0 : Type) k = ⊥ :=
  iInf_twoCentralSeries (G := (DM 2 0 : Type)) (dm_topologicallyFinGen_zero 2) (isProP_DM 2 0)

/-- ⭐ **THE PER-CLASS CRITERION.**  If the `M6` ansatz can be solved to every class of the
two-central tower - the campaign's per-class discipline, one finite quotient at a time - then
it can be solved outright, and `MpcPivShift 2` follows.  There is no inverse-limit step to
lose: nestedness, closedness, compactness of the correction space and the tower separation
`mpcWord_iInf_twoCentralSeries` are the whole argument.  Contrapositively, **if `M6` is false
then it fails at a finite class**, with a finite 2-group as the witness. -/
theorem mpcWord_shift_of_forall_class (H : ∀ k, (mpcWordSet k).Nonempty) : MpcPivShift 2 := by
  obtain ⟨p, hp⟩ := mpcWord_iInter_nonempty H
  have hmem : ∀ k, p ∈ mpcWordSet k := Set.mem_iInter.mp hp
  obtain ⟨h1, h2, h3, h4, -⟩ := hmem 0
  have hall : mWord 2 (mpcWordLetA p.1) (mpcWordLetB p.2.1) (mpcWordLetC p.2.2.1)
      (mpcWordLetD p.2.2.2) ∈ ⨅ k, twoCentralSeries (DM 2 0 : Type) k :=
    Subgroup.mem_iInf.mpr fun k => (hmem k).2.2.2.2
  rw [mpcWord_iInf_twoCentralSeries, Subgroup.mem_bot] at hall
  exact mpcWord_shift_of_word p.1 p.2.1 p.2.2.1 p.2.2.2
    (mpcWord_lambdaTwo_le_frat h1.1) (mpcWord_lambdaTwo_le_frat h2.1)
    (mpcWord_lambdaTwo_le_frat h3.1.1) (mpcWord_lambdaTwo_le_frat h4.1)
    h1.2 h2.2 h3.1.2 h4.2 (fun f => (mpcWord_mem_rowKer.mp h3.2) f) hall

/-! ## §7 The per-class extension record: classes at most three are free

The first rungs of the ladder cost nothing: *every* quadruple of `λ₂`-corrections solves the
`M6` identity to class three.  So the whole residue of the ansatz sits at classes `k ≥ 4`, and
the first class that can obstruct is class four.

[W86-HOUSE, as of `f0de6ad5`: the last clause is this module's state, superseded by wave 85.
`MpcBuild.mpcBld_nonempty_four` solves class four on this set, so the first class that can
obstruct is class FIVE.  See the module docstring's W86-HOUSE block.] -/

section Central

variable {G : Type*} [Group G]

private theorem mpcWord_conjP_center_left {x y z : G} (hz : ∀ w : G, z * w = w * z) :
    conjP (x * z) y = conjP x y * z := by
  simp only [conjP]
  have hxy : x * z * y = x * y * z := by rw [mul_assoc, hz y, ← mul_assoc]
  rw [mul_assoc, hxy]
  group

private theorem mpcWord_conjP_center_right {x y z : G} (hz : ∀ w : G, z * w = w * z) :
    conjP x (y * z) = conjP x y := by
  have hcen : ∀ w : G, z⁻¹ * w * z = w := by
    intro w
    rw [mul_assoc, ← hz w, ← mul_assoc, inv_mul_cancel, one_mul]
  simp only [conjP, mul_inv_rev]
  have hrw : z⁻¹ * y⁻¹ * x * (y * z) = z⁻¹ * (y⁻¹ * x * y) * z := by group
  rw [hrw, hcen]

private theorem mpcWord_commP_conjP (x y : G) : commP x y = x⁻¹ * conjP x y := by
  simp only [commP, conjP]
  group

private theorem mpcWord_commP_center {x y zx zy : G} (hx : ∀ w : G, zx * w = w * zx)
    (hy : ∀ w : G, zy * w = w * zy) : commP (x * zx) (y * zy) = commP x y := by
  rw [mpcWord_commP_conjP, mpcWord_conjP_center_right hy, mpcWord_conjP_center_left hx,
    mpcWord_commP_conjP]
  have hrw : (x * zx)⁻¹ * (conjP x y * zx) = zx⁻¹ * ((x⁻¹ * conjP x y) * zx) := by group
  rw [hrw, ← hx (x⁻¹ * conjP x y), ← mul_assoc, inv_mul_cancel, one_mul]

/-- **Central factors of the right order drop out of the core word.**  Multiplying the four
letters by central elements, the `Ā`-factor an involution and the `C̄₀`-factor of order dividing
`2^α`, leaves `mWord α` unchanged. -/
private theorem mpcWord_mWord_center (α : ℕ) (a b c d za zb zc zd : G)
    (hza : ∀ w : G, za * w = w * za) (hzb : ∀ w : G, zb * w = w * zb)
    (hzc : ∀ w : G, zc * w = w * zc) (hzd : ∀ w : G, zd * w = w * zd)
    (h2a : za ^ 2 = 1) (h2c : zc ^ (2 ^ α) = 1) :
    mWord α (a * za) (b * zb) (c * zc) (d * zd) = mWord α a b c d := by
  have hca : Commute a za := (hza a).symm
  have hcc : Commute c zc := (hzc c).symm
  simp only [mWord]
  rw [hca.mul_pow, h2a, mul_one, hcc.mul_pow, h2c, mul_one,
    mpcWord_commP_center hza hzb, mpcWord_commP_center hzc hzd]

end Central

section LevelThree

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Membership in `λₖ` is vanishing at level `k`. -/
theorem mpcWord_mem_iff_levelMk (k : ℕ) (r : G) :
    r ∈ twoCentralSeries G k ↔ levelMk G k r = 1 :=
  (QuotientGroup.eq_one_iff r).symm

/-- `λ₂` is central in the class-three quotient. -/
theorem mpcWord_levelMk_central {u : G} (hu : u ∈ twoCentralSeries G 2)
    (w : levelQuot G 3) : levelMk G 3 u * w = w * levelMk G 3 u := by
  obtain ⟨g, rfl⟩ := levelMk_surjective G 3 w
  rw [← map_mul, ← map_mul]
  have hc1 : levelMk G 3 (commP u g) = 1 :=
    (mpcWord_mem_iff_levelMk 3 _).mp (cfive_commP_mem_succ hu g)
  have hrw : u * g = g * u * commP u g := by
    simp only [commP]
    group
  rw [hrw, map_mul, hc1, mul_one]

/-- `λ₂` is an involution group in the class-three quotient. -/
theorem mpcWord_levelMk_sq {u : G} (hu : u ∈ twoCentralSeries G 2) :
    levelMk G 3 u ^ 2 = 1 := by
  rw [← map_pow]
  exact (mpcWord_mem_iff_levelMk 3 _).mp (sq_mem_twoCentralSeries_succ G hu)

end LevelThree

/-- ⭐ **CLASSES AT MOST THREE ARE FREE.**  For *every* quadruple of `λ₂`-corrections the `M6`
core word already dies at class three: modulo `λ₃` the letters are the marked generators times
central involutions, `B̄⁴` and the corrections all vanish, and the word collapses onto
`mpcOrb_relation`.  So the ansatz imposes no condition below class four, and the first class
that can obstruct is class four.

[W86-HOUSE, as of `f0de6ad5`: the first clause is exact and is what this theorem says; the
second is superseded, `MpcBuild.mpcBld_nonempty_four` having solved class four.  The first
class that can obstruct is class five.] -/
theorem mpcWord_mem_three (s t m n : (DM 2 0 : Type))
    (hs : s ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (ht : t ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hm : m ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hn : n ∈ twoCentralSeries (DM 2 0 : Type) 2) :
    mWord 2 (mpcWordLetA s) (mpcWordLetB t) (mpcWordLetC m) (mpcWordLetD n)
      ∈ twoCentralSeries (DM 2 0 : Type) 3 := by
  set π := levelMk (DM 2 0 : Type) 3 with hπ
  have hB2 : dmB 2 0 ^ 2 ∈ twoCentralSeries (DM 2 0 : Type) 2 :=
    sq_mem_twoCentralSeries_succ _ (Subgroup.mem_top _)
  have hB4 : π (dmB 2 0) ^ 4 = 1 := by
    have h : dmB 2 0 ^ 4 = (dmB 2 0 ^ 2) ^ 2 := by rw [← pow_mul]
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← map_pow, ← map_pow]
    exact (mpcWord_mem_iff_levelMk 3 _).mp
      (sq_mem_twoCentralSeries_succ _ hB2)
  rw [mpcWord_mem_iff_levelMk, map_mWord]
  have hA : π (mpcWordLetA s) = π (dmA 2 0) * π s := by
    rw [mpcWordLetA, map_mul, map_mul, map_inv, map_pow, hB4, inv_one, mul_one]
  have hB : π (mpcWordLetB t) = π (dmB 2 0) * π t := by rw [mpcWordLetB, map_mul]
  have hC : π (mpcWordLetC m) = π (dmC 2 0) * (π (dmB 2 0) ^ 2 * π m) := by
    rw [mpcWordLetC, map_mul, map_mul, map_pow]
    rw [← mul_assoc, ← map_pow]
    rw [mpcWord_levelMk_central hB2 (π (dmC 2 0)), map_pow]
  have hD : π (mpcWordLetD n) = π (dmD 2 0) * π n := by rw [mpcWordLetD, map_mul]
  rw [hA, hB, hC, hD]
  have hzc : ∀ w : levelQuot (DM 2 0 : Type) 3,
      (π (dmB 2 0) ^ 2 * π m) * w = w * (π (dmB 2 0) ^ 2 * π m) := by
    intro w
    rw [mul_assoc, mpcWord_levelMk_central hm w, ← mul_assoc, ← map_pow,
      mpcWord_levelMk_central hB2 w, mul_assoc, map_pow]
  have h2c : (π (dmB 2 0) ^ 2 * π m) ^ (2 ^ 2) = 1 := by
    have hcm : Commute (π (dmB 2 0) ^ 2) (π m) := by
      rw [← map_pow]
      exact mpcWord_levelMk_central hB2 (π m)
    have hsq : (π (dmB 2 0) ^ 2 * π m) ^ 2 = 1 := by
      rw [hcm.mul_pow, ← map_pow, mpcWord_levelMk_sq hB2, mpcWord_levelMk_sq hm, one_mul]
    rw [show (2 : ℕ) ^ 2 = 2 * 2 from rfl, pow_mul, hsq, one_pow]
  rw [mpcWord_mWord_center 2 _ _ _ _ _ _ _ _
    (fun w => mpcWord_levelMk_central hs w) (fun w => mpcWord_levelMk_central ht w)
    hzc (fun w => mpcWord_levelMk_central hn w) (mpcWord_levelMk_sq hs) h2c]
  rw [← map_mWord, mpcOrb_relation, map_one]

/-- The class-`k` solution set is nonempty for every `k ≤ 3`, witnessed by the bare ansatz. -/
theorem mpcWord_nonempty_of_le_three {k : ℕ} (hk : k ≤ 3) : (mpcWordSet k).Nonempty := by
  refine ⟨(1, 1, 1, 1), one_mem _, one_mem _, one_mem _, one_mem _, ?_⟩
  exact twoCentralSeries_antitone (G := (DM 2 0 : Type)) hk
    (mpcWord_mem_three 1 1 1 1 (one_mem _) (one_mem _) (one_mem _) (one_mem _))

/-- ⭐ **THE RESIDUE, EXACTLY.**  `MpcPivShift 2` follows from the class-`k` solvability of the
`M6` ansatz for `k ≥ 4` alone: classes at most three are theorems.

[W86-HOUSE, as of `f0de6ad5`: the theorem is unchanged, still true and still the route every
sharper form takes; only the superlative has moved.  Class four is a theorem too now
(`MpcBuild.mpcBld_nonempty_four`), so the exact residue is `k ≥ 5`, and the sharp form is
`MpcBuild.mpcBld_shift_of_forall_class_five`, which is proved through THIS theorem.] -/
theorem mpcWord_shift_of_forall_class_four
    (H : ∀ k, 4 ≤ k → (mpcWordSet k).Nonempty) : MpcPivShift 2 := by
  refine mpcWord_shift_of_forall_class fun k => ?_
  by_cases hk : 4 ≤ k
  · exact H k hk
  · exact mpcWord_nonempty_of_le_three (by omega)

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
#print axioms mpcWord_lambdaTwo_le_frat
#print axioms mpcWordCorr
#print axioms mpcWordRowKer
#print axioms mpcWordCorrC
#print axioms mpcWord_mem_corr
#print axioms mpcWord_mem_rowKer
#print axioms mpcWordSet
#print axioms mpcWordSet_antitone
#print axioms mpcWord_continuous
#print axioms mpcWord_isClosed_corr
#print axioms mpcWord_isClosed_rowKer
#print axioms mpcWord_isClosed_corrC
#print axioms mpcWord_isClosed_set
#print axioms mpcWord_iInter_nonempty
#print axioms mpcWord_iInf_twoCentralSeries
#print axioms mpcWord_shift_of_forall_class
#print axioms mpcWord_mem_iff_levelMk
#print axioms mpcWord_levelMk_central
#print axioms mpcWord_levelMk_sq
#print axioms mpcWord_mem_three
#print axioms mpcWord_nonempty_of_le_three
#print axioms mpcWord_shift_of_forall_class_four

end AxiomPins

end

end GQ2.Dyadic.Instances.MpcWord
