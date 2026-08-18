/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedTargetCABDObstruction

/-!
# A concrete class-four seed at one handle

The compact W4 correction `(W,W,1,1)`, with `W = [D,B]`, can be written directly in
`D_M(2,1)` while retaining the standard handle pair.  Its full six-letter relator is already in
`lambda_4`.  This is stronger than the finite quotient rank evidence: the class-four seed is an
exact theorem in the presented pro-2 group.

The same marking is mod-two independent, topologically generating, chi-oriented, and has the
universal `C + 2B` row.  Thus every static base clause needed by a direct one-handle ladder is
available; the remaining work begins with the successor out of this concrete fourth rung.
-/

namespace GQ2.Dyadic.Instances.MpcOneHandleClassFourSeed

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcGeneralHandleDefectAbsorption
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Roe.Labute

private abbrev H := DM 2 1

def oneHandleW4 : H := commP (dmD 2 1) (dmB 2 1)

def oneHandleW4Mark : Fin (coreRank 1) → H :=
  standardHandleMark
    (dmA 2 1 * (dmB 2 1 ^ 4)⁻¹ * oneHandleW4)
    (dmB 2 1 * oneHandleW4)
    (dmB 2 1 ^ 2 * dmC 2 1)
    (dmD 2 1)

private theorem kill6 {Q : Type*} [Group Q] {z₁ z₂ z₃ : Q}
    (h₁ : ∀ x : Q, z₁ * x = x * z₁)
    (e₁ : z₁ ^ 2 = 1) (e₂ : z₂ ^ 2 = 1) (e₃ : z₃ ^ 2 = 1) :
    z₁ * z₂ * (z₂ * z₃) * (z₁ * z₃) = 1 := by
  calc z₁ * z₂ * (z₂ * z₃) * (z₁ * z₃)
      = z₁ * z₂ * (z₂ * z₃) * z₁ * z₃ := by group
    _ = z₁ * (z₁ * z₂ * (z₂ * z₃)) * z₃ := by
      rw [← h₁ (z₁ * z₂ * (z₂ * z₃))]
    _ = z₁ ^ 2 * z₂ ^ 2 * z₃ ^ 2 := by
      rw [pow_two, pow_two, pow_two]
      group
    _ = 1 := by rw [e₁, e₂, e₃, one_mul, one_mul]

private theorem commP_swap {Q : Type*} [Group Q] (x y : Q) :
    commP x y = (commP y x)⁻¹ := by
  simp only [commP]
  group

theorem oneHandleW4Mark_relator_mem_four :
    mRelWord 2 oneHandleW4Mark ∈ twoCentralSeries H 4 := by
  rw [lim_mem_twoCentralSeries_iff_levelMk]
  let p := levelMk H 4 (dmA 2 1)
  let q := levelMk H 4 (dmB 2 1)
  let r := levelMk H 4 (dmC 2 1)
  let w := levelMk H 4 (dmD 2 1)
  let u := levelMk H 4 (dmGen 2 1 (handleIdxU (0 : Fin 1)))
  let v := levelMk H 4 (dmGen 2 1 (handleIdxV (0 : Fin 1)))
  let beta := commP w q
  have hbeta : beta ∈ lambdaImage H 2 4 := cfour_commP_mem_lambdaTwo w q
  have hz : (q ^ 4)⁻¹ ∈ zLayer H 3 :=
    Subgroup.inv_mem _ (cfour_pow_four_mem_zLayer q)
  have hword := mpcBld_mWord_four (G := H)
    (p := p) (q := q) (r := r) (w := w)
    (σ := beta) (τ := beta) (μ := 1) (ν := 1) (z := (q ^ 4)⁻¹)
    hbeta hbeta (one_mem _) (one_mem _) hz
  have hbeta' : commP q w ∈ lambdaImage H 2 4 :=
    cfour_commP_mem_lambdaTwo q w
  have hbeta2 : commP q w ^ 2 ∈ zLayer H 3 := cfour_sq_mem_zLayer hbeta'
  have hkappa : commP (commP q w) q ∈ zLayer H 3 :=
    cfour_commP_mem_zLayer_left hbeta' q
  have hP : commP (commP w q) p ∈ zLayer H 3 :=
    cfour_commP_mem_zLayer_left hbeta p
  have hsq : commP w q ^ 2 = commP q w ^ 2 := by
    rw [commP_swap w q, inv_pow]
    exact zLayer_inv_self hbeta2
  have hswapA : commP p (commP w q) = commP (commP w q) p := by
    rw [commP_swap p (commP w q)]
    exact zLayer_inv_self hP
  have hswapB : commP (commP w q) q = commP (commP q w) q := by
    rw [commP_swap w q, mpcBld_commP_inv_left hbeta' q]
    exact zLayer_inv_self hkappa
  have hincr :
      beta ^ 2 * commP beta p *
          (commP p beta * commP beta q) *
          (commP q w ^ 2 * commP (commP q w) q) = 1 := by
    rw [hsq, hswapA, hswapB]
    exact kill6 (fun x => (zLayer_commute hbeta2 x).eq) (zLayer_sq _ hbeta2)
      (zLayer_sq _ hP) (zLayer_sq _ hkappa)
  have hbase : mWord 2 p q r w * commP u v = 1 := by
    have h := congrArg (levelMk H 4) (dm_relation 2 1)
    rw [map_one] at h
    rw [map_mRelWord, mRelWord, handleWord_one] at h
    change mWord 2 p q r w * commP u v = 1 at h
    exact h
  change levelMk H 4 (mRelWord 2 oneHandleW4Mark) = 1
  simp only [oneHandleW4Mark, mRelWord, standardHandleMark_zero,
    standardHandleMark_one, standardHandleMark_two, standardHandleMark_three,
    standardHandleMark_handleU, standardHandleMark_handleV, handleWord,
    List.finRange, map_mul, oneHandleW4]
  change mWord 2 (p * (q ^ 4)⁻¹ * beta) (q * beta) (q ^ 2 * r) w *
      commP u v = 1
  simp only [cfour_comm_one, cfour_one_comm, mul_one] at hword
  rw [hword]
  rw [hincr, mul_one]
  exact hbase

/-- The six W4 letters are independent in every index-two quotient. -/
theorem oneHandleW4Mark_modTwoIndep : OneHandleModTwoIndep oneHandleW4Mark := by
  intro M hM
  by_contra hall
  push Not at hall
  have hA' := hall (0 : Fin (coreRank 1))
  have hB' := hall (1 : Fin (coreRank 1))
  have hC' := hall (2 : Fin (coreRank 1))
  have hD' := hall (3 : Fin (coreRank 1))
  have hU := hall (handleIdxU (0 : Fin 1))
  have hV := hall (handleIdxV (0 : Fin 1))
  simp only [oneHandleW4Mark, standardHandleMark_zero] at hA'
  simp only [oneHandleW4Mark, standardHandleMark_one] at hB'
  simp only [oneHandleW4Mark, standardHandleMark_two] at hC'
  simp only [oneHandleW4Mark, standardHandleMark_three] at hD'
  simp only [oneHandleW4Mark, standardHandleMark_handleU] at hU
  simp only [oneHandleW4Mark, standardHandleMark_handleV] at hV
  have hW : oneHandleW4 ∈ M.toSubgroup :=
    commP_mem_of_index_two hM (dmD 2 1) (dmB 2 1)
  have hB2 : dmB 2 1 ^ 2 ∈ M.toSubgroup := sq_mem_of_index_two hM _
  have hB4 : dmB 2 1 ^ 4 ∈ M.toSubgroup := by
    rw [show (4 : ℕ) = 2 * 2 by omega, pow_mul]
    exact sq_mem_of_index_two hM _
  have hA : dmA 2 1 ∈ M.toSubgroup := by
    have heq : dmA 2 1 =
        (dmA 2 1 * (dmB 2 1 ^ 4)⁻¹ * oneHandleW4) *
          oneHandleW4⁻¹ * dmB 2 1 ^ 4 := by group
    rw [heq]
    exact M.toSubgroup.mul_mem
      (M.toSubgroup.mul_mem hA' (M.toSubgroup.inv_mem hW)) hB4
  have hB : dmB 2 1 ∈ M.toSubgroup := by
    have heq : dmB 2 1 = (dmB 2 1 * oneHandleW4) * oneHandleW4⁻¹ := by group
    rw [heq]
    exact M.toSubgroup.mul_mem hB' (M.toSubgroup.inv_mem hW)
  have hC : dmC 2 1 ∈ M.toSubgroup := by
    have heq : dmC 2 1 = (dmB 2 1 ^ 2)⁻¹ * (dmB 2 1 ^ 2 * dmC 2 1) := by group
    rw [heq]
    exact M.toSubgroup.mul_mem (M.toSubgroup.inv_mem hB2) hC'
  have hgens : Subgroup.closure (Set.range (dmGen 2 1)) ≤ M.toSubgroup := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    exacts [hA, hB, hC, hD', hU, hV]
  have htop : M.toSubgroup = ⊤ := by
    apply top_unique
    rw [← dm_topGen 2 1]
    exact Subgroup.topologicalClosure_minimal _ hgens M.toOpenSubgroup.isClosed
  have : M.toSubgroup.index = 1 := Subgroup.index_eq_one.mpr htop
  omega

theorem oneHandleW4Mark_topGen :
    (Subgroup.closure (Set.range oneHandleW4Mark)).topologicalClosure = ⊤ :=
  topGen_of_oneHandleModTwoIndep oneHandleW4Mark_modTwoIndep

theorem oneHandleW4Mark_chi (i : Fin (coreRank 1)) :
    chiM 2 1 (oneHandleW4Mark i) = chiM 2 1 (dmGen 2 1 i) := by
  rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨k, rfl⟩
  · change chiM 2 1 (oneHandleW4Mark 0) = chiM 2 1 (dmA 2 1)
    simp [oneHandleW4Mark, oneHandleW4, commP, map_mul, map_inv]
    rw [show (4 : ℕ) = 2 * 2 by omega, pow_mul, neg_one_sq, one_pow]
  · change chiM 2 1 (oneHandleW4Mark 1) = chiM 2 1 (dmB 2 1)
    simp [oneHandleW4Mark, oneHandleW4, commP, map_mul, map_inv]
  · change chiM 2 1 (oneHandleW4Mark 2) = chiM 2 1 (dmC 2 1)
    simp [oneHandleW4Mark, oneHandleW4, commP, map_mul]
  · change chiM 2 1 (oneHandleW4Mark 3) = chiM 2 1 (dmD 2 1)
    simp [oneHandleW4Mark]
  · rcases mHandleCoord_cases k with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
      simp [oneHandleW4Mark, mHandleIdx_coordU, mHandleIdx_coordV]

theorem oneHandleW4Mark_C_row
    (f : ContinuousMonoidHom H (Multiplicative ℤ_[2])) :
    toAdd (f (oneHandleW4Mark 2)) =
      toAdd (f (dmC 2 1)) + 2 * toAdd (f (dmB 2 1)) := by
  simp only [oneHandleW4Mark, standardHandleMark_two, map_mul, map_pow,
    toAdd_mul, toAdd_pow, nsmul_eq_mul]
  ring

/-- The checked W4 marking supplies every static clause of a one-handle class-four seed. -/
theorem oneHandleW4Mark_seed :
    OneHandleModTwoIndep oneHandleW4Mark ∧
      (∀ i, chiM 2 1 (oneHandleW4Mark i) = chiM 2 1 (dmGen 2 1 i)) ∧
      (∀ f : ContinuousMonoidHom H (Multiplicative ℤ_[2]),
        toAdd (f (oneHandleW4Mark 2)) =
          toAdd (f (dmC 2 1)) + 2 * toAdd (f (dmB 2 1))) ∧
      mRelWord 2 oneHandleW4Mark ∈ twoCentralSeries H 4 :=
  ⟨oneHandleW4Mark_modTwoIndep, oneHandleW4Mark_chi,
    oneHandleW4Mark_C_row, oneHandleW4Mark_relator_mem_four⟩

#print axioms oneHandleW4Mark_relator_mem_four
#print axioms oneHandleW4Mark_modTwoIndep
#print axioms oneHandleW4Mark_topGen
#print axioms oneHandleW4Mark_chi
#print axioms oneHandleW4Mark_C_row
#print axioms oneHandleW4Mark_seed

end
end GQ2.Dyadic.Instances.MpcOneHandleClassFourSeed
