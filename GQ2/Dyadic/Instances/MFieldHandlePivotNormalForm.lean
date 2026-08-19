/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MFieldPositiveHandleDichotomy
import GQ2.Dyadic.Instances.MpcGeneralHandleRealization

/-!
# Normal form for the general M handle pivot

W309 and W310 reduce both unresolved M selector families to the same alternative: either the
distinguished C row has the required pivot, or an exact pivot lies on a standard hyperbolic
handle.  This module shows that the latter alternative has one uniform normal form in every
degree and at every level.

Existing lifted handle-plane automorphisms move either an exact U- or V-handle pivot to the U
row, scale it to exactly `2^r`, and kill its paired V row.  The correction preserves `chiM` and
fixes C.  Thus the remaining M boundary is a single alternate certificate problem for a
normalized handle-supported pivot; it is not a collection of class-specific cases.
-/

namespace GQ2.Dyadic.Instances.MFieldHandlePivotNormalForm

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcGeneralHandleRealization
open GQ2.Dyadic.Instances.MpcGeneralHandleFamily
open GQ2.Dyadic.Instances.MpcGeneralHandleCertificate
open GQ2.Dyadic.Instances.MFieldMobileHandleDichotomy

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- An exact U-handle pivot can be normalized to `2^r`, with its paired V row killed, by a
chi-preserving core automorphism that fixes C. -/
theorem exists_normalizedHandlePivot_of_U
    {alpha r h : ℕ}
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (hlev : MpcChiKerLevelH alpha r h nu) (j : Fin h) (gamma : ℤ_[2]ˣ)
    (hU : toAdd (nu (dmGen alpha h (handleIdxU j))) =
      (gamma : ℤ_[2]) * 2 ^ r) :
    ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
      toAdd (nu (Psi (dmGen alpha h (handleIdxU j)))) = 2 ^ r ∧
      nu (Psi (dmGen alpha h (handleIdxV j))) = 1 ∧
      nu (Psi (dmC alpha h)) = nu (dmC alpha h) := by
  obtain ⟨qV, hV⟩ := hlev (dmGen alpha h (handleIdxV j)) (chiM_handleV alpha h j)
  let k : ℤ_[2] := -((gamma : ℤ_[2]) * qV)
  let F : Function.End (Fin (coreRank h) → ℤ_[2]) :=
    frameEnd (frameTauV j k) * frameEnd (frameTheta j gamma⁻¹)
  have hF : F ∈ Submonoid.closure (frameClearGens h) :=
    mul_mem (Submonoid.subset_closure (frameTauV_mem_clearGens j k))
      (frameTheta_mem_clearGens j gamma⁻¹)
  obtain ⟨Psi, hmem, hbridge⟩ := exists_dmRealizes alpha h hF
  refine ⟨Psi, chiM_of_mem_dmClearAuts alpha h hmem, ?_, ?_, ?_⟩
  · have hu := congrFun (hbridge nu) (handleIdxU j)
    change toAdd (nu (Psi (dmGen alpha h (handleIdxU j)))) = _ at hu
    dsimp only [F] at hu
    rw [frameEnd_mul_apply, frameTauV_handleU_self,
      frameTheta_handleU_self, smul_eq_mul] at hu
    simp only [nuFrame_apply] at hu
    rw [hU] at hu
    rw [hu, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  · apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    have hv := congrFun (hbridge nu) (handleIdxV j)
    change toAdd (nu (Psi (dmGen alpha h (handleIdxV j)))) = _ at hv
    dsimp only [F] at hv
    rw [frameEnd_mul_apply, frameTauV_handleV_self,
      frameTheta_handleV_self, frameTheta_handleU_self, smul_eq_mul, smul_eq_mul] at hv
    simp only [nuFrame_apply] at hv
    rw [hU, hV] at hv
    rw [hv]
    dsimp only [k]
    rw [show (((gamma⁻¹)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = (gamma : ℤ_[2]) by simp]
    simp only [smul_eq_mul]
    have hginv : ((gamma⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (gamma : ℤ_[2]) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [← mul_assoc (((gamma⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) (gamma : ℤ_[2]) (2 ^ r),
      hginv, one_mul]
    ring
  · apply Multiplicative.toAdd.injective
    have hc := congrFun (hbridge nu) 2
    change toAdd (nu (Psi (dmC alpha h))) = _ at hc
    dsimp only [F] at hc
    rw [frameEnd_mul_apply,
      frameTauV_of_ne j _ _
        (Fin.ne_of_val_ne (by rw [coreVal_two, handleIdxU_val]; omega))
        (Fin.ne_of_val_ne (by rw [coreVal_two, handleIdxV_val]; omega)),
      frameTheta_of_ne j _ _
        (Fin.ne_of_val_ne (by rw [coreVal_two, handleIdxU_val]; omega))
        (Fin.ne_of_val_ne (by rw [coreVal_two, handleIdxV_val]; omega))] at hc
    simp only [nuFrame_apply] at hc
    exact hc

/-- The V-handle case is first swapped into U, then normalized in the same handle plane. -/
theorem exists_normalizedHandlePivot_of_V
    {alpha r h : ℕ}
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (hlev : MpcChiKerLevelH alpha r h nu) (j : Fin h) (gamma : ℤ_[2]ˣ)
    (hV : toAdd (nu (dmGen alpha h (handleIdxV j))) =
      (gamma : ℤ_[2]) * 2 ^ r) :
    ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
      toAdd (nu (Psi (dmGen alpha h (handleIdxU j)))) = 2 ^ r ∧
      nu (Psi (dmGen alpha h (handleIdxV j))) = 1 ∧
      nu (Psi (dmC alpha h)) = nu (dmC alpha h) := by
  obtain ⟨qU, hU⟩ := hlev (dmGen alpha h (handleIdxU j)) (chiM_handleU alpha h j)
  let k : ℤ_[2] := (gamma : ℤ_[2]) * qU
  let F : Function.End (Fin (coreRank h) → ℤ_[2]) :=
    frameEnd (frameTauV j k) * frameEnd (frameTheta j gamma⁻¹) * frameEnd (frameS j)
  have hF : F ∈ Submonoid.closure (frameClearGens h) :=
    mul_mem
      (mul_mem (Submonoid.subset_closure (frameTauV_mem_clearGens j k))
        (frameTheta_mem_clearGens j gamma⁻¹))
      (frameS_mem_clearGens j)
  obtain ⟨Psi, hmem, hbridge⟩ := exists_dmRealizes alpha h hF
  refine ⟨Psi, chiM_of_mem_dmClearAuts alpha h hmem, ?_, ?_, ?_⟩
  · have hu := congrFun (hbridge nu) (handleIdxU j)
    change toAdd (nu (Psi (dmGen alpha h (handleIdxU j)))) = _ at hu
    dsimp only [F] at hu
    change toAdd (nu (Psi (dmGen alpha h (handleIdxU j)))) =
      frameTauV j k (frameTheta j gamma⁻¹
        (frameS j (nuFrame nu (dmGen alpha h)))) (handleIdxU j) at hu
    rw [frameTauV_handleU_self,
      frameTheta_handleU_self, frameS_handleU_self, smul_eq_mul] at hu
    simp only [nuFrame_apply] at hu
    rw [hV] at hu
    rw [hu, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  · apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    have hv := congrFun (hbridge nu) (handleIdxV j)
    change toAdd (nu (Psi (dmGen alpha h (handleIdxV j)))) = _ at hv
    dsimp only [F] at hv
    change toAdd (nu (Psi (dmGen alpha h (handleIdxV j)))) =
      frameTauV j k (frameTheta j gamma⁻¹
        (frameS j (nuFrame nu (dmGen alpha h)))) (handleIdxV j) at hv
    rw [frameTauV_handleV_self,
      frameTheta_handleV_self, frameTheta_handleU_self,
      frameS_handleV_self, frameS_handleU_self, smul_eq_mul, smul_eq_mul] at hv
    simp only [nuFrame_apply] at hv
    rw [hU, hV] at hv
    rw [hv]
    dsimp only [k]
    rw [show (((gamma⁻¹)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = (gamma : ℤ_[2]) by simp]
    simp only [smul_eq_mul]
    have hginv : ((gamma⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (gamma : ℤ_[2]) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [← mul_assoc (((gamma⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) (gamma : ℤ_[2]) (2 ^ r),
      hginv, one_mul]
    ring
  · apply Multiplicative.toAdd.injective
    have hc := congrFun (hbridge nu) 2
    change toAdd (nu (Psi (dmC alpha h))) = _ at hc
    dsimp only [F] at hc
    change toAdd (nu (Psi (dmC alpha h))) =
      frameTauV j k (frameTheta j gamma⁻¹
        (frameS j (nuFrame nu (dmGen alpha h)))) 2 at hc
    rw [frameTauV_of_ne j _ _
        (Fin.ne_of_val_ne (by rw [coreVal_two, handleIdxU_val]; omega))
        (Fin.ne_of_val_ne (by rw [coreVal_two, handleIdxV_val]; omega)),
      frameTheta_of_ne j _ _
        (Fin.ne_of_val_ne (by rw [coreVal_two, handleIdxU_val]; omega))
        (Fin.ne_of_val_ne (by rw [coreVal_two, handleIdxV_val]; omega)),
      frameS_of_ne j _
        (Fin.ne_of_val_ne (by rw [coreVal_two, handleIdxU_val]; omega))
        (Fin.ne_of_val_ne (by rw [coreVal_two, handleIdxV_val]; omega))] at hc
    simp only [nuFrame_apply] at hc
    exact hc

/-- A normalized exact pivot on one handle plane. -/
def NormalizedMHandlePivotAtLevel {alpha r h : ℕ}
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2])) : Prop :=
  ∃ j : Fin h,
    ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
      toAdd (nu (Psi (dmGen alpha h (handleIdxU j)))) = 2 ^ r ∧
      nu (Psi (dmGen alpha h (handleIdxV j))) = 1 ∧
      nu (Psi (dmC alpha h)) = nu (dmC alpha h)

/-- Either orientation of an exact handle pivot admits the same normalized U/V form. -/
theorem normalizedMHandlePivotAtLevel_of_handlePivot
    {alpha r h : ℕ}
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (hlev : MpcChiKerLevelH alpha r h nu)
    (H : (∃ j : Fin h, ∃ gamma : ℤ_[2]ˣ,
          toAdd (nu (dmGen alpha h (handleIdxU j))) =
            (gamma : ℤ_[2]) * 2 ^ r) ∨
        ∃ j : Fin h, ∃ gamma : ℤ_[2]ˣ,
          toAdd (nu (dmGen alpha h (handleIdxV j))) =
            (gamma : ℤ_[2]) * 2 ^ r) :
    NormalizedMHandlePivotAtLevel (r := r) nu := by
  rcases H with ⟨j, gamma, hU⟩ | ⟨j, gamma, hV⟩
  · obtain ⟨Psi, hchi, hU', hV', hC⟩ :=
      exists_normalizedHandlePivot_of_U nu hlev j gamma hU
    exact ⟨j, Psi, hchi, hU', hV', hC⟩
  · obtain ⟨Psi, hchi, hU', hV', hC⟩ :=
      exists_normalizedHandlePivot_of_V nu hlev j gamma hV
    exact ⟨j, Psi, hchi, hU', hV', hC⟩

/-- Field-side spelling of the normalized handle-pivot alternative. -/
def MFieldNormalizedHandlePivotAtLevel {R : LocalReciprocity}
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (B : MarkedRecip R K) (alpha r h : ℕ) : Prop :=
  ∃ e : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)),
    ∃ j : Fin h,
      toAdd (nuUrKTwo B (e.1 (dmGen alpha h (handleIdxU j)))) = 2 ^ r ∧
      nuUrKTwo B (e.1 (dmGen alpha h (handleIdxV j))) = 1

/-- Every exact field handle pivot can be put in normalized U/V form without changing the
orientation, provided the field level is r. -/
theorem mFieldNormalizedHandlePivotAtLevel_of_handlePivot
    {R : LocalReciprocity}
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (B : MarkedRecip R K) {alpha r h : ℕ} (hr : B.r = r)
    (H : MFieldHandlePivotAtLevel B alpha r h) :
    MFieldNormalizedHandlePivotAtLevel B alpha r h := by
  obtain ⟨e, H⟩ := H
  let nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]) :=
    transport (nuUrKTwo B).toMonoidHom e.1
      ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun)
  have hlev := chiKerLevel_of_level B hr e
  change MpcChiKerLevelH alpha r h nu at hlev
  change ((∃ j : Fin h, ∃ gamma : ℤ_[2]ˣ,
      toAdd (nu (dmGen alpha h (handleIdxU j))) =
        (gamma : ℤ_[2]) * 2 ^ r) ∨
    ∃ j : Fin h, ∃ gamma : ℤ_[2]ˣ,
      toAdd (nu (dmGen alpha h (handleIdxV j))) =
        (gamma : ℤ_[2]) * 2 ^ r) at H
  obtain ⟨j, Psi, hchi, hU, hV, _hC⟩ :=
    normalizedMHandlePivotAtLevel_of_handlePivot nu hlev H
  let e' : OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K)) :=
    ⟨Psi.trans e.1, fun x => (e.2 (Psi x)).trans (hchi x)⟩
  refine ⟨e', j, ?_, ?_⟩
  · change toAdd (nu (Psi (dmGen alpha h (handleIdxU j)))) = 2 ^ r
    exact hU
  · change nu (Psi (dmGen alpha h (handleIdxV j))) = 1
    exact hV

#print axioms exists_normalizedHandlePivot_of_U
#print axioms exists_normalizedHandlePivot_of_V
#print axioms NormalizedMHandlePivotAtLevel
#print axioms normalizedMHandlePivotAtLevel_of_handlePivot
#print axioms MFieldNormalizedHandlePivotAtLevel
#print axioms mFieldNormalizedHandlePivotAtLevel_of_handlePivot

end

end GQ2.Dyadic.Instances.MFieldHandlePivotNormalForm
