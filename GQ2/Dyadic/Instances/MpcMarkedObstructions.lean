/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcMarkedSecondary
import GQ2.Dyadic.Instances.EvenFamilyConstruct
import GQ2.Dyadic.Instances.EvenStratumShift

/-!
# Five necessary obstruction coordinates for the marked Mpc successor

This module packages five necessary vanishings: the three independent chi-twisted
crossed-derivation offsets at `A`, `C`, and `D`, the top digit of `nuM`, and the one-deeper digit
of `chiM`.  It proves that the explicit secondary defect from `MpcMarkedSecondary.lean` lies in
their intersection.  A later exact carrier audit shows that `chiM` is an additional necessary
vanishing, not the second carrier-annihilator coordinate; that role belongs to the additive
`D`-coordinate formalized in `MpcMarkedDelta.lean`.

The additive coordinate exposes a genuine recursive invariant.  Every full marked move is
nu-trivial, so it preserves a nu-neutral head correction, but the existing `MpcMkGood` predicate
does not require its chosen head to be nu-neutral.  `MpcMkNuGood` is the compatible strengthened
state: it projects to `MpcMkGood`, starts at the existing class-five base, and its nu-neutrality is
preserved by `mpcMkAdvance`.

Nothing here identifies the intersection of the five kernels with the marked cost range, proves
that the range has exactly this annihilator, or proves the missing successor range membership.
Those statements require a normal-form/reflection theorem not present in the tree.  The results
below are necessary-coordinate vanishings only.

Declaration prefix `mpcMk` (namespace `GQ2.Dyadic.Instances.MpcMk`).  No `sorry`, no new axiom,
no `native_decide`, and no heartbeat or recursion override.
-/

namespace GQ2.Dyadic.Instances.MpcMk

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcWord GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcLad GQ2.Dyadic.Instances.MpcSx
open GQ2.Roe.Labute GQ2.Dyadic.SqCore
open GQ2.Dyadic.StageGeneric GQ2.Dyadic.EvenFamily

noncomputable section

/-! ## 1. The crossed-derivation coordinates -/

/-- The model crossed derivation with one marked offset. -/
def mpcMkCoordinateDeriv (N : ℕ) (hN : 1 ≤ N) (i : Fin 4) :
    ContinuousMonoidHom (DM 2 0 : Type) (WL N) :=
  evenFamDerivModelM 2 0 (by omega) hN (Pi.single i 1)

/-- Every legal Mpc defect is killed by every model coordinate derivation. -/
theorem mpcMkDefectTop_mem_coordinateDerivKer {j : ℕ} {p : MpcMkPoint}
    (hp : p ∈ mpcWordSet (j + 1)) (i : Fin 4) :
    ((mpcMkDefectTop j p hp : zLayer (DM 2 0 : Type) (j + 1)) :
        levelQuot (DM 2 0 : Type) (j + 2)) ∈
      derivKer (mpcMkCoordinateDeriv (j + 2) (by omega) i) (j + 1) := by
  let x : Fin (coreRank 0) → (DM 2 0 : Type) :=
    coreMark (mpcWordLetA p.1) (mpcWordLetB p.2.1)
      (mpcWordLetC p.2.2.1) (mpcWordLetD p.2.2.2)
  have hxWord : (mStageWord 2 0 (by omega)).word x = mpcLadDefect p := by
    change mRelWord 2 x = mpcLadDefect p
    rw [show x = coreMark (mpcWordLetA p.1) (mpcWordLetB p.2.1)
      (mpcWordLetC p.2.2.1) (mpcWordLetD p.2.2.2) from rfl,
      mRelWord_coreMark]
    rfl
  have hchi : ∀ k, chiM 2 0 (x k) = @vM 2 0 k := by
    intro k
    fin_cases k
    · change chiM 2 0 (mpcWordLetA p.1) = vM 2 0
      rw [mpcWordLetA, map_mul, map_mul, map_inv, map_pow,
        chiM_dmA, chiM_dmB, show chiM 2 0 p.1 = 1 from hp.1.2]
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, neg_one_sq, one_pow]
      simp
    · change chiM 2 0 (mpcWordLetB p.2.1) = vM 2 1
      rw [mpcWordLetB, map_mul, chiM_dmB,
        show chiM 2 0 p.2.1 = 1 from hp.2.1.2, mul_one]
      rfl
    · change chiM 2 0 (mpcWordLetC p.2.2.1) = vM 2 2
      rw [mpcWordLetC, map_mul, map_mul, map_pow, chiM_dmB, chiM_dmC,
        show chiM 2 0 p.2.2.1 = 1 from hp.2.2.1.1.2, neg_one_sq]
      simp
    · change chiM 2 0 (mpcWordLetD p.2.2.2) = vM 2 3
      rw [mpcWordLetD, map_mul, chiM_dmD,
        show chiM 2 0 p.2.2.2 = 1 from hp.2.2.2.1.2, mul_one]
      rfl
  have hrel : (mStageWord 2 0 (by omega)).word
      (fun i ↦ levelMk (DM 2 0 : Type) (j + 1) (x i)) = 1 := by
    have hh := (mpcWord_mem_iff_levelMk (j + 1) _).mp hp.2.2.2.2
    rw [← (mStageWord 2 0 (by omega)).map_word
      (levelMk (DM 2 0 : Type) (j + 1)) x, hxWord]
    exact hh
  have h := evenFam_word_mem_derivKer
    (W := mStageWord 2 0 (by omega)) (v := @vM 2 0)
    (evenFam_mRelWord_wordLift 2 (by omega))
    (evenFamDerivModelM_isChiShadow 2 0 (by omega) (by omega)
      (Pi.single i 1)) x hchi hrel
  rw [hxWord] at h
  simpa only [mpcMkDefectTop, mpcMkCoordinateDeriv,
    show j + 1 + 1 = j + 2 by omega] using h

/-- The secondary defect product is killed by every model coordinate derivation. -/
theorem mpcMkSecondary_mem_coordinateDerivKer {j : ℕ} (hj : 3 ≤ j)
    {p : MpcMkPoint} (hp : p ∈ mpcWordSet (j + 1)) (u : MpcMkCostDomain j)
    (hu : mpcMkCost j (by omega) p.2.1 p.2.2.2 u = mpcMkDefectTop j p hp)
    (i : Fin 4) :
    (((mpcMkKillLiftResidual (by omega) hp u hu * mpcMkAdvanceHallTop hp u :
          zLayer (DM 2 0 : Type) (j + 2)) :
        levelQuot (DM 2 0 : Type) (j + 3))) ∈
      derivKer (mpcMkCoordinateDeriv (j + 3) (by omega) i) (j + 2) := by
  rw [← mpcMkDefectTop_advance_eq_liftResidual_mul_hall hj hp u hu]
  exact mpcMkDefectTop_mem_coordinateDerivKer
    (mpcMk_advance_mem (by omega) hp u hu) i

/-! ## 2. The additive recursive invariant -/

/-- The marked carrier is invisible to the canonical additive marking. -/
theorem mpcSx_marked_nu {x : (DM 2 0 : Type)} (hx : x ∈ mpcSxMarked) :
    nuM 2 0 (by omega) x = 1 := by
  have hle : mpcSxMarked ≤ (nuM 2 0 (by omega)).toMonoidHom.ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro y (rfl | ⟨a, b, rfl⟩)
    · refine MonoidHom.mem_ker.2 ?_
      rw [map_pow]
      change nuM 2 0 (by omega) (dmB 2 0) ^ 2 = 1
      rw [nuM_dmB]
      simp
    · exact MonoidHom.mem_ker.2
        (map_commP_eq_one (nuM 2 0 (by omega)).toMonoidHom a b)
  exact MonoidHom.mem_ker.1 (hle hx)

/-- The recursive Mpc orbit singled out by the explicit base has a nu-neutral head. -/
def MpcMkNuNeutral (p : MpcMkPoint) : Prop :=
  nuM 2 0 (by omega) p.1 = 1

theorem mpcMk_nuNeutral_w4 : MpcMkNuNeutral mpcLadW4 := by
  change nuM 2 0 (by omega) mpcBldW = 1
  exact map_commP_eq_one (nuM 2 0 (by omega)).toMonoidHom _ _

/-- Full marked moves preserve nu-neutrality of the head correction. -/
theorem mpcMk_nuNeutral_advance {j : ℕ} {p : MpcMkPoint}
    (hp : MpcMkNuNeutral p) (u : MpcMkCostDomain j) :
    MpcMkNuNeutral (mpcMkAdvance j p u) := by
  change nuM 2 0 (by omega) (p.1 * (u.1 : (DM 2 0 : Type))) = 1
  rw [map_mul, hp, mpcSx_marked_nu u.1.2.1, one_mul]

/-- The exact range state `MpcMkGood`, strengthened by a nu-neutral chosen witness. -/
def MpcMkNuGood (j : ℕ) : Prop :=
  ∃ hj : 2 ≤ j, ∃ p, ∃ hp : p ∈ mpcWordSet (j + 1),
    MpcMkNuNeutral p ∧
      mpcMkDefectTop j p hp ∈
        MonoidHom.range (mpcMkCost j hj p.2.1 p.2.2.2)

/-- Forgetting nu-neutrality recovers the existing good-rung API. -/
theorem mpcMk_nuGood_good {j : ℕ} (h : MpcMkNuGood j) : MpcMkGood j := by
  obtain ⟨hj, p, hp, _, hr⟩ := h
  exact ⟨hj, p, hp, hr⟩

/-- The existing class-five step starts the strengthened recursive state. -/
theorem mpcMk_nuGood_three : MpcMkNuGood 3 := by
  refine ⟨by omega, mpcLadW4, mpcLad_w4_mem, mpcMk_nuNeutral_w4, ?_⟩
  exact (mpcMk_fullSupply_iff_mem_costRange (by omega) mpcLad_w4_mem).mp
    mpcMk_fullSupply_three

/-- A legal point with nu-neutral head has exactly nu-trivial defect. -/
theorem mpcMk_defect_nu_eq_one {j : ℕ} {p : MpcMkPoint}
    (hp : p ∈ mpcWordSet (j + 1)) (hnu : MpcMkNuNeutral p) :
    nuM 2 0 (by omega) (mpcLadDefect p) = 1 := by
  change nuM 2 0 (by omega) p.1 = 1 at hnu
  have hmnu : nuM 2 0 (by omega) p.2.2.1 = 1 :=
    (mpcWord_mem_rowKer.mp hp.2.2.1.2) (nuM 2 0 (by omega))
  rw [mpcLadDefect, map_mWord, mWord_comm]
  simp only [mpcWordLetA, mpcWordLetC, map_mul, map_inv, map_pow,
    nuM_dmA, nuM_dmB, nuM_dmC, hnu, hmnu]
  simp only [mul_one]
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_inv, toAdd_pow, toAdd_ofAdd, toAdd_one,
    nsmul_eq_mul]
  norm_num

/-- Every legal Mpc defect is exactly chi-trivial. -/
theorem mpcMk_defect_chi_eq_one {j : ℕ} {p : MpcMkPoint}
    (hp : p ∈ mpcWordSet (j + 1)) :
    chiM 2 0 (mpcLadDefect p) = 1 := by
  rw [mpcLadDefect, map_mWord, mWord_comm]
  simp only [mpcWordLetA, mpcWordLetC, map_mul, map_inv, map_pow,
    chiM_dmA, chiM_dmB, chiM_dmC,
    show chiM 2 0 p.1 = 1 from hp.1.2,
    show chiM 2 0 p.2.2.1 = 1 from hp.2.2.1.1.2]
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, neg_one_sq, one_pow]
  simp

/-! ## 3. Quotient-level additive and cyclotomic coordinates -/

/-- Reduction of the canonical additive marking modulo `2^k`. -/
def mpcMkNuMod (k : ℕ) :
    ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative (ZMod (2 ^ k))) where
  toMonoidHom :=
    (AddMonoidHom.toMultiplicative (PadicInt.toZModPow k).toAddMonoidHom).comp
      (nuM 2 0 (by omega)).toMonoidHom
  continuous_toFun := by
    have hred : Continuous (PadicInt.toZModPow (p := 2) k) := by
      rw [continuous_def]
      intro T _
      exact isOpen_preimage_toZModPow k T
    exact continuous_ofAdd.comp
      (hred.comp (continuous_toAdd.comp (nuM 2 0 (by omega)).continuous_toFun))

private theorem mpcMkNuMod_pow (k : ℕ) (x : Multiplicative (ZMod (2 ^ k))) :
    x ^ 2 ^ k = 1 := by
  obtain ⟨a, rfl⟩ : ∃ a : ZMod (2 ^ k), Multiplicative.ofAdd a = x :=
    ⟨Multiplicative.toAdd x, rfl⟩
  rw [← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

/-- The top additive digit on `Q_(k+1)`.  It is well-defined because the target is abelian
of exponent `2^k`, so its `(k+1)`st two-central layer is trivial. -/
def mpcMkNuLevel (k : ℕ) :
    levelQuot (DM 2 0 : Type) (k + 1) →* Multiplicative (ZMod (2 ^ k)) :=
  QuotientGroup.lift (twoCentralSeries (DM 2 0 : Type) (k + 1))
    (mpcMkNuMod k).toMonoidHom (fun g hg ↦ by
      have him : mpcMkNuMod k g ∈
          twoCentralSeries (Multiplicative (ZMod (2 ^ k))) (k + 1) :=
        map_twoCentralSeries_le (mpcMkNuMod k).toMonoidHom
          (mpcMkNuMod k).continuous_toFun (k + 1) ⟨g, hg, rfl⟩
      obtain ⟨x, hx⟩ := evenStratumShift_twoCentralSeries_le_pow k him
      rw [MonoidHom.mem_ker]
      change mpcMkNuMod k g = 1
      rw [← hx]
      exact mpcMkNuMod_pow k x)

@[simp] theorem mpcMkNuLevel_levelMk (k : ℕ) (g : (DM 2 0 : Type)) :
    mpcMkNuLevel k (levelMk (DM 2 0 : Type) (k + 1) g) = mpcMkNuMod k g :=
  rfl

/-- Vanishing of the additive top digit. -/
def mpcMkNuKernel (k : ℕ) : Subgroup (levelQuot (DM 2 0 : Type) (k + 1)) :=
  (mpcMkNuLevel k).ker

/-- Vanishing of the one-deeper cyclotomic digit. -/
def mpcMkChiKernel (k : ℕ) : Subgroup (levelQuot (DM 2 0 : Type) (k + 1)) :=
  (chiLevel (chiM 2 0) (k + 1)).ker

/-- The three independent coordinate-derivation directions plus the additive and
cyclotomic top digits.  No equality with the marked cost range is asserted. -/
def mpcMkFiveNecessaryKernel (k : ℕ) :
    Subgroup (levelQuot (DM 2 0 : Type) (k + 1)) :=
  derivKer (mpcMkCoordinateDeriv (k + 1) (by omega) 0) k ⊓
    derivKer (mpcMkCoordinateDeriv (k + 1) (by omega) 2) k ⊓
    derivKer (mpcMkCoordinateDeriv (k + 1) (by omega) 3) k ⊓
    mpcMkNuKernel k ⊓ mpcMkChiKernel k

/-! ## 4. The five necessary secondary vanishings -/

/-- A nu-neutral secondary defect has vanishing additive top digit. -/
theorem mpcMkSecondary_mem_nuKernel {j : ℕ} (hj : 3 ≤ j)
    {p : MpcMkPoint} (hp : p ∈ mpcWordSet (j + 1)) (hnu : MpcMkNuNeutral p)
    (u : MpcMkCostDomain j)
    (hu : mpcMkCost j (by omega) p.2.1 p.2.2.2 u = mpcMkDefectTop j p hp) :
    (((mpcMkKillLiftResidual (by omega) hp u hu * mpcMkAdvanceHallTop hp u :
          zLayer (DM 2 0 : Type) (j + 2)) :
        levelQuot (DM 2 0 : Type) (j + 3))) ∈ mpcMkNuKernel (j + 2) := by
  rw [← mpcMkDefectTop_advance_eq_liftResidual_mul_hall hj hp u hu]
  rw [mpcMkNuKernel, MonoidHom.mem_ker]
  change mpcMkNuMod (j + 2) (mpcLadDefect (mpcMkAdvance j p u)) = 1
  change Multiplicative.ofAdd
    (PadicInt.toZModPow (j + 2)
      (nuM 2 0 (by omega) (mpcLadDefect (mpcMkAdvance j p u))).toAdd) = 1
  rw [mpcMk_defect_nu_eq_one (mpcMk_advance_mem (by omega) hp u hu)
    (mpcMk_nuNeutral_advance hnu u)]
  simp

/-- Every secondary defect has vanishing one-deeper cyclotomic digit. -/
theorem mpcMkSecondary_mem_chiKernel {j : ℕ} (hj : 3 ≤ j)
    {p : MpcMkPoint} (hp : p ∈ mpcWordSet (j + 1)) (u : MpcMkCostDomain j)
    (hu : mpcMkCost j (by omega) p.2.1 p.2.2.2 u = mpcMkDefectTop j p hp) :
    (((mpcMkKillLiftResidual (by omega) hp u hu * mpcMkAdvanceHallTop hp u :
          zLayer (DM 2 0 : Type) (j + 2)) :
        levelQuot (DM 2 0 : Type) (j + 3))) ∈ mpcMkChiKernel (j + 2) := by
  rw [← mpcMkDefectTop_advance_eq_liftResidual_mul_hall hj hp u hu]
  rw [mpcMkChiKernel, MonoidHom.mem_ker]
  change chiLevel (chiM 2 0) (j + 3)
    (levelMk (DM 2 0 : Type) (j + 3)
      (mpcLadDefect (mpcMkAdvance j p u))) = 1
  rw [chiLevel_levelMk,
    mpcMk_defect_chi_eq_one (mpcMk_advance_mem (by omega) hp u hu), map_one]

/-- All five explicit necessary obstruction coordinates vanish on the nu-neutral secondary
defect.  This is only containment in a common kernel, not a cost-range theorem. -/
theorem mpcMkSecondary_mem_fiveNecessaryKernel {j : ℕ} (hj : 3 ≤ j)
    {p : MpcMkPoint} (hp : p ∈ mpcWordSet (j + 1)) (hnu : MpcMkNuNeutral p)
    (u : MpcMkCostDomain j)
    (hu : mpcMkCost j (by omega) p.2.1 p.2.2.2 u = mpcMkDefectTop j p hp) :
    (((mpcMkKillLiftResidual (by omega) hp u hu * mpcMkAdvanceHallTop hp u :
          zLayer (DM 2 0 : Type) (j + 2)) :
        levelQuot (DM 2 0 : Type) (j + 3))) ∈
      mpcMkFiveNecessaryKernel (j + 2) := by
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · change _ ∈ derivKer (mpcMkCoordinateDeriv (j + 2 + 1) (by omega) 0) (j + 2)
    convert mpcMkSecondary_mem_coordinateDerivKer hj hp u hu 0 using 1
  · change _ ∈ derivKer (mpcMkCoordinateDeriv (j + 2 + 1) (by omega) 2) (j + 2)
    convert mpcMkSecondary_mem_coordinateDerivKer hj hp u hu 2 using 1
  · change _ ∈ derivKer (mpcMkCoordinateDeriv (j + 2 + 1) (by omega) 3) (j + 2)
    convert mpcMkSecondary_mem_coordinateDerivKer hj hp u hu 3 using 1
  · exact mpcMkSecondary_mem_nuKernel hj hp hnu u hu
  · exact mpcMkSecondary_mem_chiKernel hj hp u hu

/-! ## 5. Axiom pins -/

#print axioms mpcMkCoordinateDeriv
#print axioms mpcMkDefectTop_mem_coordinateDerivKer
#print axioms mpcMkSecondary_mem_coordinateDerivKer
#print axioms mpcSx_marked_nu
#print axioms MpcMkNuNeutral
#print axioms mpcMk_nuNeutral_w4
#print axioms mpcMk_nuNeutral_advance
#print axioms MpcMkNuGood
#print axioms mpcMk_nuGood_good
#print axioms mpcMk_nuGood_three
#print axioms mpcMk_defect_nu_eq_one
#print axioms mpcMk_defect_chi_eq_one
#print axioms mpcMkNuMod
#print axioms mpcMkNuLevel
#print axioms mpcMkNuLevel_levelMk
#print axioms mpcMkNuKernel
#print axioms mpcMkChiKernel
#print axioms mpcMkFiveNecessaryKernel
#print axioms mpcMkSecondary_mem_nuKernel
#print axioms mpcMkSecondary_mem_chiKernel
#print axioms mpcMkSecondary_mem_fiveNecessaryKernel

end

end GQ2.Dyadic.Instances.MpcMk
