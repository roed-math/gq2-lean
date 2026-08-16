/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcMarkedCarrierAudit
import GQ2.Dyadic.MarkedCore.MFrameExists

/-!
# The D-coordinate obstruction for the marked Mpc successor

Exact finite evaluation falsifies the previously proposed use of `chi` as the second source
carrier-annihilator coordinate: `chi` composed with the graded cost is zero in the tested
rungs, and the resulting kernel is too large already at `r = 2`.  The corrected candidate
uses the additive `D`-coordinate `deltaD` from the canonical M-frame alongside `nu`.

This module formalizes the corrected coordinate and the structural facts that do not require
the missing all-degree graded theorem.  It proves that marked costs and the recursively
arising secondary have zero `deltaD` digit, packages the corrected five-coordinate kernel,
and shows that membership in that kernel still yields the existing unrestricted cost witness.
For the recursive statement, `nu`-neutrality alone is insufficient: the state explicitly
tracks that the head remains in `mpcSxMarked`.

The candidate equality

`ker ((nu, deltaD) ∘ c_r) = M_r + ker c_r`

holds in exact finite calculations for `r = 2, 3, 4`, but those calculations are not a proof.
The all-degree equality remains open and is neither stated as an assumption nor introduced as
an axiom here.  The existing `chi` vanishing theorem remains a valid extra necessary condition
on the recursive secondary; it is not a source carrier-annihilator coordinate.

Declaration prefix `mpcMk` (namespace `GQ2.Dyadic.Instances.MpcMk`).  No `sorry`, no new
axiom, no `native_decide`, and no heartbeat or recursion override.
-/

namespace GQ2.Dyadic.Instances.MpcMk

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcPiv GQ2.Dyadic.Instances.MpcOrb
open GQ2.Dyadic.Instances.MpcWord GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcLad GQ2.Dyadic.Instances.MpcFv
open GQ2.Dyadic.Instances.MpcSx GQ2.Roe.Labute GQ2.Dyadic.SqCore
open GQ2.Dyadic.EvenFamily
open GQ2.Dyadic.StageGeneric

noncomputable section

/-! ## 1. The additive D-coordinate and its finite-level digit -/

/-- The additive D-coordinate of the canonical M-frame, pulled back to `DM 2 0`. -/
def mpcMkDeltaD :
    ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative ℤ_[2]) :=
  (mDHom 2 0).comp (mAbMkHom 2 0)

@[simp] theorem mpcMkDeltaD_dmA : mpcMkDeltaD (dmA 2 0) = 1 := by
  change mDHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 0)) = 1
  rw [mDHom, mCoordHom_gen, coreMark_zero]

@[simp] theorem mpcMkDeltaD_dmB : mpcMkDeltaD (dmB 2 0) = 1 := by
  change mDHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 1)) = 1
  rw [mDHom, mCoordHom_gen, coreMark_one]

@[simp] theorem mpcMkDeltaD_dmC : mpcMkDeltaD (dmC 2 0) = 1 := by
  change mDHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 2)) = 1
  rw [mDHom, mCoordHom_gen, coreMark_two]

@[simp] theorem mpcMkDeltaD_dmD :
    mpcMkDeltaD (dmD 2 0) = ofAdd (1 : ℤ_[2]) := by
  change mDHom 2 0 (GQ2.SectionThree.abMk (dmGen 2 0 3)) =
    ofAdd (1 : ℤ_[2])
  rw [mDHom, mCoordHom_gen, coreMark_three]

/-- The marked carrier has zero D-coordinate. -/
theorem mpcSx_marked_deltaD {x : (DM 2 0 : Type)} (hx : x ∈ mpcSxMarked) :
    mpcMkDeltaD x = 1 := by
  have hle : mpcSxMarked ≤ mpcMkDeltaD.toMonoidHom.ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro y (rfl | ⟨a, b, rfl⟩)
    · change mpcMkDeltaD (dmB 2 0 ^ 2) = 1
      rw [map_pow, mpcMkDeltaD_dmB, one_pow]
    · exact MonoidHom.mem_ker.2
        (map_commP_eq_one mpcMkDeltaD.toMonoidHom a b)
  exact MonoidHom.mem_ker.1 (hle hx)

/-- Reduction of the D-coordinate modulo `2^k`. -/
def mpcMkDeltaDMod (k : ℕ) :
    ContinuousMonoidHom (DM 2 0 : Type) (Multiplicative (ZMod (2 ^ k))) where
  toMonoidHom :=
    (AddMonoidHom.toMultiplicative (PadicInt.toZModPow k).toAddMonoidHom).comp
      mpcMkDeltaD.toMonoidHom
  continuous_toFun := by
    have hred : Continuous (PadicInt.toZModPow (p := 2) k) := by
      rw [continuous_def]
      intro T _
      exact isOpen_preimage_toZModPow k T
    exact continuous_ofAdd.comp
      (hred.comp (continuous_toAdd.comp mpcMkDeltaD.continuous_toFun))

private theorem mpcMkDeltaDMod_pow (k : ℕ)
    (x : Multiplicative (ZMod (2 ^ k))) : x ^ 2 ^ k = 1 := by
  obtain ⟨a, rfl⟩ : ∃ a : ZMod (2 ^ k), Multiplicative.ofAdd a = x :=
    ⟨Multiplicative.toAdd x, rfl⟩
  rw [← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

/-- The top D-coordinate digit on `Q_(k+1)`. -/
def mpcMkDeltaDLevel (k : ℕ) :
    levelQuot (DM 2 0 : Type) (k + 1) →* Multiplicative (ZMod (2 ^ k)) :=
  QuotientGroup.lift (twoCentralSeries (DM 2 0 : Type) (k + 1))
    (mpcMkDeltaDMod k).toMonoidHom (fun g hg ↦ by
      have him : mpcMkDeltaDMod k g ∈
          twoCentralSeries (Multiplicative (ZMod (2 ^ k))) (k + 1) :=
        map_twoCentralSeries_le (mpcMkDeltaDMod k).toMonoidHom
          (mpcMkDeltaDMod k).continuous_toFun (k + 1) ⟨g, hg, rfl⟩
      obtain ⟨x, hx⟩ := evenStratumShift_twoCentralSeries_le_pow k him
      rw [MonoidHom.mem_ker]
      change mpcMkDeltaDMod k g = 1
      rw [← hx]
      exact mpcMkDeltaDMod_pow k x)

@[simp] theorem mpcMkDeltaDLevel_levelMk (k : ℕ) (g : (DM 2 0 : Type)) :
    mpcMkDeltaDLevel k (levelMk (DM 2 0 : Type) (k + 1) g) =
      mpcMkDeltaDMod k g :=
  rfl

/-- The kernel of the top D-coordinate digit on `Q_(k+1)`. -/
def mpcMkDeltaDKernel (k : ℕ) :
    Subgroup (levelQuot (DM 2 0 : Type) (k + 1)) :=
  (mpcMkDeltaDLevel k).ker

/-! ## 2. Marked-head state and recursive neutrality -/

/-- A recursive point whose head remains in the marked carrier. -/
def MpcMkMarkedHead (p : MpcMkPoint) : Prop :=
  p.1 ∈ mpcSxMarked

theorem mpcMk_markedHead_w4 : MpcMkMarkedHead mpcLadW4 := by
  change mpcBldW ∈ mpcSxMarked
  exact Subgroup.subset_closure (Or.inr ⟨dmD 2 0, dmB 2 0, rfl⟩)

theorem mpcMk_markedHead_advance {j : ℕ} {p : MpcMkPoint}
    (hp : MpcMkMarkedHead p) (u : MpcMkCostDomain j) :
    MpcMkMarkedHead (mpcMkAdvance j p u) := by
  exact Subgroup.mul_mem _ hp u.1.2.1

theorem mpcMk_markedHead_nuNeutral {p : MpcMkPoint}
    (hp : MpcMkMarkedHead p) : MpcMkNuNeutral p :=
  mpcSx_marked_nu hp

/-- A legal point with marked head has D-neutral defect. -/
theorem mpcMk_defect_deltaD_eq_one {j : ℕ} {p : MpcMkPoint}
    (hp : p ∈ mpcWordSet (j + 1)) (hmarked : MpcMkMarkedHead p) :
    mpcMkDeltaD (mpcLadDefect p) = 1 := by
  have hm : mpcMkDeltaD p.2.2.1 = 1 :=
    (mpcWord_mem_rowKer.mp hp.2.2.1.2) mpcMkDeltaD
  rw [mpcLadDefect, map_mWord, mWord_comm]
  simp only [mpcWordLetA, mpcWordLetC, map_mul, map_inv, map_pow,
    mpcMkDeltaD_dmA, mpcMkDeltaD_dmB, mpcMkDeltaD_dmC,
    mpcSx_marked_deltaD hmarked, hm]
  simp

/-! ## 3. The corrected five-coordinate kernel -/

/-- Every full marked cost has zero D-coordinate top digit. -/
theorem mpcMkCost_mem_deltaDKernel {r : ℕ} (hr : 2 ≤ r)
    (t n : (DM 2 0 : Type)) (u : MpcMkCostDomain r) :
    (((mpcMkCost r hr t n u : zLayer (DM 2 0 : Type) (r + 1)) :
        levelQuot (DM 2 0 : Type) (r + 2))) ∈
      mpcMkDeltaDKernel (r + 1) := by
  rw [mpcMkDeltaDKernel, MonoidHom.mem_ker]
  change mpcMkDeltaDMod (r + 1)
    (mpcBldIncr t n u.1 u.2.1 u.2.2.1 u.2.2.2) = 1
  have hs : mpcMkDeltaDMod (r + 1) u.1 = 1 := by
    change Multiplicative.ofAdd
      (PadicInt.toZModPow (r + 1) (mpcMkDeltaD u.1).toAdd) = 1
    rw [mpcSx_marked_deltaD u.1.2.1]
    simp
  simp only [mpcBldIncr, map_mul, map_pow, hs, one_pow, one_mul]
  simp [commP, mul_comm]

/-- The corrected five carrier-annihilator coordinates. -/
def mpcMkFiveCarrierKernel (k : ℕ) :
    Subgroup (levelQuot (DM 2 0 : Type) (k + 1)) :=
  derivKer (mpcMkCoordinateDeriv (k + 1) (by omega) 0) k ⊓
    derivKer (mpcMkCoordinateDeriv (k + 1) (by omega) 2) k ⊓
    derivKer (mpcMkCoordinateDeriv (k + 1) (by omega) 3) k ⊓
    mpcMkNuKernel k ⊓ mpcMkDeltaDKernel k

/-- The corrected five carrier coordinates still give the existing unrestricted cost
witness. Only the three crossed-derivation components are used at this stage. -/
theorem mpcMk_exists_unrestrictedCost_of_fiveCarrierKernel {r : ℕ}
    (hr : 2 ≤ r) {t n : (DM 2 0 : Type)}
    (ht : t ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hn : n ∈ twoCentralSeries (DM 2 0 : Type) 2)
    {q : levelQuot (DM 2 0 : Type) (r + 2)}
    (hq : q ∈ zLayer (DM 2 0 : Type) (r + 1))
    (hfive : q ∈ mpcMkFiveCarrierKernel (r + 1)) :
    ∃ us ut um un : (DM 2 0 : Type),
      us ∈ twoCentralSeries (DM 2 0 : Type) r ∧
      ut ∈ twoCentralSeries (DM 2 0 : Type) r ∧
      um ∈ twoCentralSeries (DM 2 0 : Type) r ∧
      un ∈ twoCentralSeries (DM 2 0 : Type) r ∧
      q = levelMk (DM 2 0 : Type) (r + 2)
        (mpcBldIncr t n us ut um un) := by
  obtain ⟨⟨⟨⟨h0, h2⟩, h3⟩, _⟩, _⟩ := hfive
  apply (mpcMk_mem_rawShiftSpan_iff_exists_unrestrictedCost r hr t n q).mp
  apply mpcMk_canonicalRawShiftSpan_le_rawBase r hr t n ht hn
  exact mpcMk_mem_canonicalRawShiftSpan_of_threeKernels
    (by omega) hq h0 h2 h3

/-! ## 4. The recursive secondary -/

/-- The explicit recursive secondary has zero D-coordinate once its head is tracked in the
marked carrier. -/
theorem mpcMkSecondary_mem_deltaDKernel {j : ℕ} (hj : 3 ≤ j)
    {p : MpcMkPoint} (hp : p ∈ mpcWordSet (j + 1))
    (hmarked : MpcMkMarkedHead p) (u : MpcMkCostDomain j)
    (hu : mpcMkCost j (by omega) p.2.1 p.2.2.2 u = mpcMkDefectTop j p hp) :
    (((mpcMkKillLiftResidual (by omega) hp u hu * mpcMkAdvanceHallTop hp u :
          zLayer (DM 2 0 : Type) (j + 2)) :
        levelQuot (DM 2 0 : Type) (j + 3))) ∈ mpcMkDeltaDKernel (j + 2) := by
  rw [← mpcMkDefectTop_advance_eq_liftResidual_mul_hall hj hp u hu]
  rw [mpcMkDeltaDKernel, MonoidHom.mem_ker]
  change mpcMkDeltaDMod (j + 2)
    (mpcLadDefect (mpcMkAdvance j p u)) = 1
  change Multiplicative.ofAdd
    (PadicInt.toZModPow (j + 2)
      (mpcMkDeltaD (mpcLadDefect (mpcMkAdvance j p u))).toAdd) = 1
  rw [mpcMk_defect_deltaD_eq_one
    (mpcMk_advance_mem (by omega) hp u hu)
    (mpcMk_markedHead_advance hmarked u)]
  simp

/-- The explicit recursive secondary lies in the corrected carrier kernel. -/
theorem mpcMkSecondary_mem_fiveCarrierKernel {j : ℕ} (hj : 3 ≤ j)
    {p : MpcMkPoint} (hp : p ∈ mpcWordSet (j + 1))
    (hmarked : MpcMkMarkedHead p) (u : MpcMkCostDomain j)
    (hu : mpcMkCost j (by omega) p.2.1 p.2.2.2 u = mpcMkDefectTop j p hp) :
    (((mpcMkKillLiftResidual (by omega) hp u hu * mpcMkAdvanceHallTop hp u :
          zLayer (DM 2 0 : Type) (j + 2)) :
        levelQuot (DM 2 0 : Type) (j + 3))) ∈
      mpcMkFiveCarrierKernel (j + 2) := by
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · change _ ∈ derivKer (mpcMkCoordinateDeriv (j + 2 + 1) (by omega) 0) (j + 2)
    convert mpcMkSecondary_mem_coordinateDerivKer hj hp u hu 0 using 1
  · change _ ∈ derivKer (mpcMkCoordinateDeriv (j + 2 + 1) (by omega) 2) (j + 2)
    convert mpcMkSecondary_mem_coordinateDerivKer hj hp u hu 2 using 1
  · change _ ∈ derivKer (mpcMkCoordinateDeriv (j + 2 + 1) (by omega) 3) (j + 2)
    convert mpcMkSecondary_mem_coordinateDerivKer hj hp u hu 3 using 1
  · exact mpcMkSecondary_mem_nuKernel hj hp
      (mpcMk_markedHead_nuNeutral hmarked) u hu
  · exact mpcMkSecondary_mem_deltaDKernel hj hp hmarked u hu

/-! ## 5. Axiom pins

Every public declaration in this module is on the standard three
(`propext`, `Classical.choice`, `Quot.sound`). This module introduces no axiom.
-/

#print axioms mpcMkDeltaD
#print axioms mpcMkDeltaD_dmA
#print axioms mpcMkDeltaD_dmB
#print axioms mpcMkDeltaD_dmC
#print axioms mpcMkDeltaD_dmD
#print axioms mpcSx_marked_deltaD
#print axioms mpcMkDeltaDMod
#print axioms mpcMkDeltaDLevel
#print axioms mpcMkDeltaDLevel_levelMk
#print axioms mpcMkDeltaDKernel
#print axioms MpcMkMarkedHead
#print axioms mpcMk_markedHead_w4
#print axioms mpcMk_markedHead_advance
#print axioms mpcMk_markedHead_nuNeutral
#print axioms mpcMk_defect_deltaD_eq_one
#print axioms mpcMkCost_mem_deltaDKernel
#print axioms mpcMkFiveCarrierKernel
#print axioms mpcMk_exists_unrestrictedCost_of_fiveCarrierKernel
#print axioms mpcMkSecondary_mem_deltaDKernel
#print axioms mpcMkSecondary_mem_fiveCarrierKernel

end

end GQ2.Dyadic.Instances.MpcMk
