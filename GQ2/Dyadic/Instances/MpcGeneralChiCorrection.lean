/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.MpcGeneralConstraintShadow
import GQ2.Dyadic.Instances.EvenResidual

/-!
# Uniform exact-character correction for the general Mpc stages

The all-degree even climb produces exact row-fibre representatives at every stage.  This
module transports them from the canonical quotient lifts to the actual general-stage
marking.  The result is a simultaneous depth correction with exact trivial `chiM` value in
every coordinate.  It is uniform in `alpha`, the handle count, and the stage.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralChiCorrection

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.EvenResidual
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.Instances.MpcGeneralFiniteStages
open GQ2.Dyadic.Instances.MpcGeneralFiniteSpan
open GQ2.Dyadic.Instances.MpcGeneralDerivationBridge
open GQ2.Dyadic.Instances.MpcGeneralConstraintShadow
open GQ2.Roe.Labute

/-- A simultaneous stage correction with exact trivial `chiM` rows.  This is the general
correction interface before imposing the additional additive-neutral condition at `C`. -/
structure MpcGeneralChiStageCorrection {alpha h : ℕ}
    (m : Fin (coreRank h) → (DM alpha h : Type)) (k : ℕ) where
  factors : Fin (coreRank h) → (DM alpha h : Type)
  depth : ∀ i, factors i ∈ twoCentralSeries (DM alpha h : Type) (k - 1)
  chi : ∀ i, chiM alpha h (factors i) = 1
  nextRel : mRelWord alpha (mpcGeneralModify m factors) ∈
    twoCentralSeries (DM alpha h : Type) (k + 1)

/-- The finite image of exact depth and exact `chiM` neutrality, without the distinguished
additive-row constraint. -/
def mpcGeneralChiCorrectionImage (alpha h j n : ℕ) :
    Subgroup (levelQuot (DM alpha h) n) :=
  (twoCentralSeries (DM alpha h : Type) j ⊓ mpcGeneralChiKer alpha h).map
    (levelMk (DM alpha h) n)

/-- Every general Mpc stage has an actual-defect correction with exact row fibres. -/
theorem mpcGeneralTuple_defectReachable {alpha h k : ℕ} (halpha : 2 ≤ alpha)
    (m : Fin (coreRank h) → (DM alpha h : Type))
    (hm : m ∈ mpcGeneralStage alpha h k) (hk : 3 ≤ k) :
    Tuple.DefectReachable (mpcGeneralTuple halpha m hm hk) := by
  apply evenClimb_defectReachable hk
  · exact evenResidual_residualSupply_of_rawDefect_M halpha (by omega)
      (range_chiM alpha h) (mpcModelRawDefectSupply halpha)
  · exact evenSharpDbarShiftSupply_m halpha (by omega) hk
  · exact evenClimb_deepRowSupply_m halpha (range_chiM alpha h)

/-- Exact row-fibre reachability supplies a simultaneous exact-character correction of the
actual marking. -/
theorem exists_mpcGeneralChiStageCorrection {alpha h k : ℕ} (halpha : 2 ≤ alpha)
    (m : Fin (coreRank h) → (DM alpha h : Type))
    (hm : m ∈ mpcGeneralStage alpha h k) (hk : 3 ≤ k) :
    Nonempty (MpcGeneralChiStageCorrection m k) := by
  let T := mpcGeneralTuple halpha m hm hk
  let Wc := (mpcGeneralTuple_defectReachable halpha m hm hk).defectKillingCorrection T
  have hrow : ∀ i, ∃ x : DM alpha h,
      chiM alpha h x = vM alpha i ∧
      stageModified (fun i => canonLift (DM alpha h) k (T.generators i))
          Wc.correction i = levelMk (DM alpha h) (k + 1) x :=
    Wc.rows
  choose x hxchi hxmod using hrow
  have hbaseProj : ∀ i,
      levelProj (DM alpha h) k
          (canonLift (DM alpha h) k (T.generators i)) =
        levelProj (DM alpha h) k (levelMk (DM alpha h) (k + 1) (m i)) := by
    intro i
    simp only [levelProj_canonLift, levelProj_levelMk, T, mpcGeneralTuple_generators]
  choose z hz hcanon using fun i =>
    exists_zLayer_mul (G := DM alpha h) (hbaseProj i)
  let e : Fin (coreRank h) → (DM alpha h : Type) := fun i => (m i)⁻¹ * x i
  have helevel : ∀ i, levelMk (DM alpha h) (k + 1) (e i) = Wc.correction i * z i := by
    intro i
    simp only [e, map_mul, map_inv]
    rw [← hxmod i]
    simp only [stageModified, hcanon i]
    have hcomm := (zLayer_commute (hz i)
      (levelMk (DM alpha h) (k + 1) (m i))).eq
    calc
      (levelMk (DM alpha h) (k + 1) (m i))⁻¹ *
          (z i * levelMk (DM alpha h) (k + 1) (m i) * Wc.correction i) =
          (levelMk (DM alpha h) (k + 1) (m i))⁻¹ *
            (levelMk (DM alpha h) (k + 1) (m i) * z i * Wc.correction i) := by
              rw [hcomm]
      _ = Wc.correction i * z i := by
        calc
          (levelMk (DM alpha h) (k + 1) (m i))⁻¹ *
                (levelMk (DM alpha h) (k + 1) (m i) * z i * Wc.correction i) =
              (levelMk (DM alpha h) (k + 1) (m i))⁻¹ *
                (levelMk (DM alpha h) (k + 1) (m i) *
                  (z i * Wc.correction i)) := by
                    congr 1
                    exact mul_assoc _ _ _
          _ =
              z i * Wc.correction i := by
                rw [← mul_assoc
                  (levelMk (DM alpha h) (k + 1) (m i))⁻¹
                  (levelMk (DM alpha h) (k + 1) (m i))
                  (z i * Wc.correction i),
                  inv_mul_cancel, one_mul]
          _ = Wc.correction i * z i := (zLayer_commute (hz i) _).eq
  have hedepth : ∀ i, e i ∈ twoCentralSeries (DM alpha h : Type) (k - 1) := by
    intro i
    exact rep_mem_twoCentralSeries_of_mem_lambdaImage
      (j := k - 1) (n := k + 1) (by omega)
      (Subgroup.mul_mem _ (Wc.depth i) (lambdaImage_le_of_le (by omega) (hz i)))
      (helevel i).symm
  have hechi : ∀ i, chiM alpha h (e i) = 1 := by
    intro i
    simp only [e, map_mul, map_inv, hxchi]
    have hmi : chiM alpha h (m i) = vM alpha i :=
      (hm.2.1 i).trans (chiM_dmGen alpha h i)
    rw [hmi, inv_mul_cancel]
  have hmodified : mpcGeneralModify m e = x := by
    funext i
    simp only [mpcGeneralModify, e]
    group
  have hnext : mRelWord alpha x ∈ twoCentralSeries (DM alpha h : Type) (k + 1) := by
    apply (GQ2.Dyadic.SqCore.lim_mem_twoCentralSeries_iff_levelMk (k + 1) _).mpr
    rw [map_mRelWord]
    let Tnext := Wc.toNext T hk (dm_topologicallyFinGen alpha h) (isProP_DM alpha h)
    have hgens : Tnext.generators =
        fun i => levelMk (DM alpha h) (k + 1) (x i) := by
      funext i
      exact hxmod i
    rw [← hgens]
    exact Tnext.relation
  exact ⟨{
    factors := e
    depth := hedepth
    chi := hechi
    nextRel := by rw [hmodified]; exact hnext }⟩

/-- Uniformly, the raw affine defect fibre contains a point represented by exact
`chiM`-neutral elements in every coordinate. -/
theorem mpcGeneralRawFiber_exists_exactChi {alpha h k : ℕ} (halpha : 2 ≤ alpha)
    (m : Fin (coreRank h) → (DM alpha h : Type))
    (hm : m ∈ mpcGeneralStage alpha h k) (hk : 3 ≤ k) :
    ∃ V ∈ mpcGeneralRawFiber m hm hk,
      ∀ i, V.correction i ∈
        mpcGeneralChiCorrectionImage alpha h (k - 1) (k + 1) := by
  obtain ⟨E⟩ := exists_mpcGeneralChiStageCorrection halpha m hm hk
  let V : EvenRawDepthCorrection (DM alpha h) h k :=
    { correction := fun i => levelMk (DM alpha h) (k + 1) (E.factors i)
      depth := fun i => ⟨E.factors i, E.depth i, rfl⟩ }
  refine ⟨V, ?_, ?_⟩
  · apply Subtype.ext
    change evenRawDbarWord
        (fun i => levelMk (DM alpha h) (k + 1) (m i)) V.correction =
      (mpcGeneralLevelTarget hm).1
    rw [← evenRawStageShift_m (G := DM alpha h) halpha (by omega) h k hk _ _ V.depth]
    change stageShift (mStageWord alpha h (by omega))
        (fun i => levelMk (DM alpha h) (k + 1) (m i))
        (fun i => levelMk (DM alpha h) (k + 1) (E.factors i)) = _
    rw [mpcGeneralStageShift_eq (by omega)]
    have hnext : levelMk (DM alpha h) (k + 1)
        (mRelWord alpha (mpcGeneralModify m E.factors)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr E.nextRel
    change (levelMk (DM alpha h) (k + 1) (mRelWord alpha m))⁻¹ *
        levelMk (DM alpha h) (k + 1)
          (mRelWord alpha (mpcGeneralModify m E.factors)) =
      (levelMk (DM alpha h) (k + 1) (mRelWord alpha m))⁻¹
    rw [hnext, mul_one]
  · intro i
    exact ⟨E.factors i, ⟨E.depth i, MonoidHom.mem_ker.mpr (E.chi i)⟩, rfl⟩

end

end GQ2.Dyadic.Instances.MpcGeneralChiCorrection

section AxiomPins

open GQ2.Dyadic.Instances.MpcGeneralChiCorrection

#print axioms MpcGeneralChiStageCorrection
#print axioms mpcGeneralChiCorrectionImage
#print axioms mpcGeneralTuple_defectReachable
#print axioms exists_mpcGeneralChiStageCorrection
#print axioms mpcGeneralRawFiber_exists_exactChi

end AxiomPins
