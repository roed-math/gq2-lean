/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.MpcGeneralDerivationBridge
import GQ2.Dyadic.Instances.StageAbstractionDeepCorrections
import GQ2.Dyadic.Instances.StageAbstractionEvenStageClimb

/-!
# Finite shadows of the general Mpc correction constraints

The unrestricted relator fiber is nonempty at every `alpha`, handle count, and stage.  This
module identifies the exact finite conditions cutting out the admissible part of that fiber.
Away from the distinguished `C` coordinate, exact `chiM`-neutrality is equivalent to the
vanishing of the depth-`(alpha-1)` character shadow.  At `C`, the same shadow is necessary,
and the only additional condition is membership in the exact abelian-neutral image.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralConstraintShadow

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.EvenRowSupply
open GQ2.Dyadic.Instances.MpcGeneralFiniteStages
open GQ2.Dyadic.Instances.MpcGeneralFiniteSpan
open GQ2.Dyadic.Instances.MpcGeneralDerivationBridge
open GQ2.Roe.Labute

/-- The canonical `M` character satisfies the deep-shadow well-definedness bound. -/
theorem mpcGeneralDeepChi_bound {alpha h n : ℕ} (halpha : 2 ≤ alpha) (hn : 2 ≤ n) :
    (twoCentralSeries (DM alpha h : Type) n).map (chiM alpha h).toMonoidHom ≤
      (Units.map (PadicInt.toZModPow (n + (alpha - 1))).toMonoidHom).ker := by
  apply evenSharp_map_le_deep (by omega)
  · intro g
    apply evenSharp_pmOne_of_mem_imChiM (by omega)
    rw [← range_chiM alpha h]
    exact ⟨g, rfl⟩
  · exact hn

/-- The finite depth-`(alpha-1)` character shadow on the level-`n` quotient. -/
noncomputable def mpcGeneralDeepChi {alpha h n : ℕ} (halpha : 2 ≤ alpha) (hn : 2 ≤ n) :
    levelQuot (DM alpha h) n →* (ZMod (2 ^ (n + (alpha - 1))))ˣ :=
  evenSharpDeepChiLevel (chiM alpha h) n (alpha - 1)
    (mpcGeneralDeepChi_bound halpha hn)

@[simp] theorem mpcGeneralDeepChi_levelMk {alpha h n : ℕ} (halpha : 2 ≤ alpha)
    (hn : 2 ≤ n) (g : DM alpha h) :
    mpcGeneralDeepChi halpha hn (levelMk (DM alpha h) n g) =
      Units.map (PadicInt.toZModPow (n + (alpha - 1))).toMonoidHom (chiM alpha h g) :=
  rfl

/-- Any representative of a depth-`j` finite class remains at depth `j`, provided `j ≤ n`. -/
theorem rep_mem_twoCentralSeries_of_mem_lambdaImage {alpha h j n : ℕ} (hjn : j ≤ n)
    {q : levelQuot (DM alpha h) n} (hq : q ∈ lambdaImage (DM alpha h) j n)
    {g : DM alpha h} (hg : q = levelMk (DM alpha h) n g) :
    g ∈ twoCentralSeries (DM alpha h : Type) j := by
  obtain ⟨w, hw, hwq⟩ := hq
  have hker : g * w⁻¹ ∈ twoCentralSeries (DM alpha h : Type) n := by
    have hone : levelMk (DM alpha h) n (g * w⁻¹) = 1 := by
      rw [map_mul, map_inv, ← hg, hwq, mul_inv_cancel]
    rwa [levelMk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hone
  have hle : twoCentralSeries (DM alpha h : Type) n ≤
      twoCentralSeries (DM alpha h : Type) j :=
    twoCentralSeries_antitone (G := (DM alpha h : Type)) hjn
  have hmem := Subgroup.mul_mem _ (hle hker) hw
  simpa using hmem

/-- Away from `C`, the exact neutral image is precisely the deep-shadow kernel inside the
required tower layer. -/
theorem mem_mpcGeneralCorrectionImage_iff_deepChi
    {alpha h j n : ℕ} (halpha : 2 ≤ alpha) (hn : 2 ≤ n) (hjn : j ≤ n)
    {i : Fin (coreRank h)} (hi : i ≠ 2) (q : levelQuot (DM alpha h) n) :
    q ∈ mpcGeneralCorrectionImage alpha h j n i ↔
      q ∈ lambdaImage (DM alpha h) j n ∧ mpcGeneralDeepChi halpha hn q = 1 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [mpcGeneralCorrectionSource, if_neg hi] at hg
    refine ⟨⟨g, hg.1, rfl⟩, ?_⟩
    have hchi : chiM alpha h g = 1 := MonoidHom.mem_ker.mp hg.2
    rw [mpcGeneralDeepChi_levelMk, hchi, map_one]
  · rintro ⟨hqdepth, hqchi⟩
    have Hlift : EvenRowDeepFibreLiftSupply (alpha - 1) (vM alpha (h := h))
        (DM alpha h : Type) (chiM alpha h) :=
      GQ2.Dyadic.StageGeneric.evenClimb_deepRowSupply_m halpha (range_chiM alpha h)
    obtain ⟨g, hgchi, hgq⟩ := evenRow_deepSupply_lift_quot Hlift n hn
      (mpcGeneralDeepChi_bound halpha hn) (0 : Fin (coreRank h)) q (by
        change mpcGeneralDeepChi halpha hn q =
          Units.map (PadicInt.toZModPow (n + (alpha - 1))).toMonoidHom (vM alpha 0)
        simpa only [vM_zero, map_one] using hqchi)
    refine ⟨g, ?_, hgq.symm⟩
    rw [mpcGeneralCorrectionSource, if_neg hi]
    refine ⟨rep_mem_twoCentralSeries_of_mem_lambdaImage hjn hqdepth hgq, ?_⟩
    apply MonoidHom.mem_ker.mpr
    exact hgchi

/-- The forgetful finite map has exactly the coordinatewise exact-image range. -/
theorem mem_mpcGeneralLevelToRaw_range_iff {alpha h k : ℕ}
    (V : EvenRawDepthCorrection (DM alpha h) h k) :
    V ∈ (mpcGeneralLevelToRawHom alpha h k).range ↔
      ∀ i, V.correction i ∈
        mpcGeneralCorrectionImage alpha h (k - 1) (k + 1) i := by
  constructor
  · rintro ⟨E, rfl⟩ i
    exact (E i).2
  · intro H
    let E : MpcGeneralLevelCorrection alpha h k :=
      fun i => ⟨V.correction i, H i⟩
    refine ⟨E, ?_⟩
    apply EvenRawDepthCorrection.ext
    rfl

/-- Exact finite description of the admissible part of the raw correction space.  All
ordinary coordinates are cut out by the deep character shadow; `C` retains exactly one
additional abelian-neutral image condition. -/
theorem mem_mpcGeneralLevelToRaw_range_iff_shadows_and_C
    {alpha h k : ℕ} (halpha : 2 ≤ alpha) (hk : 3 ≤ k)
    (V : EvenRawDepthCorrection (DM alpha h) h k) :
    V ∈ (mpcGeneralLevelToRawHom alpha h k).range ↔
      (∀ i, i ≠ 2 → mpcGeneralDeepChi halpha (by omega : 2 ≤ k + 1)
        (V.correction i) = 1) ∧
      V.correction 2 ∈ mpcGeneralCorrectionImage alpha h (k - 1) (k + 1) 2 := by
  rw [mem_mpcGeneralLevelToRaw_range_iff]
  constructor
  · intro H
    refine ⟨fun i hi =>
      ((mem_mpcGeneralCorrectionImage_iff_deepChi halpha (by omega) (by omega) hi
        (V.correction i)).mp (H i)).2, H 2⟩
  · rintro ⟨Hshadow, HC⟩ i
    by_cases hi : i = 2
    · simpa only [hi] using HC
    · exact (mem_mpcGeneralCorrectionImage_iff_deepChi halpha (by omega) (by omega) hi
        (V.correction i)).mpr ⟨V.depth i, Hshadow i hi⟩

/-- Final uniform fiber statement: the campaign is reduced to finding, in the already
nonempty raw affine fiber, one point satisfying the finite shadows and the exact `C` image. -/
theorem mpcGeneral_target_mem_constrainedRange_iff_fiber_shadows_and_C
    {alpha h k : ℕ} (halpha : 2 ≤ alpha)
    (m : Fin (coreRank h) → (DM alpha h : Type))
    (hm : m ∈ mpcGeneralStage alpha h k) (hk : 3 ≤ k) :
    mpcGeneralLevelTarget hm ∈ (mpcGeneralLevelShiftHom m k hk).range ↔
      ∃ V ∈ mpcGeneralRawFiber m hm hk,
        (∀ i, i ≠ 2 → mpcGeneralDeepChi halpha (by omega : 2 ≤ k + 1)
          (V.correction i) = 1) ∧
        V.correction 2 ∈ mpcGeneralCorrectionImage alpha h (k - 1) (k + 1) 2 := by
  rw [mpcGeneral_target_mem_constrainedRange_iff_fiber_meets]
  constructor
  · rintro ⟨V, hV, hVr⟩
    exact ⟨V, hV, (mem_mpcGeneralLevelToRaw_range_iff_shadows_and_C halpha hk V).mp hVr⟩
  · rintro ⟨V, hV, hVc⟩
    exact ⟨V, hV, (mem_mpcGeneralLevelToRaw_range_iff_shadows_and_C halpha hk V).mpr hVc⟩

end

end GQ2.Dyadic.Instances.MpcGeneralConstraintShadow

section AxiomPins

open GQ2.Dyadic.Instances.MpcGeneralConstraintShadow

#print axioms mpcGeneralDeepChi_bound
#print axioms mpcGeneralDeepChi
#print axioms mpcGeneralDeepChi_levelMk
#print axioms rep_mem_twoCentralSeries_of_mem_lambdaImage
#print axioms mem_mpcGeneralCorrectionImage_iff_deepChi
#print axioms mem_mpcGeneralLevelToRaw_range_iff
#print axioms mem_mpcGeneralLevelToRaw_range_iff_shadows_and_C
#print axioms mpcGeneral_target_mem_constrainedRange_iff_fiber_shadows_and_C

end AxiomPins
