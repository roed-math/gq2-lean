/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3UniversalRelationLift

/-!
# Eventual Fox generation for the improved square presentation

For a fixed finite quotient `DSq h / U`, the subgroup `modTwoFoxRangeKernel` is exactly the
kernel of the information relevant to eventual relation generation: evaluation in the quotient,
together with the universal mod-two Fox derivative modulo the improved relator row.  Its quotient
is finite and a two-group.  The defining universal property of `DSq h` therefore maps onto this
finite detector quotient.  Intersecting the kernel with `U` gives a fine enough open normal
subgroup at which every relation word is invisible to the detector, which is precisely the
required Fox-range condition.

This proves `SqEventualRelationFoxGeneration` directly from the defining pro-two presentation.
It deliberately bypasses the strictly stronger word-level normal-closure approximation.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh GQ2.FoxH
open GQ2.Dyadic.SqCore

/-- The normal subgroup of free words invisible to the finite quotient and to its improved
relator Fox row. -/
private abbrev sqFoxDetectorKernel (h : ℕ)
    (U : OpenNormalSubgroup (DSq h : Type)) :
    Subgroup (FreeGroup (Fin (sqRank h))) :=
  modTwoFoxRangeKernel (sqOpenQuotientMarking h U)
    (fun _ : Unit ↦ sqDiscreteRelator h)

/-- The finite quotient detecting failure of the target Fox-generation condition. -/
private abbrev SqFoxDetector (h : ℕ)
    (U : OpenNormalSubgroup (DSq h : Type)) :=
  FreeGroup (Fin (sqRank h)) ⧸ sqFoxDetectorKernel h U

/-- The universal Fox lift at a fixed open quotient. -/
private def sqUniversalFoxLiftAt (h : ℕ)
    (U : OpenNormalSubgroup (DSq h : Type)) :
    FreeGroup (Fin (sqRank h)) →*
      WordLift
        (RegularModTwoRelationModule
          ((DSq h : Type) ⧸ U.toSubgroup) (Fin (sqRank h)))
        ((DSq h : Type) ⧸ U.toSubgroup) :=
  FreeGroup.lift <| foxLift (sqOpenQuotientMarking h U)
    (modTwoFoxGenerator
      (L := (DSq h : Type) ⧸ U.toSubgroup))

/-- The kernel of the universal Fox lift is contained in the detector kernel. -/
private theorem sqUniversalFoxLiftAt_ker_le_detector (h : ℕ)
    (U : OpenNormalSubgroup (DSq h : Type)) :
    (sqUniversalFoxLiftAt h U).ker ≤ sqFoxDetectorKernel h U := by
  intro f hf
  have hfox : modTwoFoxDerivative (sqOpenQuotientMarking h U) f = 0 := by
    change (sqUniversalFoxLiftAt h U f).u = 0
    rw [MonoidHom.mem_ker.mp hf]
    rfl
  constructor
  · change FreeGroup.lift (sqOpenQuotientMarking h U) f = 1
    rw [← lift_foxLift_g (sqOpenQuotientMarking h U)
      (modTwoFoxGenerator
        (L := (DSq h : Type) ⧸ U.toSubgroup)) f]
    change (sqUniversalFoxLiftAt h U f).g = 1
    rw [MonoidHom.mem_ker.mp hf]
    rfl
  · rw [hfox]
    exact Submodule.zero_mem _

/-- The universal Fox lift has finite target at every open quotient. -/
private theorem sqFoxDetector_finite (h : ℕ)
    (U : OpenNormalSubgroup (DSq h : Type)) : Finite (SqFoxDetector h U) := by
  classical
  letI : Finite ((DSq h : Type) ⧸ U.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen'
  letI : Fintype ((DSq h : Type) ⧸ U.toSubgroup) := Fintype.ofFinite _
  letI : Fintype
      (RegularModTwoRelationModule
        ((DSq h : Type) ⧸ U.toSubgroup) (Fin (sqRank h))) :=
    Finsupp.fintype
  letI : (sqUniversalFoxLiftAt h U).ker.FiniteIndex :=
    Subgroup.finiteIndex_ker (sqUniversalFoxLiftAt h U)
  letI : (sqFoxDetectorKernel h U).FiniteIndex :=
    Subgroup.finiteIndex_of_le (sqUniversalFoxLiftAt_ker_le_detector h U)
  exact Subgroup.finite_quotient_of_finiteIndex

/-- A universal Fox lift of a finite two-group remains a two-group: its exponent can at most
double because the coefficient module is elementary abelian. -/
private theorem sqUniversalFoxLiftTarget_isPGroup (h : ℕ)
    (U : OpenNormalSubgroup (DSq h : Type)) :
    IsPGroup 2
      (WordLift
        (RegularModTwoRelationModule
          ((DSq h : Type) ⧸ U.toSubgroup) (Fin (sqRank h)))
        ((DSq h : Type) ⧸ U.toSubgroup)) := by
  intro p
  obtain ⟨k, hk⟩ := (isProP_DSq h U) p.g
  refine ⟨k + 1, orderOf_dvd_iff_pow_eq_one.mp ?_⟩
  calc
    orderOf p ∣ 2 * orderOf p.g :=
      WordLift.orderOf_dvd_two_mul_orderOf_base
        (fun a ↦ regularModTwoRelationModule_add_self
          ((DSq h : Type) ⧸ U.toSubgroup) (Fin (sqRank h)) a) p
    _ ∣ 2 * 2 ^ k := Nat.mul_dvd_mul_left 2 (orderOf_dvd_of_pow_eq_one hk)
    _ = 2 ^ (k + 1) := by rw [pow_succ']

/-- The detector quotient is a finite two-group. -/
private theorem sqFoxDetector_isPGroup (h : ℕ)
    (U : OpenNormalSubgroup (DSq h : Type)) : IsPGroup 2 (SqFoxDetector h U) := by
  let Φ := sqUniversalFoxLiftAt h U
  intro x
  obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective (sqFoxDetectorKernel h U) x
  obtain ⟨k, hk⟩ := sqUniversalFoxLiftTarget_isPGroup h U (Φ f)
  refine ⟨k, ?_⟩
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff (f ^ 2 ^ k)).mpr
    (sqUniversalFoxLiftAt_ker_le_detector h U <| MonoidHom.mem_ker.mpr <| by
      rw [map_pow, hk])

/-- The detector marking is the image of the free generators. -/
private def sqFoxDetectorMarking (h : ℕ)
    (U : OpenNormalSubgroup (DSq h : Type)) :
    Fin (sqRank h) → SqFoxDetector h U :=
  fun i ↦ QuotientGroup.mk' (sqFoxDetectorKernel h U) (FreeGroup.of i)

private theorem sqFoxDetector_lift (h : ℕ)
    (U : OpenNormalSubgroup (DSq h : Type)) (f : FreeGroup (Fin (sqRank h))) :
    FreeGroup.lift (sqFoxDetectorMarking h U) f =
      QuotientGroup.mk' (sqFoxDetectorKernel h U) f := by
  apply congrArg (fun φ : FreeGroup (Fin (sqRank h)) →* SqFoxDetector h U ↦ φ f)
  apply FreeGroup.ext_hom
  intro i
  simp [sqFoxDetectorMarking]

/-- The improved square relator lies in the detector kernel. -/
private theorem sqDiscreteRelator_mem_sqFoxDetectorKernel (h : ℕ)
    (U : OpenNormalSubgroup (DSq h : Type)) :
    sqDiscreteRelator h ∈ sqFoxDetectorKernel h U := by
  constructor
  · exact sqOpenQuotientMarking_sqDiscreteRelator h U
  · exact modTwoFoxDerivative_mem_range_of_mem_normalClosure
      (sqOpenQuotientMarking h U)
      (fun _ : Unit ↦ sqDiscreteRelator h)
      (fun _ ↦ sqOpenQuotientMarking_sqDiscreteRelator h U)
      (Subgroup.subset_normalClosure ⟨(), rfl⟩)

/-- The detector marking kills the defining improved square relator. -/
private theorem sqFoxDetectorMarking_relation (h : ℕ)
    (U : OpenNormalSubgroup (DSq h : Type)) :
    sqRelWord (sqFoxDetectorMarking h U) = 1 := by
  rw [← FreeGroup.lift_sqDiscreteRelator]
  rw [sqFoxDetector_lift]
  exact (QuotientGroup.eq_one_iff (sqDiscreteRelator h)).mpr
    (sqDiscreteRelator_mem_sqFoxDetectorKernel h U)

/-- **Eventual relation Fox generation for the improved square presentation.**  This is an
unconditional consequence of the defining pro-two quotient: the minimal finite Fox detector is
itself a finite two-group and hence receives the universal presentation map. -/
theorem sqEventualRelationFoxGeneration (h : ℕ) :
    SqEventualRelationFoxGeneration h := by
  intro U
  letI : Finite (SqFoxDetector h U) := sqFoxDetector_finite h U
  letI : TopologicalSpace (SqFoxDetector h U) := ⊥
  letI : DiscreteTopology (SqFoxDetector h U) := ⟨rfl⟩
  let F : ContinuousMonoidHom (DSq h : Type) (SqFoxDetector h U) :=
    sqLiftHom h (isProP_of_isPGroup (sqFoxDetector_isPGroup h U))
      (sqFoxDetectorMarking h U) (sqFoxDetectorMarking_relation h U)
  let W₀ : OpenNormalSubgroup (DSq h : Type) := {
    toSubgroup := F.toMonoidHom.ker
    isOpen' := by
      change IsOpen (F ⁻¹' {1})
      exact (isOpen_discrete ({1} : Set (SqFoxDetector h U))).preimage
        F.continuous_toFun
  }
  let W : OpenNormalSubgroup (DSq h : Type) := W₀ ⊓ U
  refine ⟨W, inf_le_right, fun r ↦ ?_⟩
  have hwordW : FreeGroup.lift (sqGen h) r.1 ∈ W.toSubgroup := by
    rw [← QuotientGroup.eq_one_iff]
    calc
      QuotientGroup.mk' W.toSubgroup (FreeGroup.lift (sqGen h) r.1) =
          FreeGroup.lift (sqOpenQuotientMarking h W) r.1 :=
        map_freeGroup_lift (QuotientGroup.mk' W.toSubgroup) (sqGen h) r.1
      _ = 1 := r.2
  have hwordW₀ : FreeGroup.lift (sqGen h) r.1 ∈ W₀.toSubgroup :=
    (show W ≤ W₀ from inf_le_left) hwordW
  have hFword : F (FreeGroup.lift (sqGen h) r.1) = 1 :=
    MonoidHom.mem_ker.mp hwordW₀
  have hdetector : QuotientGroup.mk' (sqFoxDetectorKernel h U) r.1 = 1 := by
    calc
      QuotientGroup.mk' (sqFoxDetectorKernel h U) r.1 =
          FreeGroup.lift (sqFoxDetectorMarking h U) r.1 :=
        (sqFoxDetector_lift h U r.1).symm
      _ = F (FreeGroup.lift (sqGen h) r.1) := by
        calc
          FreeGroup.lift (sqFoxDetectorMarking h U) r.1 =
              FreeGroup.lift (fun i ↦ F (sqGen h i)) r.1 := by
            apply congrArg
              (fun φ : FreeGroup (Fin (sqRank h)) →* SqFoxDetector h U ↦ φ r.1)
            apply FreeGroup.ext_hom
            intro i
            simp only [FreeGroup.lift_apply_of]
            exact (sqLiftHom_gen h
              (isProP_of_isPGroup (sqFoxDetector_isPGroup h U))
              (sqFoxDetectorMarking h U) (sqFoxDetectorMarking_relation h U) i).symm
          _ = F (FreeGroup.lift (sqGen h) r.1) :=
            (map_freeGroup_lift F.toMonoidHom (sqGen h) r.1).symm
      _ = 1 := hFword
  exact (QuotientGroup.eq_one_iff r.1).mp hdetector

end

end GQ2.Dyadic.Count
