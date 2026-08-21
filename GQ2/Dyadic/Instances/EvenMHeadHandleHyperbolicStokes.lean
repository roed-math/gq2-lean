import GQ2.Dyadic.Instances.EvenMHeadHandleHyperbolicFox
import GQ2.Dyadic.Instances.EvenMRamifiedPairing

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.FoxH
open Count Certificates Words Certificates.MProcyclic
open Instances.GammaRPWordNielsen
open Instances.GammaRPWordNielsenElementary
open Instances.EvenMHeadHandleSource
open Instances.EvenMHeadHandlePairSource
open Instances.EvenMHeadHandlePairCore
open Instances.EvenMHeadHandleMixed
open Instances.EvenMHeadHandleHyperbolic
open Instances.EvenMHeadHandlePairNormalize

namespace Instances.EvenMHeadHandleHyperbolicStokes

private theorem resolved_trans_backward_forward
    {n : ℕ} (T U : PWordNielsenPair n)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hT : ∀ g, FreeGroup.lift
      (fun i ↦ heisToFree E E₂ (T.backward i))
      (heisToFree E E₂ (T.forward g)) = FreeGroup.of g)
    (hU : ∀ g, FreeGroup.lift
      (fun i ↦ heisToFree E E₂ (U.backward i))
      (heisToFree E E₂ (U.forward g)) = FreeGroup.of g)
    (g : Generator n) :
    FreeGroup.lift
      (fun i ↦ heisToFree E E₂ ((PWordNielsenPair.trans T U).backward i))
      (heisToFree E E₂ ((PWordNielsenPair.trans T U).forward g)) =
        FreeGroup.of g := by
  simp only [PWordNielsenPair.trans]
  simp_rw [heisToFree_subst]
  simp_rw [← lift_lift_freeSubst]
  have hUhom : (FreeGroup.lift (fun i ↦ heisToFree E E₂ (U.backward i))).comp
      (FreeGroup.lift (fun i ↦ heisToFree E E₂ (U.forward i))) =
      MonoidHom.id (FreeGroup (Generator n)) := by
    apply FreeGroup.ext_hom
    intro i
    simpa using hU i
  change (FreeGroup.lift (fun i ↦ heisToFree E E₂ (T.backward i)))
    (((FreeGroup.lift (fun i ↦ heisToFree E E₂ (U.backward i))).comp
      (FreeGroup.lift (fun i ↦ heisToFree E E₂ (U.forward i))))
        (heisToFree E E₂ (T.forward g))) = _
  rw [hUhom]
  exact hT g

private theorem resolved_trans_forward_backward
    {n : ℕ} (T U : PWordNielsenPair n)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hT : ∀ g, FreeGroup.lift
      (fun i ↦ heisToFree E E₂ (T.forward i))
      (heisToFree E E₂ (T.backward g)) = FreeGroup.of g)
    (hU : ∀ g, FreeGroup.lift
      (fun i ↦ heisToFree E E₂ (U.forward i))
      (heisToFree E E₂ (U.backward g)) = FreeGroup.of g)
    (g : Generator n) :
    FreeGroup.lift
      (fun i ↦ heisToFree E E₂ ((PWordNielsenPair.trans T U).forward i))
      (heisToFree E E₂ ((PWordNielsenPair.trans T U).backward g)) =
        FreeGroup.of g := by
  simp only [PWordNielsenPair.trans]
  simp_rw [heisToFree_subst]
  simp_rw [← lift_lift_freeSubst]
  have hThom : (FreeGroup.lift (fun i ↦ heisToFree E E₂ (T.forward i))).comp
      (FreeGroup.lift (fun i ↦ heisToFree E E₂ (T.backward i))) =
      MonoidHom.id (FreeGroup (Generator n)) := by
    apply FreeGroup.ext_hom
    intro i
    simpa using hT i
  change (FreeGroup.lift (fun i ↦ heisToFree E E₂ (U.forward i)))
    (((FreeGroup.lift (fun i ↦ heisToFree E E₂ (T.forward i))).comp
      (FreeGroup.lift (fun i ↦ heisToFree E E₂ (T.backward i))))
        (heisToFree E E₂ (U.backward g))) = _
  rw [hThom]
  exact hU g

private theorem pair_resolved_backward_forward
    {h : ℕ} (j : Fin h) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (g : Generator (2 + 2 * h)) :
    FreeGroup.lift
      (fun i ↦ heisToFree E E₂ ((headHandlePairNielsen j).backward i))
      (heisToFree E E₂ ((headHandlePairNielsen j).forward g)) =
        FreeGroup.of g := by
  simp [headHandlePairNielsen, PWordNielsenPair.ofEquiv, heisToFree]

private theorem pair_resolved_forward_backward
    {h : ℕ} (j : Fin h) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (g : Generator (2 + 2 * h)) :
    FreeGroup.lift
      (fun i ↦ heisToFree E E₂ ((headHandlePairNielsen j).forward i))
      (heisToFree E E₂ ((headHandlePairNielsen j).backward g)) =
        FreeGroup.of g := by
  simp [headHandlePairNielsen, PWordNielsenPair.ofEquiv, heisToFree]

private theorem rightMul_resolved_backward_forward
    {n : ℕ} (a b : Generator n) (hab : a ≠ b)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (g : Generator n) :
    FreeGroup.lift
      (fun i ↦ heisToFree E E₂ ((rightMulNielsen a b hab).backward i))
      (heisToFree E E₂ ((rightMulNielsen a b hab).forward g)) =
        FreeGroup.of g := by
  by_cases hg : g = a
  · subst g
    simp [rightMulNielsen, rightMulForward, rightMulBackward, hab.symm, heisToFree]
  · simp [rightMulNielsen, rightMulForward, rightMulBackward, hg, heisToFree]

private theorem rightMul_resolved_forward_backward
    {n : ℕ} (a b : Generator n) (hab : a ≠ b)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (g : Generator n) :
    FreeGroup.lift
      (fun i ↦ heisToFree E E₂ ((rightMulNielsen a b hab).forward i))
      (heisToFree E E₂ ((rightMulNielsen a b hab).backward g)) =
        FreeGroup.of g := by
  by_cases hg : g = a
  · subst g
    simp [rightMulNielsen, rightMulForward, rightMulBackward, hab.symm, heisToFree]
  · simp [rightMulNielsen, rightMulForward, rightMulBackward, hg, heisToFree]

theorem hyperbolic_resolved_backward_forward
    {h : ℕ} (j : Fin h) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (g : Generator (2 + 2 * h)) :
    FreeGroup.lift
      (fun i ↦ heisToFree E E₂ ((headHandleHyperbolicNielsen j).backward i))
      (heisToFree E E₂ ((headHandleHyperbolicNielsen j).forward g)) =
        FreeGroup.of g := by
  exact resolved_trans_backward_forward (headHandlePairNielsen j)
    (rightMulNielsen (handleU j) .sigma (by simp [handleU])) E E₂
    (pair_resolved_backward_forward j E E₂)
    (rightMul_resolved_backward_forward _ _ _ E E₂) g

theorem hyperbolic_resolved_forward_backward
    {h : ℕ} (j : Fin h) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (g : Generator (2 + 2 * h)) :
    FreeGroup.lift
      (fun i ↦ heisToFree E E₂ ((headHandleHyperbolicNielsen j).forward i))
      (heisToFree E E₂ ((headHandleHyperbolicNielsen j).backward g)) =
        FreeGroup.of g := by
  exact resolved_trans_forward_backward (headHandlePairNielsen j)
    (rightMulNielsen (handleU j) .sigma (by simp [handleU])) E E₂
    (pair_resolved_forward_backward j E E₂)
    (rightMul_resolved_forward_backward _ _ _ E E₂) g

/-- Both compact relators transported by the hyperbolic Nielsen map. -/
def headHandleHyperbolicFullFamily
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (alpha h q : ℕ) (j : Fin h) :
    Fin 2 → FreeGroup (Generator (2 + 2 * h)) :=
  fun l ↦ heisToFree E E₂
    (PWord.subst (headHandleHyperbolicNielsen j).backward
      (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW alpha h) l))

/-- Full Nielsen transport reduces the new Stokes problem exactly to compact M. -/
theorem stokesDuality_headHandleHyperbolicFullFamily_iff
    {h q alpha : ℕ} {C A : Type*} [Group C] [AddCommGroup A]
    [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (j : Fin h)
    (hend : IsStokesEndpoint (fun l : Fin 2 ↦ heisToFree E E₂
      (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW alpha h) l))) :
    StokesDuality ⇑t (headHandleHyperbolicFullFamily E E₂ alpha h q j) A ↔
      StokesDuality
        (freeSubstMark ⇑t (fun g ↦
          heisToFree E E₂ ((headHandleHyperbolicNielsen j).backward g)))
        (fun l : Fin 2 ↦ heisToFree E E₂
          (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW alpha h) l)) A := by
  change StokesDuality ⇑t (fun l : Fin 2 ↦ heisToFree E E₂
      (PWord.subst (headHandleHyperbolicNielsen j).backward
        (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW alpha h) l))) A ↔ _
  exact stokesDuality_heisToFree_subst_iff (A := A) E E₂ ⇑t
      (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW alpha h))
      (headHandleHyperbolicNielsen j).backward
      (headHandleHyperbolicNielsen j).forward
      (hyperbolic_resolved_forward_backward j E E₂)
      (hyperbolic_resolved_backward_forward j E E₂) hend

#print axioms hyperbolic_resolved_backward_forward
#print axioms hyperbolic_resolved_forward_backward
#print axioms headHandleHyperbolicFullFamily
#print axioms stokesDuality_headHandleHyperbolicFullFamily_iff

end Instances.EvenMHeadHandleHyperbolicStokes
end
end GQ2.Dyadic

