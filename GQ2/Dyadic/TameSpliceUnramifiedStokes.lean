/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.TameNormalStokes
import GQ2.Dyadic.TameShadowUnramified

/-!
# Unramified Stokes duality for tame splices

The splice transfers the reference word's Stokes duality in either simple
unramified branch: the surjective branch, or the trivial-action branch.
The underlying shadow comparison is only asserted on tau-normal cochains.
The scalar theorem retains explicit relator-death and endpoint hypotheses;
no source certificate is silently inferred from the word comparison.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH Count Certificates

/-- A tame splice preserves the unramified surjective Stokes branch. -/
theorem stokesDuality_tameSplice_unramified_of_surjective
    {n q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a+a=0)
    (hwild : ∀ (i : Fin (n+1)) (a : A), t.x i • a=a)
    (htau : ∀ a : A, t.τ • a=a) (hq : Even q)
    {e : ℕ} (hE : E omega2=(e:ℤ)) (he : e%4=1)
    (R H : PWord (Generator n))
    (hsurjA : Function.Surjective (heisD1 (A := A) ⇑t
      (fun k ↦ heisToFree E E₂ (gammaFam n q R k))))
    (hsurjD : Function.Surjective (heisD1 (A := ElemDual A) ⇑t
      (fun k ↦ heisToFree E E₂ (gammaFam n q R k))))
    (hR : StokesDuality ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R k)) A) :
    StokesDuality ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q (tameSplice R H) k)) A := by
  have hwildD : ∀ (i : Fin (n+1)) (y : ElemDual A), t.x i • y=y :=
    fun i ↦ HeisLift.smul_elemdual_trivial _ (hwild i)
  have htauD : ∀ y : ElemDual A, t.τ • y=y := HeisLift.smul_elemdual_trivial _ htau
  apply stokesDuality_gammaFam_of_normal_comparison_of_surjective t E E₂ hA₂ htau hq R (tameSplice R H)
  · intro x hx
    exact (heisEvalZ_tameSplice_unramified t x 0 E E₂ hA₂ hwild htau hx rfl hE he R H).1.symm
  · intro y hy
    exact (heisEvalZ_tameSplice_unramified t y 0 E E₂ ElemDual.add_self_eq_zero
      hwildD htauD hy rfl hE he R H).1.symm
  · intro x y hx hy
    exact (heisEvalZ_tameSplice_unramified t x y E E₂ hA₂ hwild htau hx hy hE he R H).2.2.1.symm
  · exact hsurjA
  · exact hsurjD
  · exact hR

/-- A tame splice preserves scalar Stokes duality when its relators die and its endpoint holds. -/
theorem stokesDuality_tameSplice_of_trivial_action
    {n q : ℕ} {C A : Type*} [Group C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a+a=0)
    (htriv : ∀ (g : Generator n) (a : A), t g • a=a) (hq : Even q)
    {e : ℕ} (hE : E omega2=(e:ℤ)) (he : e%4=1)
    (R H : PWord (Generator n))
    (hr : ∀ k, FreeGroup.lift ⇑t (heisToFree E E₂ (gammaFam n q R k))=1)
    (hr' : ∀ k, FreeGroup.lift ⇑t (heisToFree E E₂ (gammaFam n q (tameSplice R H) k))=1)
    (hend : IsStokesEndpoint (fun k ↦ heisToFree E E₂ (gammaFam n q R k)))
    (hend' : IsStokesEndpoint (fun k ↦ heisToFree E E₂ (gammaFam n q (tameSplice R H) k)))
    (hR : StokesDuality ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q R k)) A) :
    StokesDuality ⇑t (fun k ↦ heisToFree E E₂ (gammaFam n q (tameSplice R H) k)) A := by
  apply stokesDuality_gammaFam_of_normal_comparison_of_trivial_action t E E₂ hA₂ htriv hq
    R (tameSplice R H) hr hr' hend hend'
  · intro x y hx hy
    exact (heisEvalZ_tameSplice_unramified t x y E E₂ hA₂
      (fun i ↦ htriv (.wild i)) (htriv .tau) hx hy hE he R H).2.2.1.symm
  · exact hR

#print axioms stokesDuality_tameSplice_unramified_of_surjective
#print axioms stokesDuality_tameSplice_of_trivial_action

end
end GQ2.Dyadic

