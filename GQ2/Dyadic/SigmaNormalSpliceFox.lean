/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.SigmaNormalFoxRows
import GQ2.Dyadic.SigmaNormalSpliceTransport

/-!
# Explicit Fox elimination for the normalized, corrected, spliced source

The actual changed word, not only its raw ancestor, has a checked reduced Jacobian.
The tau off-diagonal coefficient is evaluated on the actual word. Its cancellation uses
the explicit row equivalence, so no equality of raw and changed full matrices is asserted.
The raw word need not die in the original possibly nonfaithful coefficient group.
-/

namespace GQ2.Dyadic.SigmaNormalFoxElimination
noncomputable section
open GQ2 GQ2.Dyadic GQ2.FoxH Count Certificates
open Instances.GammaRCorePresentationNuNormalize Certificates.MProcyclic

/-- All normalization, tame correction and shadow splicing operations admit the same
explicit two-pivot row reduction at an unramified nontrivial coefficient action. -/
theorem normalizedCorrectedSplice_reduced_rows
    {n q : ℕ} {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking n C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (k : Fin (n+1) → ℤ_[2]) (z : Zhat) (R H : PWord (Generator n))
    (j : Fin (n+1)) (hA₂ : ∀ a : A, a+a=0)
    (hwild : ∀ (i : Fin (n+1)) (a : A), t.x i • a=a)
    (htau : ∀ a : A, t.τ • a=a) (hq : Even q)
    (hsigma : ∀ a : A, t.σ • a=a → a=0)
    (hs : ∀ (i : Fin (n+1)) (a : A), t.σ ^ E (padicOmega2 (k i)) • a=a)
    {e : ℕ} (hE : E omega2=(e : ℤ)) (he : e%4=1)
    (hres : ResolverLifts E (WordLift A C))
    (hr : ∀ l, FreeGroup.lift ⇑t (heisToFree E E₂ (gammaFam n q
      (tameSplice (.mul (PWord.subst (wildShearNielsen k).backward R)
        (.inv (.profPow (.gen .tau) z))) H) l))=1)
    (hnormal : ∀ y : Generator n → A, y .sigma=0 → y .tau=0 →
      (heisEvalZ ⇑t y 0 E E₂ R).a = y (.wild j) - t.σ⁻¹ • y (.wild j))
    (x : Generator n → A) :
    let d := heisD1 (A := A) ⇑t (fun l ↦ heisToFree E E₂ (gammaFam n q
      (tameSplice (.mul (PWord.subst (wildShearNielsen k).backward R)
        (.inv (.profPow (.gen .tau) z))) H) l))
    rowElimination (actionEquiv t.σ⁻¹) (oneSubInvAction t.σ hsigma)
      (tauColumn d) (d x) = ![x .tau, x (.wild j)] := by
  apply heisD1_reduced_of_normal t E E₂ _ j hA₂ htau hwild hq hsigma hres
    (heisD1_comp_heisD0 ⇑t _ hr)
  intro y hys hyt
  exact (heisEvalZ_normalizedCorrectedSplice_unramified t y 0 E E₂ k hA₂ hwild htau
    hys rfl hyt rfl hs hE he z R H).1.trans (hnormal y hys hyt)

#print axioms normalizedCorrectedSplice_reduced_rows

end
end GQ2.Dyadic.SigmaNormalFoxElimination
