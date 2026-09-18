/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.TameShadowTauColumn
import GQ2.Dyadic.Instances.TameSpliceFoxNormal

/-!
# Fully expanded unramified Fox rows of the actual changed words

The previously abstract tau column is the identity. Thus the literal matrix has rows
`[0,S⁻¹,0,...]` and `[0,1,0,...,1-S⁻¹,...]`, uniformly for both changed source families.
The assertion concerns all cochains and the actual normalized/corrected/spliced word.
-/

namespace GQ2.Dyadic.Instances.TameSpliceUnramifiedFoxRows
noncomputable section
open GQ2 GQ2.FoxH GQ2.Dyadic Count Certificates Words MarkedCore
open SigmaNormalFoxElimination
open Certificates.MProcyclic
open Instances.TameSpliceFoxNormal
open Instances.EvenMHeadHandlePairSpliceSupply Instances.MpcMobileNuSource

variable {alpha h q : ℕ} {C A : Type} [Group C] [Finite C]
  [AddCommGroup A] [Finite A] [DistribMulAction C A]

/-- The tau column of any actual compact-template splice is literally the identity.
Only changed-word death is used; R need not die in the original coefficient group. -/
theorem compactSplice_tauColumn
    (t : Marking (2+2*h) C) (R : PWord (Generator (2+2*h)))
    (hA2 : ∀ a : A, a+a=0)
    (hwild : ∀ (i : Fin (2+2*h+1)) (a : A), t.x i • a=a)
    (htau : ∀ a : A, t.τ • a=a)
    (hsigma2 : ∀ a : A, powOmega2 t.σ • a=a)
    (hr : ∀ l, FreeGroup.lift ⇑t
      (pinnedResolvedFamily (2+2*h) q (tameSplice R (MCompact.mCompactW alpha h))
        (4*Monoid.exponent C) l)=1) :
    tauColumn (heisD1 (A := A) ⇑t
      (pinnedResolvedFamily (2+2*h) q (tameSplice R (MCompact.mCompactW alpha h))
        (4*Monoid.exponent C))) = AddMonoidHom.id A := by
  let E := omegaPinnedLevelZhatResolver (4*Monoid.exponent C)
  let E2 := omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)
  have hres := omegaPinnedLevelZhatResolver_fourMulExponent_wordLift (C := C) hA2
  have hdeath : PWord.evalZ ⇑t E E2 (tameSplice R (MCompact.mCompactW alpha h))=1 := by
    rw [evalZ_eq_lift_heisToFree]
    exact hr 1
  ext a
  change (FreeGroup.lift (heisGen ⇑t (Pi.single .tau a) 0)
    (heisToFree E E2 (tameSplice R (MCompact.mCompactW alpha h)))).a=a
  rw [← heisEvalZ_eq_lift,
    heisEvalZ_tameSplice_tauOnly t a E E2 hA2 hwild htau
      (omegaPinnedLevelZhatResolver_omega2 _) (omega2Exp_fourMulExponent_mod_four C)
      R (MCompact.mCompactW alpha h) hdeath,
    heisEvalZ_a_eq_foxD hres,
    Certificates.MCompact.foxD_mCompact_unram_simple t E E2 hA2 hwild htau hsigma2]
  simp [coreLetter]

omit [Finite A] in
private theorem rows_of_identity_tau_reduction {n : ℕ}
    (d : (Generator n → A) →+ (Fin 2 → A)) (U D : A ≃+ A)
    (j : Fin (n+1)) (htau : tauColumn d=AddMonoidHom.id A)
    (x : Generator n → A)
    (hred : rowElimination U D (tauColumn d) (d x) = ![x .tau, x (.wild j)]) :
    d x = ![U (x .tau), x .tau + D (x (.wild j))] := by
  rw [htau] at hred
  have H := congrArg (rowElimination U D (AddMonoidHom.id A)).symm hred
  rw [AddEquiv.symm_apply_apply] at H
  exact H

variable [TopologicalSpace C] [DiscreteTopology C]

/-- Full actual pair-splice matrix, with its tau entry evaluated rather than left opaque. -/
theorem pairSplice_unramified_rows
    (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA2 : ∀ a : A, a+a=0)
    (hwild : ∀ (i : Fin (2+2*h+1)) (a : A), t.x i • a=a)
    (htau : ∀ a : A, t.τ • a=a)
    (hsigma : ∀ a : A, t.σ • a=a → a=0)
    (hsigma2 : ∀ a : A, powOmega2 t.σ • a=a)
    (hr : ∀ l, FreeGroup.lift ⇑t
      (pinnedResolvedFamily (2+2*h) q
        (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP)
        (4*Monoid.exponent C) l)=1)
    (x : Generator (2+2*h) → A) :
    heisD1 (A := A) ⇑t
      (pinnedResolvedFamily (2+2*h) q
        (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP)
        (4*Monoid.exponent C)) x =
      ![t.σ⁻¹ • x .tau, x .tau + (x (.wild (x2Idx h)) - t.σ⁻¹ • x (.wild (x2Idx h)))] := by
  exact rows_of_identity_tau_reduction _ (actionEquiv t.σ⁻¹)
    (oneSubInvAction t.σ hsigma) (x2Idx h)
    (compactSplice_tauColumn t _ hA2 hwild htau hsigma2 hr) x
    (pairSplice_reducedFox t halpha hq0 hqe j nuP hA2 hwild htau hsigma hsigma2 hr x)

/-- Full actual mobile-splice matrix for arbitrary two-adic unit and all handle ranks. -/
theorem mobileSplice_unramified_rows {r p : ℕ}
    (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (eta : ℤ_[2]ˣ) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA2 : ∀ a : A, a+a=0)
    (hwild : ∀ (i : Fin (2+2*h+1)) (a : A), t.x i • a=a)
    (htau : ∀ a : A, t.τ • a=a)
    (hsigma : ∀ a : A, t.σ • a=a → a=0)
    (hsigma2 : ∀ a : A, powOmega2 t.σ • a=a)
    (hr : ∀ l, FreeGroup.lift ⇑t
      (pinnedResolvedFamily (2+2*h) q
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
          (MCompact.mCompactW alpha h)) (4*Monoid.exponent C) l)=1)
    (x : Generator (2+2*h) → A) :
    heisD1 (A := A) ⇑t
      (pinnedResolvedFamily (2+2*h) q
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
          (MCompact.mCompactW alpha h)) (4*Monoid.exponent C)) x =
      ![t.σ⁻¹ • x .tau, x .tau + (x (.wild (x2Idx h)) - t.σ⁻¹ • x (.wild (x2Idx h)))] := by
  exact rows_of_identity_tau_reduction _ (actionEquiv t.σ⁻¹)
    (oneSubInvAction t.σ hsigma) (x2Idx h)
    (compactSplice_tauColumn t _ hA2 hwild htau hsigma2 hr) x
    (mobileSplice_reducedFox t halpha hq0 hqe eta nuP hA2 hwild htau hsigma hsigma2 hr x)

#print axioms compactSplice_tauColumn
#print axioms pairSplice_unramified_rows
#print axioms mobileSplice_unramified_rows

end
end GQ2.Dyadic.Instances.TameSpliceUnramifiedFoxRows
