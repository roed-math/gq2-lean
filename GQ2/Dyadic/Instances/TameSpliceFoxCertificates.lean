/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.TameSpliceUnramifiedFoxRows
import GQ2.Dyadic.Instances.TameSpliceRamifiedFoxNormal
import GQ2.Dyadic.Instances.TameSpliceScalarFoxNormal

/-!
# Original-format Fox certificates for the actual changed sources

The original FoxCertificate API already supports these words. We identify its
foxJacobian carrier with the fully resolved Heisenberg differential at the same
lift-level pinned resolver, then transport the existing compact-M formal
operation lists and normal targets to the actual pair and mobile splice words.
The scalar sector has a literal tau/zero target and one fixed row subtraction.

Every concrete producer pins the actual normalized, prime-corrected, spliced
word in its result type and discharges the complete matrix equality. No raw
relator-death premise, assumed matrix, or change to the old certificate grammar
is introduced. The nontrivial unramified sector retains actual changed-word
death; the projected ramified sector retains its explicit head/action data.
-/

namespace GQ2.Dyadic.Instances.TameSpliceFoxCertificates
noncomputable section
open GQ2 GQ2.FoxH GQ2.Dyadic Count Certificates Words MarkedCore
open Certificates.MProcyclic
open Instances.TameSpliceUnramifiedFoxRows Instances.TameSpliceRamifiedFoxNormal
open Instances.TameSpliceScalarFoxNormal
open Instances.EvenMHeadHandlePairNormalize Instances.EvenMHeadHandlePairSpliceSupply
open Instances.EvenMHeadHandlePairSplice
open Instances.MpcMobileNuSource Instances.MpcMobileSpliceSupply

variable {C A : Type} [Group C] [Finite C] [AddCommGroup A] [Finite A]
  [DistribMulAction C A] {alpha h q n : ℕ}

/-- Carrier bridge at the actual pinned lift resolver, not merely at base-group level. -/
theorem foxJacobian_pinned_apply (t : Marking n C) (hA2 : ∀ a : A, a+a=0)
    (R : PWord (Generator n)) (x : Generator n → A) :
    foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
      (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW n q) R x =
      (heisD1 (A := A) ⇑t (pinnedResolvedFamily n q R (4*Monoid.exponent C)) x 0,
       heisD1 (A := A) ⇑t (pinnedResolvedFamily n q R (4*Monoid.exponent C)) x 1) := by
  have hres := omegaPinnedLevelZhatResolver_fourMulExponent_wordLift (C := C) hA2
  apply Prod.ext
  · change foxD ⇑t x _ _ (tameRelW n q) =
      (FreeGroup.lift (heisGen ⇑t x 0) (heisToFree _ _ (tameRelW n q))).a
    rw [← heisEvalZ_eq_lift, heisEvalZ_a_eq_foxD hres]
  · change foxD ⇑t x _ _ R =
      (FreeGroup.lift (heisGen ⇑t x 0) (heisToFree _ _ R)).a
    rw [← heisEvalZ_eq_lift, heisEvalZ_a_eq_foxD hres]

/-- Equality of complete resolved differentials transports the original Fox carrier. -/
theorem foxJacobian_pinned_eq_of_heisD1_eq
    (t : Marking n C) (hA2 : ∀ a : A, a+a=0) (R H : PWord (Generator n))
    (heq : heisD1 (A := A) ⇑t (pinnedResolvedFamily n q R (4*Monoid.exponent C)) =
      heisD1 (A := A) ⇑t (pinnedResolvedFamily n q H (4*Monoid.exponent C))) :
    foxJacobian (A := A) ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
      (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW n q) R =
    foxJacobian (A := A) ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
      (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW n q) H := by
  apply AddMonoidHom.ext
  intro x
  rw [foxJacobian_pinned_apply t hA2, foxJacobian_pinned_apply t hA2, heq]

private def unramCertificateOfRows
    (t : Marking (2+2*h) C) (R : PWord (Generator (2+2*h)))
    (hA2 : ∀ a : A, a+a=0)
    (hwild : ∀ (i : Fin (2+2*h+1)) (a : A), t.x i • a=a)
    (htau : ∀ a : A, t.τ • a=a)
    (hsigma2 : ∀ a : A, powOmega2 t.σ • a=a) (hqe : Even q)
    (hrow : ∀ x, heisD1 (A := A) ⇑t
      (pinnedResolvedFamily (2+2*h) q R (4*Monoid.exponent C)) x =
      ![t.σ⁻¹ • x .tau, x .tau + (x (.wild (x2Idx h)) - t.σ⁻¹ • x (.wild (x2Idx h)))]) :
    FoxCertificate (TameSym.splitEnd (A := A) t)
      (foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q) R) := by
  have heq : heisD1 (A := A) ⇑t
      (pinnedResolvedFamily (2+2*h) q R (4*Monoid.exponent C)) =
      heisD1 (A := A) ⇑t (pinnedResolvedFamily (2+2*h) q
        (Words.MCompact.mCompactW alpha h) (4*Monoid.exponent C)) := by
    apply AddMonoidHom.ext
    intro x
    rw [hrow]
    change _ = heisD1 (A := A) ⇑t (fun k => heisToFree _ _
      (gammaFam (2+2*h) q (Words.MCompact.mCompactW alpha h) k)) x
    rw [mCompact_pinned_family_eq]
    exact (heisD1_mCompactFam_unramified_apply t hA2 hwild htau hsigma2 hqe x).symm
  rw [foxJacobian_pinned_eq_of_heisD1_eq t hA2 R _ heq]
  exact Certificates.MCompact.mCompactJacobianCertUnram t _ _ hA2 hwild htau hsigma2 hqe

private def scalarCertificateOfRows
    (t : Marking (2+2*h) C) (R : PWord (Generator (2+2*h)))
    (hA2 : ∀ a : A, a+a=0)
    (hrow : ∀ x, heisD1 (A := A) ⇑t
      (pinnedResolvedFamily (2+2*h) q R (4*Monoid.exponent C)) x = ![x .tau,x .tau]) :
    FoxCertificate (TameSym.splitEnd (A := A) t)
      (foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q) R) where
  rowOps := [.addSnd (.neg .one)]
  colOps := []
  target := ⟨.single .tau, ⟨fun _ => .zero⟩⟩
  rowOps_invertible := by intro r hr; simp only [List.mem_singleton] at hr; subst r; trivial
  colOps_invertible := by simp
  verifies := by
    apply AddMonoidHom.ext
    intro x
    rw [foxApplyOps_apply, FoxColOp.listHom_nil, AddMonoidHom.id_apply,
      FoxRowOp.listHom_cons, FoxRowOp.listHom_nil, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, foxJacobian_pinned_apply t hA2, hrow]
    rw [FoxRowOp.toHom_addSnd_apply, FoxNormalForm.toHom_apply]
    simp only [FoxCoeff.eval_neg_apply, FoxCoeff.eval_one_apply,
      FoxRowNormalForm.single_toHom_apply]
    apply Prod.ext
    · rfl
    · change x .tau + -(x .tau) = ∑ _g : Generator (2+2*h), (0 : A)
      simp

/-- Original-format ramified Fox certificate of an actual splice, using the already
proved full projected differential equality. No relation death is added. -/
def tameSplice_FoxCertificate_ramified
    {D : Type} [Group D] [Finite D] [DistribMulAction D A]
    (t : Marking (2+2*h) C) (pi : C →* D)
    (hpi : ∀ (c : C) (a : A), c • a=pi c • a) (hsurj : Function.Surjective pi)
    (hA2 : ∀ a : A, a+a=0) (ht : t.TameRelAt q) (hq0 : q≠0) (hqe : Even q)
    (hwild : ∀ i, pi (t.x i)=1)
    (hfpf : ∀ a : A, t.τ • a=a → a=0)
    (hodd : ∀ a : A, powOmega2 t.τ • a=a)
    (R : PWord (Generator (2+2*h))) (hspec : TameSpec.TameSpecializes (2+2*h) q R)
    (hend : IsStokesEndpoint (pinnedResolvedFamily (2+2*h) q R (4*Monoid.exponent C))) :
    FoxCertificate (TameSym.ramifiedEnd (A := A) t)
      (foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q)
        (tameSplice R (Words.MCompact.mCompactW alpha h))) := by
  have hfpfD : ∀ a : A, pi t.τ • a=a → a=0 :=
    fun a ha => hfpf a ((hpi _ a).trans ha)
  have hoddD : ∀ a : A, powOmega2 (pi t.τ) • a=a := by
    intro a
    rw [← powOmega2_map pi, ← hpi]
    exact hodd a
  have heq := heisD1_tameSplice_mCompact_ramified_of_projected (alpha := alpha)
    t pi hpi hsurj hA2 hq0 hqe hwild hfpfD hoddD R hspec hend
  rw [← mCompact_pinned_family_eq] at heq
  rw [foxJacobian_pinned_eq_of_heisD1_eq t hA2 _ _ heq]
  exact Certificates.MCompact.mCompactJacobianCertRam t _ _ hA2
    (fun i a => by rw [hpi, hwild, one_smul]) hfpf hodd ht


/-- Original-format scalar certificate for the actual pair splice; the target
is literally the tau pivot and a zero row. No relation-death premise. -/
def pairSplice_FoxCertificate_scalar
    (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA2 : ∀ a : A, a+a=0)
    (htriv : ∀ (g : Generator (2+2*h)) (a : A), t g • a=a) :
    FoxCertificate (TameSym.splitEnd (A := A) t)
      (foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q)
        (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP)) :=
  scalarCertificateOfRows t _ hA2
    (pairSplice_scalar_rows t halpha hq0 hqe j nuP hA2 htriv)

/-- Original-format unramified certificate of the actual pair splice. Its fixed
formal operation list and target are the compact-M certificate's; only actual changed-word
death is assumed, not raw-word death. -/
def pairSplice_FoxCertificate_unramified
    [TopologicalSpace C] [DiscreteTopology C]
    (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA2 : ∀ a : A, a+a=0)
    (hwild : ∀ (i : Fin (2+2*h+1)) (a : A), t.x i • a=a)
    (htau : ∀ a : A, t.τ • a=a)
    (hsigma : ∀ a : A, t.σ • a=a → a=0)
    (hsigma2 : ∀ a : A, powOmega2 t.σ • a=a)
    (hr : ∀ l, FreeGroup.lift ⇑t
      (pinnedResolvedFamily (2+2*h) q (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP)
        (4*Monoid.exponent C) l)=1) :
    FoxCertificate (TameSym.splitEnd (A := A) t)
      (foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q)
        (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP)) :=
  unramCertificateOfRows (alpha := alpha) t _ hA2 hwild htau hsigma2 hqe
    (pairSplice_unramified_rows t halpha hq0 hqe j nuP
      hA2 hwild htau hsigma hsigma2 hr)

/-- Original-format ramified certificate for the actual pair splice. The full
projected source transport discharges the matrix equality, with no raw-death premise. -/
def pairSplice_FoxCertificate_ramified
    {D : Type} [Group D] [Finite D] [DistribMulAction D A]
    (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA2 : ∀ a : A, a+a=0)
    (pi : C →* D) (hpi : ∀ (c : C) (a : A), c • a=pi c • a)
    (hsurj : Function.Surjective pi) (ht : t.TameRelAt q)
    (hwild : ∀ i, pi (t.x i)=1)
    (hfpf : ∀ a : A, t.τ • a=a → a=0)
    (hodd : ∀ a : A, powOmega2 t.τ • a=a) :
    FoxCertificate (TameSym.ramifiedEnd (A := A) t)
      (foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q)
        (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP)) :=
  tameSplice_FoxCertificate_ramified t pi hpi hsurj hA2 ht hq0 hqe hwild hfpf hodd
    (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hqe j nuP)
    (headHandlePairPrimeCorrectedW_specializes alpha h q halpha hq0 hqe j nuP)
    (headHandlePairPrime_pinned_endpoint halpha hq0 hqe j nuP
      (fourMulExponent_ne_zero_and_even C).1 (fourMulExponent_ne_zero_and_even C).2)

/-- Original-format scalar certificate for the actual mobile splice; the target
is literally the tau pivot and a zero row. No relation-death premise. -/
def mobileSplice_FoxCertificate_scalar {r p : ℕ}
    (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (eta : ℤ_[2]ˣ) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA2 : ∀ a : A, a+a=0)
    (htriv : ∀ (g : Generator (2+2*h)) (a : A), t g • a=a) :
    FoxCertificate (TameSym.splitEnd (A := A) t)
      (foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q)
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP) (Words.MCompact.mCompactW alpha h))) :=
  scalarCertificateOfRows t _ hA2
    (mobileSplice_scalar_rows t halpha hq0 hqe eta nuP hA2 htriv)

/-- Original-format unramified certificate of the actual mobile splice. Its fixed
formal operation list and target are the compact-M certificate's; only actual changed-word
death is assumed, not raw-word death. -/
def mobileSplice_FoxCertificate_unramified {r p : ℕ}
    [TopologicalSpace C] [DiscreteTopology C]
    (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (eta : ℤ_[2]ˣ) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA2 : ∀ a : A, a+a=0)
    (hwild : ∀ (i : Fin (2+2*h+1)) (a : A), t.x i • a=a)
    (htau : ∀ a : A, t.τ • a=a)
    (hsigma : ∀ a : A, t.σ • a=a → a=0)
    (hsigma2 : ∀ a : A, powOmega2 t.σ • a=a)
    (hr : ∀ l, FreeGroup.lift ⇑t
      (pinnedResolvedFamily (2+2*h) q (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP) (Words.MCompact.mCompactW alpha h))
        (4*Monoid.exponent C) l)=1) :
    FoxCertificate (TameSym.splitEnd (A := A) t)
      (foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q)
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP) (Words.MCompact.mCompactW alpha h))) :=
  unramCertificateOfRows (alpha := alpha) t _ hA2 hwild htau hsigma2 hqe
    (mobileSplice_unramified_rows t halpha hq0 hqe eta nuP
      hA2 hwild htau hsigma hsigma2 hr)

/-- Original-format ramified certificate for the actual mobile splice. The full
projected source transport discharges the matrix equality, with no raw-death premise. -/
def mobileSplice_FoxCertificate_ramified {r p : ℕ}
    {D : Type} [Group D] [Finite D] [DistribMulAction D A]
    (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (eta : ℤ_[2]ˣ) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hA2 : ∀ a : A, a+a=0)
    (pi : C →* D) (hpi : ∀ (c : C) (a : A), c • a=pi c • a)
    (hsurj : Function.Surjective pi) (ht : t.TameRelAt q)
    (hwild : ∀ i, pi (t.x i)=1)
    (hfpf : ∀ a : A, t.τ • a=a → a=0)
    (hodd : ∀ a : A, powOmega2 t.τ • a=a) :
    FoxCertificate (TameSym.ramifiedEnd (A := A) t)
      (foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q)
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP) (Words.MCompact.mCompactW alpha h))) :=
  tameSplice_FoxCertificate_ramified t pi hpi hsurj hA2 ht hq0 hqe hwild hfpf hodd
    (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
    (mpcMobileTameCorrectedW_specializes hq0 hqe eta halpha nuP)
    (mpcMobileTameCorrected_endpoint hq0 hqe eta halpha nuP
      (fourMulExponent_ne_zero_and_even C).1 (fourMulExponent_ne_zero_and_even C).2)

#print axioms foxJacobian_pinned_apply
#print axioms foxJacobian_pinned_eq_of_heisD1_eq
#print axioms tameSplice_FoxCertificate_ramified
#print axioms pairSplice_FoxCertificate_scalar
#print axioms pairSplice_FoxCertificate_unramified
#print axioms pairSplice_FoxCertificate_ramified
#print axioms mobileSplice_FoxCertificate_scalar
#print axioms mobileSplice_FoxCertificate_unramified
#print axioms mobileSplice_FoxCertificate_ramified

end
end GQ2.Dyadic.Instances.TameSpliceFoxCertificates

