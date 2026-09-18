/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GQ2.Dyadic.Instances.TameSpliceFoxTemplateBinding

/-!
# Exact exported Fox inputs for the actual pair/mobile words

These six equalities bind the typed profile's entire input matrix, on every
cochain, to the actual pinned Fox Jacobian. They complement the operation/target
signature equalities without introducing a supplied row identity. All semantic
source parameters and finite-action hypotheses remain explicit.
-/

namespace GQ2.Dyadic.GeneralFoxTemplate
noncomputable section
open GQ2 FoxH Count Certificates Words MarkedCore
open Instances.TameSpliceFoxCertificates Instances.TameSpliceScalarFoxNormal
open Instances.TameSpliceUnramifiedFoxRows Instances.TameSpliceRamifiedFoxNormal
open Instances.TameSplicePolynomialFoxCertificates
open Instances.TameSpliceRamifiedPolynomialFoxCertificates
open Instances.EvenMHeadHandlePairNormalize Instances.EvenMHeadHandlePairSplice
open Instances.EvenMHeadHandlePairSpliceSupply
open Instances.MpcMobileNuSource Instances.MpcMobileSpliceSupply

variable {alpha h q : ℕ} {C A : Type} [Group C] [Finite C]
  [AddCommGroup A] [Finite A] [DistribMulAction C A]
  (t : Marking (2+2*h) C) (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
  (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) (hA2 : ∀ a : A, a+a=0)

include hA2

theorem scalar_pair_input (j : Fin h)
    (htriv : ∀ (g : Generator (2+2*h)) (a : A), t g • a=a) :
    ((scalar (2+2*h)).inputMatrix q 0).toHom (TameSym.splitEnd (A := A) t) =
      foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q)
        (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP) := by
  apply AddMonoidHom.ext
  intro x
  rw [scalar_input_apply, foxJacobian_pinned_apply t hA2,
    pairSplice_scalar_rows t halpha hq0 hqe j nuP hA2 htriv]
  rfl

theorem scalar_mobile_input {r p : ℕ} (eta : ℤ_[2]ˣ)
    (htriv : ∀ (g : Generator (2+2*h)) (a : A), t g • a=a) :
    ((scalar (2+2*h)).inputMatrix q 0).toHom (TameSym.splitEnd (A := A) t) =
      foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q)
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
          (MCompact.mCompactW alpha h)) := by
  apply AddMonoidHom.ext
  intro x
  rw [scalar_input_apply, foxJacobian_pinned_apply t hA2,
    mobileSplice_scalar_rows t halpha hq0 hqe eta nuP hA2 htriv]
  rfl

section Unramified
variable [TopologicalSpace C] [DiscreteTopology C]
  (hwild : ∀ (i : Fin (2+2*h+1)) (a : A), t.x i • a=a)
  (htau : ∀ a : A, t.τ • a=a)
  (hsigma : ∀ a : A, t.σ • a=a → a=0)
  (hsigma2 : ∀ a : A, powOmega2 t.σ • a=a)

include hwild htau hsigma hsigma2

theorem unramified_pair_input (j : Fin h)
    (hr : ∀ l, FreeGroup.lift ⇑t
      (pinnedResolvedFamily (2+2*h) q (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP)
        (4*Monoid.exponent C) l)=1) :
    ((unramified (x2Idx h)).inputMatrix q (sigmaActionHalfPeriod (A := A) t)).toHom
      (TameSym.splitEnd (A := A) t) =
      foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q)
        (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP) := by
  apply AddMonoidHom.ext
  intro x
  rw [unramified_input_apply, foxJacobian_pinned_apply t hA2,
    pairSplice_unramified_rows t halpha hq0 hqe j nuP hA2 hwild htau hsigma hsigma2 hr]
  rfl

theorem unramified_mobile_input {r p : ℕ} (eta : ℤ_[2]ˣ)
    (hr : ∀ l, FreeGroup.lift ⇑t
      (pinnedResolvedFamily (2+2*h) q
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
          (MCompact.mCompactW alpha h)) (4*Monoid.exponent C) l)=1) :
    ((unramified (x2Idx h)).inputMatrix q (sigmaActionHalfPeriod (A := A) t)).toHom
      (TameSym.splitEnd (A := A) t) =
      foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q)
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
          (MCompact.mCompactW alpha h)) := by
  apply AddMonoidHom.ext
  intro x
  rw [unramified_input_apply, foxJacobian_pinned_apply t hA2,
    mobileSplice_unramified_rows t halpha hq0 hqe eta nuP hA2 hwild htau hsigma hsigma2 hr]
  rfl
end Unramified

section Ramified
variable {D : Type} [Group D] [Finite D] [DistribMulAction D A]
  (pi : C →* D) (hpi : ∀ (c : C) (a : A), c • a=pi c • a)
  (hsurj : Function.Surjective pi) (ht : t.TameRelAt q)
  (hwild : ∀ i, pi (t.x i)=1)
  (hfpf : ∀ a : A, t.τ • a=a → a=0)
  (hodd : ∀ a : A, powOmega2 t.τ • a=a)

include hq0 hqe hA2 pi hpi hsurj ht hwild hfpf hodd

private theorem ramified_input_of_specializes
    (R : PWord (Generator (2+2*h))) (hspec : TameSpec.TameSpecializes (2+2*h) q R)
    (hend : IsStokesEndpoint (pinnedResolvedFamily (2+2*h) q R (4*Monoid.exponent C))) :
    ((ramified (x2Idx h)).inputMatrix q (tauActionHalfPeriod (A := A) t)).toHom
      (TameSym.ramifiedEnd (A := A) t) =
      foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q)
        (tameSplice R (MCompact.mCompactW alpha h)) := by
  apply AddMonoidHom.ext
  intro x
  rw [ramified_input_apply, foxJacobian_pinned_apply t hA2,
    tameSplice_ramified_rows t pi hpi hsurj hA2 ht hq0 hqe hwild hfpf hodd R hspec hend]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  apply Prod.ext
  · simp only [smul_sub, smul_add]
    abel
  · rfl

theorem ramified_pair_input (j : Fin h) :
    ((ramified (x2Idx h)).inputMatrix q (tauActionHalfPeriod (A := A) t)).toHom
      (TameSym.ramifiedEnd (A := A) t) =
      foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q)
        (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP) := by
  exact ramified_input_of_specializes t hq0 hqe hA2 pi hpi hsurj ht hwild hfpf hodd
    (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hqe j nuP)
    (headHandlePairPrimeCorrectedW_specializes alpha h q halpha hq0 hqe j nuP)
    (headHandlePairPrime_pinned_endpoint halpha hq0 hqe j nuP
      (fourMulExponent_ne_zero_and_even C).1 (fourMulExponent_ne_zero_and_even C).2)

theorem ramified_mobile_input {r p : ℕ} (eta : ℤ_[2]ˣ) :
    ((ramified (x2Idx h)).inputMatrix q (tauActionHalfPeriod (A := A) t)).toHom
      (TameSym.ramifiedEnd (A := A) t) =
      foxJacobian ⇑t (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
        (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (tameRelW (2+2*h) q)
        (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
          (MCompact.mCompactW alpha h)) := by
  exact ramified_input_of_specializes t hq0 hqe hA2 pi hpi hsurj ht hwild hfpf hodd
    (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
    (mpcMobileTameCorrectedW_specializes hq0 hqe eta halpha nuP)
    (mpcMobileTameCorrected_endpoint hq0 hqe eta halpha nuP
      (fourMulExponent_ne_zero_and_even C).1 (fourMulExponent_ne_zero_and_even C).2)
end Ramified

#print axioms scalar_pair_input
#print axioms scalar_mobile_input
#print axioms unramified_pair_input
#print axioms unramified_mobile_input
#print axioms ramified_pair_input
#print axioms ramified_mobile_input
end
end GQ2.Dyadic.GeneralFoxTemplate
