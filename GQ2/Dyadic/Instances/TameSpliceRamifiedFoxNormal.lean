/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.SigmaRamifiedFoxElimination
import GQ2.Dyadic.Instances.TameSpliceRamifiedNormal
import GQ2.Dyadic.Instances.EvenMHeadHandlePairSpliceSupply
import GQ2.Dyadic.Instances.MpcMobileSpliceSupply

/-!
# Explicit ramified Fox elimination for the actual tame-splice words

The existing projected-head transport gives equality of the complete differentials, not only
their kernels. This module displays that actual row and applies an invertible sigma-column
shear and diagonal row scaling. The reduced pivots are sigma and x2 at every handle rank.
Pair and arbitrary-unit mobile sources discharge their structural endpoint hypotheses.

Every action and tame hypothesis is explicit. This staged compositional artifact does not
weaken source certificates or claim approval of a replacement acceptance-appendix format.
-/

namespace GQ2.Dyadic.Instances.TameSpliceRamifiedFoxNormal
noncomputable section
open GQ2 GQ2.FoxH GQ2.Dyadic Count Certificates Words MarkedCore
open SigmaRamifiedFoxElimination
open Instances.EvenMHeadHandlePairNormalize
open Instances.EvenMHeadHandlePairSplice Instances.EvenMHeadHandlePairSpliceSupply
open Instances.MpcMobileNuSource Instances.MpcMobileSpliceSupply

variable {C D A : Type} [Group C] [Finite C] [Group D] [Finite D]
  [AddCommGroup A] [Finite A] [DistribMulAction C A] [DistribMulAction D A]
  {alpha h q : ℕ}

/-- The literal ramified matrix of the actual splice after a faithful-enough head projection.
Wild elements may be nontrivial in C; they must map to one in the projected head D. -/
theorem tameSplice_ramified_rows
    (t : Marking (2+2*h) C) (pi : C →* D)
    (hpi : ∀ (c : C) (a : A), c • a = pi c • a) (hsurj : Function.Surjective pi)
    (hA2 : ∀ a : A, a+a=0) (ht : t.TameRelAt q) (hq0 : q≠0) (hqe : Even q)
    (hwild : ∀ i, pi (t.x i)=1)
    (hfpf : ∀ a : A, t.τ • a=a → a=0)
    (hodd : ∀ a : A, powOmega2 t.τ • a=a)
    (R : PWord (Generator (2+2*h))) (hspec : TameSpec.TameSpecializes (2+2*h) q R)
    (hend : IsStokesEndpoint (pinnedResolvedFamily (2+2*h) q R (4*Monoid.exponent C)))
    (x : Generator (2+2*h) → A) :
    heisD1 (A := A) ⇑t (pinnedResolvedFamily (2+2*h) q
      (tameSplice R (MCompact.mCompactW alpha h)) (4*Monoid.exponent C)) x =
    ![t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
        - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau,
      -(t.σ⁻¹ • x (.wild (Certificates.x2Idx h)))] := by
  have hwildC : ∀ (i : Fin (2+2*h+1)) (a : A), t.x i • a=a := by
    intro i a
    rw [hpi, hwild, one_smul]
  have hfpfD : ∀ a : A, pi t.τ • a=a → a=0 := by
    intro a ha
    exact hfpf a ((hpi _ a).trans ha)
  have hoddD : ∀ a : A, powOmega2 (pi t.τ) • a=a := by
    intro a
    rw [← powOmega2_map pi, ← hpi]
    exact hodd a
  have heq := heisD1_tameSplice_mCompact_ramified_of_projected (alpha := alpha)
    t pi hpi hsurj hA2 hq0 hqe hwild hfpfD hoddD R hspec hend
  change heisD1 (A := A) ⇑t (fun k => heisToFree
    (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
    (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C))
    (gammaFam (2+2*h) q (tameSplice R (MCompact.mCompactW alpha h)) k)) x = _
  rw [heq]
  exact heisD1_mCompactFam_ramified_apply t hA2 ht hwildC hfpf hodd x

/-- All-cochain identity for the actual source matrix after the explicit invertible operations. -/
theorem tameSplice_ramified_reducedFox
    (t : Marking (2+2*h) C) (pi : C →* D)
    (hpi : ∀ (c : C) (a : A), c • a = pi c • a) (hsurj : Function.Surjective pi)
    (hA2 : ∀ a : A, a+a=0) (ht : t.TameRelAt q) (hq0 : q≠0) (hqe : Even q)
    (hwild : ∀ i, pi (t.x i)=1)
    (hfpf : ∀ a : A, t.τ • a=a → a=0)
    (hodd : ∀ a : A, powOmega2 t.τ • a=a)
    (R : PWord (Generator (2+2*h))) (hspec : TameSpec.TameSpecializes (2+2*h) q R)
    (hend : IsStokesEndpoint (pinnedResolvedFamily (2+2*h) q R (4*Monoid.exponent C)))
    (x : Generator (2+2*h) → A) :
    let d := heisD1 (A := A) ⇑t (pinnedResolvedFamily (2+2*h) q
      (tameSplice R (MCompact.mCompactW alpha h)) (4*Monoid.exponent C))
    rowScaling (sigmaPivot t.σ t.τ hfpf) (wildPivot t.σ)
      (d (columnShear (sigmaPivot t.σ t.τ hfpf) (tauCoefficient t.σ t.τ q) x)) =
      ![x .sigma, x (.wild (Certificates.x2Idx h))] := by
  apply reduced_rows_of_action_row t q (Certificates.x2Idx h) hfpf
  exact tameSplice_ramified_rows t pi hpi hsurj hA2 ht hq0 hqe hwild hfpf hodd R hspec hend

/-- The actual normalized, prime-to-two-corrected pair splice has the displayed ramified
identity pivots. No selected-handle unit premise is needed for this first-jet statement. -/
theorem pairSplice_ramified_reducedFox
    (t : Marking (2+2*h) C) (pi : C →* D)
    (hpi : ∀ (c : C) (a : A), c • a = pi c • a) (hsurj : Function.Surjective pi)
    (hA2 : ∀ a : A, a+a=0) (ht : t.TameRelAt q)
    (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (j : Fin h) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hwild : ∀ i, pi (t.x i)=1)
    (hfpf : ∀ a : A, t.τ • a=a → a=0)
    (hodd : ∀ a : A, powOmega2 t.τ • a=a)
    (x : Generator (2+2*h) → A) :
    let d := heisD1 (A := A) ⇑t (pinnedResolvedFamily (2+2*h) q
      (headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP) (4*Monoid.exponent C))
    rowScaling (sigmaPivot t.σ t.τ hfpf) (wildPivot t.σ)
      (d (columnShear (sigmaPivot t.σ t.τ hfpf) (tauCoefficient t.σ t.τ q) x)) =
      ![x .sigma, x (.wild (Certificates.x2Idx h))] := by
  exact tameSplice_ramified_reducedFox t pi hpi hsurj hA2 ht hq0 hqe hwild hfpf hodd
    (headHandlePairPrimeCorrectedW alpha h q halpha hq0 hqe j nuP)
    (headHandlePairPrimeCorrectedW_specializes alpha h q halpha hq0 hqe j nuP)
    (headHandlePairPrime_pinned_endpoint halpha hq0 hqe j nuP
      (fourMulExponent_ne_zero_and_even C).1 (fourMulExponent_ne_zero_and_even C).2) x

/-- The same ramified matrix certificate for every mobile level, charge, arbitrary two-adic
unit and handle count, including h=0. No source equation is replaced by a kernel-only claim. -/
theorem mobileSplice_ramified_reducedFox {r p : ℕ}
    (t : Marking (2+2*h) C) (pi : C →* D)
    (hpi : ∀ (c : C) (a : A), c • a = pi c • a) (hsurj : Function.Surjective pi)
    (hA2 : ∀ a : A, a+a=0) (ht : t.TameRelAt q)
    (halpha : 1 ≤ alpha) (hq0 : q≠0) (hqe : Even q)
    (eta : ℤ_[2]ˣ) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hwild : ∀ i, pi (t.x i)=1)
    (hfpf : ∀ a : A, t.τ • a=a → a=0)
    (hodd : ∀ a : A, powOmega2 t.τ • a=a)
    (x : Generator (2+2*h) → A) :
    let d := heisD1 (A := A) ⇑t (pinnedResolvedFamily (2+2*h) q
      (tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
        (MCompact.mCompactW alpha h)) (4*Monoid.exponent C))
    rowScaling (sigmaPivot t.σ t.τ hfpf) (wildPivot t.σ)
      (d (columnShear (sigmaPivot t.σ t.τ hfpf) (tauCoefficient t.σ t.τ q) x)) =
      ![x .sigma, x (.wild (Certificates.x2Idx h))] := by
  exact tameSplice_ramified_reducedFox t pi hpi hsurj hA2 ht hq0 hqe hwild hfpf hodd
    (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
    (mpcMobileTameCorrectedW_specializes hq0 hqe eta halpha nuP)
    (mpcMobileTameCorrected_endpoint hq0 hqe eta halpha nuP
      (fourMulExponent_ne_zero_and_even C).1 (fourMulExponent_ne_zero_and_even C).2) x

#print axioms tameSplice_ramified_rows
#print axioms tameSplice_ramified_reducedFox
#print axioms pairSplice_ramified_reducedFox
#print axioms mobileSplice_ramified_reducedFox

end
end GQ2.Dyadic.Instances.TameSpliceRamifiedFoxNormal
