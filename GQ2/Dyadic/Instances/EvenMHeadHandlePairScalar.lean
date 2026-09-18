/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.TameRenamingStokes
import GQ2.Dyadic.Instances.EvenMHeadHandlePairNielsenStokes
import GQ2.Dyadic.Instances.N0M0ScalarStokes
import GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalizedUnramified

/-!
# Scalar Stokes duality for the all-rank head-handle pair source

The pair exchange is an involutive alphabet permutation. Full-family Nielsen
transport gives Stokes duality from the established compact-M scalar theorem.
The generic tau-fixing renaming comparison restores the canonical tame row.

The first theorem states the actual resolved-word death premise explicitly.
The pinned wrapper discharges it when tau and the wild generators are one;
only sigma may remain a nontrivial group element, acting trivially on A.
-/

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairScalar
noncomputable section
open GQ2 GQ2.Dyadic GQ2.FoxH Count Certificates Words
open Instances.EvenMHeadHandlePairSource Instances.EvenMHeadHandlePairCore
open Instances.EvenMHeadHandlePairNormalize
open Instances.EvenMHeadHandlePairNormalizedUnramified

/-- Scalar duality at any resolver with the required finite omega representative. -/
theorem headHandlePairStokesDuality_scalar
    {h alpha q : ℕ} {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking (2+2*h) C) (j : Fin h)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hA₂ : ∀ a : A, a+a=0)
    (htriv : ∀ (g : Generator (2+2*h)) (a : A), t g • a=a)
    (htau : t.τ=1) (hq : Even q) (hα : 2≤alpha)
    (hE : E omega2=(omega2Exp (4*Monoid.exponent C):ℤ))
    (hR : PWord.evalZ ⇑t E E₂ (headHandlePairCompactW alpha j)=1) :
    StokesDuality ⇑t (fun k ↦ heisToFree E E₂
      (gammaFam (2+2*h) q (headHandlePairCompactW alpha j) k)) A := by
  let f : Generator (2+2*h) ≃ Generator (2+2*h) := (headHandlePairSwap j).symm
  have hf : f .tau=.tau := by simp [f, headHandlePairSwap_symm]
  let s : Marking (2+2*h) C := ⟨fun g ↦ t (f g)⟩
  have hsτ : s.τ=1 := by change t (f .tau)=1; rw [hf]; exact htau
  have hst : s.TameRelAt q := by simp [Marking.TameRelAt, conjR, hsτ]
  have hsact : ∀ (g : Generator (2+2*h)) (a : A), s g • a=a := fun g ↦ htriv (f g)
  have hw : headHandlePairCompactW alpha j =
      PWord.subst (fun g ↦ .gen (f g)) (MCompact.mCompactW alpha h) :=
    headHandlePairCompactW_eq_nielsenBackward j
  have hMsE : PWord.evalZ ⇑s E E₂ (MCompact.mCompactW alpha h)=1 := by
    rw [hw, PWord.evalZ_subst] at hR
    exact hR
  have hMs : PWord.evalZ ⇑s
      (fun _ ↦ (omega2Exp (4*Monoid.exponent C):ℤ))
      (fun _ ↦ (omega2Exp (4*Monoid.exponent C):ℤ)) (MCompact.mCompactW alpha h)=1 := by
    rw [← PWord.evalZ_eq_of_isOmega2Only (⇑s) hE _ (MCompact.isOmega2Only_mCompact alpha h)]
    exact hMsE
  have HC := mCompactStokesDuality_scalar s hA₂ hq hst
    (fun i ↦ hsact (.wild i)) (hsact .tau) (hsact .sigma) hα hMs
  have hfamily : (fun k ↦ heisToFree E E₂ (gammaFam (2+2*h) q (MCompact.mCompactW alpha h) k)) =
      MCompact.mCompactFam alpha h q (omega2Exp (4*Monoid.exponent C)) := by
    rw [mCompactFam_eq_gammaFam]
    funext k
    exact PWord.evalZ_eq_of_isOmega2Only FreeGroup.of hE _
      (isOmega2Only_gammaFam _ _ (MCompact.isOmega2Only_mCompact alpha h) k)
  have hend : IsStokesEndpoint (fun k ↦ heisToFree E E₂
      (gammaFam (2+2*h) q (MCompact.mCompactW alpha h) k)) := by
    rw [hfamily]
    exact MCompact.mCompact_isStokesEndpoint hq
      (odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
        (fourMulExponent_ne_zero_and_even C).2)
  have Hfull : StokesDuality ⇑t (fun k ↦ heisToFree E E₂
      (PWord.subst (fun g ↦ .gen (f g)) (gammaFam (2+2*h) q (MCompact.mCompactW alpha h) k))) A := by
    apply (stokesDuality_heisToFree_subst_iff E E₂ (⇑t) _
      (fun g ↦ .gen (f g)) (fun g ↦ .gen (f.symm g))
      (by intro g; simp [heisToFree]) (by intro g; simp [heisToFree]) hend).mpr
    have hc : freeSubstMark (⇑t) (fun g ↦ heisToFree E E₂ (.gen (f g))) = ⇑s := by
      funext g
      simp [freeSubstMark, heisToFree, s]
    rw [hc, hfamily]
    exact HC
  rw [hw]
  exact stokesDuality_gammaFam_subst_gen_of_trivial_action t E E₂ hA₂ htriv hq f hf _ Hfull

/-- The pinned scalar supply with actual wild-trivial and tau-trivial marking. -/
theorem headHandlePairStokesDuality_pinned_scalar
    {h alpha q : ℕ} {C A : Type} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A]
    (t : Marking (2+2*h) C) (j : Fin h)
    (hA₂ : ∀ a : A, a+a=0) (hwild : ∀ i, t.x i=1)
    (htau : t.τ=1) (hq : Even q) (hα : 2≤alpha)
    (hσ : ∀ a : A, t.σ • a=a) :
    StokesDuality ⇑t (fun k ↦ heisToFree
      (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
      (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C))
      (gammaFam (2+2*h) q (headHandlePairCompactW alpha j) k)) A := by
  apply headHandlePairStokesDuality_scalar t j _ _ hA₂ ?_ htau hq hα
    (omegaPinnedLevelZhatResolver_omega2 _)
    (evalZ_headHandlePair_of_wild_tau_one t j _ _ hwild htau)
  intro g a
  cases g with
  | sigma => exact hσ a
  | tau => change t.τ • a=a; rw [htau, one_smul]
  | wild i => change t.x i • a=a; rw [hwild, one_smul]

#print axioms headHandlePairStokesDuality_scalar
#print axioms headHandlePairStokesDuality_pinned_scalar

end
end GQ2.Dyadic.Instances.EvenMHeadHandlePairScalar

