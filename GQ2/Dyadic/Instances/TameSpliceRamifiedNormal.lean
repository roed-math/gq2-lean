/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.TameSpliceRamifiedPhase

/-!
# Ramified Fox transport through an actual projected head

The original acting group can retain wild kernel elements. Its differential is
transported along the action-compatible head projection, where wild bases are
actually one, and the complete shadow equality gives the compact-M row.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH Count Words Certificates LSquare
open Certificates.MProcyclic
attribute [local instance] Count.heisTopologicalSpace Count.heisDiscreteTopology

private theorem projectedWordLiftResolver
    {C D A : Type} [Group C] [Finite C] [Group D] [AddCommGroup A]
    [DistribMulAction D A] (pi : C →* D) (hpi : Function.Surjective pi)
    (hA2 : ∀ a : A, a+a=0) :
    ResolverLifts (omegaPinnedLevelZhatResolver (4*Monoid.exponent C)) (WordLift A D) := by
  intro p
  rw [omegaPinnedLevelZhatResolver_omega2, zpow_natCast]
  exact powOmega2_pow_eq p
    ((WordLift.orderOf_dvd_two_mul hA2
      (fun d ↦ (Monoid.order_dvd_exponent d).trans (MonoidHom.exponent_dvd hpi)) p).trans
      ⟨2, by ring⟩) (fourMulExponent_ne_zero_and_even C).1

theorem heisD1_tameSplice_mCompact_ramified_of_projected
    {C D A : Type} [Group C] [Finite C] [Group D] [Finite D]
    [AddCommGroup A] [Finite A] [DistribMulAction C A] [DistribMulAction D A]
    {alpha h q : ℕ} (t : Marking (2+2*h) C)
    (pi : C →* D) (hpi : ∀ (c : C) (a : A), c•a=pi c•a)
    (hsurj : Function.Surjective pi) (hA2 : ∀ a : A, a+a=0)
    (hq0 : q≠0) (hq : Even q)
    (hwild : ∀ i, pi (t.x i)=1)
    (hfpf : ∀ a : A, pi t.τ • a=a → a=0)
    (hodd : ∀ a : A, powOmega2 (pi t.τ) • a=a)
    (R : PWord (Generator (2+2*h))) (hspec : TameSpec.TameSpecializes (2+2*h) q R)
    (hend : IsStokesEndpoint (fun k ↦ heisToFree
      (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
      (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)) (gammaFam (2+2*h) q R k))) :
    heisD1 (A := A) ⇑t (fun k ↦ heisToFree
      (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
      (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C))
      (gammaFam (2+2*h) q (tameSplice R (Words.MCompact.mCompactW alpha h)) k)) =
    heisD1 (A := A) ⇑t (Certificates.MCompact.mCompactFam alpha h q
      (omega2Exp (4*Monoid.exponent C))) := by
  rw [← mCompact_pinned_family_eq, heisD1_map_base pi hpi, heisD1_map_base pi hpi]
  let E := omegaPinnedLevelZhatResolver (4*Monoid.exponent C)
  let E₂ := omegaPinnedLevelZtwoResolver (4*Monoid.exponent C)
  have hendH : IsStokesEndpoint (fun k ↦ heisToFree E E₂
      (gammaFam (2+2*h) q (Words.MCompact.mCompactW alpha h) k)) := by
    change IsStokesEndpoint (fun k ↦ heisToFree
      (omegaPinnedLevelZhatResolver (4*Monoid.exponent C))
      (omegaPinnedLevelZtwoResolver (4*Monoid.exponent C))
      (gammaFam (2+2*h) q (Words.MCompact.mCompactW alpha h) k))
    rw [mCompact_pinned_family_eq]
    exact Certificates.MCompact.mCompact_isStokesEndpoint hq
      (odd_omega2Exp (fourMulExponent_ne_zero_and_even C).1
        (fourMulExponent_ne_zero_and_even C).2)
  apply AddMonoidHom.ext
  intro x
  funext k
  fin_cases k
  · rfl
  · have H := heisEvalZ_tameSplice_ramified (fun i ↦ pi (t i)) x
      (0 : Generator (2+2*h) → ElemDual A) E E₂ R (Words.MCompact.mCompactW alpha h)
      (projectedWordLiftResolver pi hsurj hA2)
      (projectedWordLiftResolver pi hsurj (fun lam : ElemDual A ↦ lam.add_self_eq_zero))
      hwild hfpf hodd hend hendH hspec (tameSpecializes_mCompact hq0 hq alpha h)
      (fun p ↦ resolvedAt_omegaPinnedLevelResolvers (fourMulExponent_ne_zero_and_even C).1
        (orderOf_heisLift_dvd_four_mul hA2
          (fun d ↦ (Monoid.order_dvd_exponent d).trans (MonoidHom.exponent_dvd hsurj))) _ R)
      (fun p ↦ resolvedAt_omegaPinnedLevelResolvers (fourMulExponent_ne_zero_and_even C).1
        (orderOf_heisLift_dvd_four_mul hA2
          (fun d ↦ (Monoid.order_dvd_exponent d).trans (MonoidHom.exponent_dvd hsurj))) _
        (Words.MCompact.mCompactW alpha h))
    rw [heisEvalZ_eq_lift, heisEvalZ_eq_lift] at H
    exact congrArg HeisLift.a H

#print axioms heisD1_tameSplice_mCompact_ramified_of_projected
end
end GQ2.Dyadic

