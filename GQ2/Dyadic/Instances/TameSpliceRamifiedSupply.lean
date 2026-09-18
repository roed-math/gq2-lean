/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.TameShadowRamified
import GQ2.Dyadic.Instances.OmegaPinnedLevelResolver
import GQ2.Dyadic.Instances.EvenMRamifiedPairing
import GQ2.Dyadic.Instances.StokesEndpointSubstitution

/-!
# Uniform ramified supply for tame splicing

The structural word may be arbitrary. Tame specialization and its mod-two endpoint are
the only word-specific inputs to ramified transfer. The fixed compact-M template supplies
the analytic conclusion for every handle rank, without a selected handle or coefficient
dependent word. The resolver level is `4 * exponent C`.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.Certificates.MProcyclic

attribute [local instance] Count.heisTopologicalSpace Count.heisDiscreteTopology

/-- A tame-specializing word dies in any profinite tame marking whose wild entries are one. -/
theorem eval_eq_one_of_tameSpecializes_of_wild_eq_one
    {n q : ℕ} {R : PWord (Generator n)}
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (t : Marking n G) (ht : t.TameRelAt q) (hwild : ∀ i, t.x i = 1)
    (hspec : TameSpec.TameSpecializes n q R) : t.eval R = 1 := by
  have ht' : conjP t.τ t.σ = t.τ ^ q := ht
  let f : ContinuousMonoidHom (Tq q) G := tqClassify q (ProfiniteGrp.of G) ht'
  have hmark : (tameMarking n q).map (⇑f) = t := by
    ext a
    cases a with
    | sigma => exact tqClassify_tqSigma q (ProfiniteGrp.of G) ht'
    | tau => exact tqClassify_tqTau q (ProfiniteGrp.of G) ht'
    | wild i => exact (map_one f).trans (hwild i).symm
  have H := congrArg (fun x ↦ f x) hspec
  rw [Marking.map_eval, hmark, map_one] at H
  exact H

/-- No resolver premises remain in ramified gluing at the pinned finite level. -/
theorem stokesDuality_tameSplice_ramified_pinned_iff
    {C A : Type} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A] {n q : ℕ}
    (c : Generator n → C) (R H : PWord (Generator n))
    (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ i, c (.wild i) = 1)
    (hfpf : ∀ a : A, c .tau • a = a → a = 0)
    (hodd : ∀ a : A, powOmega2 (c .tau) • a = a)
    (hendR : IsStokesEndpoint (fun k ↦ heisToFree
      (omegaPinnedLevelZhatResolver (4 * Monoid.exponent C))
      (omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C)) (gammaFam n q R k)))
    (hendH : IsStokesEndpoint (fun k ↦ heisToFree
      (omegaPinnedLevelZhatResolver (4 * Monoid.exponent C))
      (omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C)) (gammaFam n q H k)))
    (hspecR : TameSpec.TameSpecializes n q R)
    (hspecH : TameSpec.TameSpecializes n q H) :
    StokesDuality c (fun k ↦ heisToFree
      (omegaPinnedLevelZhatResolver (4 * Monoid.exponent C))
      (omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C))
      (gammaFam n q (tameSplice R H) k)) A ↔
    StokesDuality c (fun k ↦ heisToFree
      (omegaPinnedLevelZhatResolver (4 * Monoid.exponent C))
      (omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C)) (gammaFam n q H k)) A := by
  apply stokesDuality_tameSplice_ramified_iff c _ _ R H
    (omegaPinnedLevelZhatResolver_fourMulExponent_wordLift hA₂)
    (omegaPinnedLevelZhatResolver_fourMulExponent_wordLift
      (fun lam : ElemDual A ↦ lam.add_self_eq_zero))
    hwild hfpf hodd hendR hendH hspecR hspecH
  all_goals
    intro p
    exact resolvedAt_omegaPinnedLevelResolvers (fourMulExponent_ne_zero_and_even C).1
      (orderOf_heisLift_dvd_four_mul hA₂ (fun c : C ↦ Monoid.order_dvd_exponent c)) _ _

/-- The compact-M family at any pinned level is its familiar constant-omega family. -/
theorem mCompact_pinned_family_eq_level (α h q N : ℕ) :
    (fun k ↦ heisToFree (omegaPinnedLevelZhatResolver N)
      (omegaPinnedLevelZtwoResolver N)
      (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW α h) k)) =
      Certificates.MCompact.mCompactFam α h q (omega2Exp N) := by
  funext k
  have H := PWord.evalZ_eq_of_isOmega2Only (FreeGroup.of : Generator (2 + 2 * h) → _)
    (E := omegaPinnedLevelZhatResolver N)
    (E₂ := omegaPinnedLevelZtwoResolver N)
    (F := fun _ ↦ (omega2Exp N : ℤ))
    (F₂ := fun _ ↦ (omega2Exp N : ℤ))
    (omegaPinnedLevelZhatResolver_omega2 _)
    (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW α h) k)
    (Count.isOmega2Only_gammaFam (2 + 2 * h) q
      (Words.MCompact.isOmega2Only_mCompact α h) k)
  fin_cases k <;> exact H

/-- Specialization to the coefficient-independent Heisenberg level. -/
theorem mCompact_pinned_family_eq {C : Type} [Group C] [Finite C] (α h q : ℕ) :
    (fun k ↦ heisToFree (omegaPinnedLevelZhatResolver (4 * Monoid.exponent C))
      (omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C))
      (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW α h) k)) =
      Certificates.MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent C)) :=
  mCompact_pinned_family_eq_level α h q _

/-- Compact M supplies ramified Stokes for every structural tame endpoint word. -/
theorem stokesDuality_tameSplice_mCompact_ramified
    {C A : Type} [Group C] [Finite C] [AddCommGroup A] [Finite A]
    [DistribMulAction C A] {α h q : ℕ}
    (t : Marking (2 + 2 * h) C) (R : PWord (Generator (2 + 2 * h)))
    (hA₂ : ∀ a : A, a + a = 0) (hq0 : q ≠ 0) (hqe : Even q)
    (ht : t.TameRelAt q) (hwild : ∀ i, t.x i = 1)
    (hfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hodd : ∀ a : A, powOmega2 t.τ • a = a)
    (hendR : IsStokesEndpoint (fun k ↦ heisToFree
      (omegaPinnedLevelZhatResolver (4 * Monoid.exponent C))
      (omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C))
      (gammaFam (2 + 2 * h) q R k)))
    (hspecR : TameSpec.TameSpecializes (2 + 2 * h) q R) :
    StokesDuality ⇑t (fun k ↦ heisToFree
      (omegaPinnedLevelZhatResolver (4 * Monoid.exponent C))
      (omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C))
      (gammaFam (2 + 2 * h) q (tameSplice R (Words.MCompact.mCompactW α h)) k)) A := by
  have hN := (fourMulExponent_ne_zero_and_even C).1
  have he := odd_omega2Exp hN (fourMulExponent_ne_zero_and_even C).2
  have hsH := Count.tameSpecializes_mCompact hq0 hqe α h
  have hendH : IsStokesEndpoint (fun k ↦ heisToFree
      (omegaPinnedLevelZhatResolver (4 * Monoid.exponent C))
      (omegaPinnedLevelZtwoResolver (4 * Monoid.exponent C))
      (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW α h) k)) := by
    rw [mCompact_pinned_family_eq]
    exact Certificates.MCompact.mCompact_isStokesEndpoint hqe he
  apply (stokesDuality_tameSplice_ramified_pinned_iff ⇑t R
    (Words.MCompact.mCompactW α h) hA₂ hwild hfpf hodd hendR hendH hspecR hsH).mpr
  rw [mCompact_pinned_family_eq]
  have hwildA : ∀ i (a : A), t.x i • a = a := by
    intro i a
    rw [hwild, one_smul]
  apply mCompactStokesDuality_ramified_of_separation t hA₂ hqe ht hwildA hfpf hodd
  · letI : TopologicalSpace C := ⊥
    letI : DiscreteTopology C := ⟨rfl⟩
    have hres := PWord.resolvedAt_of_isOmega2Only ⇑t
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
      (fun _ ↦ (omega2Exp (4 * Monoid.exponent C) : ℤ))
      (fun c ↦ PWord.zpowHat_omega2_zpow hN
        ((Monoid.order_dvd_exponent c).trans ⟨4, by ring⟩)) _
      (Words.MCompact.isOmega2Only_mCompact α h)
    rw [← PWord.eval_eq_evalZ _ _ _ _ hres]
    exact eval_eq_one_of_tameSpecializes_of_wild_eq_one t ht hwild hsH
  · exact MCompactRam.mCompactFam_normal_pairing_separates_left t hA₂ hwildA hfpf hodd

#print axioms eval_eq_one_of_tameSpecializes_of_wild_eq_one
#print axioms stokesDuality_tameSplice_ramified_pinned_iff
#print axioms mCompact_pinned_family_eq
#print axioms stokesDuality_tameSplice_mCompact_ramified

end
end GQ2.Dyadic
