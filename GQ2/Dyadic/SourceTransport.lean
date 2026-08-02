/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.QTwo
import GQ2.Dyadic.GammaRHom

/-!
# `SourceDataN` transport across an isomorphism  (dyadic campaign, ticket CB-TRN)

Work in progress.
-/

namespace GQ2.Dyadic.SourceTransport

open GQ2 GQ2.Dyadic GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH

/-! ## §1 Precomposition with a continuous isomorphism

Every object the degree-`n` recursion counts is a set of *continuous maps out of the source*
cut out by a *pointwise* condition, so a continuous isomorphism of sources moves all of them by
precomposition.  §1 is that single mechanism; §§2–5 apply it family by family. -/

section Precomp

variable {A B : Type} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B]

/-- Precomposition with `e : A ≃ₜ* B` is a bijection `Hom_c(B, Y) ≃ Hom_c(A, Y)`. -/
@[simps] def precompEquiv (e : A ≃ₜ* B) (Y : Type*) [Group Y] [TopologicalSpace Y] :
    ContinuousMonoidHom B Y ≃ ContinuousMonoidHom A Y where
  toFun f := f.comp (e : ContinuousMonoidHom A B)
  invFun g := g.comp (e.symm : ContinuousMonoidHom B A)
  left_inv f := ContinuousMonoidHom.ext fun b => congrArg f (e.apply_symm_apply b)
  right_inv g := ContinuousMonoidHom.ext fun a => congrArg g (e.symm_apply_apply a)

theorem precompEquiv_apply_apply (e : A ≃ₜ* B) {Y : Type*} [Group Y] [TopologicalSpace Y]
    (f : ContinuousMonoidHom B Y) (a : A) : precompEquiv e Y f a = f (e a) := rfl

/-- Precomposition on continuous *surjections* (`GQ2.ContSurj`). -/
@[simps] def contSurjEquiv (e : A ≃ₜ* B) (Y : Type*) [Group Y] [TopologicalSpace Y] :
    ContSurj B Y ≃ ContSurj A Y where
  toFun f := ⟨precompEquiv e Y f.1, f.2.comp e.surjective⟩
  invFun g := ⟨(precompEquiv e Y).symm g.1, g.2.comp e.symm.surjective⟩
  left_inv f := Subtype.ext ((precompEquiv e Y).left_inv f.1)
  right_inv g := Subtype.ext ((precompEquiv e Y).right_inv g.1)

end Precomp

/-! ## §2 Continuous cohomology under an isomorphism, for the trivial `𝔽₂`-action

The obstruction indicator `ι_Γ` (`GQ2.SectionEight.iotaB`) is a membership test against
`B²(Γ, 𝔽₂)`, so it transports as soon as the coboundary subgroup does.  Both sources carry
*their own* `DistribMulAction _ (ZMod 2)`; the actions correspond because both are trivial
(`WordCertificate.htriv` / `SourceDataN.htriv`), which is the only compatibility the differentials
need. -/

section Cohomology

variable {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
  [DistribMulAction A (ZMod 2)] [DistribMulAction B (ZMod 2)]

omit [IsTopologicalGroup A] [IsTopologicalGroup B] in
/-- **Coboundaries transport.**  If `φ` is the `δ¹` of a continuous `1`-cochain on `B`, then its
pullback along `e` is the `δ¹` of the pulled-back cochain.  Only *one* direction is proved here;
the equivalence follows by running it along `e.symm` (`mem_B2_comp_iff`). -/
theorem mem_B2_comp_of (htA : ∀ (γ : A) (m : ZMod 2), γ • m = m)
    (htB : ∀ (γ : B) (m : ZMod 2), γ • m = m) (e : A ≃ₜ* B) {φ : B × B → ZMod 2}
    (hφ : φ ∈ B2 B (ZMod 2)) : (fun p : A × A => φ (e p.1, e p.2)) ∈ B2 A (ZMod 2) := by
  obtain ⟨ψ, hψc, rfl⟩ := hφ
  refine ⟨fun a => ψ (e a), hψc.comp e.continuous_toFun, funext fun p => ?_⟩
  show p.1 • ψ (e p.2) - ψ (e (p.1 * p.2)) + ψ (e p.1)
    = e p.1 • ψ (e p.2) - ψ (e p.1 * e p.2) + ψ (e p.1)
  rw [htA, htB, map_mul e]

omit [IsTopologicalGroup A] [IsTopologicalGroup B] in
/-- **The coboundary test is invariant under transport.** -/
theorem mem_B2_comp_iff (htA : ∀ (γ : A) (m : ZMod 2), γ • m = m)
    (htB : ∀ (γ : B) (m : ZMod 2), γ • m = m) (e : A ≃ₜ* B) (φ : B × B → ZMod 2) :
    (fun p : A × A => φ (e p.1, e p.2)) ∈ B2 A (ZMod 2) ↔ φ ∈ B2 B (ZMod 2) := by
  refine ⟨fun h => ?_, mem_B2_comp_of htA htB e⟩
  have h2 := mem_B2_comp_of htB htA e.symm h
  have : (fun p : B × B => (fun r : A × A => φ (e r.1, e r.2)) (e.symm p.1, e.symm p.2)) = φ := by
    funext p; simp
  rwa [this] at h2

omit [IsTopologicalGroup A] [IsTopologicalGroup B] in
/-- **`ι_Γ` is invariant under transport** (the key naturality for `betaChi` and `QZero`). -/
theorem iotaB_comp (htA : ∀ (γ : A) (m : ZMod 2), γ • m = m)
    (htB : ∀ (γ : B) (m : ZMod 2), γ • m = m) (e : A ≃ₜ* B) (φ : B × B → ZMod 2) :
    iotaB (fun p : A × A => φ (e p.1, e p.2)) = iotaB φ := by
  have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  by_cases h : φ ∈ B2 B (ZMod 2)
  · rw [iotaB_of_mem_B2 ((mem_B2_comp_iff htA htB e φ).mpr h), iotaB_of_mem_B2 h]
  · rw [key _ fun hc => h ((mem_B2_comp_iff htA htB e φ).mp (iotaB_eq_zero_iff.mp hc)),
      key _ fun hc => h (iotaB_eq_zero_iff.mp hc)]

end Cohomology

end GQ2.Dyadic.SourceTransport
