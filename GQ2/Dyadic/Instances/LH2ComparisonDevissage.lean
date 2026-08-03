/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLSimpleDualSurjectivity
import GQ2.Dyadic.Instances.LDeltaComparison
import GQ2.Dyadic.Instances.LWordExact

/-!
# Coefficient devissage for the L degree-two comparison

This file assembles the continuous coefficient snake, the word coefficient snake, their
comparison square, and the four-term diagram chase.  It proves that simple-coefficient
surjectivity extends to every finite elementary coefficient once the genuine CD-2 tail
`H2RightExactAt` is supplied.

Thus the direct all-coefficient comparison has one precise remaining cohomological input:
surjectivity of continuous `H²` under finite elementary coefficient quotients.  No Tate
duality, Euler characteristic, or field realization is used in the assembly.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH
open ContCoh
open GQ2.Dyadic.Count
open GQ2.Dyadic.Certificates.LSqStokes

/-- The exact continuous CD-2 tail needed by elementary coefficient devissage for `GammaL`.

It is deliberately stated only for surjections of finite exponent-two modules, which is the
full strength consumed by the composition-series argument below. -/
noncomputable abbrev GammaLH2RightExactSupply (h q : ℕ) : Prop :=
  ∀ (A A'' : Type) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [DiscreteTopology A] [Finite A]
    [DistribMulAction (gamma h q : Type) A] [ContinuousSMul (gamma h q : Type) A]
    [AddCommGroup A''] [TopologicalSpace A'']
    [IsTopologicalAddGroup A''] [DiscreteTopology A''] [Finite A'']
    [DistribMulAction (gamma h q : Type) A''] [ContinuousSMul (gamma h q : Type) A'']
    (g : A →+ A'') (hg : Continuous g)
    (hgeq : ∀ (c : (gamma h q : Type)) (a : A), g (c • a) = c • g a),
    (∀ a : A, a + a = 0) → (∀ a : A'', a + a = 0) →
      Function.Surjective g → H2RightExactAt g hg hgeq

private theorem continuousSMul_comp_finite_devissage
    {G C A : Type} [Monoid G] [TopologicalSpace G]
    [Monoid C] [TopologicalSpace C] [DiscreteTopology C]
    [TopologicalSpace A] [DiscreteTopology A] [SMul C A]
    (rho : ContinuousMonoidHom G C) [SMul G A]
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a) : ContinuousSMul G A := by
  constructor
  have hfac : (fun p : G × A ↦ p.1 • p.2) =
      (fun p : C × A ↦ p.1 • p.2) ∘ (fun p : G × A ↦ (rho p.1, p.2)) := by
    funext p
    exact hcompat p.1 p.2
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

set_option maxHeartbeats 2400000 in
/-- Simple-coefficient surjectivity plus the continuous CD-2 tail makes the canonical L
continuous-to-word `H²` comparison bijective for every finite elementary coefficient with its
action pulled back from one finite target.

This is the complete coefficient-devissage assembly: the only hypothesis not already proved
for the L word is `GammaLH2RightExactSupply`. -/
theorem lModuleH2WordFlexible_bijective_of_simple_and_rightExact
    {h q : ℕ} {C : Type}
    [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom (gamma h q : Type) C)
    (hsimple : UniformSimpleH2SurjectiveSingleProvider rho)
    (hright : GammaLH2RightExactSupply h q)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := ⟨rfl⟩
    letI : DistribMulAction (gamma h q : Type) A := DistribMulAction.compHom A rho.toMonoidHom
    letI : ContinuousSMul (gamma h q : Type) A :=
      continuousSMul_comp_finite_devissage rho (by
        intro g a
        change rho g • a = rho g • a
        rfl)
    Function.Bijective
      (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hA₂
        (lUniform_wordLift_resolver hA₂)) := by
  let P : ContCoh.FiniteTwoModuleProperty (C := C) := fun B _ _ _ ↦
    ∀ hB₂ : ∀ b : B, b + b = 0,
      letI : TopologicalSpace B := ⊥
      letI : DiscreteTopology B := ⟨rfl⟩
      letI : DistribMulAction (gamma h q : Type) B :=
        DistribMulAction.compHom B rho.toMonoidHom
      letI : ContinuousSMul (gamma h q : Type) B :=
        continuousSMul_comp_finite_devissage rho (by
          intro g b
          change rho g • b = rho g • b
          rfl)
      Function.Bijective
        (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hB₂
          (lUniform_wordLift_resolver hB₂))
  refine (ContCoh.finiteTwoModuleProperty_of_simple P ?_ ?_ ?_ hA₂) hA₂
  · intro B _ _ _ _
    intro hB₂
    letI : TopologicalSpace B := ⊥
    letI : DiscreteTopology B := ⟨rfl⟩
    letI : DistribMulAction (gamma h q : Type) B :=
      DistribMulAction.compHom B rho.toMonoidHom
    letI : ContinuousSMul (gamma h q : Type) B :=
      continuousSMul_comp_finite_devissage rho (by
        intro g b
        change rho g • b = rho g • b
        rfl)
    change Function.Bijective
      (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hB₂
        (lUniform_wordLift_resolver hB₂))
    constructor
    · exact lModuleH2WordFlexible_injective rho (fun _ _ ↦ rfl)
        hB₂ (lUniform_wordLift_resolver hB₂)
    · intro y
      refine ⟨0, ?_⟩
      obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective y
      rw [map_zero]
      symm
      apply (QuotientAddGroup.eq_zero_iff _).mpr
      rw [show z = 0 from Subsingleton.elim _ _]
      exact AddSubgroup.zero_mem _
  · intro B _ _ _ hB₂ hBsimple
    intro hB₂'
    letI : TopologicalSpace B := ⊥
    letI : DiscreteTopology B := ⟨rfl⟩
    letI : DistribMulAction (gamma h q : Type) B :=
      DistribMulAction.compHom B rho.toMonoidHom
    letI : ContinuousSMul (gamma h q : Type) B :=
      continuousSMul_comp_finite_devissage rho (by
        intro g b
        change rho g • b = rho g • b
        rfl)
    change Function.Bijective
      (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hB₂'
        (lUniform_wordLift_resolver hB₂'))
    exact lModuleH2WordFlexible_bijective_of_surjective rho (fun _ _ ↦ rfl) hB₂'
      (lUniform_wordLift_resolver hB₂') (hsimple B (fun _ _ ↦ rfl) hB₂' hBsimple)
  · intro B _ _ _ _hB₂ W hWstable _hWbot _hWtop ihW ihQ
    intro hB₂
    letI : DistribMulAction C ↥W := stableSubAction W hWstable
    letI : DistribMulAction C (B ⧸ W) := stableQuotAction W hWstable
    letI : TopologicalSpace B := ⊥
    letI : DiscreteTopology B := ⟨rfl⟩
    letI : TopologicalSpace ↥W := ⊥
    letI : DiscreteTopology ↥W := ⟨rfl⟩
    letI : TopologicalSpace (B ⧸ W) := ⊥
    letI : DiscreteTopology (B ⧸ W) := ⟨rfl⟩
    letI : DistribMulAction (gamma h q : Type) B := DistribMulAction.compHom B rho.toMonoidHom
    letI : DistribMulAction (gamma h q : Type) ↥W := DistribMulAction.compHom ↥W rho.toMonoidHom
    letI : DistribMulAction (gamma h q : Type) (B ⧸ W) :=
      DistribMulAction.compHom (B ⧸ W) rho.toMonoidHom
    letI : ContinuousSMul (gamma h q : Type) B :=
      continuousSMul_comp_finite_devissage rho (by
        intro g b
        change rho g • b = rho g • b
        rfl)
    letI : ContinuousSMul (gamma h q : Type) ↥W :=
      continuousSMul_comp_finite_devissage rho (by
        intro g w
        change rho g • w = rho g • w
        rfl)
    letI : ContinuousSMul (gamma h q : Type) (B ⧸ W) :=
      continuousSMul_comp_finite_devissage rho (by
        intro g b
        change rho g • b = rho g • b
        rfl)
    let f : ↥W →+ B := W.subtype
    let g : B →+ B ⧸ W := QuotientAddGroup.mk' W
    have hfG : ∀ (c : (gamma h q : Type)) (w : ↥W), f (c • w) = c • f w := fun _ _ ↦ rfl
    have hgG : ∀ (c : (gamma h q : Type)) (b : B), g (c • b) = c • g b := fun _ _ ↦ rfl
    have hfC : ∀ (c : C) (w : ↥W), f (c • w) = c • f w := fun _ _ ↦ rfl
    have hgC : ∀ (c : C) (b : B), g (c • b) = c • g b := fun _ _ ↦ rfl
    let S : FiniteDiscreteCoeffSES (G := (gamma h q : Type)) (A' := ↥W) (A := B)
        (A'' := B ⧸ W) := {
      f := f
      g := g
      f_equivariant := hfG
      g_equivariant := hgG
      f_injective := Subtype.val_injective
      g_surjective := QuotientAddGroup.mk'_surjective W
      range_eq_ker := by
        rw [show f.range = W by ext b; simp [f]]
        exact (QuotientAddGroup.ker_mk' W).symm
    }
    have hW₂ : ∀ w : ↥W, w + w = 0 := two_torsion_sub W hB₂
    have hQ₂ : ∀ x : B ⧸ W, x + x = 0 := two_torsion_quot W hB₂
    let hresW := lUniform_wordLift_resolver (h := h) (q := q) (C := C) hW₂
    let hresB := lUniform_wordLift_resolver (h := h) (q := q) (C := C) hB₂
    let hresQ := lUniform_wordLift_resolver (h := h) (q := q) (C := C) hQ₂
    let c := fun i ↦ rho (gammaGen (2 * h + 1) q (Words.LSq.lSqW h) i)
    let w := lSqFam h q (omega2Exp (4 * Monoid.exponent C))
    have hr : ∀ k, FreeGroup.lift c (w k) = 1 := fun k ↦
      lower_rel (A := B) rho (fun _ ↦ rfl)
        (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (Words.LSq.lSqW h)) hresB k
    have hrightS : H2RightExactAt S.g S.continuous_g S.g_equivariant :=
      hright B (B ⧸ W) S.g S.continuous_g S.g_equivariant hB₂ hQ₂ S.g_surjective
    have ihW' := ihW hW₂
    have ihQ' := ihQ hQ₂
    change Function.Bijective
      (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hW₂ hresW) at ihW'
    change Function.Bijective
      (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hQ₂ hresQ) at ihQ'
    change Function.Bijective
      (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hB₂ hresB)
    exact ContCoh.fourTermComparison_bijective
      S.delta1
      (mapCoeff2 S.f S.continuous_f S.f_equivariant)
      (mapCoeff2 S.g S.continuous_g S.g_equivariant)
      (S.wordDelta1 c w hfC hgC hr)
      (S.wordH2MapF c w hfC)
      (S.wordH2MapG c w hgC)
      (lSourceH1Equiv rho (fun _ _ ↦ rfl) hQ₂ hresQ)
      (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hW₂ hresW)
      (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hB₂ hresB)
      (lModuleH2WordFlexible rho (fun _ _ ↦ rfl) hQ₂ hresQ)
      (fun x ↦ (l_delta1_comparison S rho (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        (fun _ _ ↦ rfl) hW₂ hQ₂ hresW hresB hresQ hfC hgC x).symm)
      (fun x ↦ (lModuleH2WordFlexible_natural rho (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        hW₂ hB₂ hresW hresB S.f S.f_equivariant hfC x).symm)
      (fun x ↦ (lModuleH2WordFlexible_natural rho (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        hB₂ hQ₂ hresB hresQ S.g S.g_equivariant hgC x).symm)
      S.exact_left S.exact_middle
      (S.wordH2_exact_left c w hfC hgC hr)
      (S.wordH2_exact_middle c w hfC hgC)
      hrightS (lSourceH1Equiv rho (fun _ _ ↦ rfl) hQ₂ hresQ).bijective ihW' ihQ'

end

end GQ2.Dyadic.LSquare
