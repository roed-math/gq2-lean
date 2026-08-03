/-
Copyright (c) 2026 Geoffrey Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Roe
-/
import GQ2.Dyadic.Instances.GammaLTateDirect
import GQ2.Dyadic.Instances.LRoeStokesDuality

/-!
# The finite action image of a `GammaL` coefficient

The full additive automorphism group of a finite coefficient is a convenient canonical target,
but its marked generators need not generate it.  This file restricts the canonical action hom to
its actual finite image.  The restricted hom is surjective, so the admissible-presentation API
supplies both algebraic generation and the pro-`2` wild closure.  On a simple elementary
coefficient, Lemma 5.12 then makes every wild generator act trivially.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic.Count
open GQ2.Dyadic.Words.LSq GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes

noncomputable abbrev FiniteActionImage (h q : ℕ) (M : Type)
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M] : Type :=
  ↥((finiteActionHom (G := (gamma h q : Type)) (M := M)).toMonoidHom.range)

noncomputable def finiteActionImageHom (h q : ℕ) (M : Type)
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M] :
    ContinuousMonoidHom ((gamma h q : Type)) (FiniteActionImage h q M) where
  toMonoidHom :=
    (finiteActionHom (G := (gamma h q : Type)) (M := M)).toMonoidHom.rangeRestrict
  continuous_toFun :=
    (finiteActionHom (G := (gamma h q : Type)) (M := M)).continuous_toFun.subtype_mk _

noncomputable def finiteActionImageGenerators (h q : ℕ) (M : Type)
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M] :
    Generator (2 * h + 1) → FiniteActionImage h q M :=
  fun i ↦ finiteActionImageHom h q M (gammaGen (2 * h + 1) q (lSqW h) i)

@[simp] theorem finiteActionImageHom_smul
    {h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    (g : (gamma h q : Type)) (m : M) : finiteActionImageHom h q M g • m = g • m := rfl

theorem finiteActionImageGenerators_generate
    {h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M] :
    Subgroup.closure (Set.range (finiteActionImageGenerators h q M)) = ⊤ := by
  exact closure_range_lower_eq_top (finiteActionImageHom h q M) (fun _ ↦ rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h))
    (finiteActionHom (G := (gamma h q : Type)) (M := M)).toMonoidHom.rangeRestrict_surjective

theorem finiteActionImageGenerators_isWildTwo
    {h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M] :
    IsWildTwo (wildAlphabet (2 * h + 1)) (finiteActionImageGenerators h q M) := by
  exact isWildTwo_of_gammaGen (finiteActionImageHom h q M)
    (finiteActionHom (G := (gamma h q : Type)) (M := M)).toMonoidHom.rangeRestrict_surjective
    (fun _ ↦ rfl)

theorem isSimpleModTwo_finiteActionImage
    {h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    (hsimple : IsSimpleModTwo (gamma h q : Type) M) :
    IsSimpleModTwo (FiniteActionImage h q M) M := by
  refine ⟨hsimple.1, fun W hW ↦ hsimple.2 W ?_⟩
  intro g m hm
  rw [← finiteActionImageHom_smul (h := h) (q := q) g m]
  exact hW (finiteActionImageHom h q M g) m hm

theorem finiteActionImage_wild_smul
    {h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0) (hsimple : IsSimpleModTwo (gamma h q : Type) M) :
    ∀ (i : Fin (2 * h + 1 + 1)) (m : M),
      finiteActionImageGenerators h q M (.wild i) • m = m := by
  let L : Subgroup (FiniteActionImage h q M) := Subgroup.normalClosure
    (finiteActionImageGenerators h q M '' wildAlphabet (2 * h + 1))
  have htriv := lemma_5_12 hM₂ (isSimpleModTwo_finiteActionImage hsimple) L
    Subgroup.normalClosure_normal finiteActionImageGenerators_isWildTwo
  intro i m
  apply htriv (finiteActionImageGenerators h q M (.wild i))
    (Subgroup.subset_normalClosure ?_) m
  exact ⟨.wild i, ⟨i, rfl⟩, rfl⟩

end

end GQ2.Dyadic.LSquare
