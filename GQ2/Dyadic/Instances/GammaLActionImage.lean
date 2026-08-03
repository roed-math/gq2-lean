/-
Copyright (c) 2026 Geoffrey Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Roe
-/
import GQ2.Dyadic.Instances.GammaLTateDirect
import GQ2.Dyadic.Instances.LEvenQStokes
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

/-- The canonical `GammaL` marking with codomain restricted to the actual finite action image. -/
noncomputable def finiteActionImageMarking (h q : ℕ) (M : Type)
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M] :
    Marking (2 * h + 1) (FiniteActionImage h q M) :=
  ⟨finiteActionImageGenerators h q M⟩

@[simp] theorem finiteActionImageMarking_apply
    {h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    (g : Generator (2 * h + 1)) :
    finiteActionImageMarking h q M g = finiteActionImageGenerators h q M g := rfl

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

/-- Both intrinsic `L_sq` relators die in the canonical action image.  This is presentation
death, before choosing any integer resolver for the profinite exponents. -/
theorem finiteActionImageGenerators_relator_death
    {h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    (k : Fin 2) :
    PWord.eval (finiteActionImageGenerators h q M)
      (gammaFam (2 * h + 1) q (lSqW h) k) = 1 :=
  (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h)).rel
    (finiteActionImageHom h q M) k

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

/-- The action image acts faithfully: an element fixing every coefficient is the identity. -/
theorem finiteActionImage_eq_one_of_smul_eq
    {h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    (g : FiniteActionImage h q M) (hg : ∀ m : M, g • m = m) : g = 1 := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  ext m
  exact hg m

set_option maxHeartbeats 1200000 in
/-- In the unramified simple branch, the degree-one core of the canonical action-image marking
is automatically Roe-admissible for every tame exponent `q`.  Lemma 5.12 kills every wild
action, and faithfulness of the action image turns that and the unramified `tau` hypothesis into
literal triviality.  Roe's `q = 2` tame relation and both wild-core clauses then follow directly. -/
theorem finiteActionImage_core_admissibleR
    {h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0)
    (hsimple : IsSimpleModTwo (gamma h q : Type) M)
    (hτ : ∀ m : M, gammaGen (2 * h + 1) q (lSqW h) .tau • m = m) :
    (Marking.toQ2 (Certificates.LSq.coreMarking
      (finiteActionImageMarking h q M))).AdmissibleR := by
  let t := finiteActionImageMarking h q M
  let tc := Marking.toQ2 (Certificates.LSq.coreMarking t)
  have hwild : ∀ (i : Fin (2 * h + 1 + 1)) (m : M), t.x i • m = m :=
    finiteActionImage_wild_smul hM₂ hsimple
  have hτ' : ∀ m : M, t.τ • m = m := by
    intro m
    exact hτ m
  have hwild_one : ∀ i : Fin (2 * h + 1 + 1), t.x i = 1 :=
    fun i ↦ finiteActionImage_eq_one_of_smul_eq (t.x i) (hwild i)
  have hτ_one : t.τ = 1 := finiteActionImage_eq_one_of_smul_eq t.τ hτ'
  have hxcore : ∀ i : Fin 2, t (coreLetter h i) = 1 := by
    intro i
    change t.x _ = 1
    exact hwild_one _
  have hx0 : tc.x₀ = 1 := by
    change t (coreLetter h 0) = 1
    exact hxcore 0
  have hx1 : tc.x₁ = 1 := by
    change t (coreLetter h 1) = 1
    exact hxcore 1
  have hτc_one : tc.τ = 1 := by
    exact hτ_one
  have ht : tc.TameRel := by
    change GQ2.conjP t.τ t.σ = t.τ ^ (2 : ℕ)
    rw [hτ_one]
    simp [GQ2.conjP]
  have hw : tc.WildRelR := by
    apply Marking.wildRelR_of_trivial_wild tc hx0 hx1
    rw [hτc_one]
    unfold GQ2.powOmega2
    simp
  have hgen : tc.Generates := by
    rw [Marking.Generates]
    apply top_unique
    rw [← finiteActionImageGenerators_generate (h := h) (q := q) (M := M)]
    apply Subgroup.closure_mono
    rintro _ ⟨g, rfl⟩
    change t g ∈ {tc.σ, tc.τ, tc.x₀, tc.x₁}
    cases g with
    | sigma => simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inl rfl
    | tau => simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inr (Or.inl rfl)
    | wild i =>
      have hi : t (.wild i) = 1 := hwild_one i
      rw [hi, hx0]
      simp
  have hcore : tc.Pro2Core := by
    rw [Marking.Pro2Core, hx0, hx1]
    have hbot : Subgroup.normalClosure ({1, 1} : Set (FiniteActionImage h q M)) = ⊥ := by
      rw [eq_bot_iff]
      exact Subgroup.normalClosure_le_normal (by simp)
    rw [hbot]
    exact IsPGroup.of_bot
  exact ⟨hgen, ht, hw, hcore⟩

set_option maxHeartbeats 1200000 in
/-- Roe's `q = 2` Stokes theorem on the action image of an arbitrary `GammaL(h,q)` coefficient.
The target stays fixed while only the certificate's tame exponent is specialized to `2`. -/
theorem finiteActionImage_stokesDuality_roe_unramified_simple
    {h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0)
    (hsimple : IsSimpleModTwo (gamma h q : Type) M)
    (hτ : ∀ m : M, gammaGen (2 * h + 1) q (lSqW h) .tau • m = m) :
    StokesDuality (finiteActionImageGenerators h q M)
      (lSqFam h 2
        (omega2Exp (4 * Monoid.exponent (FiniteActionImage h q M)))) M := by
  let t := finiteActionImageMarking h q M
  have hadm := finiteActionImage_core_admissibleR hM₂ hsimple hτ
  have hwild : ∀ (i : Fin (2 * h + 1 + 1)) (m : M), t.x i • m = m :=
    finiteActionImage_wild_smul hM₂ hsimple
  have hτ' : ∀ m : M, t.τ • m = m := by
    intro m
    exact hτ m
  exact lSqStokesDuality_uniform_unramified_of_roe_core t
    hadm.2.1 hadm.2.2.1 hadm.1 hadm.2.2.2 hM₂ hwild hτ'

set_option maxHeartbeats 1200000 in
/-- The direct unramified-simple Stokes theorem for the canonical `GammaL(h,q)` action marking
at every even tame exponent.  Its finite target is exactly the action image, so the uniform
resolver is chosen using that target's exponent and no extraneous ambient automorphisms enter
the statement. -/
theorem finiteActionImage_stokesDuality_unramified_simple
    {h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0)
    (hsimple : IsSimpleModTwo (gamma h q : Type) M)
    (hτ : ∀ m : M, gammaGen (2 * h + 1) q (lSqW h) .tau • m = m)
    (hq : Even q) :
    StokesDuality (finiteActionImageGenerators h q M)
      (lSqFam h q
        (omega2Exp (4 * Monoid.exponent (FiniteActionImage h q M)))) M := by
  let t := finiteActionImageMarking h q M
  have hτ' : ∀ m : M, t.τ • m = m := by
    intro m
    exact hτ m
  have hroe := finiteActionImage_stokesDuality_roe_unramified_simple hM₂ hsimple hτ
  exact (stokesDuality_lSqFam_all_even_congr_unram
    (q := 2) (r := q) t hM₂ hτ' (by norm_num) hq).mp hroe

end

end GQ2.Dyadic.LSquare
