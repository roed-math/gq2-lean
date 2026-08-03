/-
Copyright (c) 2026 Geoffrey Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Roe
-/
import GQ2.Dyadic.Instances.GammaLTateDirect
import GQ2.Dyadic.Instances.LEvenQStokes
import GQ2.Dyadic.Instances.LRoeStokesDuality
import GQ2.Dyadic.Instances.LRamifiedStokes

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

/-- The intrinsic tame relator of `GammaL(h,q)` gives the q-parametric tame equation on its
canonical finite action image. -/
theorem finiteActionImage_tameRelAt
    {h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M] :
    (finiteActionImageMarking h q M).TameRelAt q := by
  let t := finiteActionImageMarking h q M
  have hrel := finiteActionImageGenerators_relator_death
    (h := h) (q := q) (M := M) (0 : Fin 2)
  change PWord.eval ⇑t (Certificates.tameRelW (2 * h + 1) q) = 1 at hrel
  rw [← Marking.eval_def, Certificates.eval_tameRelW] at hrel
  exact mul_inv_eq_one.mp hrel

set_option maxHeartbeats 1200000 in
/-- On a simple elementary coefficient, the two-primary part of the ramified tame generator
acts trivially.  Its fixed space is stable under `sigma` by the q-parametric tame relation,
under `tau` by commutation, and under every wild generator by Lemma 5.12. -/
theorem finiteActionImage_tau_powOmega2_smul_trivial
    {h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0) (hsimple : IsSimpleModTwo (gamma h q : Type) M) :
    ∀ m : M, powOmega2 (finiteActionImageMarking h q M).τ • m = m := by
  let t := finiteActionImageMarking h q M
  have ht : t.TameRelAt q := finiteActionImage_tameRelAt
  have hwild : ∀ (i : Fin (2 * h + 1 + 1)) (m : M), t.x i • m = m :=
    finiteActionImage_wild_smul hM₂ hsimple
  refine pow2_smul_trivial_of_stable hM₂ (isSimpleModTwo_finiteActionImage hsimple)
    (powOmega2 t.τ) (isPGroup_zpowers_powOmega2 t.τ) ?_
  have hσ : ∀ v : M, powOmega2 t.τ • v = v →
      powOmega2 t.τ • (t.σ • v) = t.σ • v :=
    fun v hv ↦ powOmega2_fixed_sigma_stable_of_tameRelAt t ht hv
  have hτ : ∀ v : M, powOmega2 t.τ • v = v →
      powOmega2 t.τ • (t.τ • v) = t.τ • v := by
    intro v hv
    have hcomm : powOmega2 t.τ * t.τ = t.τ * powOmega2 t.τ := by
      rw [powOmega2]
      exact ((Commute.refl t.τ).pow_left _).eq
    rw [← mul_smul, hcomm, mul_smul, hv]
  let S : Subgroup (FiniteActionImage h q M) :=
    { carrier := {c | ∀ v : M, powOmega2 t.τ • v = v →
          powOmega2 t.τ • (c • v) = c • v}
      one_mem' := fun v hv ↦ by rwa [one_smul]
      mul_mem' := fun {a b} ha hb v hv ↦ by rw [mul_smul]; exact ha _ (hb v hv)
      inv_mem' := fun {a} ha v hv ↦ by
        let W : AddSubgroup M :=
          { carrier := {w | powOmega2 t.τ • w = w}
            zero_mem' := smul_zero _
            add_mem' := fun {x y} hx hy ↦ by
              show powOmega2 t.τ • (x + y) = x + y
              rw [smul_add, hx, hy]
            neg_mem' := fun {x} hx ↦ by
              show powOmega2 t.τ • (-x) = -x
              rw [smul_neg, hx] }
        have hφinj : Function.Injective
            (fun u : W ↦ (⟨a • u.1, ha u.1 u.2⟩ : W)) := by
          intro x y hxy
          exact Subtype.ext (MulAction.injective a (congrArg Subtype.val hxy))
        obtain ⟨⟨u, hu⟩, hux⟩ :=
          (Finite.injective_iff_surjective.mp hφinj) ⟨v, hv⟩
        have huv : a • u = v := congrArg Subtype.val hux
        rw [show a⁻¹ • v = u from by rw [← huv, inv_smul_smul]]
        exact hu }
  have hgenS : Subgroup.closure (Set.range (finiteActionImageGenerators h q M)) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    cases g with
    | sigma => exact hσ
    | tau => exact hτ
    | wild i =>
        intro v hv
        change powOmega2 t.τ • (t.x i • v) = t.x i • v
        rw [hwild i v]
        exact hv
  rw [finiteActionImageGenerators_generate] at hgenS
  exact fun c ↦ hgenS (Subgroup.mem_top c)

/-- The intrinsic `L_sq` relator death agrees with the uniform integer resolver used by the
ramified Stokes complex. -/
theorem finiteActionImage_lSq_relator_death_resolved
    {h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M] :
    PWord.evalZ (finiteActionImageGenerators h q M)
      (fun _ ↦ (omega2Exp
        (4 * Monoid.exponent (FiniteActionImage h q M)) : ℤ))
      (fun _ ↦ (omega2Exp
        (4 * Monoid.exponent (FiniteActionImage h q M)) : ℤ))
      (lSqW h) = 1 := by
  let C := FiniteActionImage h q M
  let N := 4 * Monoid.exponent C
  have hN : N ≠ 0 := (fourMulExponent_ne_zero_and_even C).1
  have hord : ∀ c : C, orderOf c ∣ N := by
    intro c
    exact (Monoid.order_dvd_exponent c).trans (by
      simpa [N, mul_comm] using dvd_mul_right (Monoid.exponent C) 4)
  have hresolved : PWord.ResolvedAt (finiteActionImageGenerators h q M)
      (fun _ ↦ (omega2Exp N : ℤ)) (fun _ ↦ (omega2Exp N : ℤ)) (lSqW h) :=
    PWord.resolvedAt_of_isOmega2Only _ _ _
      (fun c ↦ PWord.zpowHat_omega2_zpow hN (hord c)) _ (isOmega2Only_lSq h)
  have hrel := finiteActionImageGenerators_relator_death
    (h := h) (q := q) (M := M) (1 : Fin 2)
  change PWord.eval (finiteActionImageGenerators h q M) (lSqW h) = 1 at hrel
  rw [PWord.eval_eq_evalZ _ _ _ _ hresolved] at hrel
  simpa [C, N] using hrel

set_option maxHeartbeats 2400000 in
/-- The direct ramified-simple Stokes theorem for the canonical `GammaL(h,q)` action image at
every even tame exponent.  Simplicity supplies nontriviality and wild triviality; presentation
death supplies the tame and improved `L_sq` relations; the ramified hypothesis is precisely
fixed-point-freeness of `tau`.  No Tate-duality hypothesis is used. -/
theorem finiteActionImage_stokesDuality_ramified_simple
    {h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0)
    (hsimple : IsSimpleModTwo (gamma h q : Type) M)
    (hτfpf : ∀ m : M,
      gammaGen (2 * h + 1) q (lSqW h) .tau • m = m → m = 0)
    (hq : Even q) :
    StokesDuality (finiteActionImageGenerators h q M)
      (lSqFam h q
        (omega2Exp (4 * Monoid.exponent (FiniteActionImage h q M)))) M := by
  let t := finiteActionImageMarking h q M
  have ht : t.TameRelAt q := finiteActionImage_tameRelAt
  have hwild : ∀ (i : Fin (2 * h + 1 + 1)) (m : M), t.x i • m = m :=
    finiteActionImage_wild_smul hM₂ hsimple
  have hτfpf' : ∀ m : M, t.τ • m = m → m = 0 := by
    intro m hm
    exact hτfpf m hm
  have hTodd : ∀ m : M, powOmega2 t.τ • m = m :=
    finiteActionImage_tau_powOmega2_smul_trivial hM₂ hsimple
  have hL : PWord.evalZ ⇑t
      (fun _ ↦ (omega2Exp
        (4 * Monoid.exponent (FiniteActionImage h q M)) : ℤ))
      (fun _ ↦ (omega2Exp
        (4 * Monoid.exponent (FiniteActionImage h q M)) : ℤ))
      (lSqW h) = 1 :=
    finiteActionImage_lSq_relator_death_resolved
  exact lSqStokesDuality_ramified t hM₂ hq ht hwild hτfpf' hTodd hL

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
