/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLTateDirect
import GQ2.Dyadic.Instances.LEvenQStokes

/-!
# The finite action image of a coefficient, for an arbitrary branch word

`GammaLActionImage` restricts the canonical action homomorphism of a finite `GammaL`-coefficient
to its actual finite image, and derives everything that the improved odd row's simple Stokes
theorems consume.  None of that derivation looks at the word `lSqW h`: it uses only the
admissible marked presentation of `GammaR n q R`, Lemma 5.12, and the tame relator, all of which
are supplied by `GammaR` for every branch word.

This file therefore states the same development once, for an arbitrary `R : PWord (Generator n)`.
The compact-`N` and compact-`M` rows instantiate it verbatim; the odd row's own copy is left
untouched.

What remains genuinely word-specific is only the *simple* Stokes theorem in each of the two
branches of `actionImage_tau_split_or_ramified_simple`.
-/

namespace GQ2.Dyadic.RowActionImage

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic.Count GQ2.Dyadic.LSquare
open GQ2.Dyadic.Certificates

/-! ## The action image and its marking -/

/-- The actual finite image of the canonical action homomorphism of a finite discrete
`GammaR n q R`-coefficient. -/
noncomputable abbrev ActionImage (n q : ℕ) (R : PWord (Generator n)) (M : Type)
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M] : Type :=
  ↥((finiteActionHom (G := (GammaR n q R : Type)) (M := M)).toMonoidHom.range)

/-- The canonical action homomorphism, corestricted to its image. -/
noncomputable def actionImageHom (n q : ℕ) (R : PWord (Generator n)) (M : Type)
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M] :
    ContinuousMonoidHom ((GammaR n q R : Type)) (ActionImage n q R M) where
  toMonoidHom :=
    (finiteActionHom (G := (GammaR n q R : Type)) (M := M)).toMonoidHom.rangeRestrict
  continuous_toFun :=
    (finiteActionHom (G := (GammaR n q R : Type)) (M := M)).continuous_toFun.subtype_mk _

/-- The marked generators of the branch presentation, read in the action image. -/
noncomputable def actionImageGenerators (n q : ℕ) (R : PWord (Generator n)) (M : Type)
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M] :
    Generator n → ActionImage n q R M :=
  fun i ↦ actionImageHom n q R M (gammaGen n q R i)

/-- The canonical marking with codomain restricted to the actual finite action image. -/
noncomputable def actionImageMarking (n q : ℕ) (R : PWord (Generator n)) (M : Type)
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M] :
    Marking n (ActionImage n q R M) :=
  ⟨actionImageGenerators n q R M⟩

@[simp] theorem actionImageMarking_apply
    {n q : ℕ} {R : PWord (Generator n)} {M : Type}
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M] (g : Generator n) :
    actionImageMarking n q R M g = actionImageGenerators n q R M g := rfl

@[simp] theorem actionImageHom_smul
    {n q : ℕ} {R : PWord (Generator n)} {M : Type}
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M]
    (g : (GammaR n q R : Type)) (m : M) : actionImageHom n q R M g • m = g • m := rfl

/-! ## Generation, wildness, and relator death -/

theorem actionImageGenerators_generate
    {n q : ℕ} {R : PWord (Generator n)} {M : Type}
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M] :
    Subgroup.closure (Set.range (actionImageGenerators n q R M)) = ⊤ :=
  closure_range_lower_eq_top (actionImageHom n q R M) (fun _ ↦ rfl)
    (isAdmissibleMarkedPresentation_gammaR n q R)
    (finiteActionHom (G := (GammaR n q R : Type)) (M := M)).toMonoidHom.rangeRestrict_surjective

theorem actionImageGenerators_isWildTwo
    {n q : ℕ} {R : PWord (Generator n)} {M : Type}
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M] :
    IsWildTwo (wildAlphabet n) (actionImageGenerators n q R M) :=
  isWildTwo_of_gammaGen (actionImageHom n q R M)
    (finiteActionHom (G := (GammaR n q R : Type)) (M := M)).toMonoidHom.rangeRestrict_surjective
    (fun _ ↦ rfl)

/-- Both intrinsic relators die in the canonical action image.  This is presentation death,
before choosing any integer resolver for the profinite exponents. -/
theorem actionImageGenerators_relator_death
    {n q : ℕ} {R : PWord (Generator n)} {M : Type}
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M] (k : Fin 2) :
    PWord.eval (actionImageGenerators n q R M) (gammaFam n q R k) = 1 :=
  (isAdmissibleMarkedPresentation_gammaR n q R).rel (actionImageHom n q R M) k

theorem isSimpleModTwo_actionImage
    {n q : ℕ} {R : PWord (Generator n)} {M : Type}
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M]
    (hsimple : IsSimpleModTwo (GammaR n q R : Type) M) :
    IsSimpleModTwo (ActionImage n q R M) M := by
  refine ⟨hsimple.1, fun W hW ↦ hsimple.2 W ?_⟩
  intro g m hm
  rw [← actionImageHom_smul (n := n) (q := q) (R := R) g m]
  exact hW (actionImageHom n q R M g) m hm

theorem actionImage_wild_smul
    {n q : ℕ} {R : PWord (Generator n)} {M : Type}
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0) (hsimple : IsSimpleModTwo (GammaR n q R : Type) M) :
    ∀ (i : Fin (n + 1)) (m : M), actionImageGenerators n q R M (.wild i) • m = m := by
  let L : Subgroup (ActionImage n q R M) := Subgroup.normalClosure
    (actionImageGenerators n q R M '' wildAlphabet n)
  have htriv := lemma_5_12 hM₂ (isSimpleModTwo_actionImage hsimple) L
    Subgroup.normalClosure_normal actionImageGenerators_isWildTwo
  intro i m
  apply htriv (actionImageGenerators n q R M (.wild i))
    (Subgroup.subset_normalClosure ?_) m
  exact ⟨.wild i, ⟨i, rfl⟩, rfl⟩

/-- The action image acts faithfully: an element fixing every coefficient is the identity. -/
theorem actionImage_eq_one_of_smul_eq
    {n q : ℕ} {R : PWord (Generator n)} {M : Type}
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M]
    (g : ActionImage n q R M) (hg : ∀ m : M, g • m = m) : g = 1 := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  ext m
  exact hg m

/-- The intrinsic tame relator gives the `q`-parametric tame equation on the action image. -/
theorem actionImage_tameRelAt
    {n q : ℕ} {R : PWord (Generator n)} {M : Type}
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M] :
    (actionImageMarking n q R M).TameRelAt q := by
  let t := actionImageMarking n q R M
  have hrel := actionImageGenerators_relator_death
    (n := n) (q := q) (R := R) (M := M) (0 : Fin 2)
  change PWord.eval ⇑t (Certificates.tameRelW n q) = 1 at hrel
  rw [← Marking.eval_def, Certificates.eval_tameRelW] at hrel
  exact mul_inv_eq_one.mp hrel

/-! ## The two structural consequences of simplicity -/

set_option maxHeartbeats 1200000 in
/-- On a simple elementary coefficient, the two-primary part of the ramified tame generator
acts trivially.  Its fixed space is stable under `sigma` by the `q`-parametric tame relation,
under `tau` by commutation, and under every wild generator by Lemma 5.12. -/
theorem actionImage_tau_powOmega2_smul_trivial
    {n q : ℕ} {R : PWord (Generator n)} {M : Type}
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0) (hsimple : IsSimpleModTwo (GammaR n q R : Type) M) :
    ∀ m : M, powOmega2 (actionImageMarking n q R M).τ • m = m := by
  let t := actionImageMarking n q R M
  have ht : t.TameRelAt q := actionImage_tameRelAt
  have hwild : ∀ (i : Fin (n + 1)) (m : M), t.x i • m = m :=
    actionImage_wild_smul hM₂ hsimple
  refine pow2_smul_trivial_of_stable hM₂ (isSimpleModTwo_actionImage hsimple)
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
  let S : Subgroup (ActionImage n q R M) :=
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
  have hgenS : Subgroup.closure (Set.range (actionImageGenerators n q R M)) ≤ S := by
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
  rw [actionImageGenerators_generate] at hgenS
  exact fun c ↦ hgenS (Subgroup.mem_top c)

set_option maxHeartbeats 1200000 in
/-- A simple elementary `GammaR n q R`-module is either unramified (`tau` acts trivially) or
ramified (`tau` has no nonzero fixed vector).  This is the dichotomy that splits the word's
simple Stokes theorem into its two branches. -/
theorem actionImage_tau_split_or_ramified_simple
    {n q : ℕ} {R : PWord (Generator n)} {M : Type}
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0) (hsimple : IsSimpleModTwo (GammaR n q R : Type) M) :
    (∀ m : M, gammaGen n q R .tau • m = m) ∨
      (∀ m : M, gammaGen n q R .tau • m = m → m = 0) := by
  let t := actionImageMarking n q R M
  let W : AddSubgroup M :=
    { carrier := {m | t.τ • m = m}
      zero_mem' := smul_zero _
      add_mem' := fun {a b} ha hb ↦ by
        change t.τ • (a + b) = a + b
        rw [smul_add, ha, hb]
      neg_mem' := fun {a} ha ↦ by
        change t.τ • (-a) = -a
        rw [smul_neg, ha] }
  have ht : t.TameRelAt q := actionImage_tameRelAt
  have hwild : ∀ (i : Fin (n + 1)) (m : M), t.x i • m = m :=
    actionImage_wild_smul hM₂ hsimple
  let S : Subgroup (ActionImage n q R M) :=
    { carrier := {c | ∀ m : M, m ∈ W → c • m ∈ W}
      one_mem' := fun m hm ↦ by simpa using hm
      mul_mem' := fun {a b} ha hb m hm ↦ by rw [mul_smul]; exact ha _ (hb m hm)
      inv_mem' := fun {a} ha m hm ↦ by
        have hφinj : Function.Injective (fun u : W ↦ (⟨a • u.1, ha u.1 u.2⟩ : W)) := by
          intro x y hxy
          exact Subtype.ext (MulAction.injective a (congrArg Subtype.val hxy))
        obtain ⟨⟨u, hu⟩, hux⟩ :=
          (Finite.injective_iff_surjective.mp hφinj) ⟨m, hm⟩
        have hum : a • u = m := congrArg Subtype.val hux
        show t.τ • (a⁻¹ • m) = a⁻¹ • m
        rw [show a⁻¹ • m = u from by rw [← hum, inv_smul_smul]]
        exact hu }
  have hσ : t.σ ∈ S := by
    intro m hm
    change t.τ • (t.σ • m) = t.σ • m
    exact tau_fixed_sigma_stable_of_tameRelAt t ht hm
  have hτ : t.τ ∈ S := by
    intro m hm
    change t.τ • m = m at hm
    show t.τ • (t.τ • m) = t.τ • m
    exact congrArg (fun x ↦ t.τ • x) hm
  have hx : ∀ i, t.x i ∈ S := by
    intro i m hm
    change t.τ • (t.x i • m) = t.x i • m
    rw [hwild i m]
    exact hm
  have hgenS : Subgroup.closure (Set.range (actionImageGenerators n q R M)) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    cases g with
    | sigma => exact hσ
    | tau => exact hτ
    | wild i => exact hx i
  rw [actionImageGenerators_generate] at hgenS
  have hstable : ∀ (c : ActionImage n q R M) (m : M), m ∈ W → c • m ∈ W := by
    intro c
    exact hgenS (Subgroup.mem_top c)
  rcases (isSimpleModTwo_actionImage hsimple).2 W hstable with hbot | htop
  · right
    intro m hm
    have hmW : m ∈ W := hm
    rw [hbot, AddSubgroup.mem_bot] at hmW
    exact hmW
  · left
    intro m
    have hmW : m ∈ W := by rw [htop]; exact AddSubgroup.mem_top m
    exact hmW

/-- Transport of continuity along a continuous homomorphism into a finite discrete target. -/
theorem continuousSMul_of_comp_finite
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

end

end GQ2.Dyadic.RowActionImage
