/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.AdmissibleCount
public import GQ2.GaussCount

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# The deep/quotient Hom-count duality

Produces the `hduality` input of the f6 capstone `card_deepPart_sq_of_duality`
(`GQ2/AdmissibleCount.lean`):

`#Hom_C(V^∨, deep) = #Hom_C(V^∨, H¹(N)/deep)`.

## The minimal route (design note)

The paper (§6.3 p. 34) runs the full graded computation: eq. (93) square-class sizes, the
per-level Hilbert duality `U_i^⊥ = U_{2e−i+1}` of eq. (94) pairing `gr_j ≅ (gr_{2e−j})^∨`,
self-duality `V ≅ V^∨` for equal multiplicities, and Lemma 6.10 killing the middle `j = e`.
This file implements a **strictly smaller** route discovered at design time: with
`E := U_e`-classes (norm-vocabulary `‖A−1‖ ≤ ‖2‖` — no uniformizer needed) and
`Deep := U_{e+1}`-classes, the chain

`#Hom(U, M/Deep) = #Hom(M/Deep, U)            -- Hom-symmetry (§D)
                 = #Hom(M/Deep, U^∨)           -- U self-dual
                 = #Hom(U, (M/Deep)^∨)         -- currying (§C)
                 = #Hom(U, Deep^⊥)             -- nondegeneracy: ann(Deep) ≅ (M/Deep)^∨ (§E)
                 = #Hom(U, Deep)·#Hom(U, Deep^⊥/Deep)   -- f6 SES engine at Deep ≤ Deep^⊥
                 = #Hom(U, Deep)                -- middle-kill (§B): Deep^⊥/Deep ⊆ E/Deep
                                                --   is inertia-trivial, U ramified simple`

needs from the arithmetic side ONLY:
* **(H2) nondegeneracy** of one `C`-invariant pairing `B` on `M = H¹(N,𝔽₂)`;
* **(H3) isotropy** `Deep ≤ Deep^⊥` — banked (Tier-5 `cup_deepClasses`, std-3 ∪ {B11a});
* **(H4) ONE sharp instance** `Deep^⊥ ≤ E` — the ⊆-half of eq. (94) at `i = e+1`
  (`U_{e+1}^⊥ = U_e`); NO other level of (94) is consumed;
* **(H5) the middle twist** — conjugates of the inertia generator act trivially on `E/Deep`
  (Lemma 6.10; the `θ^e ≡ 1` twist is derivable norm-algebra per `GQ2/UnitFiltration.lean`).

No per-level graded (93) computation, no `U_i^⊥ = U_{2e−i+1}` beyond (H4), no new axiom in
this file: (H2)/(H4)/(H5) enter as *hypotheses*, so the leaf decision (prove vs. cite
Serre LF XIV §§1–3 / FV IV §5 Thm (5.2)) is deferred to the instantiation and needs user
approval only there.

## Contents

* §A — generic restricted/quotient `DistribMulAction`s on a `C`-stable `AddSubgroup`
  (abstract twins of f6's `conjModuleDeep`/`conjModuleQuot`).
* §B — `card_equivHoms_eq_one_of_conjSmulTrivial`: if some `t₀ : C` acts nontrivially on the
  simple module `U` while every conjugate `d t₀ d⁻¹` acts trivially on `T`, then
  `#Hom_C(U, T) = 1` (homs factor through the inertia-coinvariants, which vanish).
* §C — the currying bijection `#Hom_C(U, W^∨) = #Hom_C(W, U^∨)` (duals via `dualModule`).
* §D — **Hom-symmetry** `#Hom_C(U, W) = #Hom_C(W, U)` for `U` simple, nontrivial,
  self-dual, with a regular-summand package (Lemma 6.11's output shape): strong induction on
  `#W`, splitting off `U`-copies via the banked `equivariant_lift_of_regular_summand` (epi
  side) and its dual (mono side).  This is the precise module-theoretic content behind the
  paper's "self-duality gives equal multiplicities".
* §E — the perp layer: `pairPerp`, stability, `perpEquivDualQuot` (`ann(S) ≅ (M/S)^∨`).
* §F — the assembly `card_equivHoms_deep_eq_quot` (abstract `hduality`).

The main consumer is `card_deepPart_sq_of_duality`.
-/

namespace GQ2

section ActionHelpers

variable {C : Type} [Group C] {M : Type} [AddCommGroup M] [DistribMulAction C M]

/-- The restricted `C`-action on a `C`-stable additive subgroup (abstract twin of f6's
`conjModuleDeep`).  Provided as a `@[reducible]` `def`; consumers `letI` it. -/
@[reducible] def stabSubAction (S : AddSubgroup M)
    (hS : ∀ (c : C), ∀ x ∈ S, c • x ∈ S) : DistribMulAction C ↥S where
  smul c x := ⟨c • x.1, hS c x.1 x.2⟩
  one_smul x := Subtype.ext (one_smul C x.1)
  mul_smul c d x := Subtype.ext (mul_smul c d x.1)
  smul_zero c := Subtype.ext (smul_zero c)
  smul_add c x y := Subtype.ext (smul_add c x.1 y.1)

/-- `c • ·` as an additive endomorphism of `M`. -/
def smulHom (c : C) : M →+ M := DistribSMul.toAddMonoidHom M c

/-- The descent of `c • ·` to `M ⧸ S` for a `C`-stable `S`. -/
noncomputable def stabQuotHom (S : AddSubgroup M)
    (hS : ∀ (c : C), ∀ x ∈ S, c • x ∈ S) (c : C) : (M ⧸ S) →+ (M ⧸ S) :=
  QuotientAddGroup.map S S (smulHom c)
    (fun x hx => AddSubgroup.mem_comap.mpr (hS c x hx))

/-- Computation rule for `stabQuotHom` on a class. -/
theorem stabQuotHom_mk (S : AddSubgroup M) (hS : ∀ (c : C), ∀ x ∈ S, c • x ∈ S)
    (c : C) (a : M) :
    stabQuotHom S hS c (QuotientAddGroup.mk a) = QuotientAddGroup.mk (c • a) :=
  QuotientAddGroup.map_mk _ _ (smulHom c) _ a

/-- The induced `C`-action on `M ⧸ S` for a `C`-stable `S` (abstract twin of f6's
`conjModuleQuot`).  Provided as a `@[reducible]` `def`; consumers `letI` it. -/
@[reducible] noncomputable def stabQuotAction (S : AddSubgroup M)
    (hS : ∀ (c : C), ∀ x ∈ S, c • x ∈ S) : DistribMulAction C (M ⧸ S) where
  smul c x := stabQuotHom S hS c x
  one_smul x := by
    refine QuotientAddGroup.induction_on x (fun a => ?_)
    show stabQuotHom S hS 1 (QuotientAddGroup.mk a) = QuotientAddGroup.mk a
    rw [stabQuotHom_mk, one_smul]
  mul_smul c d x := by
    refine QuotientAddGroup.induction_on x (fun a => ?_)
    show stabQuotHom S hS (c * d) (QuotientAddGroup.mk a)
      = stabQuotHom S hS c (stabQuotHom S hS d (QuotientAddGroup.mk a))
    simp only [stabQuotHom_mk, mul_smul]
  smul_zero c := map_zero _
  smul_add c x y := map_add _ x y

end ActionHelpers

section InertiaKill

variable {C : Type} [Group C]
variable {U : Type} [AddCommGroup U] [DistribMulAction C U]
variable {T : Type} [AddCommGroup T] [DistribMulAction C T]

/-- **The inertia-coinvariants kill** (Lemma 6.10's consumer form): if some `t₀ : C` acts
nontrivially on the simple module `U` while every conjugate `d t₀ d⁻¹` acts trivially on `T`,
then the only equivariant map `U →+ T` is zero — an equivariant map kills the (nonzero,
`C`-stable, hence full) subgroup generated by `{(d t₀ d⁻¹) • u − u}`. -/
theorem card_equivHoms_eq_one_of_conjSmulTrivial
    (hsimple : ∀ W : AddSubgroup U, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (t₀ : C) (hU : ∃ u : U, t₀ • u ≠ u)
    (hT : ∀ (d : C) (x : T), (d * t₀ * d⁻¹) • x = x) :
    Nat.card ↥(equivHoms C U T) = 1 := by
  classical
  -- the inertia-displacement subgroup
  set K : AddSubgroup U :=
    AddSubgroup.closure {w | ∃ (d : C) (u : U), (d * t₀ * d⁻¹) • u - u = w} with hK
  -- C-stable
  have hKstable : ∀ (h : C), ∀ w ∈ K, h • w ∈ K := by
    intro h w hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨d, u, rfl⟩ := hx
      refine AddSubgroup.subset_closure ⟨h * d, h • u, ?_⟩
      rw [smul_sub, ← mul_smul, ← mul_smul]
      congr 2
      group
    | zero => rw [smul_zero]; exact zero_mem K
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  -- nonzero
  obtain ⟨u₀, hu₀⟩ := hU
  have hne : K ≠ ⊥ := by
    intro hbot
    have hmem : t₀ • u₀ - u₀ ∈ K :=
      AddSubgroup.subset_closure ⟨1, u₀, by rw [one_mul, inv_one, mul_one]⟩
    rw [hbot, AddSubgroup.mem_bot, sub_eq_zero] at hmem
    exact hu₀ hmem
  have hKtop : K = ⊤ := (hsimple K hKstable).resolve_left hne
  -- every equivariant map vanishes on K = ⊤
  have hzero : ∀ f : ↥(equivHoms C U T), f = 0 := by
    intro f
    apply Subtype.ext
    ext u
    have hu : u ∈ K := hKtop ▸ AddSubgroup.mem_top u
    show f.1 u = 0
    induction hu using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨d, v, rfl⟩ := hx
      rw [map_sub, f.2 (d * t₀ * d⁻¹) v, hT, sub_self]
    | zero => exact map_zero f.1
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | neg x _ hx => rw [map_neg, hx, neg_zero]
  haveI : Subsingleton ↥(equivHoms C U T) :=
    ⟨fun f g => (hzero f).trans (hzero g).symm⟩
  haveI : Nonempty ↥(equivHoms C U T) := ⟨0⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

end InertiaKill

section Curry

variable {C : Type} [Group C]
variable {U : Type} [AddCommGroup U] [DistribMulAction C U]
variable {W : Type} [AddCommGroup W] [DistribMulAction C W]

/-- **The currying bijection**: equivariant maps into the dual are equivariant pairings, read
from either side — `Hom_C(U, W^∨) ≃ Hom_C(W, U^∨)` (both duals carrying `dualModule`).
`f ↦ AddMonoidHom.flip f`. -/
noncomputable def equivHomsCurry :
    letI : DistribMulAction C (W →+ ZMod 2) := dualModule
    letI : DistribMulAction C (U →+ ZMod 2) := dualModule
    ↥(equivHoms C U (W →+ ZMod 2)) ≃ ↥(equivHoms C W (U →+ ZMod 2)) :=
  letI : DistribMulAction C (W →+ ZMod 2) := dualModule
  letI : DistribMulAction C (U →+ ZMod 2) := dualModule
  { toFun := fun f => ⟨f.1.flip, by
      intro c w
      ext u
      show f.1 u (c • w) = (f.1 (c⁻¹ • u)) w
      have h1 : f.1 (c⁻¹ • u) = dualModule.toSMul.smul c⁻¹ (f.1 u) := f.2 c⁻¹ u
      rw [h1]
      show f.1 u (c • w) = (f.1 u) ((c⁻¹)⁻¹ • w)
      rw [inv_inv]⟩
    invFun := fun g => ⟨g.1.flip, by
      intro c u
      ext w
      show g.1 w (c • u) = (g.1 (c⁻¹ • w)) u
      have h1 : g.1 (c⁻¹ • w) = dualModule.toSMul.smul c⁻¹ (g.1 w) := g.2 c⁻¹ w
      rw [h1]
      show g.1 w (c • u) = (g.1 w) ((c⁻¹)⁻¹ • u)
      rw [inv_inv]⟩
    left_inv := fun f => Subtype.ext (AddMonoidHom.ext fun u => AddMonoidHom.ext fun w => rfl)
    right_inv := fun g => Subtype.ext (AddMonoidHom.ext fun w => AddMonoidHom.ext fun u => rfl) }

/-- Cardinality form of the currying bijection. -/
theorem card_equivHoms_curry :
    letI : DistribMulAction C (W →+ ZMod 2) := dualModule
    letI : DistribMulAction C (U →+ ZMod 2) := dualModule
    Nat.card ↥(equivHoms C U (W →+ ZMod 2)) = Nat.card ↥(equivHoms C W (U →+ ZMod 2)) :=
  Nat.card_congr equivHomsCurry

end Curry

section ProdCounts

variable {C : Type} [Group C]
variable {X A B : Type} [AddCommGroup X] [AddCommGroup A] [AddCommGroup B]
variable [DistribMulAction C X] [DistribMulAction C A] [DistribMulAction C B]

/-- Equivariant maps into a product split componentwise. -/
noncomputable def equivHomsProdTarget :
    ↥(equivHoms C X (A × B)) ≃ ↥(equivHoms C X A) × ↥(equivHoms C X B) where
  toFun f := (⟨(AddMonoidHom.fst A B).comp f.1, fun c x => by
      show (f.1 (c • x)).1 = c • (f.1 x).1
      rw [f.2 c x]; rfl⟩,
    ⟨(AddMonoidHom.snd A B).comp f.1, fun c x => by
      show (f.1 (c • x)).2 = c • (f.1 x).2
      rw [f.2 c x]; rfl⟩)
  invFun gh := ⟨gh.1.1.prod gh.2.1, fun c x => by
    show (gh.1.1 (c • x), gh.2.1 (c • x)) = c • (gh.1.1 x, gh.2.1 x)
    rw [gh.1.2 c x, gh.2.2 c x]; rfl⟩
  left_inv f := Subtype.ext (AddMonoidHom.ext fun x => rfl)
  right_inv gh := Prod.ext (Subtype.ext (AddMonoidHom.ext fun x => rfl))
    (Subtype.ext (AddMonoidHom.ext fun x => rfl))

/-- `#Hom_C(X, A × B) = #Hom_C(X, A) · #Hom_C(X, B)`. -/
theorem card_equivHoms_prod_target :
    Nat.card ↥(equivHoms C X (A × B))
      = Nat.card ↥(equivHoms C X A) * Nat.card ↥(equivHoms C X B) := by
  rw [Nat.card_congr equivHomsProdTarget, Nat.card_prod]

/-- Equivariant maps out of a product split componentwise. -/
noncomputable def equivHomsProdSource :
    ↥(equivHoms C (A × B) X) ≃ ↥(equivHoms C A X) × ↥(equivHoms C B X) where
  toFun f := (⟨f.1.comp (AddMonoidHom.inl A B), fun c a => by
      show f.1 (c • a, 0) = c • f.1 (a, 0)
      rw [← f.2 c (a, 0)]
      congr 1
      show (c • a, (0 : B)) = (c • a, c • (0 : B))
      rw [smul_zero]⟩,
    ⟨f.1.comp (AddMonoidHom.inr A B), fun c b => by
      show f.1 (0, c • b) = c • f.1 (0, b)
      rw [← f.2 c (0, b)]
      congr 1
      show ((0 : A), c • b) = (c • (0 : A), c • b)
      rw [smul_zero]⟩)
  invFun gh := ⟨gh.1.1.coprod gh.2.1, fun c ab => by
    show gh.1.1 (c • ab.1) + gh.2.1 (c • ab.2) = c • (gh.1.1 ab.1 + gh.2.1 ab.2)
    rw [gh.1.2 c ab.1, gh.2.2 c ab.2, smul_add]⟩
  left_inv f := Subtype.ext (AddMonoidHom.ext fun ab => by
    show f.1 (ab.1, 0) + f.1 (0, ab.2) = f.1 ab
    rw [← map_add]
    congr 1
    exact Prod.ext (add_zero _) (zero_add _))
  right_inv gh := Prod.ext
    (Subtype.ext (AddMonoidHom.ext fun a => by
      show gh.1.1 a + gh.2.1 0 = gh.1.1 a
      rw [map_zero, add_zero]))
    (Subtype.ext (AddMonoidHom.ext fun b => by
      show gh.1.1 0 + gh.2.1 b = gh.2.1 b
      rw [map_zero, zero_add]))

/-- `#Hom_C(A × B, X) = #Hom_C(A, X) · #Hom_C(B, X)`. -/
theorem card_equivHoms_prod_source :
    Nat.card ↥(equivHoms C (A × B) X)
      = Nat.card ↥(equivHoms C A X) * Nat.card ↥(equivHoms C B X) := by
  rw [Nat.card_congr equivHomsProdSource, Nat.card_prod]

/-- **Source transport**: the equivariant-Hom count is invariant under precomposition with an
equivariant additive isomorphism (the source twin of f5's `card_equivHoms_congr`). -/
theorem card_equivHoms_congr_source (e : A ≃+ B) (he : ∀ (c : C) (a : A), e (c • a) = c • e a) :
    Nat.card ↥(equivHoms C B X) = Nat.card ↥(equivHoms C A X) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun f : ↥(equivHoms C B X) =>
      (⟨f.1.comp e.toAddMonoidHom, fun c a => by
        show f.1 (e (c • a)) = c • f.1 (e a)
        rw [he c a, f.2 c (e a)]⟩ : ↥(equivHoms C A X))) ⟨?_, ?_⟩)
  · intro f g h
    apply Subtype.ext
    ext b
    simpa [e.apply_symm_apply] using DFunLike.congr_fun (Subtype.ext_iff.mp h) (e.symm b)
  · intro g
    refine ⟨⟨g.1.comp e.symm.toAddMonoidHom, fun c b => by
      show g.1 (e.symm (c • b)) = c • g.1 (e.symm b)
      have hsymm : e.symm (c • b) = c • e.symm b := by
        apply e.injective
        rw [he, e.apply_symm_apply, e.apply_symm_apply]
      rw [hsymm, g.2 c (e.symm b)]⟩, ?_⟩
    apply Subtype.ext
    ext a
    show g.1 (e.symm (e a)) = g.1 a
    rw [e.symm_apply_apply]

end ProdCounts

section Fp2Substrate

variable {V : Type} [AddCommGroup V]

/-- **Dual surjectivity of an injection** over `𝔽₂`: for finite 2-torsion groups, restriction
of functionals along an injective additive map is surjective (every functional on the source
extends).  Via a linear left inverse over the field `ZMod 2`. -/
theorem dualHom_surjective_of_injective {W : Type} [AddCommGroup W] [Finite V] [Finite W]
    (h2V : ∀ v : V, v + v = 0) (h2W : ∀ w : W, w + w = 0)
    (f : V →+ W) (hf : Function.Injective f) :
    Function.Surjective (fun ψ : W →+ ZMod 2 => ψ.comp f) := by
  have hz2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact h2V v)
  letI : Module (ZMod 2) W := AddCommGroup.zmodModule (fun w => by rw [two_nsmul]; exact h2W w)
  have hsmul : ∀ (a : ZMod 2) (v : V), f (a • v) = a • f v := by
    intro a v
    rcases hz2 a with rfl | rfl
    · rw [zero_smul, zero_smul, map_zero]
    · rw [one_smul, one_smul]
  set fL : V →ₗ[ZMod 2] W := ⟨⟨⇑f, map_add f⟩, fun a v => hsmul a v⟩ with hfL
  have hker : LinearMap.ker fL = ⊥ := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    exact ⟨fun hv => hf (by rw [show f v = fL v from rfl, hv, map_zero]),
      fun hv => by rw [hv]; exact map_zero fL⟩
  obtain ⟨gL, hgL⟩ := LinearMap.exists_leftInverse_of_injective fL hker
  intro φ
  refine ⟨(φ.comp gL.toAddMonoidHom : W →+ ZMod 2), ?_⟩
  ext v
  show φ (gL (f v)) = φ v
  congr 1
  exact DFunLike.congr_fun hgL v

end Fp2Substrate

section EvalDual

variable {C : Type} [Group C]

/-- Precomposition with `f` as an additive map between `ZMod 2`-duals. -/
def precompHom {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) :
    (B →+ ZMod 2) →+ (A →+ ZMod 2) where
  toFun ψ := ψ.comp f
  map_zero' := rfl
  map_add' := fun _ _ => rfl


/-- Equivariance of `precompHom` (both duals under `dualModule`). -/
theorem precompHom_equivariant {A B : Type} [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction C A] [DistribMulAction C B]
    (f : A →+ B) (hf : ∀ (c : C) (a : A), f (c • a) = c • f a) (c : C) (ψ : B →+ ZMod 2) :
    precompHom f ((dualModule : DistribMulAction C (B →+ ZMod 2)).toSMul.smul c ψ)
      = (dualModule : DistribMulAction C (A →+ ZMod 2)).toSMul.smul c (precompHom f ψ) := by
  ext a
  show ψ (c⁻¹ • f a) = ψ (f (c⁻¹ • a))
  rw [hf c⁻¹ a]

/-- Evaluation into the `ZMod 2` double dual, as an additive map. -/
def evalDualHom {W : Type} [AddCommGroup W] : W →+ ((W →+ ZMod 2) →+ ZMod 2) where
  toFun w := { toFun := fun φ => φ w, map_zero' := rfl, map_add' := fun _ _ => rfl }
  map_zero' := by ext φ; exact map_zero φ
  map_add' := fun x y => by ext φ; exact map_add φ x y

@[simp] private theorem evalDualHom_apply {W : Type} [AddCommGroup W] (w : W) (φ : W →+ ZMod 2) :
    evalDualHom w φ = φ w := rfl

/-- **The double-dual evaluation is an isomorphism** for a finite 2-torsion group:
injective by functional separation, bijective by the cardinality `#W^∨∨ = #W^∨ = #W`
(`card_addHom_zmod2` twice). -/
noncomputable def evalDualEquiv {W : Type} [AddCommGroup W] [Finite W]
    (h2 : ∀ w : W, w + w = 0) : W ≃+ ((W →+ ZMod 2) →+ ZMod 2) := by
  haveI : Finite (W →+ ZMod 2) :=
    Finite.of_injective (DFunLike.coe : (W →+ ZMod 2) → (W → ZMod 2)) DFunLike.coe_injective
  haveI : Finite ((W →+ ZMod 2) →+ ZMod 2) :=
    Finite.of_injective
      (DFunLike.coe : ((W →+ ZMod 2) →+ ZMod 2) → ((W →+ ZMod 2) → ZMod 2))
      DFunLike.coe_injective
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Fintype ((W →+ ZMod 2) →+ ZMod 2) := Fintype.ofFinite _
  have hinj : Function.Injective (evalDualHom (W := W)) := by
    intro x y hxy
    by_contra hne
    obtain ⟨φ, hφ⟩ := LocalKummer.exists_functional_ne_zero h2 (sub_ne_zero.mpr hne)
    apply hφ
    rw [map_sub]
    have := DFunLike.congr_fun hxy φ
    simp only [evalDualHom_apply] at this
    rw [this, sub_self]
  have hcard : Fintype.card W = Fintype.card ((W →+ ZMod 2) →+ ZMod 2) := by
    have h1 : Nat.card (W →+ ZMod 2) = Nat.card W := QuadraticFp2.card_addHom_zmod2 W h2
    have h2' : Nat.card ((W →+ ZMod 2) →+ ZMod 2) = Nat.card (W →+ ZMod 2) :=
      QuadraticFp2.card_addHom_zmod2 (W →+ ZMod 2) (fun φ => by ext w; show φ w + φ w = 0; exact
        (by rw [← map_add, h2, map_zero]))
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h2', h1]
  exact AddEquiv.ofBijective evalDualHom
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩)


/-- Equivariance of the double-dual evaluation (`dualModule` twice on the target). -/
theorem evalDualEquiv_equivariant {W : Type} [AddCommGroup W] [Finite W]
    [DistribMulAction C W] (h2 : ∀ w : W, w + w = 0) (c : C) (w : W) :
    letI : DistribMulAction C (W →+ ZMod 2) := dualModule
    evalDualEquiv h2 (c • w)
      = (dualModule : DistribMulAction C ((W →+ ZMod 2) →+ ZMod 2)).toSMul.smul c
          (evalDualEquiv h2 w) := by
  letI : DistribMulAction C (W →+ ZMod 2) := dualModule
  ext φ
  show φ (c • w) = (evalDualEquiv h2 w) (c⁻¹ • φ)
  show φ (c • w) = ((c⁻¹ • φ : W →+ ZMod 2)) w
  show φ (c • w) = φ ((c⁻¹)⁻¹ • w)
  rw [inv_inv]

end EvalDual

section SplitOff

variable {C : Type} [Group C]
variable {U W : Type} [AddCommGroup U] [AddCommGroup W]
variable [DistribMulAction C U] [DistribMulAction C W]

/-- **The complement isomorphism of a split pair**: a retraction `ρ` of `ι` splits `W` as
`U × ker ρ`. -/
noncomputable def splitProdEquiv (ι : U →+ W) (ρ : W →+ U) (hρι : ∀ u, ρ (ι u) = u) :
    W ≃+ U × ↥ρ.ker where
  toFun w := (ρ w, ⟨w - ι (ρ w), by
    rw [AddMonoidHom.mem_ker, map_sub, hρι, sub_self]⟩)
  invFun uk := ι uk.1 + uk.2.1
  left_inv w := by
    show ι (ρ w) + (w - ι (ρ w)) = w
    rw [add_comm, sub_add_cancel]
  right_inv uk := by
    have hk : ρ uk.2.1 = 0 := AddMonoidHom.mem_ker.mp uk.2.2
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show ρ (ι uk.1 + uk.2.1) = uk.1
      rw [map_add, hρι, hk, add_zero]
    · show ι uk.1 + uk.2.1 - ι (ρ (ι uk.1 + uk.2.1)) = uk.2.1
      rw [map_add, hρι, hk, add_zero, add_sub_cancel_left]
  map_add' x y := by
    refine Prod.ext ?_ (Subtype.ext ?_)
    · exact map_add ρ x y
    · show x + y - ι (ρ (x + y)) = (x - ι (ρ x)) + (y - ι (ρ y))
      rw [map_add, map_add]
      abel

/-- The kernel of an equivariant map is `C`-stable. -/
theorem ker_stable (ρ : W →+ U) (hρeq : ∀ (c : C) (w : W), ρ (c • w) = c • ρ w) :
    ∀ (c : C), ∀ w ∈ ρ.ker, c • w ∈ ρ.ker := by
  intro c w hw
  rw [AddMonoidHom.mem_ker, hρeq, AddMonoidHom.mem_ker.mp hw, smul_zero]

/-- Equivariance of the complement isomorphism (`ker ρ` under the restricted action). -/
theorem splitProdEquiv_equivariant (ι : U →+ W) (ρ : W →+ U) (hρι : ∀ u, ρ (ι u) = u)
    (hιeq : ∀ (c : C) (u : U), ι (c • u) = c • ι u)
    (hρeq : ∀ (c : C) (w : W), ρ (c • w) = c • ρ w) (c : C) (w : W) :
    letI : DistribMulAction C ↥ρ.ker := stabSubAction ρ.ker (ker_stable ρ hρeq)
    splitProdEquiv ι ρ hρι (c • w) = c • splitProdEquiv ι ρ hρι w := by
  letI : DistribMulAction C ↥ρ.ker := stabSubAction ρ.ker (ker_stable ρ hρeq)
  refine Prod.ext ?_ (Subtype.ext ?_)
  · exact hρeq c w
  · show c • w - ι (ρ (c • w)) = c • (w - ι (ρ w))
    rw [hρeq, hιeq, smul_sub]

/-- **The epi split** — a surjective equivariant map onto the packaged module splits: the
banked `equivariant_lift_of_regular_summand` lifts `id`. -/
theorem exists_section_of_epi [Finite C]
    (h2U : ∀ u : U, u + u = 0) (h2W : ∀ w : W, w + w = 0)
    {N : ℕ} (ι : U →+ (Fin N → C → ZMod 2)) (r : (Fin N → C → ZMod 2) →+ U)
    (hι : ∀ (h : C) (v : U) (n : Fin N) (x : C), ι (h • v) n x = ι v n (h⁻¹ * x))
    (hr : ∀ (h : C) (F : Fin N → C → ZMod 2), r (fun n x => F n (h⁻¹ * x)) = h • r F)
    (hri : ∀ v : U, r (ι v) = v)
    (g : W →+ U) (hgeq : ∀ (c : C) (w : W), g (c • w) = c • g w)
    (hgsurj : Function.Surjective ⇑g) :
    ∃ σ : U →+ W, (∀ (c : C) (u : U), σ (c • u) = c • σ u) ∧ ∀ u, g (σ u) = u := by
  obtain ⟨σ, hσeq, hσ⟩ := equivariant_lift_of_regular_summand h2W h2U ι r hι hr hri
    g hgeq hgsurj (AddMonoidHom.id U) (fun h v => rfl)
  exact ⟨σ, hσeq, hσ⟩

/-- **The mono split** — an injective equivariant map out of the packaged self-dual module
admits an equivariant retraction: dualize (`precompHom f` is onto by `𝔽₂` functional
extension), lift `id` on the dual side with the `eU`-transported package, and pull the
section back through the double-dual evaluations. -/
theorem exists_retraction_of_mono [Finite C] [Finite U] [Finite W]
    (h2U : ∀ u : U, u + u = 0) (h2W : ∀ w : W, w + w = 0)
    {N : ℕ} (ι : U →+ (Fin N → C → ZMod 2)) (r : (Fin N → C → ZMod 2) →+ U)
    (hι : ∀ (h : C) (v : U) (n : Fin N) (x : C), ι (h • v) n x = ι v n (h⁻¹ * x))
    (hr : ∀ (h : C) (F : Fin N → C → ZMod 2), r (fun n x => F n (h⁻¹ * x)) = h • r F)
    (hri : ∀ v : U, r (ι v) = v)
    (eU : U ≃+ (U →+ ZMod 2))
    (heU : ∀ (c : C) (u : U),
      eU (c • u) = (dualModule : DistribMulAction C (U →+ ZMod 2)).toSMul.smul c (eU u))
    (f : U →+ W) (hfeq : ∀ (c : C) (u : U), f (c • u) = c • f u)
    (hfinj : Function.Injective ⇑f) :
    ∃ ρ : W →+ U, (∀ (c : C) (w : W), ρ (c • w) = c • ρ w) ∧ ∀ u, ρ (f u) = u := by
  letI : DistribMulAction C (U →+ ZMod 2) := dualModule
  letI : DistribMulAction C (W →+ ZMod 2) := dualModule
  haveI : Finite (U →+ ZMod 2) :=
    Finite.of_injective (DFunLike.coe : (U →+ ZMod 2) → (U → ZMod 2)) DFunLike.coe_injective
  haveI : Finite (W →+ ZMod 2) :=
    Finite.of_injective (DFunLike.coe : (W →+ ZMod 2) → (W → ZMod 2)) DFunLike.coe_injective
  have h2U' : ∀ φ : U →+ ZMod 2, φ + φ = 0 := fun φ => by
    ext u; show φ u + φ u = 0; rw [← map_add, h2U, map_zero]
  have h2W' : ∀ ψ : W →+ ZMod 2, ψ + ψ = 0 := fun ψ => by
    ext w; show ψ w + ψ w = 0; rw [← map_add, h2W, map_zero]
  -- the eU-transported package for U^∨
  set ι' : (U →+ ZMod 2) →+ (Fin N → C → ZMod 2) := ι.comp eU.symm.toAddMonoidHom with hι'def
  set r' : (Fin N → C → ZMod 2) →+ (U →+ ZMod 2) := eU.toAddMonoidHom.comp r with hr'def
  have heU_symm : ∀ (c : C) (φ : U →+ ZMod 2), eU.symm
      ((dualModule : DistribMulAction C (U →+ ZMod 2)).toSMul.smul c φ) = c • eU.symm φ := by
    intro c φ
    apply eU.injective
    rw [eU.apply_symm_apply, heU, eU.apply_symm_apply]
  have hι'eq : ∀ (h : C) (φ : U →+ ZMod 2) (n : Fin N) (x : C),
      ι' ((dualModule : DistribMulAction C (U →+ ZMod 2)).toSMul.smul h φ) n x
        = ι' φ n (h⁻¹ * x) := by
    intro h φ n x
    show ι (eU.symm (dualModule.toSMul.smul h φ)) n x = ι (eU.symm φ) n (h⁻¹ * x)
    rw [heU_symm, hι]
  have hr'eq : ∀ (h : C) (F : Fin N → C → ZMod 2),
      r' (fun n x => F n (h⁻¹ * x))
        = (dualModule : DistribMulAction C (U →+ ZMod 2)).toSMul.smul h (r' F) := by
    intro h F
    show eU (r fun n x => F n (h⁻¹ * x)) = dualModule.toSMul.smul h (eU (r F))
    rw [hr, heU]
  have hr'i : ∀ φ : U →+ ZMod 2, r' (ι' φ) = φ := by
    intro φ
    show eU (r (ι (eU.symm φ))) = φ
    rw [hri, eU.apply_symm_apply]
  -- dual surjection + lift of the identity
  have hdualsurj : Function.Surjective ⇑(precompHom f) :=
    dualHom_surjective_of_injective h2U h2W f hfinj
  have hpre_eq : ∀ (c : C) (ψ : W →+ ZMod 2),
      precompHom f ((dualModule : DistribMulAction C (W →+ ZMod 2)).toSMul.smul c ψ)
        = (dualModule : DistribMulAction C (U →+ ZMod 2)).toSMul.smul c (precompHom f ψ) :=
    precompHom_equivariant f hfeq
  obtain ⟨σ, hσeq, hσ⟩ := equivariant_lift_of_regular_summand h2W' h2U' ι' r' hι'eq hr'eq hr'i
    (precompHom f) hpre_eq hdualsurj (AddMonoidHom.id (U →+ ZMod 2)) (fun h v => rfl)
  -- pull back through the double-dual evaluations
  set ρ : W →+ U := (evalDualEquiv h2U).symm.toAddMonoidHom.comp
    ((precompHom σ).comp (evalDualEquiv h2W).toAddMonoidHom) with hρdef
  have hρval : ∀ w : W, evalDualEquiv h2U (ρ w) = precompHom σ (evalDualEquiv h2W w) := by
    intro w
    show evalDualEquiv h2U ((evalDualEquiv h2U).symm _) = _
    rw [AddEquiv.apply_symm_apply]
    rfl
  refine ⟨ρ, ?_, ?_⟩
  · -- equivariance: chain through the three equivariant pieces
    intro c w
    apply (evalDualEquiv h2U).injective
    rw [hρval, evalDualEquiv_equivariant h2W c w]
    letI : DistribMulAction C ((W →+ ZMod 2) →+ ZMod 2) := dualModule
    letI : DistribMulAction C ((U →+ ZMod 2) →+ ZMod 2) := dualModule
    rw [show precompHom σ (dualModule.toSMul.smul c (evalDualEquiv h2W w))
        = dualModule.toSMul.smul c (precompHom σ (evalDualEquiv h2W w)) from
      precompHom_equivariant σ hσeq c _]
    rw [evalDualEquiv_equivariant h2U c (ρ w), hρval]
  · -- retraction identity, via evalU-injectivity
    intro u
    apply (evalDualEquiv h2U).injective
    rw [hρval]
    ext φ
    show (evalDualEquiv h2W (f u)) (σ φ) = (evalDualEquiv h2U u) φ
    show (σ φ) (f u) = φ u
    exact DFunLike.congr_fun (hσ φ) u

end SplitOff

section HomSymmetry

variable {C : Type} [Group C] [Finite C]
variable {U : Type} [AddCommGroup U] [DistribMulAction C U]

/-- The cardinality-bounded induction core of `card_equivHoms_comm`. -/
private theorem card_equivHoms_comm_aux [Finite U]
    (h2U : ∀ u : U, u + u = 0)
    (hsimple : ∀ S : AddSubgroup U, (∀ (h : C), ∀ w ∈ S, h • w ∈ S) → S = ⊥ ∨ S = ⊤)
    (hnt : Nontrivial U)
    {N : ℕ} (ι : U →+ (Fin N → C → ZMod 2)) (r : (Fin N → C → ZMod 2) →+ U)
    (hι : ∀ (h : C) (v : U) (n : Fin N) (x : C), ι (h • v) n x = ι v n (h⁻¹ * x))
    (hr : ∀ (h : C) (F : Fin N → C → ZMod 2), r (fun n x => F n (h⁻¹ * x)) = h • r F)
    (hri : ∀ v : U, r (ι v) = v)
    (eU : U ≃+ (U →+ ZMod 2))
    (heU : ∀ (c : C) (u : U),
      eU (c • u) = (dualModule : DistribMulAction C (U →+ ZMod 2)).toSMul.smul c (eU u)) :
    ∀ (n : ℕ) (W : Type) (_ : AddCommGroup W), ∀ (_ : DistribMulAction C W) (_ : Finite W),
      (∀ w : W, w + w = 0) → Nat.card W ≤ n →
      Nat.card ↥(equivHoms C U W) = Nat.card ↥(equivHoms C W U) := by
  intro n
  induction n with
  | zero =>
    intro W instW1 instW2 instW3 h2W hcard
    haveI : Nonempty W := ⟨0⟩
    have := Nat.card_pos (α := W)
    omega
  | succ n IH =>
    intro W instW1 instW2 instW3 h2W hcard
    by_cases hall : (∀ f : ↥(equivHoms C U W), f = 0) ∧ (∀ g : ↥(equivHoms C W U), g = 0)
    · -- both Hom-sets trivial: both counts are 1
      haveI hs1 : Subsingleton ↥(equivHoms C U W) :=
        ⟨fun a b => (hall.1 a).trans (hall.1 b).symm⟩
      haveI hs2 : Subsingleton ↥(equivHoms C W U) :=
        ⟨fun a b => (hall.2 a).trans (hall.2 b).symm⟩
      haveI : Nonempty ↥(equivHoms C U W) := ⟨0⟩
      haveI : Nonempty ↥(equivHoms C W U) := ⟨0⟩
      rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩,
        Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩]
    · -- a nonzero equivariant map in one direction yields a split pair (ι₀, ρ₀)
      have hsplit : ∃ (ι₀ : U →+ W) (ρ₀ : W →+ U),
          (∀ (c : C) (u : U), ι₀ (c • u) = c • ι₀ u)
            ∧ (∀ (c : C) (w : W), ρ₀ (c • w) = c • ρ₀ w) ∧ ∀ u, ρ₀ (ι₀ u) = u := by
        rcases not_and_or.mp hall with h | h
        · -- mono case: 0 ≠ f : U →+ W equivariant, injective by simplicity of the kernel
          obtain ⟨f, hf0⟩ := not_forall.mp h
          have hf1 : f.1 ≠ 0 := fun hz => hf0 (Subtype.ext hz)
          have hkerstab : ∀ (c : C), ∀ u ∈ f.1.ker, c • u ∈ f.1.ker :=
            ker_stable f.1 (fun c u => f.2 c u)
          have hker : f.1.ker = ⊥ := by
            refine (hsimple f.1.ker hkerstab).resolve_right (fun htop => hf1 ?_)
            ext u
            exact AddMonoidHom.mem_ker.mp (htop ▸ AddSubgroup.mem_top u)
          have hinj : Function.Injective ⇑f.1 := by
            rw [← AddMonoidHom.ker_eq_bot_iff]
            exact hker
          obtain ⟨ρ₀, hρeq, hρf⟩ := exists_retraction_of_mono h2U h2W ι r hι hr hri eU heU
            f.1 (fun c u => f.2 c u) hinj
          exact ⟨f.1, ρ₀, fun c u => f.2 c u, hρeq, hρf⟩
        · -- epi case: 0 ≠ g : W →+ U equivariant, surjective by simplicity of the range
          obtain ⟨g, hg0⟩ := not_forall.mp h
          have hg1 : g.1 ≠ 0 := fun hz => hg0 (Subtype.ext hz)
          have hrangestab : ∀ (c : C), ∀ u ∈ g.1.range, c • u ∈ g.1.range := by
            rintro c u ⟨w, rfl⟩
            exact ⟨c • w, g.2 c w⟩
          have hrange : g.1.range = ⊤ := by
            refine (hsimple g.1.range hrangestab).resolve_left (fun hbot => hg1 ?_)
            ext w
            have : g.1 w ∈ g.1.range := ⟨w, rfl⟩
            rwa [hbot, AddSubgroup.mem_bot] at this
          have hsurj : Function.Surjective ⇑g.1 := by
            intro u
            have : u ∈ g.1.range := hrange ▸ AddSubgroup.mem_top u
            exact this
          obtain ⟨ι₀, hιeq, hgι⟩ := exists_section_of_epi h2U h2W ι r hι hr hri
            g.1 (fun c w => g.2 c w) hsurj
          exact ⟨ι₀, g.1, hιeq, fun c w => g.2 c w, hgι⟩
      obtain ⟨ι₀, ρ₀, hιeq, hρeq, hρι⟩ := hsplit
      -- the complement K := ker ρ₀ with the restricted action
      letI instK : DistribMulAction C ↥ρ₀.ker := stabSubAction ρ₀.ker (ker_stable ρ₀ hρeq)
      have h2K : ∀ k : ↥ρ₀.ker, k + k = 0 := fun k => Subtype.ext (h2W k.1)
      have hsplEq : ∀ (c : C) (w : W),
          splitProdEquiv ι₀ ρ₀ hρι (c • w) = c • splitProdEquiv ι₀ ρ₀ hρι w :=
        splitProdEquiv_equivariant ι₀ ρ₀ hρι hιeq hρeq
      -- cardinality bookkeeping: #W = #U · #K, #U ≥ 2 ⟹ #K ≤ n
      have hWcard : Nat.card W = Nat.card U * Nat.card ↥ρ₀.ker := by
        rw [Nat.card_congr (splitProdEquiv ι₀ ρ₀ hρι).toEquiv, Nat.card_prod]
      have hUtwo : 2 ≤ Nat.card U := Finite.one_lt_card_iff_nontrivial.mpr hnt
      haveI : Nonempty ↥ρ₀.ker := ⟨0⟩
      have hKpos : 0 < Nat.card ↥ρ₀.ker := Nat.card_pos
      have hKcard : Nat.card ↥ρ₀.ker ≤ n := by
        have h2k : 2 * Nat.card ↥ρ₀.ker ≤ n + 1 := by
          calc 2 * Nat.card ↥ρ₀.ker
              ≤ Nat.card U * Nat.card ↥ρ₀.ker := Nat.mul_le_mul_right _ hUtwo
            _ = Nat.card W := hWcard.symm
            _ ≤ n + 1 := hcard
        omega
      -- factor both counts through W ≅ U × K and recurse on K
      have hT : Nat.card ↥(equivHoms C U W)
          = Nat.card ↥(equivHoms C U U) * Nat.card ↥(equivHoms C U ↥ρ₀.ker) := by
        rw [card_equivHoms_congr (splitProdEquiv ι₀ ρ₀ hρι) hsplEq, card_equivHoms_prod_target]
      have hS : Nat.card ↥(equivHoms C W U)
          = Nat.card ↥(equivHoms C U U) * Nat.card ↥(equivHoms C ↥ρ₀.ker U) := by
        rw [← card_equivHoms_congr_source (splitProdEquiv ι₀ ρ₀ hρι) hsplEq,
          card_equivHoms_prod_source]
      rw [hT, hS, IH ↥ρ₀.ker inferInstance instK inferInstance h2K hKcard]

/-- **Hom-symmetry** (§D): for a simple, nontrivial, self-dual module `U` with a
regular-summand package (Lemma 6.11's output shape), the equivariant-Hom counts are symmetric:
`#Hom_C(U, W) = #Hom_C(W, U)` for every finite 2-torsion `C`-module `W`.  This is the precise
module-theoretic content behind the paper's "self-duality gives equal multiplicities" (§6.3
p. 34): the package makes `U` both projective and injective, so `U`-copies split off `W` on
either side and the counts match block by block. -/
theorem card_equivHoms_comm [Finite U]
    {W : Type} [AddCommGroup W] [DistribMulAction C W] [Finite W]
    (h2U : ∀ u : U, u + u = 0) (h2W : ∀ w : W, w + w = 0)
    (hsimple : ∀ S : AddSubgroup U, (∀ (h : C), ∀ w ∈ S, h • w ∈ S) → S = ⊥ ∨ S = ⊤)
    (hnt : Nontrivial U)
    {N : ℕ} (ι : U →+ (Fin N → C → ZMod 2)) (r : (Fin N → C → ZMod 2) →+ U)
    (hι : ∀ (h : C) (v : U) (n : Fin N) (x : C), ι (h • v) n x = ι v n (h⁻¹ * x))
    (hr : ∀ (h : C) (F : Fin N → C → ZMod 2), r (fun n x => F n (h⁻¹ * x)) = h • r F)
    (hri : ∀ v : U, r (ι v) = v)
    (eU : U ≃+ (U →+ ZMod 2))
    (heU : ∀ (c : C) (u : U),
      eU (c • u) = (dualModule : DistribMulAction C (U →+ ZMod 2)).toSMul.smul c (eU u)) :
    Nat.card ↥(equivHoms C U W) = Nat.card ↥(equivHoms C W U) :=
  card_equivHoms_comm_aux h2U hsimple hnt ι r hι hr hri eU heU (Nat.card W) W
    inferInstance inferInstance inferInstance h2W le_rfl

end HomSymmetry

section PerpLayer

variable {C : Type} [Group C]
variable {M : Type} [AddCommGroup M] [DistribMulAction C M]

/-- The **perp of a subgroup** under a biadditive `ZMod 2` pairing. -/
def pairPerp (B : M →+ M →+ ZMod 2) (S : AddSubgroup M) : AddSubgroup M where
  carrier := {x | ∀ s ∈ S, B x s = 0}
  zero_mem' := fun s _ => by rw [map_zero]; rfl
  add_mem' := fun {x y} hx hy s hs => by
    rw [map_add, AddMonoidHom.add_apply, hx s hs, hy s hs, add_zero]
  neg_mem' := fun {x} hx s hs => by
    rw [map_neg, AddMonoidHom.neg_apply, hx s hs, neg_zero]

theorem mem_pairPerp_iff (B : M →+ M →+ ZMod 2) (S : AddSubgroup M) (x : M) :
    x ∈ pairPerp B S ↔ ∀ s ∈ S, B x s = 0 := Iff.rfl

/-- The perp of a `C`-stable subgroup is `C`-stable when the pairing is invariant. -/
theorem pairPerp_stable (B : M →+ M →+ ZMod 2)
    (hBinv : ∀ (c : C) (x y : M), B (c • x) (c • y) = B x y)
    (S : AddSubgroup M) (hS : ∀ (c : C), ∀ s ∈ S, c • s ∈ S) :
    ∀ (c : C), ∀ x ∈ pairPerp B S, c • x ∈ pairPerp B S := by
  intro c x hx s hs
  have hs' : c⁻¹ • s ∈ S := hS c⁻¹ s hs
  calc B (c • x) s = B (c • x) (c • (c⁻¹ • s)) := by rw [smul_inv_smul]
    _ = B x (c⁻¹ • s) := hBinv c x (c⁻¹ • s)
    _ = 0 := hx _ hs'

/-- **`ann(S) ≅ (M/S)^∨`**: for a nondegenerate pairing on a finite 2-torsion module, the perp
of `S` is additively isomorphic to the dual of `M ⧸ S` — `x ↦ B x` descended through `mk`.
Surjectivity is the nondegeneracy count (`φ_B : M ≃ M^∨` by injectivity + `#M^∨ = #M`). -/
noncomputable def perpEquivDualQuot (B : M →+ M →+ ZMod 2) [Finite M]
    (h2M : ∀ m : M, m + m = 0)
    (hBnd : ∀ x : M, (∀ y : M, B x y = 0) → x = 0) (S : AddSubgroup M) :
    ↥(pairPerp B S) ≃+ ((M ⧸ S) →+ ZMod 2) := by
  haveI : Finite (M →+ ZMod 2) :=
    Finite.of_injective (DFunLike.coe : (M →+ ZMod 2) → (M → ZMod 2)) DFunLike.coe_injective
  -- the underlying additive map: descend B x through the quotient
  set Φ : ↥(pairPerp B S) →+ ((M ⧸ S) →+ ZMod 2) :=
    { toFun := fun x => QuotientAddGroup.lift S (B x.1) (fun s hs => x.2 s hs)
      map_zero' := by
        ext q
        show (B (0 : M)) q = 0
        rw [map_zero]; rfl
      map_add' := fun x y => by
        ext q
        show (B (x.1 + y.1)) q = (B x.1) q + (B y.1) q
        rw [map_add, AddMonoidHom.add_apply] } with hΦdef
  have hΦinj : Function.Injective ⇑Φ := by
    intro x y hxy
    have hsub : x.1 - y.1 = 0 := by
      refine hBnd (x.1 - y.1) (fun m => ?_)
      have hm : (B x.1) m = (B y.1) m := DFunLike.congr_fun hxy (QuotientAddGroup.mk m)
      rw [map_sub, AddMonoidHom.sub_apply, hm, sub_self]
    exact Subtype.ext (sub_eq_zero.mp hsub)
  have hΦsurj : Function.Surjective ⇑Φ := by
    intro f
    -- pull f back to M^∨ and hit it with the bijectivity of φ_B = B
    have hBinj : Function.Injective ⇑B := by
      intro x y hxy
      have : x - y = 0 := by
        refine hBnd (x - y) (fun m => ?_)
        rw [map_sub, AddMonoidHom.sub_apply, DFunLike.congr_fun hxy m, sub_self]
      exact sub_eq_zero.mp this
    haveI : Fintype M := Fintype.ofFinite M
    haveI : Fintype (M →+ ZMod 2) := Fintype.ofFinite _
    have hcards : Fintype.card M = Fintype.card (M →+ ZMod 2) := by
      have := QuadraticFp2.card_addHom_zmod2 M h2M
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, this]
    have hBbij : Function.Bijective ⇑B :=
      (Fintype.bijective_iff_injective_and_card _).mpr ⟨hBinj, hcards⟩
    obtain ⟨x, hx⟩ := hBbij.2 (f.comp (QuotientAddGroup.mk' S))
    have hxperp : x ∈ pairPerp B S := by
      intro s hs
      rw [DFunLike.congr_fun hx s]
      show f (QuotientAddGroup.mk' S s) = 0
      rw [show QuotientAddGroup.mk' S s = 0 from (QuotientAddGroup.eq_zero_iff s).mpr hs,
        map_zero]
    refine ⟨⟨x, hxperp⟩, ?_⟩
    ext q
    show (B x) q = f (QuotientAddGroup.mk q)
    exact DFunLike.congr_fun hx q
  exact AddEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩

/-- Evaluation rule for `perpEquivDualQuot` on a class. -/
theorem perpEquivDualQuot_mk (B : M →+ M →+ ZMod 2) [Finite M]
    (h2M : ∀ m : M, m + m = 0) (hBnd : ∀ x : M, (∀ y : M, B x y = 0) → x = 0)
    (S : AddSubgroup M) (x : ↥(pairPerp B S)) (m : M) :
    perpEquivDualQuot B h2M hBnd S x (QuotientAddGroup.mk m) = B x.1 m := rfl

/-- Equivariance of `perpEquivDualQuot`: the perp carries the restricted action, the dual of
the quotient the `dualModule` action over a compatible quotient action `instQ`. -/
theorem perpEquivDualQuot_equivariant (B : M →+ M →+ ZMod 2) [Finite M]
    (h2M : ∀ m : M, m + m = 0) (hBnd : ∀ x : M, (∀ y : M, B x y = 0) → x = 0)
    (S : AddSubgroup M)
    (hBinv : ∀ (c : C) (x y : M), B (c • x) (c • y) = B x y)
    (hS : ∀ (c : C), ∀ s ∈ S, c • s ∈ S)
    [instQ : DistribMulAction C (M ⧸ S)]
    (hπ : ∀ (c : C) (m : M), (QuotientAddGroup.mk (c • m) : M ⧸ S) = c • QuotientAddGroup.mk m)
    (c : C) (x : ↥(pairPerp B S)) :
    letI := stabSubAction (pairPerp B S) (pairPerp_stable B hBinv S hS)
    letI : DistribMulAction C ((M ⧸ S) →+ ZMod 2) := dualModule
    perpEquivDualQuot B h2M hBnd S (c • x) = c • perpEquivDualQuot B h2M hBnd S x := by
  letI := stabSubAction (pairPerp B S) (pairPerp_stable B hBinv S hS)
  letI : DistribMulAction C ((M ⧸ S) →+ ZMod 2) := dualModule
  ext q
  show B (c • x.1) q = perpEquivDualQuot B h2M hBnd S x (c⁻¹ • QuotientAddGroup.mk q)
  rw [← hπ c⁻¹ q, perpEquivDualQuot_mk]
  calc B (c • x.1) q = B (c • x.1) (c • (c⁻¹ • q)) := by rw [smul_inv_smul]
    _ = B x.1 (c⁻¹ • q) := hBinv c x.1 (c⁻¹ • q)

/-- **The perp count** `#S^⊥ = #(M ⧸ S)`: the nondegenerate-duality cardinality through
`perpEquivDualQuot` and `#(A^∨) = #A` for elementary-2 `A`. -/
theorem card_pairPerp (B : M →+ M →+ ZMod 2) [Finite M]
    (h2M : ∀ m : M, m + m = 0) (hBnd : ∀ x : M, (∀ y : M, B x y = 0) → x = 0)
    (S : AddSubgroup M) :
    Nat.card ↥(pairPerp B S) = Nat.card (M ⧸ S) := by
  rw [Nat.card_congr (perpEquivDualQuot B h2M hBnd S).toEquiv]
  exact QuadraticFp2.card_addHom_zmod2 (M ⧸ S) (fun q =>
    QuotientAddGroup.induction_on q (fun m => by
      rw [← QuotientAddGroup.mk_add, h2M, QuotientAddGroup.mk_zero]))

/-- **Sharpness from the easy inclusion + the cardinality balance**: if `E ≤ S^⊥` and
`#(M ⧸ S) ≤ #E`, then `S^⊥ ≤ E` (the two are equal).  This reduces (H4)'s `hsharp` to the
structural count `#(M ⧸ Deep) ≤ #E`. -/
theorem pairPerp_le_of_card_le (B : M →+ M →+ ZMod 2) [Finite M]
    (h2M : ∀ m : M, m + m = 0) (hBnd : ∀ x : M, (∀ y : M, B x y = 0) → x = 0)
    {S E : AddSubgroup M} (hE : E ≤ pairPerp B S)
    (hcard : Nat.card (M ⧸ S) ≤ Nat.card ↥E) :
    pairPerp B S ≤ E := by
  have hcard' : (pairPerp B S : Set M).ncard ≤ (E : Set M).ncard := by
    show Nat.card ↥(pairPerp B S : Set M) ≤ Nat.card ↥(E : Set M)
    calc Nat.card ↥(pairPerp B S : Set M)
        = Nat.card (M ⧸ S) := card_pairPerp B h2M hBnd S
      _ ≤ Nat.card ↥E := hcard
  have heq : (E : Set M) = (pairPerp B S : Set M) :=
    Set.eq_of_subset_of_ncard_le hE hcard' (Set.toFinite _)
  exact le_of_eq (SetLike.coe_injective heq).symm

end PerpLayer

section Assembly

variable {C : Type} [Group C] [Finite C]

/-- **The abstract `hduality`** (the deep-part proof §F): for a finite 2-torsion `C`-module `M` with a
`C`-invariant nondegenerate pairing `B`, `C`-stable subgroups `Deep ≤ E`, the banked isotropy
`Deep ≤ Deep^⊥`, the ONE sharp instance `Deep^⊥ ≤ E`, and the middle twist (conjugates of `t₀`
trivial on `E/Deep`), the equivariant-Hom counts from a simple, nontrivial, self-dual,
packaged `U` into the deep subgroup and the quotient agree:

`#Hom_C(U, Deep) = #Hom_C(U, M ⧸ Deep)`.

Instantiated at `M := H¹(N,𝔽₂)`, `U := V^∨`, `Deep := deepClassesSubgroup`, `E := U_e`-classes
with the conjugation actions, this is exactly the `hduality` input of the f6 capstone
`card_deepPart_sq_of_duality`. -/
theorem card_equivHoms_deep_eq_quot
    {M : Type} [AddCommGroup M] [DistribMulAction C M] [Finite M]
    {U : Type} [AddCommGroup U] [DistribMulAction C U] [Finite U]
    (h2M : ∀ m : M, m + m = 0) (h2U : ∀ u : U, u + u = 0)
    (hsimple : ∀ S : AddSubgroup U, (∀ (h : C), ∀ w ∈ S, h • w ∈ S) → S = ⊥ ∨ S = ⊤)
    (hnt : Nontrivial U)
    {N : ℕ} (ι : U →+ (Fin N → C → ZMod 2)) (r : (Fin N → C → ZMod 2) →+ U)
    (hι : ∀ (h : C) (v : U) (n : Fin N) (x : C), ι (h • v) n x = ι v n (h⁻¹ * x))
    (hr : ∀ (h : C) (F : Fin N → C → ZMod 2), r (fun n x => F n (h⁻¹ * x)) = h • r F)
    (hri : ∀ v : U, r (ι v) = v)
    (eU : U ≃+ (U →+ ZMod 2))
    (heU : ∀ (c : C) (u : U),
      eU (c • u) = (dualModule : DistribMulAction C (U →+ ZMod 2)).toSMul.smul c (eU u))
    (t₀ : C) (ht₀U : ∃ u : U, t₀ • u ≠ u)
    (B : M →+ M →+ ZMod 2)
    (hBinv : ∀ (c : C) (x y : M), B (c • x) (c • y) = B x y)
    (hBnd : ∀ x : M, (∀ y : M, B x y = 0) → x = 0)
    (Deep E : AddSubgroup M)
    (hDeepStab : ∀ (c : C), ∀ x ∈ Deep, c • x ∈ Deep)
    (hiso : Deep ≤ pairPerp B Deep)
    (hsharp : pairPerp B Deep ≤ E)
    (hmid : ∀ (d : C), ∀ x ∈ E, (d * t₀ * d⁻¹) • x - x ∈ Deep)
    [instDeep : DistribMulAction C ↥Deep]
    (hjeq : ∀ (c : C) (x : ↥Deep), ((c • x : ↥Deep) : M) = c • (x : M))
    [instQ : DistribMulAction C (M ⧸ Deep)]
    (hπeq : ∀ (c : C) (m : M),
      (QuotientAddGroup.mk (c • m) : M ⧸ Deep) = c • QuotientAddGroup.mk m) :
    Nat.card ↥(equivHoms C U ↥Deep) = Nat.card ↥(equivHoms C U (M ⧸ Deep)) := by
  classical
  -- the perp with its restricted action
  set P : AddSubgroup M := pairPerp B Deep with hPdef
  have hPstab : ∀ (c : C), ∀ x ∈ P, c • x ∈ P := pairPerp_stable B hBinv Deep hDeepStab
  letI instP : DistribMulAction C ↥P := stabSubAction P hPstab
  letI instUdual : DistribMulAction C (U →+ ZMod 2) := dualModule
  letI instQdual : DistribMulAction C ((M ⧸ Deep) →+ ZMod 2) := dualModule
  haveI : Finite (M ⧸ Deep) := QuotientAddGroup.finite
  have h2Q : ∀ q : M ⧸ Deep, q + q = 0 := by
    intro q
    refine QuotientAddGroup.induction_on q (fun m => ?_)
    calc (QuotientAddGroup.mk m : M ⧸ Deep) + QuotientAddGroup.mk m
        = QuotientAddGroup.mk (m + m) := rfl
      _ = QuotientAddGroup.mk (0 : M) := by rw [h2M]
      _ = 0 := rfl
  -- Step 1: Hom-symmetry at W := M ⧸ Deep
  have h1 : Nat.card ↥(equivHoms C U (M ⧸ Deep))
      = Nat.card ↥(equivHoms C (M ⧸ Deep) U) :=
    card_equivHoms_comm h2U h2Q hsimple hnt ι r hι hr hri eU heU
  -- Step 2: swap the target to U^∨ along eU
  have h2 : Nat.card ↥(equivHoms C (M ⧸ Deep) U)
      = Nat.card ↥(equivHoms C (M ⧸ Deep) (U →+ ZMod 2)) :=
    card_equivHoms_congr eU (fun c u => heU c u)
  -- Step 3: curry
  have h3 : Nat.card ↥(equivHoms C (M ⧸ Deep) (U →+ ZMod 2))
      = Nat.card ↥(equivHoms C U ((M ⧸ Deep) →+ ZMod 2)) :=
    (card_equivHoms_curry (U := U) (W := M ⧸ Deep)).symm
  -- Step 4: pull the dual of the quotient back to the perp
  have h4 : Nat.card ↥(equivHoms C U ((M ⧸ Deep) →+ ZMod 2))
      = Nat.card ↥(equivHoms C U ↥P) := by
    have hsymm_eq : ∀ (c : C) (φ : (M ⧸ Deep) →+ ZMod 2),
        (perpEquivDualQuot B h2M hBnd Deep).symm (c • φ)
          = c • (perpEquivDualQuot B h2M hBnd Deep).symm φ := by
      intro c φ
      apply (perpEquivDualQuot B h2M hBnd Deep).injective
      rw [AddEquiv.apply_symm_apply,
        perpEquivDualQuot_equivariant B h2M hBnd Deep hBinv hDeepStab hπeq c _,
        AddEquiv.apply_symm_apply]
    exact card_equivHoms_congr (perpEquivDualQuot B h2M hBnd Deep).symm hsymm_eq
  -- Step 5: the SES count at Deep ≤ P
  have hDeepP : Deep ≤ P := hiso
  set D' : AddSubgroup ↥P := Deep.addSubgroupOf P with hD'def
  have hD'stab : ∀ (c : C), ∀ x ∈ D', c • x ∈ D' := by
    intro c x hx
    have : (x : M) ∈ Deep := hx
    exact AddSubgroup.mem_addSubgroupOf.mpr (hDeepStab c _ this)
  letI instD' : DistribMulAction C ↥D' := stabSubAction D' hD'stab
  letI instQ' : DistribMulAction C (↥P ⧸ D') := stabQuotAction D' hD'stab
  have h2P : ∀ x : ↥P, x + x = 0 := fun x => Subtype.ext (h2M x.1)
  have h5 : Nat.card ↥(equivHoms C U ↥P)
      = Nat.card ↥(equivHoms C U ↥D') * Nat.card ↥(equivHoms C U (↥P ⧸ D')) :=
    card_equivHoms_quotient_ses (C := C) (U := U) (A := ↥P) D' h2P ι r hι hr hri
      (fun c w => rfl)
      (fun c w => (stabQuotHom_mk D' hD'stab c w).symm)
  -- Step 6: transport the first factor to ↥Deep
  have h6 : Nat.card ↥(equivHoms C U ↥D') = Nat.card ↥(equivHoms C U ↥Deep) := by
    have heq : ∀ (c : C) (x : ↥D'),
        AddSubgroup.addSubgroupOfEquivOfLe hDeepP (c • x)
          = c • AddSubgroup.addSubgroupOfEquivOfLe hDeepP x := by
      intro c x
      apply Subtype.ext
      calc ((AddSubgroup.addSubgroupOfEquivOfLe hDeepP (c • x) : ↥Deep) : M)
          = (((c • x : ↥D') : ↥P) : M) :=
            AddSubgroup.addSubgroupOfEquivOfLe_apply_coe hDeepP (c • x)
        _ = c • ((x : ↥P) : M) := rfl
        _ = c • ((AddSubgroup.addSubgroupOfEquivOfLe hDeepP x : ↥Deep) : M) := by
            rw [AddSubgroup.addSubgroupOfEquivOfLe_apply_coe hDeepP x]
        _ = ((c • AddSubgroup.addSubgroupOfEquivOfLe hDeepP x : ↥Deep) : M) :=
            (hjeq c _).symm
    exact card_equivHoms_congr (AddSubgroup.addSubgroupOfEquivOfLe hDeepP) heq
  -- Step 7: the middle is killed by the inertia conjugates
  have h7 : Nat.card ↥(equivHoms C U (↥P ⧸ D')) = 1 := by
    refine card_equivHoms_eq_one_of_conjSmulTrivial hsimple t₀ ht₀U ?_
    intro d ξ
    refine QuotientAddGroup.induction_on ξ (fun x => ?_)
    show stabQuotHom D' hD'stab (d * t₀ * d⁻¹) (QuotientAddGroup.mk x) = QuotientAddGroup.mk x
    rw [stabQuotHom_mk, QuotientAddGroup.eq]
    have hmem : (d * t₀ * d⁻¹) • (x : M) - (x : M) ∈ Deep := hmid d (x : M) (hsharp x.2)
    rw [AddSubgroup.mem_addSubgroupOf]
    show -((d * t₀ * d⁻¹) • (x : M)) + (x : M) ∈ Deep
    have := Deep.neg_mem hmem
    rwa [neg_sub, sub_eq_neg_add] at this
  -- assemble
  rw [h1, h2, h3, h4, h5, h6, h7, mul_one]

end Assembly

/-! ## §G — the concrete `E`: mid (depth-`e`) Kummer classes

The `U_e`-classes in π-free norm vocabulary: `IsMidUnit` is the `IsDeepUnit` idiom with
`‖b‖ ≤ 1` (`‖A−1‖ ≤ ‖2‖ = ‖π‖^e`) in place of `‖b‖ < 1`.  `midClassesSubgroup` and
`conjAct_midClasses` mirror the deep versions (`GQ2/AdmissibleCount.lean`) with `≤` for `<`;
`deepClassesSubgroup ≤ midClassesSubgroup` is strict-to-weak.  These are the `E`-side
instantiation inputs of `card_equivHoms_deep_eq_quot` (handoff §8). -/

section MidClasses

open ContCoh LocalKummer

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- **Mid unit** (`U_e` in norm vocabulary): `A = 1 + 2b` with `b` `N`-fixed and `‖b‖ ≤ 1`,
i.e. `‖A − 1‖ ≤ ‖2‖`.  The `≤`-relaxation of `SectionSix.IsDeepUnit`. -/
def IsMidUnit (N : Subgroup (Kummer.GaloisGroup ℚ_[2])) (A : ℚ̄₂) : Prop :=
  A ≠ 0 ∧ (∀ g ∈ N, g • A = A) ∧
    ∃ b : ℚ̄₂, (∀ g ∈ N, g • b = b) ∧ A = 1 + 2 * b ∧ ‖b‖ ≤ 1


/-- **The mid Kummer classes** in `H¹(N, 𝔽₂)`: classes of restricted Kummer cocycles of mid
units (the image of `U_e(K)`).  The subgroup structure mirrors
`GQ2.deepClassesSubgroup`. -/
noncomputable def midClassesSubgroup (N : Subgroup (Kummer.GaloisGroup ℚ_[2])) :
    AddSubgroup (H1 ↥N (ZMod 2)) where
  carrier := {ξ | ∃ A β : ℚ̄₂, IsMidUnit N A ∧ β ^ 2 = A ∧ β ≠ 0 ∧
    H1ofFun ↥N (fun n : ↥N => Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2])) = ξ}
  zero_mem' := by
    refine ⟨1, 1, ⟨one_ne_zero, fun g _ => by rw [AlgEquiv.smul_def, map_one], 0,
      fun g _ => smul_zero g, by ring, by rw [norm_zero]; exact zero_le_one⟩,
      one_pow 2, one_ne_zero, ?_⟩
    have hk1 : (fun n : ↥N => Kummer.kummerCocycleFun (1 : ℚ̄₂)
        ((n : Kummer.GaloisGroup ℚ_[2]))) = 0 := by
      funext n
      exact Kummer.kummerCocycleFun_eq0 (by rw [AlgEquiv.smul_def, map_one])
    rw [hk1, H1ofFun_of_mem (zero_mem _)]
    exact map_zero (H1mk ↥N (ZMod 2))
  add_mem' := by
    rintro ξ η ⟨A₁, β₁, hd₁, hsq₁, hne₁, rfl⟩ ⟨A₂, β₂, hd₂, hsq₂, hne₂, rfl⟩
    obtain ⟨hA₁0, hA₁fix, b₁, hb₁fix, hA₁eq, hb₁⟩ := hd₁
    obtain ⟨hA₂0, hA₂fix, b₂, hb₂fix, hA₂eq, hb₂⟩ := hd₂
    have h2le : ‖(2 : ℚ̄₂)‖ ≤ 1 := by
      rw [show (2 : ℚ̄₂) = 1 + 1 by norm_num]
      exact (IsUltrametricDist.norm_add_le_max 1 1).trans (by rw [norm_one, max_self])
    refine ⟨A₁ * A₂, β₁ * β₂,
      ⟨mul_ne_zero hA₁0 hA₂0, fun g hg => ?_, b₁ + b₂ + 2 * b₁ * b₂, fun g hg => ?_,
        by rw [hA₁eq, hA₂eq]; ring, ?_⟩,
      by rw [mul_pow, hsq₁, hsq₂], mul_ne_zero hne₁ hne₂, ?_⟩
    · rw [AlgEquiv.smul_def, map_mul, ← AlgEquiv.smul_def, ← AlgEquiv.smul_def,
        hA₁fix g hg, hA₂fix g hg]
    · rw [AlgEquiv.smul_def, map_add, map_add, map_mul, map_mul, map_ofNat,
        ← AlgEquiv.smul_def, ← AlgEquiv.smul_def, hb₁fix g hg, hb₂fix g hg]
    · have hprod : ‖(2 : ℚ̄₂) * b₁ * b₂‖ ≤ 1 := by
        rw [norm_mul, norm_mul]
        calc ‖(2 : ℚ̄₂)‖ * ‖b₁‖ * ‖b₂‖
            ≤ 1 * ‖b₁‖ * ‖b₂‖ := by
              have := mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right h2le (norm_nonneg b₁)) (norm_nonneg b₂)
              simpa using this
          _ = ‖b₁‖ * ‖b₂‖ := by ring
          _ ≤ ‖b₁‖ * 1 := mul_le_mul_of_nonneg_left hb₂ (norm_nonneg b₁)
          _ = ‖b₁‖ := mul_one _
          _ ≤ 1 := hb₁
      refine le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_
      rw [max_le_iff]
      exact ⟨le_trans (IsUltrametricDist.norm_add_le_max _ _)
        (by rw [max_le_iff]; exact ⟨hb₁, hb₂⟩), hprod⟩
    · have hLHS : (fun n : ↥N => Kummer.kummerCocycleFun (β₁ * β₂)
          ((n : Kummer.GaloisGroup ℚ_[2])))
          = (fun n : ↥N => Kummer.kummerCocycleFun β₁ ((n : Kummer.GaloisGroup ℚ_[2])))
            + fun n : ↥N => Kummer.kummerCocycleFun β₂ ((n : Kummer.GaloisGroup ℚ_[2])) := by
        funext n
        exact kcf_mul_of_fixed (by rw [mul_pow, hsq₁, hsq₂]) hsq₁ hsq₂ hne₁ hne₂
          (hA₁fix (n : Kummer.GaloisGroup ℚ_[2]) n.2) (hA₂fix (n : Kummer.GaloisGroup ℚ_[2]) n.2)
      rw [hLHS, GQ2.DeepPart.H1ofFun_add (GQ2.DeepPart.kummerRestrict_mem_Z1 hsq₁ hne₁ hA₁fix)
        (GQ2.DeepPart.kummerRestrict_mem_Z1 hsq₂ hne₂ hA₂fix)]
  neg_mem' := by
    intro ξ hξ
    rwa [neg_eq_of_add_eq_zero_left (GQ2.h1_add_self ξ)]


variable {C : Type} [Group C] [TopologicalSpace C]
variable (ρ : ContinuousMonoidHom AbsGalQ2 C)


end MidClasses

/-! ## §G′ — the middle twist (H5): residue-trivial conjugation moves mid by deep

Paper Lemma 6.10 in the π-free norm vocabulary.  `IsResidueTrivial N g` says `g` acts
trivially on the residue field of `K = ℚ̄₂^N`: every `N`-fixed integral `x` moves by norm
`< 1`.  The twist lemma: for such `g` and a mid class `ξ = [κ_β]` (`β² = A = 1 + 2b`,
`‖b‖ ≤ 1`), the difference `conjAct ρ g ξ − ξ` is a DEEP class.  Since `H¹` is 2-torsion the
difference is the sum `[κ_{g•β}] + [κ_β] = [κ_{(g•β)β}]`, and the PRODUCT
`(g•A)·A = 1 + 2·(g•b + b + 2(g•b)b)` is a deep unit: `g•b + b = (g•b − b) + 2b` has norm
`< 1` by residue-triviality at `x := b` (`p = 2` turns the paper's division `(g•A)/A` into a
product — no root-factoring needed).  Residue-triviality is conjugation-stable
(`norm_galois` + normality of `ker ρ`) and depends only on the image under `ρ` at the
`conjAct` level (`conjAct_ker`), so a single residue-trivial lift `g₀` of `t₀` yields the
literal `hmid` input of `card_equivHoms_deep_eq_quot` for ALL `C`-conjugates `d·t₀·d⁻¹`
(`conjAct_surjInv_conj_mid_sub_mem_deep`).  The arithmetic fact that tame-inertia lifts ARE
residue-trivial is delivered at instantiation (f8). -/

section MidTwist

open ContCoh LocalKummer

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- **Residue-trivial element** (norm form): `g` moves every `N`-fixed integral `x` by norm
`< 1` — i.e. `g` acts trivially on the residue field of `K = ℚ̄₂^N`.  Tame inertia lifts are
residue-trivial (arithmetic input, f8); this predicate is all the twist lemma consumes. -/
def IsResidueTrivial (N : Subgroup (Kummer.GaloisGroup ℚ_[2]))
    (g : Kummer.GaloisGroup ℚ_[2]) : Prop :=
  ∀ x : ℚ̄₂, (∀ m ∈ N, m • x = x) → ‖x‖ ≤ 1 → ‖g • x - x‖ < 1

variable {C : Type} [Group C] [TopologicalSpace C]
variable (ρ : ContinuousMonoidHom AbsGalQ2 C)

/-- **Residue-triviality is conjugation-stable** (for `N = ker ρ`, normal): conjugating the
test vector back by `h` preserves `N`-fixedness (normality) and the norm (`norm_galois`). -/
theorem IsResidueTrivial.conj {g : Kummer.GaloisGroup ℚ_[2]}
    (hg : IsResidueTrivial (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) g)
    (h : Kummer.GaloisGroup ℚ_[2]) :
    IsResidueTrivial (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (h * g * h⁻¹) := by
  intro x hxfix hx1
  have hyfix : ∀ m : Kummer.GaloisGroup ℚ_[2],
      m ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) → m • (h⁻¹ • x) = h⁻¹ • x := by
    intro m hm
    have hconj : (h⁻¹⁻¹ * m * h⁻¹) • x = x := hxfix _ (conj_mem_ker ρ h⁻¹ ⟨m, hm⟩)
    calc m • (h⁻¹ • x) = h⁻¹ • ((h⁻¹⁻¹ * m * h⁻¹) • x) := by
          rw [← mul_smul, ← mul_smul]; congr 1; group
      _ = h⁻¹ • x := by rw [hconj]
  have hy1 : ‖h⁻¹ • x‖ ≤ 1 := by rw [norm_galois]; exact hx1
  have hkey : (h * g * h⁻¹) • x - x = h • (g • (h⁻¹ • x) - h⁻¹ • x) := by
    rw [AlgEquiv.smul_def h, map_sub, ← AlgEquiv.smul_def, ← AlgEquiv.smul_def,
      smul_inv_smul, ← mul_smul, ← mul_smul]
  rw [hkey, norm_galois]
  exact hg (h⁻¹ • x) hyfix hy1

/-- **The middle twist, class level** (paper Lemma 6.10 / the (H5) core): a residue-trivial
`g` moves a mid class by a deep class.  With `ξ = [κ_β]`, `β² = A = 1 + 2b` mid, 2-torsion
turns the difference into `[κ_{g•β}] + [κ_β] = [κ_{(g•β)β}]` (`kcf_mul_of_fixed`), and
`(g•A)·A = 1 + 2(g•b + b + 2(g•b)b)` is a deep unit by residue-triviality at `x := b`. -/
theorem conjAct_mid_sub_mem_deep (g : Kummer.GaloisGroup ℚ_[2])
    (hg : IsResidueTrivial (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) g)
    {ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)}
    (hξ : ξ ∈ midClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :
    conjAct ρ g ξ - ξ ∈ deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) := by
  obtain ⟨A, β, hmid', hsq, hβ0, rfl⟩ := hξ
  obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hmid'
  have h2lt1 : ‖(2 : ℚ̄₂)‖ < 1 := by
    rw [show (2 : ℚ̄₂) = algebraMap ℚ_[2] ℚ̄₂ 2 from (map_ofNat _ 2).symm,
      norm_algebraMap' (𝕜' := ℚ̄₂) (2 : ℚ_[2])]
    exact Padic.norm_p_lt_one
  -- conjugated data (the §4 idiom: `g` in the `GaloisGroup` view, witnesses before `conjAct`)
  have hgA0 : g • A ≠ 0 := by rw [AlgEquiv.smul_def]; simpa using hA0
  have hgβ0 : g • β ≠ 0 := by rw [AlgEquiv.smul_def]; simpa using hβ0
  have hgsq : (g • β) ^ 2 = g • A := by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, ← map_pow, hsq]
  have hgAeq : g • A = 1 + 2 * (g • b) := by
    rw [hAeq, AlgEquiv.smul_def, map_add, map_one, map_mul, map_ofNat, ← AlgEquiv.smul_def]
  have hsqprod : ((g • β) * β) ^ 2 = (g • A) * A := by
    rw [mul_pow, hgsq, hsq]
  have hgAfix : ∀ m : Kummer.GaloisGroup ℚ_[2],
      m ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) → m • (g • A) = g • A := by
    intro m hm
    have hconj : (g⁻¹ * m * g) • A = A := hAfix _ (conj_mem_ker ρ g ⟨m, hm⟩)
    calc m • (g • A) = g • ((g⁻¹ * m * g) • A) := by
          rw [← mul_smul, ← mul_smul]; congr 1; group
      _ = g • A := by rw [hconj]
  have hgbfix : ∀ m : Kummer.GaloisGroup ℚ_[2],
      m ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) → m • (g • b) = g • b := by
    intro m hm
    have hconj : (g⁻¹ * m * g) • b = b := hbfix _ (conj_mem_ker ρ g ⟨m, hm⟩)
    calc m • (g • b) = g • ((g⁻¹ * m * g) • b) := by
          rw [← mul_smul, ← mul_smul]; congr 1; group
      _ = g • b := by rw [hconj]
  refine ⟨(g • A) * A, (g • β) * β, ⟨mul_ne_zero hgA0 hA0, fun m hm => ?_,
      g • b + b + 2 * (g • b) * b, fun m hm => ?_, by rw [hgAeq, hAeq]; ring, ?_⟩,
    hsqprod, mul_ne_zero hgβ0 hβ0, ?_⟩
  · -- `N`-fixedness of the product `(g•A)·A`
    rw [AlgEquiv.smul_def, map_mul, ← AlgEquiv.smul_def, ← AlgEquiv.smul_def,
      hgAfix m hm, hAfix m hm]
  · -- `N`-fixedness of `b' = g•b + b + 2(g•b)b`
    rw [AlgEquiv.smul_def, map_add, map_add, map_mul, map_mul, map_ofNat,
      ← AlgEquiv.smul_def, ← AlgEquiv.smul_def, hgbfix m hm, hbfix m hm]
  · -- `‖b'‖ < 1`: the inertia estimate.  `g•b + b = (g•b − b) + 2b`, all three pieces small.
    have hgb1 : ‖g • b‖ ≤ 1 := by rw [norm_galois]; exact hb
    have hsum : ‖g • b + b‖ < 1 := by
      have hsplit : g • b + b = g • b - b + 2 * b := by ring
      rw [hsplit]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
      rw [max_lt_iff]
      refine ⟨hg b hbfix hb, ?_⟩
      calc ‖2 * b‖ = ‖(2 : ℚ̄₂)‖ * ‖b‖ := norm_mul _ _
        _ ≤ ‖(2 : ℚ̄₂)‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = ‖(2 : ℚ̄₂)‖ := mul_one _
        _ < 1 := h2lt1
    have hprod : ‖2 * (g • b) * b‖ < 1 := by
      rw [norm_mul, norm_mul]
      calc ‖(2 : ℚ̄₂)‖ * ‖g • b‖ * ‖b‖
          ≤ ‖(2 : ℚ̄₂)‖ * 1 * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hgb1 (norm_nonneg _)) hb (norm_nonneg _)
              (by positivity)
        _ = ‖(2 : ℚ̄₂)‖ := by ring
        _ < 1 := h2lt1
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
    rw [max_lt_iff]
    exact ⟨hsum, hprod⟩
  · -- the class identity `[κ_{(g•β)β}] = conjAct ρ g [κ_β] − [κ_β]`
    have hZ1g : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
          Kummer.kummerCocycleFun (g • β) (n : AbsGalQ2))
        ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) :=
      GQ2.DeepPart.kummerRestrict_mem_Z1 hgsq hgβ0 hgAfix
    have hZ1 : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
          Kummer.kummerCocycleFun β (n : AbsGalQ2))
        ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) :=
      GQ2.DeepPart.kummerRestrict_mem_Z1 hsq hβ0 hAfix
    have heq : conjAct ρ g (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
          (fun n => Kummer.kummerCocycleFun β (n : AbsGalQ2)))
        = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
          (fun n => Kummer.kummerCocycleFun (g • β) (n : AbsGalQ2)) :=
      calc conjAct ρ g (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
              (fun n => Kummer.kummerCocycleFun β (n : AbsGalQ2)))
          = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
              (fun n => Kummer.kummerCocycleFun β ((conjMap ρ g n : AbsGalQ2))) :=
            conjAct_h1ofFun ρ g (GQ2.DeepPart.kummerRestrict_mem_Z1 hsq hβ0 hAfix)
        _ = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
              (fun n => Kummer.kummerCocycleFun (g • β) (n : AbsGalQ2)) := by
            congr 1; funext n; exact kcf_conj β g (n : AbsGalQ2)
    exact calc
      H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
          (fun n => Kummer.kummerCocycleFun ((g • β) * β) (n : AbsGalQ2))
          = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
              ((fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
                  Kummer.kummerCocycleFun (g • β) (n : AbsGalQ2))
                + fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
                  Kummer.kummerCocycleFun β (n : AbsGalQ2)) := by
            congr 1
            funext n
            exact kcf_mul_of_fixed hsqprod hgsq hsq hgβ0 hβ0
              (hgAfix n.1 n.2) (hAfix n.1 n.2)
        _ = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
              (fun n => Kummer.kummerCocycleFun (g • β) (n : AbsGalQ2))
            + H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
              (fun n => Kummer.kummerCocycleFun β (n : AbsGalQ2)) :=
            GQ2.DeepPart.H1ofFun_add hZ1g hZ1
        _ = conjAct ρ g (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
              (fun n => Kummer.kummerCocycleFun β (n : AbsGalQ2)))
            + H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
              (fun n => Kummer.kummerCocycleFun β (n : AbsGalQ2)) := by
            rw [heq]
        _ = conjAct ρ g (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
              (fun n => Kummer.kummerCocycleFun β (n : AbsGalQ2)))
            - H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
              (fun n => Kummer.kummerCocycleFun β (n : AbsGalQ2)) := by
            rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left
              (h1_add_self (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
                (fun n => Kummer.kummerCocycleFun β (n : AbsGalQ2))))]

/-- **The middle twist, `C`-conjugate form** — the literal `hmid` input of
`card_equivHoms_deep_eq_quot` at the `conjModule` instantiation: if SOME lift `g₀` of `t₀` is
residue-trivial, then for EVERY `d : C` the `surjInv`-lift of `d·t₀·d⁻¹` twists mid classes by
deep classes (`conjAct` only sees the `ρ`-image by `conjAct_ker`, and residue-triviality is
conjugation-stable). -/
theorem conjAct_surjInv_conj_mid_sub_mem_deep (hρsurj : Function.Surjective ⇑ρ)
    {g₀ : AbsGalQ2} {t₀ : C} (hg₀ : ρ g₀ = t₀)
    (hg₀rt : IsResidueTrivial (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) g₀) (d : C)
    {ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)}
    (hξ : ξ ∈ midClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :
    conjAct ρ (Function.surjInv hρsurj (d * t₀ * d⁻¹)) ξ - ξ
      ∈ deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) := by
  have hkey : conjAct ρ (Function.surjInv hρsurj (d * t₀ * d⁻¹)) ξ
      = conjAct ρ (Function.surjInv hρsurj d * g₀ * (Function.surjInv hρsurj d)⁻¹) ξ :=
    conjAct_ker ρ _ _ (by
      rw [Function.surjInv_eq hρsurj, map_mul, map_mul, map_inv,
        Function.surjInv_eq hρsurj, hg₀]) ξ
  rw [hkey]
  exact conjAct_mid_sub_mem_deep ρ _ (hg₀rt.conj ρ (Function.surjInv hρsurj d)) hξ

end MidTwist

/-! ## §H — the `U`-side inputs: self-duality from the invariant form, inertia dualization

The remaining module-theoretic inputs of `card_equivHoms_deep_eq_quot` at `U := V^∨`:
`eU` (built from 6.17's invariant-form package `(q, hq, hns, hinv)` through the polar
self-duality `V ≃+ V^∨` and the banked double-dual `evalDualEquiv`) and `ht₀U` (the
`hram`-inertia nontriviality transported to the dual by functional separation). -/

section SelfDual

open QuadraticFp2

variable {C : Type} [Group C]
variable {V : Type} [AddCommGroup V] [DistribMulAction C V] [Finite V]

/-- The polar form of a nonsingular quadratic map as a self-duality `V ≃+ V^∨`:
`v ↦ polar q v ·` — additive by `IsQuadraticFp2`, injective by nonsingularity, bijective by the
`𝔽₂`-dual count. -/
noncomputable def polarSelfDual (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (h2V : ∀ v : V, v + v = 0) : V ≃+ (V →+ ZMod 2) := by
  haveI : Finite (V →+ ZMod 2) :=
    Finite.of_injective (DFunLike.coe : (V →+ ZMod 2) → (V → ZMod 2)) DFunLike.coe_injective
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype (V →+ ZMod 2) := Fintype.ofFinite _
  refine AddEquiv.ofBijective
    (AddMonoidHom.mk'
      (fun v => AddMonoidHom.mk' (fun w => polar q v w) (fun w w' => hq.polar_add_right v w w'))
      (fun v v' => by ext w; exact hq.polar_add_left v v' w))
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩)
  · intro v v' hvv
    by_contra hne
    obtain ⟨w, hw⟩ := hns (v - v') (sub_ne_zero.mpr hne)
    apply hw
    have h1 : polar q v w = polar q v' w := DFunLike.congr_fun hvv w
    have h2 : polar q (v - v' + v') w = polar q (v - v') w + polar q v' w :=
      hq.polar_add_left _ _ _
    rw [sub_add_cancel, h1] at h2
    -- h2 : polar q v' w = polar q (v - v') w + polar q v' w
    have h3 : (0 : ZMod 2) + polar q v' w = polar q (v - v') w + polar q v' w := by
      rw [zero_add]
      exact h2
    exact (add_right_cancel h3).symm
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_addHom_zmod2 V h2V]


/-- Equivariance of the polar self-duality (target under `dualModule`). -/
theorem polarSelfDual_equivariant (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (h2V : ∀ v : V, v + v = 0) (hinv : IsInvariant C q)
    (c : C) (v : V) :
    polarSelfDual q hq hns h2V (c • v)
      = (dualModule : DistribMulAction C (V →+ ZMod 2)).toSMul.smul c
          (polarSelfDual q hq hns h2V v) := by
  ext w
  show polar q (c • v) w = polar q v (c⁻¹ • w)
  conv_lhs => rw [show w = c • (c⁻¹ • w) from (smul_inv_smul c w).symm]
  show q (c • v + c • (c⁻¹ • w)) + q (c • v) + q (c • (c⁻¹ • w)) = polar q v (c⁻¹ • w)
  rw [← smul_add, hinv, hinv, hinv]
  rfl

/-- **The `eU` input**: the induced self-duality of the dual module `U := V^∨` — the polar
self-duality inverted, then evaluated into the double dual. -/
noncomputable def dualSelfDual (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (h2V : ∀ v : V, v + v = 0) :
    (V →+ ZMod 2) ≃+ ((V →+ ZMod 2) →+ ZMod 2) :=
  (polarSelfDual q hq hns h2V).symm.trans (evalDualEquiv h2V)

/-- **The `heU` input**: equivariance of `dualSelfDual` (source under `dualModule`, target under
`dualModule` over it). -/
theorem dualSelfDual_equivariant (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (h2V : ∀ v : V, v + v = 0) (hinv : IsInvariant C q)
    (c : C) (φ : V →+ ZMod 2) :
    letI : DistribMulAction C (V →+ ZMod 2) := dualModule
    dualSelfDual q hq hns h2V
        ((dualModule : DistribMulAction C (V →+ ZMod 2)).toSMul.smul c φ)
      = (dualModule : DistribMulAction C ((V →+ ZMod 2) →+ ZMod 2)).toSMul.smul c
          (dualSelfDual q hq hns h2V φ) := by
  letI : DistribMulAction C (V →+ ZMod 2) := dualModule
  have hsymm : (polarSelfDual q hq hns h2V).symm
      ((dualModule : DistribMulAction C (V →+ ZMod 2)).toSMul.smul c φ)
      = c • (polarSelfDual q hq hns h2V).symm φ := by
    apply (polarSelfDual q hq hns h2V).injective
    rw [AddEquiv.apply_symm_apply,
      polarSelfDual_equivariant q hq hns h2V hinv c ((polarSelfDual q hq hns h2V).symm φ),
      AddEquiv.apply_symm_apply]
  show evalDualEquiv h2V ((polarSelfDual q hq hns h2V).symm _) = _
  rw [hsymm, evalDualEquiv_equivariant h2V c]
  rfl

omit [Finite V] in
/-- **The `ht₀U` input**: inertia nontriviality dualizes — if `t₀` moves some vector of `V`, it
moves some functional of `V^∨` (under `dualModule`; by `𝔽₂`-functional separation). -/
theorem exists_dualModule_smul_ne (h2V : ∀ v : V, v + v = 0) (t₀ : C)
    (h : ∃ v : V, t₀ • v ≠ v) :
    ∃ φ : V →+ ZMod 2,
      (dualModule : DistribMulAction C (V →+ ZMod 2)).toSMul.smul t₀ φ ≠ φ := by
  obtain ⟨v, hv⟩ := h
  by_contra hall
  have hall' : ∀ φ : V →+ ZMod 2,
      (dualModule : DistribMulAction C (V →+ ZMod 2)).toSMul.smul t₀ φ = φ := by
    intro φ
    by_contra hne
    exact hall ⟨φ, hne⟩
  have hfix : ∀ w : V, t₀⁻¹ • w = w := by
    intro w
    by_contra hne
    obtain ⟨ψ, hψ⟩ := LocalKummer.exists_functional_ne_zero h2V (sub_ne_zero.mpr hne)
    apply hψ
    have := DFunLike.congr_fun (hall' ψ) w
    -- (t₀ • ψ) w = ψ (t₀⁻¹ • w)
    rw [map_sub, show ψ (t₀⁻¹ • w) = ψ w from this, sub_self]
  apply hv
  exact (inv_smul_smul t₀ v ▸ hfix (t₀ • v)).symm

end SelfDual

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * eq. (93) = ⟦eq-squareclassgraded⟧
  * eq. (94) = ⟦eq-unitorth⟧
  * Lemma 6.10 = ⟦lem-middlelayer⟧
  * Lemma 6.11 = ⟦lem-faithfulprojective⟧
-/
