import GQ2.AdmissibleCount
import GQ2.GaussCount

/-!
# The deep/quotient Hom-count duality  (ticket P-15f7)

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

Ticket: P-15f7 (board `docs/tickets.md`); consumer: `card_deepPart_sq_of_duality` (P-15f6).
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
    simp only [stabQuotHom_mk]
    rw [mul_smul]
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
    have := DFunLike.congr_fun (Subtype.ext_iff.mp h) (e.symm b)
    simpa [e.apply_symm_apply] using this
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

/-- **Separation of points by `𝔽₂`-functionals** (local copy — the banked
`GQ2.exists_addHom_ne_zero` lives in the heavy `LocalLiftingDuality` import chain): a nonzero
vector of a finite 2-torsion group is detected by an additive functional to `ZMod 2`. -/
theorem exists_functional_ne_zero [Finite V] (h2 : ∀ v : V, v + v = 0)
    {v : V} (hv : v ≠ 0) : ∃ f : V →+ ZMod 2, f v ≠ 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact h2 v)
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let b := Module.Free.chooseBasis (ZMod 2) V
  by_contra h
  refine hv (b.forall_coord_eq_zero_iff.mp fun i => ?_)
  by_contra hne
  exact h ⟨(b.coord i).toAddMonoidHom, by simpa using hne⟩

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

@[simp] theorem precompHom_apply {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (ψ : B →+ ZMod 2) (a : A) : precompHom f ψ a = ψ (f a) := rfl

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

@[simp] theorem evalDualHom_apply {W : Type} [AddCommGroup W] (w : W) (φ : W →+ ZMod 2) :
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
    obtain ⟨φ, hφ⟩ := exists_functional_ne_zero h2 (sub_ne_zero.mpr hne)
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

@[simp] theorem evalDualEquiv_apply {W : Type} [AddCommGroup W] [Finite W]
    (h2 : ∀ w : W, w + w = 0) (w : W) (φ : W →+ ZMod 2) :
    evalDualEquiv h2 w φ = φ w := rfl

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
    have := DFunLike.congr_fun (hσ φ) u
    exact this

end SplitOff

end GQ2
