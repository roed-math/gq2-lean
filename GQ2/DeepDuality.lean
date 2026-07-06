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

end GQ2
