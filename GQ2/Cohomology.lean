import GQ2.DiscreteModule

/-!
# Continuous cohomology of topological groups in degrees ≤ 2  (ticket T-02, unlock U2)

Continuous (inhomogeneous) cochain cohomology `H⁰, H¹, H²` of a topological group `G` with
coefficients in a topological `G`-module `M`, following Serre, *Galois Cohomology* I §2.2.
This is the coefficient system for the literature axioms B3 (Demushkin), B6 (local Tate
duality), B7 (local Euler characteristic) and B9 (Evens/Kahn) — see
`docs/formalization-plan.md` (U2).  **Design constraints**: no derived functors, no new
coefficient structures (module = Mathlib classes, cf. `GQ2/DiscreteModule.lean`), everything
explicit and human-checkable.

## Definitions

Cochains are *plain functions* (`G → M`, `G × G → M`); continuity is carried by the subgroups:

* `ContCoh.C1, C2` — continuous cochains;
* `ContCoh.dZero, dOne, dTwo` — the inhomogeneous differentials
  `(δ⁰m)(g) = g•m − m`, `(δ¹ψ)(g,h) = g•ψ(h) − ψ(gh) + ψ(g)`,
  `(δ²φ)(g,h,k) = g•φ(h,k) − φ(gh,k) + φ(g,hk) − φ(g,h)`  (with `δ∘δ = 0` proved);
* `ContCoh.Z1 = C1 ⊓ ker δ¹`, `Z2 = C2 ⊓ ker δ²` — continuous cocycles
  (readable forms: `mem_Z1_iff`, `mem_Z2_iff`);
* `ContCoh.B1 = δ⁰(M)`, `B2 = δ¹(C1)` — continuous coboundaries (`B1_le_Z1`, `B2_le_Z2`);
* `ContCoh.H0` (invariants, an `AddSubgroup M`), `ContCoh.H1`, `ContCoh.H2` (cocycles mod
  coboundaries, with `AddCommGroup` instances).

## Functoriality

One general pullback along a *compatible pair*: a continuous hom `π : G →ₜ* Q` together with a
continuous additive map `f : N →+ M` intertwining the actions (`f (π g • n) = g • f n`) induces
`H0comap`, `H1comap`, `H2comap : Hⁱ(Q,N) →+ Hⁱ(G,M)`.  Specializations:

* **restriction** `res0/res1/res2 : Hⁱ(G,M) →+ Hⁱ(U,M)` for `U : Subgroup G`
  (`π` = inclusion, `f` = id — Mathlib's subgroup action instances make this definitional);
* **inflation**: for `π : G ↠ Q` and a `Q`-module `N`, instantiate the `G`-module as `N` with
  the composed action `letI := DistribMulAction.compHom N π.toMonoidHom`; then
  `hcompat` is `rfl` and `H1comap π (AddMonoidHom.id N) …` *is* inflation.  (Kept as a recipe
  rather than a def to avoid carrying two actions on one type; the finite-level comparison is
  ticket T-03.)

Corestriction (degree 1, open finite-index `U`) is ticket T-18's explicit coset formula; cup
products relative to a pairing `M →+ N →+ P` are ticket T-04.  Both build on the `Z`-level API
here.

## Stress tests

`dOne_comp_dZero = 0`, `dTwo_comp_dOne = 0`; for the **trivial action**: `B1 = ⊥`,
`mem_Z1_iff_of_trivial` (1-cocycles = continuous additive-style homs), `H1equivZ1OfTrivial`
(`H¹ ≃+ Z¹`), `H0_eq_top_of_trivial`; `Z1_apply_one` (cocycles vanish at `1`).
-/

namespace GQ2

namespace ContCoh

section Defs

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (M : Type*) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-! ## Degree 0 -/

/-- `H⁰(G, M)`: the invariants `M^G`, as an additive subgroup of `M`. -/
def H0 : AddSubgroup M where
  carrier := {m | ∀ g : G, g • m = m}
  zero_mem' g := smul_zero g
  add_mem' := fun {a b} ha hb g => by rw [smul_add, ha g, hb g]
  neg_mem' := fun {a} ha g => by rw [smul_neg, ha g]

/-! ## Cochains and differentials -/

/-- Continuous 1-cochains `C¹(G, M)`. -/
def C1 : AddSubgroup (G → M) where
  carrier := {φ | Continuous φ}
  zero_mem' := continuous_const
  add_mem' ha hb := ha.add hb
  neg_mem' ha := ha.neg

/-- Continuous 2-cochains `C²(G, M)`. -/
def C2 : AddSubgroup (G × G → M) where
  carrier := {φ | Continuous φ}
  zero_mem' := continuous_const
  add_mem' ha hb := ha.add hb
  neg_mem' ha := ha.neg

/-- The differential `δ⁰ : M → C¹`, `(δ⁰m)(g) = g•m − m`. -/
def dZero : M →+ (G → M) where
  toFun m := fun g => g • m - m
  map_zero' := by funext g; simp
  map_add' m n := by funext g; simp only [smul_add, Pi.add_apply]; abel

/-- The differential `δ¹ : C¹ → C²`, `(δ¹ψ)(g,h) = g•ψ(h) − ψ(gh) + ψ(g)`. -/
def dOne : (G → M) →+ (G × G → M) where
  toFun ψ := fun p => p.1 • ψ p.2 - ψ (p.1 * p.2) + ψ p.1
  map_zero' := by funext p; simp
  map_add' a b := by funext p; simp only [smul_add, Pi.add_apply]; abel

/-- The differential `δ² : C² → C³`,
`(δ²φ)(g,h,k) = g•φ(h,k) − φ(gh,k) + φ(g,hk) − φ(g,h)`. -/
def dTwo : (G × G → M) →+ (G × G × G → M) where
  toFun φ := fun t =>
    t.1 • φ (t.2.1, t.2.2) - φ (t.1 * t.2.1, t.2.2) + φ (t.1, t.2.1 * t.2.2) - φ (t.1, t.2.1)
  map_zero' := by funext t; simp
  map_add' a b := by funext t; simp only [smul_add, Pi.add_apply]; abel

/-! ## Cocycles, coboundaries, cohomology -/

/-- Continuous 1-cocycles: continuous cochains killed by `δ¹`. -/
def Z1 : AddSubgroup (G → M) := C1 G M ⊓ (dOne G M).ker

/-- Continuous 2-cocycles: continuous cochains killed by `δ²`. -/
def Z2 : AddSubgroup (G × G → M) := C2 G M ⊓ (dTwo G M).ker

/-- 1-coboundaries `δ⁰(M)` (automatically continuous). -/
def B1 : AddSubgroup (G → M) := (dZero G M).range

/-- 2-coboundaries `δ¹(C¹)` — the image of the **continuous** 1-cochains. -/
def B2 : AddSubgroup (G × G → M) := (C1 G M).map (dOne G M)

/-- `H¹(G, M)`: continuous 1-cocycles modulo 1-coboundaries. -/
def H1 : Type _ := Z1 G M ⧸ (B1 G M).addSubgroupOf (Z1 G M)

instance : AddCommGroup (H1 G M) :=
  inferInstanceAs (AddCommGroup (Z1 G M ⧸ (B1 G M).addSubgroupOf (Z1 G M)))

/-- The class map `Z¹ → H¹`. -/
def H1mk : Z1 G M →+ H1 G M := QuotientAddGroup.mk' _

/-- `H²(G, M)`: continuous 2-cocycles modulo coboundaries of continuous 1-cochains. -/
def H2 : Type _ := Z2 G M ⧸ (B2 G M).addSubgroupOf (Z2 G M)

instance : AddCommGroup (H2 G M) :=
  inferInstanceAs (AddCommGroup (Z2 G M ⧸ (B2 G M).addSubgroupOf (Z2 G M)))

/-- The class map `Z² → H²`. -/
def H2mk : Z2 G M →+ H2 G M := QuotientAddGroup.mk' _

end Defs

/-! ## Basic API -/

section Lemmas

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousSMul G M] in
@[simp] lemma mem_H0_iff {m : M} : m ∈ H0 G M ↔ ∀ g : G, g • m = m := Iff.rfl

omit [Group G] [IsTopologicalGroup G] [DistribMulAction G M] [ContinuousSMul G M] in
@[simp] lemma mem_C1_iff {φ : G → M} : φ ∈ C1 G M ↔ Continuous φ := Iff.rfl

omit [Group G] [IsTopologicalGroup G] [DistribMulAction G M] [ContinuousSMul G M] in
@[simp] lemma mem_C2_iff {φ : G × G → M} : φ ∈ C2 G M ↔ Continuous φ := Iff.rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- `δ¹ ∘ δ⁰ = 0`: coboundaries are cocycles (chain-complex sanity). -/
theorem dOne_comp_dZero : (dOne G M).comp (dZero G M) = 0 := by
  ext m p
  simp only [AddMonoidHom.comp_apply, dOne, dZero, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    mul_smul, smul_sub, AddMonoidHom.zero_apply, Pi.zero_apply]
  abel

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- `δ² ∘ δ¹ = 0` (chain-complex sanity). -/
theorem dTwo_comp_dOne : (dTwo G M).comp (dOne G M) = 0 := by
  ext ψ t
  simp only [AddMonoidHom.comp_apply, dTwo, dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    mul_smul, smul_sub, smul_add, mul_assoc, AddMonoidHom.zero_apply, Pi.zero_apply]
  abel

omit [IsTopologicalGroup G] [ContinuousSMul G M] in
/-- Membership in `Z¹`, in cocycle-identity form: continuous crossed homomorphisms. -/
theorem mem_Z1_iff {φ : G → M} :
    φ ∈ Z1 G M ↔ Continuous φ ∧ ∀ g h : G, φ (g * h) = φ g + g • φ h := by
  simp only [Z1, AddSubgroup.mem_inf, mem_C1_iff, AddMonoidHom.mem_ker, dOne,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, funext_iff, Prod.forall, Pi.zero_apply]
  refine and_congr_right fun _ => forall₂_congr fun g h => ?_
  rw [sub_add_eq_add_sub, sub_eq_zero, eq_comm, add_comm (g • φ h) (φ g)]

omit [IsTopologicalGroup G] [ContinuousSMul G M] in
/-- Membership in `Z²`, in Serre's cocycle-identity form
`g•φ(h,k) + φ(g,hk) = φ(gh,k) + φ(g,h)`. -/
theorem mem_Z2_iff {φ : G × G → M} :
    φ ∈ Z2 G M ↔ Continuous φ ∧ ∀ g h k : G,
      g • φ (h, k) + φ (g, h * k) = φ (g * h, k) + φ (g, h) := by
  simp only [Z2, AddSubgroup.mem_inf, mem_C2_iff, AddMonoidHom.mem_ker, dTwo,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, funext_iff, Prod.forall, Pi.zero_apply]
  refine and_congr_right fun _ => forall₃_congr fun g h k => ?_
  rw [show g • φ (h, k) - φ (g * h, k) + φ (g, h * k) - φ (g, h)
      = (g • φ (h, k) + φ (g, h * k)) - (φ (g * h, k) + φ (g, h)) from by abel,
    sub_eq_zero]

omit [IsTopologicalGroup G] [ContinuousSMul G M] in
theorem Z1_le_C1 : Z1 G M ≤ C1 G M := inf_le_left

omit [IsTopologicalGroup G] [ContinuousSMul G M] in
theorem Z2_le_C2 : Z2 G M ≤ C2 G M := inf_le_left

omit [IsTopologicalGroup G] in
theorem B1_le_Z1 : B1 G M ≤ Z1 G M := by
  rintro _ ⟨m, rfl⟩
  refine AddSubgroup.mem_inf.mpr
    ⟨(continuous_id.smul continuous_const).sub continuous_const, ?_⟩
  rw [AddMonoidHom.mem_ker, ← AddMonoidHom.comp_apply, dOne_comp_dZero,
    AddMonoidHom.zero_apply]

theorem B2_le_Z2 : B2 G M ≤ Z2 G M := by
  rintro _ ⟨ψ, hψ, rfl⟩
  refine AddSubgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact ((continuous_fst.smul (hψ.comp continuous_snd)).sub
      (hψ.comp (continuous_fst.mul continuous_snd))).add (hψ.comp continuous_fst)
  · rw [AddMonoidHom.mem_ker, ← AddMonoidHom.comp_apply, dTwo_comp_dOne,
      AddMonoidHom.zero_apply]

omit [IsTopologicalGroup G] [ContinuousSMul G M] in
theorem H1mk_surjective : Function.Surjective (H1mk G M) :=
  QuotientAddGroup.mk'_surjective _

omit [IsTopologicalGroup G] [ContinuousSMul G M] in
theorem H2mk_surjective : Function.Surjective (H2mk G M) :=
  QuotientAddGroup.mk'_surjective _

omit [IsTopologicalGroup G] [ContinuousSMul G M] in
/-- A 1-cocycle vanishes at `1`. -/
theorem Z1_apply_one (φ : Z1 G M) : φ.1 1 = 0 := by
  have h := (mem_Z1_iff.mp φ.2).2 1 1
  simpa using h

end Lemmas

/-! ## Functoriality: pullback along a compatible pair

Given `π : G →ₜ* Q` continuous and `f : N →+ M` continuous with `f (π g • n) = g • f n`,
cochains pull back by `φ ↦ f ∘ φ ∘ π` (in each degree), inducing `Hⁱ(Q,N) →+ Hⁱ(G,M)`.
Restriction and inflation are instances of this single construction (see module docstring). -/

section Comap

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
variable {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DistribMulAction Q N] [ContinuousSMul Q N]
variable (π : ContinuousMonoidHom G Q) (f : N →+ M) (hf : Continuous f)
  (hcompat : ∀ (g : G) (n : N), f (π g • n) = g • f n)

/-- Degree-0 pullback: invariants map to invariants (no continuity of `f` needed). -/
def H0comap : H0 Q N →+ H0 G M where
  toFun n := ⟨f n.1, fun g => by rw [← hcompat, n.2 (π g)]⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' a b := Subtype.ext (map_add f _ _)

/-- Degree-1 pullback on cocycles: `φ ↦ f ∘ φ ∘ π`. -/
def Z1comap : Z1 Q N →+ Z1 G M where
  toFun φ := ⟨fun g => f (φ.1 (π g)), by
    obtain ⟨hφc, hφ⟩ := mem_Z1_iff.mp φ.2
    refine mem_Z1_iff.mpr ⟨hf.comp (hφc.comp π.continuous_toFun), fun g h => ?_⟩
    rw [map_mul, hφ (π g) (π h), map_add, hcompat]⟩
  map_zero' := Subtype.ext (funext fun g => map_zero f)
  map_add' a b := Subtype.ext (funext fun g => map_add f _ _)

/-- Degree-2 pullback on cocycles: `φ ↦ f ∘ φ ∘ (π × π)`. -/
def Z2comap : Z2 Q N →+ Z2 G M where
  toFun φ := ⟨fun p => f (φ.1 (π p.1, π p.2)), by
    obtain ⟨hφc, hφ⟩ := mem_Z2_iff.mp φ.2
    refine mem_Z2_iff.mpr ⟨hf.comp (hφc.comp ((π.continuous_toFun.comp continuous_fst).prodMk
      (π.continuous_toFun.comp continuous_snd))), fun g h k => ?_⟩
    rw [map_mul, map_mul, ← map_add f, ← hφ (π g) (π h) (π k), map_add, hcompat]⟩
  map_zero' := Subtype.ext (funext fun p => map_zero f)
  map_add' a b := Subtype.ext (funext fun p => map_add f _ _)

/-- Degree-1 pullback on cohomology. -/
def H1comap : H1 Q N →+ H1 G M :=
  QuotientAddGroup.map _ _ (Z1comap π f hf hcompat) (by
    rintro ⟨φ, hφ⟩ hmem
    rw [AddSubgroup.mem_addSubgroupOf] at hmem
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    obtain ⟨n, hn⟩ := hmem
    refine ⟨f n, funext fun g => ?_⟩
    have hg : φ (π g) = π g • n - n := (congrFun hn (π g)).symm
    show g • f n - f n = f (φ (π g))
    rw [hg, map_sub, hcompat])

/-- Degree-2 pullback on cohomology. -/
def H2comap : H2 Q N →+ H2 G M :=
  QuotientAddGroup.map _ _ (Z2comap π f hf hcompat) (by
    rintro ⟨φ, hφ⟩ hmem
    rw [AddSubgroup.mem_addSubgroupOf] at hmem
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    obtain ⟨ψ, hψc, hψ⟩ := hmem
    refine ⟨fun g => f (ψ (π g)), hf.comp (hψc.comp π.continuous_toFun), funext fun p => ?_⟩
    have hp : φ (π p.1, π p.2) = π p.1 • ψ (π p.2) - ψ (π p.1 * π p.2) + ψ (π p.1) :=
      (congrFun hψ (π p.1, π p.2)).symm
    show p.1 • f (ψ (π p.2)) - f (ψ (π (p.1 * p.2))) + f (ψ (π p.1)) = f (φ (π p.1, π p.2))
    rw [hp, map_add, map_sub, hcompat, map_mul])

end Comap

/-! ### Restriction to a subgroup -/

section Res

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (M : Type*) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
variable (U : Subgroup G)

/-- The inclusion of a subgroup as a continuous monoid hom. -/
def subgroupIncl : ContinuousMonoidHom U G := ⟨U.subtype, continuous_subtype_val⟩

/-- Restriction `H⁰(G,M) → H⁰(U,M)`. -/
def res0 : H0 G M →+ H0 U M :=
  H0comap (subgroupIncl G U) (AddMonoidHom.id M) fun _ _ => rfl

/-- Restriction `H¹(G,M) → H¹(U,M)`. -/
def res1 : H1 G M →+ H1 U M :=
  H1comap (subgroupIncl G U) (AddMonoidHom.id M) continuous_id fun _ _ => rfl

/-- Restriction `H²(G,M) → H²(U,M)`. -/
def res2 : H2 G M →+ H2 U M :=
  H2comap (subgroupIncl G U) (AddMonoidHom.id M) continuous_id fun _ _ => rfl

end Res

/-! ## The trivial-action stress tests -/

section Trivial

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
variable (htriv : ∀ (g : G) (m : M), g • m = m)

include htriv in
omit [IsTopologicalGroup G] [ContinuousSMul G M] in
/-- With trivial action, `Z¹` is exactly the continuous additive-style homs
(`φ(gh) = φ(g) + φ(h)`). -/
theorem mem_Z1_iff_of_trivial {φ : G → M} :
    φ ∈ Z1 G M ↔ Continuous φ ∧ ∀ g h : G, φ (g * h) = φ g + φ h := by
  rw [mem_Z1_iff]
  simp only [htriv]

include htriv in
omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- With trivial action there are no nonzero 1-coboundaries. -/
theorem B1_eq_bot_of_trivial : B1 G M = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨m, rfl⟩
  rw [AddSubgroup.mem_bot]
  funext g
  show g • m - m = 0
  rw [htriv, sub_self]

include htriv in
omit [IsTopologicalGroup G] [ContinuousSMul G M] in
/-- With trivial action, `H¹ ≃+ Z¹` (nothing is killed). -/
noncomputable def H1equivZ1OfTrivial : H1 G M ≃+ Z1 G M := by
  refine (QuotientAddGroup.quotientAddEquivOfEq (M := (B1 G M).addSubgroupOf (Z1 G M))
    (N := ⊥) ?_).trans QuotientAddGroup.quotientBot
  rw [B1_eq_bot_of_trivial htriv]
  ext ⟨φ, hφ⟩
  simp [AddSubgroup.mem_bot, Subtype.ext_iff]

include htriv in
omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- With trivial action, everything is invariant. -/
theorem H0_eq_top_of_trivial : H0 G M = ⊤ := by
  rw [eq_top_iff]
  exact fun m _ => fun g => htriv g m

end Trivial

/-! ## Cocycle algebra (T-03)

A few more identities for continuous 1-cocycles, beyond `Z1_apply_one`. -/

section CocycleAlgebra

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

omit [IsTopologicalGroup G] [ContinuousSMul G M] in
/-- The value of a 1-cocycle at an inverse: `φ(g⁻¹) = −g⁻¹ • φ(g)`. -/
theorem Z1_apply_inv (φ : Z1 G M) (g : G) : φ.1 g⁻¹ = - (g⁻¹ • φ.1 g) := by
  have hcyc := (mem_Z1_iff.mp φ.2).2
  have h := hcyc g g⁻¹
  rw [mul_inv_cancel, Z1_apply_one] at h
  have h2 : g • φ.1 g⁻¹ = - φ.1 g := eq_neg_of_add_eq_zero_right h.symm
  have h3 := congrArg (g⁻¹ • ·) h2
  simpa only [smul_smul, inv_mul_cancel, one_smul, smul_neg] using h3

end CocycleAlgebra

/-! ## Coefficient functoriality (T-03)

The `π = id` special case of `Hicomap`: a continuous `G`-equivariant additive map `f : N →+ M`
(same group `G`) induces `Hⁱ(G,N) →+ Hⁱ(G,M)`.  Needed by B6/B9 (pairing- and connecting-maps
on coefficients). -/

section Coefficients

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
variable {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DistribMulAction G N] [ContinuousSMul G N]
variable (f : N →+ M) (hf : Continuous f) (hcompat : ∀ (g : G) (n : N), f (g • n) = g • f n)

/-- Coefficient functoriality in degree 0. -/
def mapCoeff0 : H0 G N →+ H0 G M :=
  H0comap (ContinuousMonoidHom.id G) f fun g n => hcompat g n

/-- Coefficient functoriality in degree 1. -/
def mapCoeff1 : H1 G N →+ H1 G M :=
  H1comap (ContinuousMonoidHom.id G) f hf fun g n => hcompat g n

/-- Coefficient functoriality in degree 2. -/
def mapCoeff2 : H2 G N →+ H2 G M :=
  H2comap (ContinuousMonoidHom.id G) f hf fun g n => hcompat g n

end Coefficients

/-! ## Inflation (T-03)

The `f = id` special case of `Hicomap` along a continuous hom `π : G →ₜ* Q` whose associated
`Q`-action on `M` agrees, through `π`, with a given `G`-action (`hπ : π g • m = g • m`).  For a
continuous surjection `π : G ↠ Q` this is inflation `Hⁱ(Q,M) →+ Hⁱ(G,M)` from a quotient. -/

section Inflation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M] [DistribMulAction Q M] [ContinuousSMul Q M]
variable (π : ContinuousMonoidHom G Q) (hπ : ∀ (g : G) (m : M), π g • m = g • m)

/-- Inflation in degree 0. -/
def inf0 : H0 Q M →+ H0 G M :=
  H0comap π (AddMonoidHom.id M) fun g m => hπ g m

/-- Inflation in degree 1. -/
def inf1 : H1 Q M →+ H1 G M :=
  H1comap π (AddMonoidHom.id M) continuous_id fun g m => hπ g m

/-- Inflation in degree 2. -/
def inf2 : H2 Q M →+ H2 G M :=
  H2comap π (AddMonoidHom.id M) continuous_id fun g m => hπ g m

end Inflation

/-!
## Note: comparison with Mathlib's finite group cohomology (deferred)

The plan lists a stress test that for **finite** `G` these definitions agree with Mathlib's
`groupCohomology.H1/H2`.  We deliberately **defer** it: Mathlib's group cohomology is built over
`Rep k G` (`k`-linear representations, `ModuleCat`-based, no topology), so a comparison needs a
bridge `Rep ℤ G ↝ ` (our `DistribMulAction`-modules) matching the inhomogeneous-cochain
conventions of `cocycles₁`/`cocycles₂` (for finite `G` continuity is automatic, so the underlying
groups do coincide).  That bridge is a *verification* task (step 3), **not** needed to state any
of B3/B6/B7/B9 — those are phrased entirely in terms of the `ContCoh` API here.  The
human-checkability of the definitions is already secured by the explicit cocycle-identity forms
`mem_Z1_iff`/`mem_Z2_iff` (Serre GC I §2.2) and the trivial-action characterization
`H1equivZ1OfTrivial`.
-/

end ContCoh

end GQ2
