/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import GQ2.Cohomology
public import GQ2.Statement

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# `μₙ` as a finite discrete `G_ℚ₂`-module

The literature axioms **B6** (local Tate duality) and **B7** (local Euler characteristic) are stated
for finite discrete `G_ℚ₂`-modules, and B6 uses `μₙ` (the group of `n`-th roots of unity, as the
dualizing object).  This file makes `μₙ ⊆ ℚ̄₂` such a module, i.e. a *legal coefficient* for
`GQ2.ContCoh` over `AbsGalQ2 = Field.absoluteGaloisGroup ℚ_[2]`.

## What is built

Mathlib has `rootsOfUnity n L : Subgroup Lˣ` and the tautological Galois action on `Lˣ`
(via `AlgEquiv.smul_units_def`), but **not** the induced action on `rootsOfUnity`, nor its
additive/discrete/continuous packaging (the cyclotomic-character development works pointwise, via
`g (ζ : Lˣ) = ζ ^ m`).  We supply, for any field extension `L / K`:

* `GQ2.galRootsOfUnity : MulDistribMulAction (L ≃ₐ[K] L) (rootsOfUnity n L)` — the Galois action, by
  restriction of the units action (`μₙ` is stable since `(g • ζ)ⁿ = g • ζⁿ = g • 1 = 1`);
* `GQ2.galRootsOfUnityAdd : DistribMulAction (L ≃ₐ[K] L) (Additive (rootsOfUnity n L))` — the same
  action written **additively**, the project's discrete-`G`-module convention;

and then, over `ℚ₂`:

* `GQ2.MuN n := Additive (rootsOfUnity n ℚ̄₂)`, which carries the finite **discrete** topology it
  inherits as a subspace of the valued field `ℚ̄₂` (`Finite.instDiscreteTopology`: a finite subset
  of a `T₁` space is discrete), with `DistribMulAction AbsGalQ2 (MuN n)` and
  `ContinuousSMul AbsGalQ2 (MuN n)` — the latter from the Krull-open stabilizers
  (`continuousSMul_iff_stabilizer_isOpen` + `stabilizer_isOpen_of_isIntegral`).

## Conventions / citations

* The additive convention matches `GQ2/DiscreteModule.lean` (the discrete-module conventions) and `GQ2/Cohomology.lean` (the continuous-cohomology API):
  a discrete `G`-module is `[AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]`.  `μₙ` is naturally *multiplicative*, so we transport
  it through `Additive`.
* Continuity of the Galois action on `μₙ` is the classical fact that each `ζ ∈ μₙ` lies in a finite
  (cyclotomic) subextension, hence has open stabilizer in the Krull topology.  Cf. Neukirch–Schmidt–
  Wingberg, *Cohomology of Number Fields*, and Serre, *Galois Cohomology* I §1–2 (discrete modules).

The stress tests at the bottom confirm the result: `H⁰/H¹/H²(G_ℚ₂, μₙ)` all typecheck — `μₙ` is
a legal `ContCoh` coefficient — and `μₙ` is finite.  `#print axioms` of every proof = the standard
three.
-/

namespace GQ2

open scoped Classical

/-! ## The Galois action on `μₙ` (pure algebra, any field extension) -/

section Action

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (n : ℕ)

/-- **The Galois action on `μₙ(L) = rootsOfUnity n L`.**  `Gal(L/K)` acts by restricting its
tautological action on `Lˣ`; `μₙ` is a stable subgroup because a field automorphism preserves
`ζⁿ = 1` (`(g • ζ)ⁿ = g • ζⁿ = g • 1 = 1`). -/
instance galRootsOfUnity : MulDistribMulAction (L ≃ₐ[K] L) (rootsOfUnity n L) where
  smul g ζ := ⟨g • (ζ : Lˣ), by
    rw [mem_rootsOfUnity, ← smul_pow', (mem_rootsOfUnity n (ζ : Lˣ)).1 ζ.2, smul_one]⟩
  one_smul ζ := Subtype.ext (one_smul _ (ζ : Lˣ))
  mul_smul g h ζ := Subtype.ext (mul_smul g h (ζ : Lˣ))
  smul_one g := Subtype.ext (smul_one g)
  smul_mul g ζ ξ := Subtype.ext (smul_mul' g (ζ : Lˣ) (ξ : Lˣ))

@[simp] private lemma galRootsOfUnity_val (g : L ≃ₐ[K] L) (ζ : rootsOfUnity n L) :
    ((g • ζ : rootsOfUnity n L) : Lˣ) = g • (ζ : Lˣ) := rfl

/-- **`μₙ` as an additive `Gal(L/K)`-module.**  The project's cohomology takes additive modules;
`Additive` turns the multiplicative Galois action into a `DistribMulAction`.  All laws reduce
definitionally to the multiplicative ones (`Additive`'s `+`/`0` are `μₙ`'s `*`/`1`). -/
instance galRootsOfUnityAdd :
    DistribMulAction (L ≃ₐ[K] L) (Additive (rootsOfUnity n L)) where
  smul g x := Additive.ofMul (g • x.toMul)
  one_smul x := by
    show Additive.ofMul ((1 : L ≃ₐ[K] L) • x.toMul) = x
    rw [one_smul]; rfl
  mul_smul g h x := by
    show Additive.ofMul ((g * h) • x.toMul)
        = Additive.ofMul (g • (Additive.ofMul (h • x.toMul)).toMul)
    rw [mul_smul]; rfl
  smul_zero g := by
    show Additive.ofMul (g • (1 : rootsOfUnity n L)) = 0
    rw [smul_one]; rfl
  smul_add g x y := by
    show Additive.ofMul (g • (x.toMul * y.toMul))
        = Additive.ofMul (g • x.toMul) + Additive.ofMul (g • y.toMul)
    rw [smul_mul']; rfl

@[simp] private lemma galRootsOfUnityAdd_toMul (g : L ≃ₐ[K] L) (x : Additive (rootsOfUnity n L)) :
    (g • x).toMul = g • x.toMul := rfl

/-- The units action and the field action agree under the coercion `Lˣ → L`. -/
lemma val_smul_units (g : L ≃ₐ[K] L) (u : Lˣ) : ((g • u : Lˣ) : L) = g • (u : L) := by
  rw [AlgEquiv.smul_units_def, Units.coe_map]; rfl

/-- If an equivariant map is injective, it preserves stabilizers. -/
private lemma stabilizer_eq_of_injective {G' X Y : Type*} [Group G']
    [MulAction G' X] [MulAction G' Y] (f : X → Y) (hf : Function.Injective f)
    (hf' : ∀ (g : G') (x : X), f (g • x) = g • f x) (x : X) :
    MulAction.stabilizer G' x = MulAction.stabilizer G' (f x) := by
  ext g
  simp only [MulAction.mem_stabilizer_iff, ← hf' g x, hf.eq_iff]

/-- **The stabilizer bridge.**  The stabilizer of `x : Additive (μₙ)` in `Gal(L/K)` coincides with
the stabilizer of the underlying field element `↑↑x.toMul : L` — the reduction that lets us reuse
the Krull-topology openness lemma `stabilizer_isOpen_of_isIntegral`. -/
lemma stabilizer_additive_eq_field (x : Additive (rootsOfUnity n L)) :
    MulAction.stabilizer (L ≃ₐ[K] L) x
      = MulAction.stabilizer (L ≃ₐ[K] L) (((x.toMul : Lˣ) : L)) := by
  refine stabilizer_eq_of_injective (G' := L ≃ₐ[K] L) (fun y => ((y.toMul : Lˣ) : L)) ?_ ?_ x
  · exact fun a b h => Additive.toMul.injective (Subtype.ext (Units.ext h))
  · intro g y
    simp only [galRootsOfUnityAdd_toMul, galRootsOfUnity_val, val_smul_units]

end Action

/-! ## `μₙ(ℚ̄₂)` as a finite discrete `G_ℚ₂`-module -/

section Q2

/-- Abbreviation for the algebraic closure of `ℚ₂` (carries the valued topology via
ClassFieldTheory, so finite subsets — in particular `μₙ` — are discrete). -/
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable (n : ℕ) [NeZero n]

/-- **`μₙ` over `ℚ₂`**, the group of `n`-th roots of unity in a fixed algebraic closure of `ℚ₂`,
written additively: a finite discrete `G_ℚ₂`-module.  It carries the subspace topology from the
valued field `ℚ̄₂`, which is discrete because `μₙ` is finite and `ℚ̄₂` is `T₁`. -/
abbrev MuN : Type := Additive (rootsOfUnity n ℚ̄₂)

/-- The Galois action of `G_ℚ₂` on `μₙ`, transported along
`AbsGalQ2 = (ℚ̄₂ ≃ₐ[ℚ₂] ℚ̄₂)` (definitional). -/
noncomputable instance : MulDistribMulAction AbsGalQ2 (rootsOfUnity n ℚ̄₂) :=
  inferInstanceAs (MulDistribMulAction (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂) _)

/-- The additive Galois action of `G_ℚ₂` on `μₙ`. -/
noncomputable instance : DistribMulAction AbsGalQ2 (MuN n) :=
  inferInstanceAs (DistribMulAction (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂) _)

/-- **Continuity of the Galois action on `μₙ`** (Krull topology): the stabilizer of each
`x : μₙ` is the stabilizer of an algebraic (hence open-stabilized) field element. -/
instance continuousSMul_gal : ContinuousSMul (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂) (MuN n) := by
  refine continuousSMul_iff_stabilizer_isOpen.2 fun x => ?_
  rw [stabilizer_additive_eq_field (K := ℚ_[2]) n x]
  exact stabilizer_isOpen_of_isIntegral _

/-- `ContinuousSMul` over `G_ℚ₂`, transported. -/
noncomputable instance : ContinuousSMul AbsGalQ2 (MuN n) :=
  inferInstanceAs (ContinuousSMul (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂) (MuN n))

/-! ## Stress tests (acceptance) -/

/-- **Faithfulness check.** `μₙ` is a legal `ContCoh` coefficient over `G_ℚ₂`: `H⁰/H¹/H²` all form.
This forces the whole instance bundle (`AddCommGroup`, discrete `TopologicalSpace`,
`IsTopologicalAddGroup`, `DistribMulAction`, `ContinuousSMul`). -/
example : True := by
  have _ : AddSubgroup (MuN n) := ContCoh.H0 AbsGalQ2 (MuN n)
  have _ : AddCommGroup (ContCoh.H1 AbsGalQ2 (MuN n)) := inferInstance
  have _ : AddCommGroup (ContCoh.H2 AbsGalQ2 (MuN n)) := inferInstance
  trivial

/-- `μₙ` is finite. -/
example : Finite (MuN n) := inferInstance

/-- `μₙ` is a discrete module. -/
example : DiscreteTopology (MuN n) := inferInstance

/-- `μₙ` has exactly `n` elements: over the algebraically closed, characteristic-`0` field `ℚ̄₂`
every `n`-th root of unity is present and distinct, so `μₙ ≅ ℤ/n` as an abstract group. -/
example : Nat.card (MuN n) = n :=
  (Nat.card_congr Additive.toMul).trans (HasEnoughRootsOfUnity.natCard_rootsOfUnity _ n)

/-- The additive `G_ℚ₂`-action is genuinely the multiplicative Galois action on roots of unity. -/
example (g : AbsGalQ2) (ζ : rootsOfUnity n ℚ̄₂) :
    (g • (Additive.ofMul ζ : MuN n)).toMul = g • ζ := rfl

end Q2

end GQ2
