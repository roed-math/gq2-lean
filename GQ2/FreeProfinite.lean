import Mathlib

/-!
# Free profinite groups

The paper's presentation lives in the **free profinite group** on the four generators
`σ, τ, x₀, x₁`.  Mathlib has no `FreeProfiniteGroup` (see `docs/foundations-audit.md`), but it now
has `ProfiniteGrp.profiniteCompletion` (the profinite completion functor, left adjoint to the
forgetful functor `ProfiniteGrp ⥤ GrpCat`, by A. Topaz).  Composing it with the ordinary free
group gives free profinite groups, with the expected universal property.

* `GQ2.FreeProfiniteGroup X` — the free profinite group on `X`.
* `GQ2.FreeProfiniteGroup.of` — the inclusion of generators.
* `GQ2.FreeProfiniteGroup.homEquiv` — the universal property: continuous homs
  `FreeProfiniteGroup X ⟶ P` into a profinite group `P` biject with set maps `X → P`.
-/

open CategoryTheory

namespace GQ2

universe u

/-- The **free profinite group** on a type `X`: the profinite completion of the discrete free
group `FreeGroup X`. -/
noncomputable def FreeProfiniteGroup (X : Type u) : ProfiniteGrp.{u} :=
  ProfiniteGrp.profiniteCompletion.obj (GrpCat.of (FreeGroup X))

/-- The canonical inclusion of the generators `X → FreeProfiniteGroup X`. -/
noncomputable def FreeProfiniteGroup.of {X : Type u} (x : X) : FreeProfiniteGroup X :=
  ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (FreeGroup X)) (FreeGroup.of x)

/-- `GrpCat` morphisms between `of`-objects are exactly monoid homs. -/
def grpCatHomEquiv (A : Type u) [Group A] (P : ProfiniteGrp.{u}) :
    (GrpCat.of A ⟶ GrpCat.of (P : Type u)) ≃ (A →* P) where
  toFun f := f.hom
  invFun φ := GrpCat.ofHom φ
  left_inv f := GrpCat.ofHom_hom f
  right_inv φ := GrpCat.hom_ofHom φ

/-- **Universal property of the free profinite group.**  Morphisms of profinite groups
`FreeProfiniteGroup X ⟶ P` correspond naturally to set maps `X → P`.  Obtained by composing the
profinite-completion adjunction with the universal property of the free group. -/
noncomputable def FreeProfiniteGroup.homEquiv (X : Type u) (P : ProfiniteGrp.{u}) :
    (FreeProfiniteGroup X ⟶ P) ≃ (X → P) :=
  (ProfiniteGrp.ProfiniteCompletion.homEquiv (GrpCat.of (FreeGroup X)) P).trans <|
    (grpCatHomEquiv (FreeGroup X) P).trans FreeGroup.lift.symm

/-- **Naturality / usability of the universal property.**  The bijection `homEquiv` sends a
continuous hom `f : FreeProfiniteGroup X ⟶ P` to the set map `x ↦ f (of x)` — i.e. `homEquiv`
really is "restrict to the generators".  This makes the universal property usable for defining maps
out of `FreeProfiniteGroup X` (and, in turn, profinite presentations such as `Γ_A`). -/
@[simp]
lemma FreeProfiniteGroup.homEquiv_apply {X : Type u} (P : ProfiniteGrp.{u})
    (f : FreeProfiniteGroup X ⟶ P) (x : X) :
    FreeProfiniteGroup.homEquiv X P f x = f (FreeProfiniteGroup.of x) := by
  simp only [FreeProfiniteGroup.homEquiv, grpCatHomEquiv,
    ProfiniteGrp.ProfiniteCompletion.homEquiv]
  rfl

end GQ2
