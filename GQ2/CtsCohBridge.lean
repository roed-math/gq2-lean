import GQ2.Cohomology

/-!
# Bridge to Mathlib's continuous cohomology (`Mathlib.Algebra.Category.ContinuousCohomology`)

Our `GQ2/Cohomology.lean` provides *explicit inhomogeneous* continuous cochains in degrees `≤ 2`
over the elementary coefficient interface `[DistribMulAction G M] [ContinuousSMul G M]`.  Mathlib's
`continuousCohomology (n) : Action (TopModuleCat R) G ⥤ TopModuleCat R` (built from **homogeneous**
cochains; Richard Hill's `rmhi/ctsToDiscrete` upstreamed) is the general-degree, functorial object.
Its concrete low-degree cochain description is a stated TODO — except degree `0`, where Mathlib
already has `ContinuousCohomology.continuousCohomologyZeroIso : continuousCohomology R G 0 ≅
invariants R G`.  This file is the seam between the two.

Note: Hill's standalone repo *redefines* this now-upstreamed core, so it is not co-importable with
Mathlib; we build on the canonical Mathlib version (= his upstreamed work).

**Step 1: the coefficient bridge.**  A topological `G`-module `M` is a continuous `ℤ`-representation
`g ↦ (m ↦ g • m)` (`toContRep`), hence an object `toTopRep : TopRep ℤ G` and, via
`TopRepEquivActionTop`, an object `toAction : Action (TopModuleCat ℤ) G` — exactly the coefficient
Mathlib's `continuousCohomology` consumes.

Steps 2 (`ContCoh.Hⁱ ≅ (continuousCohomology ℤ G i).obj (toAction M)`, `i ≤ 2`) and 3 (transport of
the cup products) build on this; see `docs/formalization-plan.md`.
-/

open CategoryTheory TopRep ContRepresentation ContinuousCohomology

namespace GQ2.ContCoh

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- For a fixed `g : G`, the additive self-map `m ↦ g • m` of a topological `G`-module, packaged
as a continuous `ℤ`-linear endomorphism. -/
def smulCLM (g : G) : M →L[ℤ] M where
  toLinearMap := (DistribSMul.toAddMonoidHom M g).toIntLinearMap
  cont := continuous_const_smul g

@[simp] lemma smulCLM_apply (g : G) (m : M) : smulCLM g m = g • m := rfl

/-- The **continuous `ℤ`-representation** underlying a topological `G`-module `M`: `g ↦ (m ↦ g•m)`.
This is the coefficient object of Mathlib's `continuousCohomology` corresponding to our elementary
`[DistribMulAction G M] [ContinuousSMul G M]` interface. -/
def toContRep : ContRepresentation ℤ G M where
  toFun := smulCLM
  map_one' := by ext m; simp
  map_mul' g h := by ext m; simp [mul_smul]

@[simp] lemma toContRep_apply (g : G) (m : M) : toContRep (G := G) g m = g • m := rfl

/-- `M` viewed as an object of the category `TopRep ℤ G` of topological representations. -/
def toTopRep : TopRep ℤ G := TopRep.of (toContRep (G := G) (M := M))

@[simp] lemma toTopRep_V : (toTopRep (G := G) (M := M)).V = M := rfl

omit [IsTopologicalGroup G] in
@[simp] lemma toTopRep_ρ_apply (g : G) (m : M) : (toTopRep (G := G) (M := M)).ρ g m = g • m := rfl

/-- `M` as an object of `Action (TopModuleCat ℤ) G` — the coefficient category of Mathlib's
`continuousCohomology`.  Built directly (not via the `TopRep ≌ Action` equivalence) so that
`.V` and `.ρ` are definitionally `M` and `g ↦ (m ↦ g•m)`, which keeps `invariants` concrete. -/
noncomputable def toAction : Action (TopModuleCat ℤ) G where
  V := TopModuleCat.of ℤ M
  ρ :=
  { toFun g := TopModuleCat.ofHom (smulCLM g)
    map_one' := ConcreteCategory.ext (by ext m; simp [smulCLM])
    map_mul' g h := ConcreteCategory.ext (by ext m; simp [smulCLM, mul_smul]) }

omit [IsTopologicalGroup G] in
@[simp] lemma toAction_V : (toAction (G := G) (M := M)).V = TopModuleCat.of ℤ M := rfl

omit [IsTopologicalGroup G] in
@[simp] lemma toAction_ρ_hom_apply (g : G) (m : M) :
    ((toAction (G := G) (M := M)).ρ g).hom m = g • m := rfl

/-! ## Step 2, degree 0: `H⁰` bridge

Mathlib's `continuousCohomology ℤ G 0` is `≅ invariants` (`continuousCohomologyZeroIso`), and the
invariants of `toAction M` are exactly our `H0 G M = Mᴳ` — both are `{x | ∀ g, g • x = x}` (the
membership predicates are definitionally equal, since `(toAction.ρ g).hom x = g • x` by `rfl`). -/

/-- The `G`-invariants of `toAction M` are our `H0 G M = Mᴳ` (identity on carriers). -/
def invariantsEquivH0 : ((invariants ℤ G).obj (toAction (G := G) (M := M))) ≃+ H0 G M where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- **Degree-0 bridge**: our `H0 G M` is additively isomorphic to Mathlib's continuous cohomology
`(continuousCohomology ℤ G 0).obj (toAction M)`, via `continuousCohomologyZeroIso` and the
invariants identification. -/
noncomputable def H0Equiv :
    ((continuousCohomology ℤ G 0).obj (toAction (G := G) (M := M))) ≃+ H0 G M :=
  (((continuousCohomologyZeroIso ℤ G).app
    (toAction (G := G) (M := M))).toContinuousLinearEquiv.toLinearEquiv.toAddEquiv).trans
    invariantsEquivH0

/-!
## Steps 2 (`i = 1, 2`) and 3: the remaining work

The degree-`0` bridge above is complete because Mathlib already provides
`continuousCohomologyZeroIso`.  The degree-`1` and degree-`2` bridges
(`ContCoh.H1 ≅ (continuousCohomology ℤ G 1).obj (toAction M)`, and likewise `H2`) require the
**homogeneous ↔ inhomogeneous** cochain comparison in low degree — Mathlib's own stated TODO for
`ContinuousCohomology` ("give the usual description of cochains in terms of `n`-ary functions").
Concretely, degree `1`: our inhomogeneous continuous `1`-cocycle `c : G → M`
(`c(gh) = c(g) + g • c(h)`) corresponds to the homogeneous cochain `f(g₀,g₁) = g₀ • c(g₀⁻¹ g₁)`,
and one checks this is a chain isomorphism, hence an iso on homology.  That is a substantial
formalization (Mathlib's abstract analogue over `Rep R G`, `inhomogeneousCochainsFunctor`/the iso
to `groupCohomology`, is a multi-hundred-line development) and is the natural place to coordinate
with the Mathlib/`ctsToDiscrete` effort.  Once `H1`/`H2` bridges exist, the cup products of
`GQ2/CupProduct.lean` transport onto `continuousCohomology` along them (step 3).
-/

end GQ2.ContCoh
