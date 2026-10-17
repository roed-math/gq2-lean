/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5.1
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ContinuousCohomologyIso
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Comparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2.Character
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Basic
public import GQ2.EvensKahn
public import GQ2.TauCeti.GaloisDict

@[expose] public section

/-!
# A2: the cohomology, cup and Kummer dictionary between gq2 and Tau Ceti

Ticket A2 of the Tau Ceti discharge campaign (`docs/orchestration/tauceti-tickets.md`, recon memo
`docs/orchestration/tauceti-t2-recon.md` §A2).  Everything lives in `GQ2.TauCetiBridge`.

For a topological group `G` and a topological `G`-module `M` in gq2's typeclass bundle
(`GQ2/DiscreteModule.lean`), this file identifies gq2's explicit continuous cohomology
`GQ2.ContCoh.H0/H1/H2 G M` (`GQ2/Cohomology.lean`) with Tau Ceti's
`TauCeti.ContCohomology.H0/H1/H2 G M`, then composes with Tau Ceti's comparison isomorphisms to
Mathlib's `continuousCohomology`, and records how restriction, change of group and coefficients,
the three cup products, the trivial-`𝔽₂` package and the Kummer class read across.

Tau Ceti's definitions are not exposed to `module` files (memo, cross-cutting finding 1), so the
dictionary is built by the **propositional route**: the cocycle and coboundary subgroups are proved
equal through the two sides' `mem_*_iff` lemmas (`Z1_eq`, `B1_eq`, `Z2_eq`, `B2_eq`) and the
quotients are compared by `QuotientAddGroup.congr`.  `H0` agrees definitionally (`H0_eq : … := rfl`).

## Main declarations (the API the B-tickets consume)

* `h1Equiv G M : GQ2.ContCoh.H1 G M ≃+ TauCeti.ContCohomology.H1 G M`, `h2Equiv G M`, with the
  class-map rules `h1Equiv_H1mk`, `h2Equiv_H2mk` (`rfl`, through the cocycle transports
  `toZ1`/`toZ2`) and their inverses `h1Equiv_symm_mk`, `h2Equiv_symm_mk`.
* `cont0 G M`, `cont1 G M`, `cont2 G M` into `continuousCohomology i (ofDiscreteModule ℤ G M)`
  (`G M : Type u`; degree `2` needs `[LocallyCompactSpace G]`); the `TopRep` versions
  `cont0Rep A`, `cont1Rep A`, `cont2Rep A` for a discrete `A : TopRep R G` with the action read off
  from `A`, and `cont0Mod R G M`, `cont1Mod R G M`, `cont2Mod R G M` at `A = ofDiscreteModule R G M`
  (what B7 needs).
* Naturality: `res0_eq_explicitRes0`, `h1Equiv_res1`, `h2Equiv_res2`; `H0comap_eq_explicitMap0`,
  `h1Equiv_H1comap`, `h2Equiv_H2comap` (gq2's compatible-pair pullback is Tau Ceti's
  `explicitMap{0,1,2}`; `H1comap_H1mk`, `H2comap_H2mk` record the class-map rules), the
  `≃ₜ*`/`≃+` forms `h1Equiv_H1comap_equiv`, `h2Equiv_H2comap_equiv` against
  `explicitMap{1,2}Equiv`, and `cont0_map`, `cont1_map`, `cont2_map` against
  `ContinuousCohomology.map`.
* Cups for an arbitrary pairing `μ`: `h2Equiv_cup11`, `h2Equiv_cup02`, `h2Equiv_cup20` against
  `explicitCup11/02/20`, and `cont2_cup11`, `cont2_cup02`, `cont2_cup20` against
  `(ofDiscreteModulePairing μ hμ).cup`.
* The `𝔽₂` package for a trivial action `htriv`: `cont1F2 G htriv`, `cont2F2 G htriv` into
  `continuousCohomology i (TauCeti.trivialF2 G)` in Tau Ceti's `(eqToHom _).hom` form
  (`cont1F2_apply`, `cont2F2_apply`), the class-map rules `cont1F2_H1mk`, `cont2F2_H2mk` (through
  the cocycle transports `toF2Z1`, `toF2Z2`, computed by `coe_toF2Z1`, `coe_toF2Z2`), the
  character rule `cont1F2_H1mk_eq_homClass`, the cup rule `cont2F2_trivialCupPairing`
  (`a ⌣[htriv] b` ↦ `(trivialF2TopPairing G).cup 1 1`), and naturality along a continuous
  homomorphism `trivialF2Map_cont1F2`, `trivialF2Map_cont2F2` (on explicit Tau Ceti classes:
  `trivialF2Map_eqToHom_explicitH1`, `trivialF2Map_eqToHom_explicitH2`).
* Kummer: generically, `trivialF2Map_kummerClass_of_forall` (any field `K` with `2` invertible,
  any `Φ : H →ₜ* TauCeti.AbsoluteGaloisGroup K`, any gq2 cocycle computing
  `h ↦ [Φ h • α ≠ α]` for a root `α` of `a`); for a finite
  `k : IntermediateField ℚ_[2] ℚ̄₂`, parametric in A1's data, `trivialF2Map_kummerClass`: for
  any `Φ : ↥k.fixingSubgroup ≃ₜ* TauCeti.AbsoluteGaloisGroup ↥k` and `↥k`-algebra map
  `ι : SeparableClosure ↥k →ₐ[↥k] ℚ̄₂` intertwining the two actions,
  `trivialF2Map Φ 1 (TauCeti.kummerClass a) = cont1F2 _ htriv (GQ2.kummerClassK k a)`
  (`trivialF2Iso_inv_kummerClass` in the `trivialF2Iso` form), with `kummerCocycleK`,
  `kummerClassK_eq_H1mk`, `apply_eq_iff_smul_sqrtCl_eq` as the pieces; and at A1's
  `(fixingEquivAbsGal k, sepClosureEquiv k)` (`GQ2/TauCeti/GaloisDict.lean`),
  `trivialF2Map_fixingEquivAbsGal_kummerClass`, `trivialF2Iso_fixingEquivAbsGal_inv_kummerClass`.

## Conventions

* The gq2 side is stated on gq2's names, the Tau Ceti side on Tau Ceti's spellings (memo,
  cross-cutting finding 7); Tau Ceti names are always fully qualified.
* The maps into `continuousCohomology i (trivialF2 G)` are the composites Tau Ceti itself uses:
  `(eqToHom (congrArg (continuousCohomology i) (ofDiscreteModule_trivialF2 G))).hom ∘
  explicitH{i}AddEquivContinuousCohomology`, packaged as `AddEquiv`s through `eqToAddEquiv`.
  Packaging the `eqToHom` step as `(eqToIso _).toContinuousLinearEquiv.toAddEquiv` makes `rfl`
  and `erw` against Tau Ceti's lemmas time out (memo §A2), so it is avoided.
* Triviality of the action on `ZMod 2` is taken as gq2 states it, as an explicit hypothesis
  `htriv : ∀ (g : G) (m : ZMod 2), g • m = m` (by proof irrelevance the maps do not depend on it).
* Universe restrictions come from Tau Ceti's comparison isomorphisms, which need `G` and `M` in
  one universe; `h1Equiv`/`h2Equiv` and the explicit naturality and cup rules are stated for
  `G : Type u`, `M : Type v`.
* Proof engineering: the compatibility proofs handed to Tau Ceti's `cocyclesMap{1,2}`,
  `explicitMap{1,2}` and `eqToHom_comp_trivialF2Map` are stated with exactly the binder types
  those functions expect (`trivialF2Equiv_symm_toAddMonoidHom_smul`, `trivialF2CoeffHom_smul'`,
  `id_compat_of_trivial`), because `rw` rejects motives that are type-correct only up to
  unfolding; where Tau Ceti's own statements carry such terms (`explicitMap{1,2}Equiv_apply`),
  the proofs go through `Eq.trans` instead of `rw`.  Everything elaborates within the default
  heartbeat budget.
-/

-- The dictionary sections quantify over gq2's full module bundle so that every statement reads
-- on the same typeclass context the B-tickets have; several individual lemmas use only part of it.
set_option linter.unusedSectionVars false

namespace GQ2.TauCetiBridge

open CategoryTheory

universe u v w

/-! ## Preliminaries -/

/-- An equality of objects of `TopModuleCat ℤ`, read as an additive equivalence of the underlying
groups through `eqToHom` in both directions.  The forward map is literally `(eqToHom h).hom`, the
form Tau Ceti's lemmas are stated in. -/
def eqToAddEquiv {X Y : TopModuleCat ℤ} (h : X = Y) : X ≃+ Y where
  toFun := (eqToHom h).hom
  invFun := (eqToHom h.symm).hom
  left_inv x := by subst h; rfl
  right_inv y := by subst h; rfl
  map_add' _ _ := map_add _ _ _

@[simp] theorem eqToAddEquiv_apply {X Y : TopModuleCat ℤ} (h : X = Y) (x : X) :
    eqToAddEquiv h x = (eqToHom h).hom x := rfl

@[simp] theorem eqToAddEquiv_symm_apply {X Y : TopModuleCat ℤ} (h : X = Y) (y : Y) :
    (eqToAddEquiv h).symm y = (eqToHom h.symm).hom y := rfl

/-- `QuotientAddGroup.congr` for two subquotients of the same ambient group whose subgroups are
propositionally equal. -/
noncomputable def quotCongr {X : Type*} [AddCommGroup X] {A A' B B' : AddSubgroup X}
    (hA : A = A') (hB : B = B') :
    (A ⧸ B.addSubgroupOf A) ≃+ (A' ⧸ B'.addSubgroupOf A') :=
  QuotientAddGroup.congr _ _ (AddEquiv.addSubgroupCongr hA) (by
    subst hA hB
    ext ⟨x, hx⟩
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨y, hy, he⟩
      obtain rfl : y.1 = x := congrArg Subtype.val he
      exact hy
    · intro h; exact ⟨⟨x, hx⟩, h, rfl⟩)

/-! ## The low-degree complex and the `H⁰`, `H¹`, `H²` dictionary -/

section Dict

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- Degree `0` agrees by definition (both are the subgroup of invariants). -/
theorem H0_eq : GQ2.ContCoh.H0 G M = TauCeti.ContCohomology.H0 G M := rfl

theorem C1_eq : GQ2.ContCoh.C1 G M = TauCeti.ContCohomology.C1 G M := by
  ext f; rw [GQ2.ContCoh.mem_C1_iff, TauCeti.ContCohomology.mem_C1_iff]

theorem dZero_eq : GQ2.ContCoh.dZero G M = TauCeti.ContCohomology.d0 G M := by
  ext m g; simp [GQ2.ContCoh.dZero]

theorem dOne_eq : GQ2.ContCoh.dOne G M = TauCeti.ContCohomology.d1 G M := by
  ext f ⟨g, h⟩; simp [GQ2.ContCoh.dOne]

theorem dTwo_eq : GQ2.ContCoh.dTwo G M = TauCeti.ContCohomology.d2 G M := by
  ext f ⟨g, h, k⟩; simp [GQ2.ContCoh.dTwo]

theorem Z1_eq : GQ2.ContCoh.Z1 G M = TauCeti.ContCohomology.Z1 G M := by
  ext f
  rw [GQ2.ContCoh.mem_Z1_iff, TauCeti.ContCohomology.mem_Z1_iff]
  refine and_congr_right fun _ => forall₂_congr fun g h => ?_
  rw [add_comm (f g)]

theorem B1_eq : GQ2.ContCoh.B1 G M = TauCeti.ContCohomology.B1 G M := by
  ext f
  rw [TauCeti.ContCohomology.mem_B1_iff]
  simp [GQ2.ContCoh.B1, GQ2.ContCoh.dZero, groupCohomology.IsCoboundary₁, funext_iff]

theorem Z2_eq : GQ2.ContCoh.Z2 G M = TauCeti.ContCohomology.Z2 G M := by
  ext f
  rw [GQ2.ContCoh.mem_Z2_iff, TauCeti.ContCohomology.mem_Z2_iff]
  refine and_congr_right fun _ => forall₃_congr fun g h k => ?_
  exact ⟨fun H => H.symm, fun H => H.symm⟩

theorem B2_eq : GQ2.ContCoh.B2 G M = TauCeti.ContCohomology.B2 G M := by
  ext f
  rw [GQ2.ContCoh.B2, TauCeti.ContCohomology.mem_B2_iff, AddSubgroup.mem_map, dOne_eq]
  simp only [GQ2.ContCoh.mem_C1_iff]

/-- A gq2 continuous `1`-cocycle, read as a Tau Ceti one (same underlying function). -/
def toZ1 (z : GQ2.ContCoh.Z1 G M) : TauCeti.ContCohomology.Z1 G M := ⟨z.1, (Z1_eq G M).le z.2⟩

/-- A Tau Ceti continuous `1`-cocycle, read as a gq2 one (same underlying function). -/
def ofZ1 (c : TauCeti.ContCohomology.Z1 G M) : GQ2.ContCoh.Z1 G M := ⟨c.1, (Z1_eq G M).ge c.2⟩

/-- A gq2 continuous `2`-cocycle, read as a Tau Ceti one (same underlying function). -/
def toZ2 (z : GQ2.ContCoh.Z2 G M) : TauCeti.ContCohomology.Z2 G M := ⟨z.1, (Z2_eq G M).le z.2⟩

/-- A Tau Ceti continuous `2`-cocycle, read as a gq2 one (same underlying function). -/
def ofZ2 (c : TauCeti.ContCohomology.Z2 G M) : GQ2.ContCoh.Z2 G M := ⟨c.1, (Z2_eq G M).ge c.2⟩

@[simp] theorem coe_toZ1 (z : GQ2.ContCoh.Z1 G M) : (toZ1 G M z : G → M) = z.1 := rfl
@[simp] theorem coe_ofZ1 (c : TauCeti.ContCohomology.Z1 G M) : (ofZ1 G M c : G → M) = c.1 := rfl
@[simp] theorem coe_toZ2 (z : GQ2.ContCoh.Z2 G M) : (toZ2 G M z : G × G → M) = z.1 := rfl
@[simp] theorem coe_ofZ2 (c : TauCeti.ContCohomology.Z2 G M) : (ofZ2 G M c : G × G → M) = c.1 :=
  rfl
@[simp] theorem toZ1_ofZ1 (c : TauCeti.ContCohomology.Z1 G M) : toZ1 G M (ofZ1 G M c) = c := rfl
@[simp] theorem ofZ1_toZ1 (z : GQ2.ContCoh.Z1 G M) : ofZ1 G M (toZ1 G M z) = z := rfl
@[simp] theorem toZ2_ofZ2 (c : TauCeti.ContCohomology.Z2 G M) : toZ2 G M (ofZ2 G M c) = c := rfl
@[simp] theorem ofZ2_toZ2 (z : GQ2.ContCoh.Z2 G M) : ofZ2 G M (toZ2 G M z) = z := rfl

/-- **The degree-one dictionary**: gq2's `H¹(G, M)` is Tau Ceti's explicit `H¹(G, M)`. -/
noncomputable def h1Equiv : GQ2.ContCoh.H1 G M ≃+ TauCeti.ContCohomology.H1 G M :=
  quotCongr (Z1_eq G M) (B1_eq G M)

/-- **The degree-two dictionary**: gq2's `H²(G, M)` is Tau Ceti's explicit `H²(G, M)`. -/
noncomputable def h2Equiv : GQ2.ContCoh.H2 G M ≃+ TauCeti.ContCohomology.H2 G M :=
  quotCongr (Z2_eq G M) (B2_eq G M)

@[simp] theorem h1Equiv_H1mk (z : GQ2.ContCoh.Z1 G M) :
    h1Equiv G M (GQ2.ContCoh.H1mk G M z) = (toZ1 G M z : TauCeti.ContCohomology.H1 G M) := rfl

@[simp] theorem h1Equiv_symm_mk (c : TauCeti.ContCohomology.Z1 G M) :
    (h1Equiv G M).symm (c : TauCeti.ContCohomology.H1 G M) = GQ2.ContCoh.H1mk G M (ofZ1 G M c) :=
  rfl

@[simp] theorem h2Equiv_H2mk (z : GQ2.ContCoh.Z2 G M) :
    h2Equiv G M (GQ2.ContCoh.H2mk G M z) = (toZ2 G M z : TauCeti.ContCohomology.H2 G M) := rfl

@[simp] theorem h2Equiv_symm_mk (c : TauCeti.ContCohomology.Z2 G M) :
    (h2Equiv G M).symm (c : TauCeti.ContCohomology.H2 G M) = GQ2.ContCoh.H2mk G M (ofZ2 G M c) :=
  rfl

end Dict

/-! ## Naturality of the dictionary: restriction, change of group and of coefficients -/

section Naturality

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  {Q : Type w} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DistribMulAction Q N] [ContinuousSMul Q N]
  (π : ContinuousMonoidHom G Q) (f : N →+ M) (hf : Continuous f)
  (hcompat : ∀ (g : G) (n : N), f (π g • n) = g • f n)

/-- gq2's degree-`0` pullback along a compatible pair is Tau Ceti's `explicitMap0`. -/
theorem H0comap_eq_explicitMap0 :
    GQ2.ContCoh.H0comap π f hcompat =
      TauCeti.ContCohomology.explicitMap0 Q N (π : G →* Q) f hcompat :=
  AddMonoidHom.ext fun m => Subtype.ext
    (TauCeti.ContCohomology.coe_explicitMap0 Q N (π : G →* Q) f hcompat m).symm

/-- gq2's `H1comap` on the class of a cocycle (definitional, recorded for `rw`). -/
theorem H1comap_H1mk (z : GQ2.ContCoh.Z1 Q N) :
    GQ2.ContCoh.H1comap π f hf hcompat (GQ2.ContCoh.H1mk Q N z) =
      GQ2.ContCoh.H1mk G M (GQ2.ContCoh.Z1comap π f hf hcompat z) := rfl

/-- gq2's `H2comap` on the class of a cocycle (definitional, recorded for `rw`). -/
theorem H2comap_H2mk (z : GQ2.ContCoh.Z2 Q N) :
    GQ2.ContCoh.H2comap π f hf hcompat (GQ2.ContCoh.H2mk Q N z) =
      GQ2.ContCoh.H2mk G M (GQ2.ContCoh.Z2comap π f hf hcompat z) := rfl

/-- gq2's degree-`1` pullback along a compatible pair is Tau Ceti's `explicitMap1`. -/
theorem h1Equiv_H1comap (x : GQ2.ContCoh.H1 Q N) :
    h1Equiv G M (GQ2.ContCoh.H1comap π f hf hcompat x) =
      TauCeti.ContCohomology.explicitMap1 Q N G M π f hf hcompat (h1Equiv Q N x) := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    refine Eq.trans ?_ (TauCeti.ContCohomology.explicitMap1_mk Q N G M π f hf hcompat
      (toZ1 Q N z)).symm
    exact congrArg (fun w : TauCeti.ContCohomology.Z1 G M => (w : TauCeti.ContCohomology.H1 G M))
      (Subtype.ext (funext fun g => by rw [TauCeti.ContCohomology.cocyclesMap1_apply]; rfl))

/-- gq2's degree-`2` pullback along a compatible pair is Tau Ceti's `explicitMap2`. -/
theorem h2Equiv_H2comap (x : GQ2.ContCoh.H2 Q N) :
    h2Equiv G M (GQ2.ContCoh.H2comap π f hf hcompat x) =
      TauCeti.ContCohomology.explicitMap2 Q N G M π f hf hcompat (h2Equiv Q N x) := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    refine Eq.trans ?_ (TauCeti.ContCohomology.explicitMap2_mk Q N G M π f hf hcompat
      (toZ2 Q N z)).symm
    exact congrArg (fun w : TauCeti.ContCohomology.Z2 G M => (w : TauCeti.ContCohomology.H2 G M))
      (Subtype.ext (funext fun ⟨g, h⟩ => by rw [TauCeti.ContCohomology.cocyclesMap2_apply]; rfl))

end Naturality

section NaturalityEquiv

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  {H : Type w} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DistribMulAction H N] [ContinuousSMul H N]
  (φ : H ≃ₜ* G) (e : M ≃+ N) (he : Continuous e) (he' : Continuous e.symm)
  (hequiv : ∀ (h : H) (m : M), e (φ h • m) = h • e m)

/-- Change of group and coefficients along a topological-group isomorphism `φ : H ≃ₜ* G` and an
equivariant `e : M ≃+ N`: gq2's `H1comap` is Tau Ceti's `explicitMap1Equiv` (the form B6
transports along). -/
theorem h1Equiv_H1comap_equiv (x : GQ2.ContCoh.H1 G M) :
    h1Equiv H N (GQ2.ContCoh.H1comap (φ : H →ₜ* G) e.toAddMonoidHom he hequiv x) =
      TauCeti.ContCohomology.explicitMap1Equiv G M H N φ e he he' hequiv (h1Equiv G M x) :=
  (h1Equiv_H1comap (φ : H →ₜ* G) e.toAddMonoidHom he hequiv x).trans
    (TauCeti.ContCohomology.explicitMap1Equiv_apply G M H N φ e he he' hequiv (h1Equiv G M x)).symm

/-- Degree-`2` analogue of `h1Equiv_H1comap_equiv`. -/
theorem h2Equiv_H2comap_equiv (x : GQ2.ContCoh.H2 G M) :
    h2Equiv H N (GQ2.ContCoh.H2comap (φ : H →ₜ* G) e.toAddMonoidHom he hequiv x) =
      TauCeti.ContCohomology.explicitMap2Equiv G M H N φ e he he' hequiv (h2Equiv G M x) :=
  (h2Equiv_H2comap (φ : H →ₜ* G) e.toAddMonoidHom he hequiv x).trans
    (TauCeti.ContCohomology.explicitMap2Equiv_apply G M H N φ e he he' hequiv (h2Equiv G M x)).symm

end NaturalityEquiv

section Restriction

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M] (U : Subgroup G)

/-- gq2's degree-`0` restriction is Tau Ceti's `explicitRes0`. -/
theorem res0_eq_explicitRes0 :
    GQ2.ContCoh.res0 G M U = TauCeti.ContCohomology.explicitRes0 G M U :=
  AddMonoidHom.ext fun m => Subtype.ext (TauCeti.ContCohomology.coe_explicitRes0 G M U m).symm

/-- gq2's degree-`1` restriction is Tau Ceti's `explicitRes1`. -/
theorem h1Equiv_res1 (x : GQ2.ContCoh.H1 G M) :
    h1Equiv U M (GQ2.ContCoh.res1 G M U x) =
      TauCeti.ContCohomology.explicitRes1 G M U (h1Equiv G M x) := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    refine Eq.trans ?_ (TauCeti.ContCohomology.explicitRes1_mk G M U (toZ1 G M z)).symm
    exact congrArg (fun w : TauCeti.ContCohomology.Z1 U M => (w : TauCeti.ContCohomology.H1 U M))
      (Subtype.ext (funext fun g => by rw [TauCeti.ContCohomology.cocyclesMap1_apply]; rfl))

/-- gq2's degree-`2` restriction is Tau Ceti's `explicitRes2`. -/
theorem h2Equiv_res2 (x : GQ2.ContCoh.H2 G M) :
    h2Equiv U M (GQ2.ContCoh.res2 G M U x) =
      TauCeti.ContCohomology.explicitRes2 G M U (h2Equiv G M x) := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    refine Eq.trans ?_ (TauCeti.ContCohomology.explicitRes2_mk G M U (toZ2 G M z)).symm
    exact congrArg (fun w : TauCeti.ContCohomology.Z2 U M => (w : TauCeti.ContCohomology.H2 U M))
      (Subtype.ext (funext fun ⟨g, h⟩ => by rw [TauCeti.ContCohomology.cocyclesMap2_apply]; rfl))

end Restriction

/-! ## Cup products for an arbitrary pairing -/

section Cup

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
  {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DiscreteTopology N] [DistribMulAction G N] [ContinuousSMul G N]
  {P : Type*} [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
  [DiscreteTopology P] [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : ∀ (g : G) (m : M) (n : N), μ (g • m) (g • n) = g • μ m n)

/-- gq2's `(1,1)` cup is Tau Ceti's `explicitCup11` (the cochain formulas `μ (a g) (g • b h)`
agree verbatim). -/
theorem h2Equiv_cup11 (x : GQ2.ContCoh.H1 G M) (y : GQ2.ContCoh.H1 G N) :
    h2Equiv G P (GQ2.ContCoh.cup11 μ hμ x y) =
      TauCeti.ContCohomology.explicitCup11 G M N P μ continuous_of_discreteTopology hμ
        (h1Equiv G M x) (h1Equiv G N y) := by
  induction x using QuotientAddGroup.induction_on with
  | H a => induction y using QuotientAddGroup.induction_on with
    | H b =>
      exact (TauCeti.ContCohomology.explicitCup11_mk G M N P μ _ hμ (toZ1 G M a)
        (toZ1 G N b)).symm

/-- gq2's `(0,2)` cup is Tau Ceti's `explicitCup02` (cochain `μ m (b (g, h))`). -/
theorem h2Equiv_cup02 (m : GQ2.ContCoh.H0 G M) (y : GQ2.ContCoh.H2 G N) :
    h2Equiv G P (GQ2.ContCoh.cup02 μ hμ m y) =
      TauCeti.ContCohomology.explicitCup02 G M N P μ continuous_of_discreteTopology hμ m
        (h2Equiv G N y) := by
  induction y using QuotientAddGroup.induction_on with
  | H b =>
    exact (TauCeti.ContCohomology.explicitCup02_mk G M N P μ _ hμ m (toZ2 G N b)).symm

/-- gq2's `(2,0)` cup is Tau Ceti's `explicitCup20` (cochain `μ (a (g, h)) ((g * h) • n)`). -/
theorem h2Equiv_cup20 (x : GQ2.ContCoh.H2 G M) (n : GQ2.ContCoh.H0 G N) :
    h2Equiv G P (GQ2.ContCoh.cup20 μ hμ x n) =
      TauCeti.ContCohomology.explicitCup20 G M N P μ continuous_of_discreteTopology hμ
        (h2Equiv G M x) n := by
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    exact (TauCeti.ContCohomology.explicitCup20_mk G M N P μ _ hμ (toZ2 G M a) n).symm

end Cup

/-! ## Comparison with Mathlib's `continuousCohomology` (one universe) -/

section Comparison

variable (G M : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]

/-- **Degree `0`** against the canonical object `ofDiscreteModule ℤ G M`: Tau Ceti's
`explicitH0IsoContinuousCohomology`, read as an additive equivalence from gq2's invariants. -/
noncomputable def cont0 :
    GQ2.ContCoh.H0 G M ≃+ continuousCohomology 0 (TauCeti.ofDiscreteModule ℤ G M) where
  toFun m := (TauCeti.ContCohomology.explicitH0IsoContinuousCohomology G M).hom m
  invFun y := (TauCeti.ContCohomology.explicitH0IsoContinuousCohomology G M).inv y
  left_inv m := (TauCeti.ContCohomology.explicitH0IsoContinuousCohomology G M).hom_inv_id_apply m
  right_inv y := (TauCeti.ContCohomology.explicitH0IsoContinuousCohomology G M).inv_hom_id_apply y
  map_add' _ _ := map_add _ _ _

@[simp] theorem cont0_apply (m : GQ2.ContCoh.H0 G M) :
    cont0 G M m = (TauCeti.ContCohomology.explicitH0IsoContinuousCohomology G M).hom m := rfl

@[simp] theorem cont0_symm_apply (y : continuousCohomology 0 (TauCeti.ofDiscreteModule ℤ G M)) :
    (cont0 G M).symm y = (TauCeti.ContCohomology.explicitH0IsoContinuousCohomology G M).inv y :=
  rfl

variable [ContinuousSMul G M]

/-- **Degree `1`** against the canonical object: the dictionary followed by Tau Ceti's
`explicitH1AddEquivContinuousCohomology`. -/
noncomputable def cont1 :
    GQ2.ContCoh.H1 G M ≃+ continuousCohomology 1 (TauCeti.ofDiscreteModule ℤ G M) :=
  (h1Equiv G M).trans (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology G M)

@[simp] theorem cont1_apply (x : GQ2.ContCoh.H1 G M) :
    cont1 G M x =
      TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology G M (h1Equiv G M x) := rfl

/-- **Degree `2`** against the canonical object (needs `G` locally compact, as Tau Ceti's
comparison does). -/
noncomputable def cont2 [LocallyCompactSpace G] :
    GQ2.ContCoh.H2 G M ≃+ continuousCohomology 2 (TauCeti.ofDiscreteModule ℤ G M) :=
  (h2Equiv G M).trans (TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology G M)

@[simp] theorem cont2_apply [LocallyCompactSpace G] (x : GQ2.ContCoh.H2 G M) :
    cont2 G M x =
      TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology G M (h2Equiv G M x) := rfl

end Comparison

section ComparisonNaturality

variable {G M : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]
  {H N : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N] [DistribMulAction H N]
  (φ : H →ₜ* G) (f : M →+ N) (hf : ∀ (h : H) (m : M), f (φ h • m) = h • f m)
  [ContinuousSMul G M] [ContinuousSMul H N]

/-- Naturality of `cont0` in compatible pairs, against Mathlib's `ContinuousCohomology.map`. -/
theorem cont0_map (x : GQ2.ContCoh.H0 G M) :
    ContinuousCohomology.map φ
        (TauCeti.ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap fun h m => hf h m) 0
        (cont0 G M x) =
      cont0 H N (GQ2.ContCoh.H0comap φ f hf x) := by
  rw [cont0_apply, cont0_apply, H0comap_eq_explicitMap0]
  exact TauCeti.ContCohomology.explicitH0Iso_map G M H N φ f hf x

/-- Naturality of `cont1` in compatible pairs, against Mathlib's `ContinuousCohomology.map`. -/
theorem cont1_map (x : GQ2.ContCoh.H1 G M) :
    ContinuousCohomology.map φ
        (TauCeti.ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap fun h m => hf h m) 1
        (cont1 G M x) =
      cont1 H N (GQ2.ContCoh.H1comap φ f continuous_of_discreteTopology hf x) := by
  rw [cont1_apply, cont1_apply, h1Equiv_H1comap]
  exact TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology_map G M H N φ f hf _

/-- Naturality of `cont2` in compatible pairs, against Mathlib's `ContinuousCohomology.map`. -/
theorem cont2_map [LocallyCompactSpace G] [LocallyCompactSpace H] (x : GQ2.ContCoh.H2 G M) :
    ContinuousCohomology.map φ
        (TauCeti.ofDiscreteModulePair (φ : H →* G) f.toIntLinearMap fun h m => hf h m) 2
        (cont2 G M x) =
      cont2 H N (GQ2.ContCoh.H2comap φ f continuous_of_discreteTopology hf x) := by
  rw [cont2_apply, cont2_apply, h2Equiv_H2comap]
  exact TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology_map G M H N φ f hf _

end ComparisonNaturality

section ComparisonCup

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  {M : Type u} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M]
  {N : Type u} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
  [DistribMulAction G N] [ContinuousSMul G N]
  {P : Type u} [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P]
  [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : ∀ (g : G) (m : M) (n : N), μ (g • m) (g • n) = g • μ m n)

/-- gq2's `(1,1)` cup, read in Mathlib's continuous cohomology, is the cup product of the
pairing `ofDiscreteModulePairing μ hμ`. -/
theorem cont2_cup11 (x : GQ2.ContCoh.H1 G M) (y : GQ2.ContCoh.H1 G N) :
    cont2 G P (GQ2.ContCoh.cup11 μ hμ x y) =
      (TauCeti.ofDiscreteModulePairing μ hμ).cup 1 1 (cont1 G M x) (cont1 G N y) := by
  rw [cont2_apply, cont1_apply, cont1_apply, h2Equiv_cup11,
    TauCeti.ContCohomology.explicitAddEquiv_cup11]

/-- gq2's `(0,2)` cup, read in Mathlib's continuous cohomology. -/
theorem cont2_cup02 (m : GQ2.ContCoh.H0 G M) (y : GQ2.ContCoh.H2 G N) :
    cont2 G P (GQ2.ContCoh.cup02 μ hμ m y) =
      (TauCeti.ofDiscreteModulePairing μ hμ).cup 0 2 (cont0 G M m) (cont2 G N y) := by
  rw [cont2_apply, cont2_apply, cont0_apply, h2Equiv_cup02]
  exact (TauCeti.ContCohomology.explicitAddEquiv_cup02 G M N P μ hμ m (h2Equiv G N y)).symm

/-- gq2's `(2,0)` cup, read in Mathlib's continuous cohomology. -/
theorem cont2_cup20 (x : GQ2.ContCoh.H2 G M) (n : GQ2.ContCoh.H0 G N) :
    cont2 G P (GQ2.ContCoh.cup20 μ hμ x n) =
      (TauCeti.ofDiscreteModulePairing μ hμ).cup 2 0 (cont2 G M x) (cont0 G N n) := by
  rw [cont2_apply, cont2_apply, cont0_apply, h2Equiv_cup20]
  exact (TauCeti.ContCohomology.explicitAddEquiv_cup20 G M N P μ hμ (h2Equiv G M x) n).symm

end ComparisonCup

/-! ## Comparison for a discrete `TopRep` and for `ofDiscreteModule R G M` -/

section TopRepVersions

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {R : Type*} [Ring R] [TopologicalSpace R] (A : TopRep R G) [DiscreteTopology A.V]

attribute [local instance] TopRep.distribMulAction

/-- Degree `0` for a discrete `A : TopRep R G`, the action on `A.V` read off from `A`. -/
noncomputable def cont0Rep : GQ2.ContCoh.H0 G A.V ≃+ continuousCohomology 0 A :=
  (cont0 G A.V).trans (TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv A 0)

variable [ContinuousSMul G A.V]

/-- Degree `1` for a discrete `A : TopRep R G` (`TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete`). -/
noncomputable def cont1Rep : GQ2.ContCoh.H1 G A.V ≃+ continuousCohomology 1 A :=
  (h1Equiv G A.V).trans A.explicitH1AddEquivContinuousCohomologyOfDiscrete

/-- Degree `2` for a discrete `A : TopRep R G` (`TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete`). -/
noncomputable def cont2Rep [LocallyCompactSpace G] :
    GQ2.ContCoh.H2 G A.V ≃+ continuousCohomology 2 A :=
  (h2Equiv G A.V).trans A.explicitH2AddEquivContinuousCohomologyOfDiscrete

theorem cont0Rep_apply (m : GQ2.ContCoh.H0 G A.V) :
    cont0Rep A m =
      TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv A 0 (cont0 G A.V m) := rfl

theorem cont1Rep_apply (x : GQ2.ContCoh.H1 G A.V) :
    cont1Rep A x = A.explicitH1AddEquivContinuousCohomologyOfDiscrete (h1Equiv G A.V x) := rfl

theorem cont2Rep_apply [LocallyCompactSpace G] (x : GQ2.ContCoh.H2 G A.V) :
    cont2Rep A x = A.explicitH2AddEquivContinuousCohomologyOfDiscrete (h2Equiv G A.V x) := rfl

end TopRepVersions

section OfDiscreteModule

variable (R : Type*) [Ring R] [TopologicalSpace R]
  (G M : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]
  [ContinuousSMul G M] [Module R M] [SMulCommClass G R M] [ContinuousSMul R M]

attribute [local instance] TopRep.distribMulAction

/-- Degree `0` for the canonical `R`-linear object `ofDiscreteModule R G M` of a gq2 module
(for `R = ZMod (Nat.card M)` this is the `GalRep` object B7 feeds to Tau Ceti). -/
noncomputable def cont0Mod :
    GQ2.ContCoh.H0 G M ≃+ continuousCohomology 0 (TauCeti.ofDiscreteModule R G M) :=
  cont0Rep (TauCeti.ofDiscreteModule R G M)

/-- Degree `1` for the canonical `R`-linear object `ofDiscreteModule R G M`. -/
noncomputable def cont1Mod :
    GQ2.ContCoh.H1 G M ≃+ continuousCohomology 1 (TauCeti.ofDiscreteModule R G M) :=
  haveI : ContinuousSMul G (TauCeti.ofDiscreteModule R G M).V := inferInstanceAs (ContinuousSMul G M)
  cont1Rep (TauCeti.ofDiscreteModule R G M)

/-- Degree `2` for the canonical `R`-linear object `ofDiscreteModule R G M`. -/
noncomputable def cont2Mod [LocallyCompactSpace G] :
    GQ2.ContCoh.H2 G M ≃+ continuousCohomology 2 (TauCeti.ofDiscreteModule R G M) :=
  haveI : ContinuousSMul G (TauCeti.ofDiscreteModule R G M).V := inferInstanceAs (ContinuousSMul G M)
  cont2Rep (TauCeti.ofDiscreteModule R G M)

end OfDiscreteModule

/-! ## The trivial-`𝔽₂` package

gq2 states `𝔽₂`-cohomology on `ZMod 2` with an action assumed trivial through
`htriv : ∀ g (m : ZMod 2), g • m = m`; Tau Ceti's object `trivialF2 G` has carrier
`ULift (ZMod 2)` with the trivial action.  The package below reads gq2's `H¹`, `H²` and
`trivialCupPairing` in `continuousCohomology i (trivialF2 G)`, in the `(eqToHom _).hom` form of
Tau Ceti's own lemmas (`homClass_def`, `trivialF2TopPairing_cup_one_one_explicitH1`,
`kummerClass_eq_kummerCocycleModTwoClass_of_sq_eq`).

Implementation note: the compatibility proofs fed to Tau Ceti's `cocyclesMap1`/`explicitMap1` are
stated with exactly the binder types those functions expect (`trivialF2Equiv_symm_smul`,
`trivialF2Equiv_symm_toAddMonoidHom_smul`, `trivialF2CoeffHom_smul'`); otherwise `rw` rejects
the motives as not type-correct at `implicit` transparency. -/

section F2

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
  (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)

attribute [local instance] TopRep.distribMulAction

/-- `G` acts continuously on the lifted trivial coefficients `(trivialF2 G).V` (Tau Ceti's
`isSmoothDiscrete_trivialF2`); Tau Ceti does not register it globally, so it is local here. -/
local instance continuousSMul_trivialF2 : ContinuousSMul G (TauCeti.trivialF2 G).V :=
  (TauCeti.isSmoothDiscrete_trivialF2 G).continuousSMul

include htriv in
/-- For a trivial action, the coefficient identification `ZMod 2 ≃+ (trivialF2 G).V` is
`G`-equivariant: the compatibility hypothesis of `explicitMap1Equiv` along
`ContinuousMulEquiv.refl G`. -/
theorem trivialF2Equiv_symm_smul (g : G) (m : ZMod 2) :
    (TauCeti.trivialF2Equiv G).symm ((ContinuousMulEquiv.refl G) g • m) =
      g • (TauCeti.trivialF2Equiv G).symm m := by
  rw [htriv, TopRep.distribMulAction_smul, TauCeti.trivialF2_ρ_apply_apply]

include htriv in
/-- `trivialF2Equiv_symm_smul` in the form `cocyclesMap1` expects. -/
theorem trivialF2Equiv_symm_toAddMonoidHom_smul (g : G) (m : ZMod 2) :
    (TauCeti.trivialF2Equiv G).symm.toAddMonoidHom ((ContinuousMulEquiv.refl G : G →ₜ* G) g • m) =
      g • (TauCeti.trivialF2Equiv G).symm.toAddMonoidHom m :=
  trivialF2Equiv_symm_smul G htriv g m

/-- Change of coefficients `ZMod 2 → (trivialF2 G).V` on Tau Ceti's explicit `H¹`. -/
noncomputable def toF2 :
    TauCeti.ContCohomology.H1 G (ZMod 2) ≃+ TauCeti.ContCohomology.H1 G (TauCeti.trivialF2 G).V :=
  TauCeti.ContCohomology.explicitMap1Equiv G (ZMod 2) G (TauCeti.trivialF2 G).V
    (ContinuousMulEquiv.refl G) (TauCeti.trivialF2Equiv G).symm
    continuous_of_discreteTopology continuous_of_discreteTopology (trivialF2Equiv_symm_smul G htriv)

/-- Change of coefficients `ZMod 2 → (trivialF2 G).V` on Tau Ceti's explicit `H²`. -/
noncomputable def toF2two :
    TauCeti.ContCohomology.H2 G (ZMod 2) ≃+ TauCeti.ContCohomology.H2 G (TauCeti.trivialF2 G).V :=
  TauCeti.ContCohomology.explicitMap2Equiv G (ZMod 2) G (TauCeti.trivialF2 G).V
    (ContinuousMulEquiv.refl G) (TauCeti.trivialF2Equiv G).symm
    continuous_of_discreteTopology continuous_of_discreteTopology (trivialF2Equiv_symm_smul G htriv)

/-- The cocycle-level form of `toF2`: a gq2 `1`-cocycle `z : G → ZMod 2`, read as the Tau Ceti
cocycle `g ↦ (trivialF2Equiv G).symm (z g)` valued in `(trivialF2 G).V`. -/
noncomputable def toF2Z1 (z : GQ2.ContCoh.Z1 G (ZMod 2)) :
    TauCeti.ContCohomology.Z1 G (TauCeti.trivialF2 G).V :=
  TauCeti.ContCohomology.cocyclesMap1 G (ZMod 2) G (TauCeti.trivialF2 G).V
    (ContinuousMulEquiv.refl G : G →ₜ* G) (TauCeti.trivialF2Equiv G).symm.toAddMonoidHom
    continuous_of_discreteTopology (trivialF2Equiv_symm_toAddMonoidHom_smul G htriv)
    (toZ1 G (ZMod 2) z)

/-- The cocycle-level form of `toF2two`. -/
noncomputable def toF2Z2 (z : GQ2.ContCoh.Z2 G (ZMod 2)) :
    TauCeti.ContCohomology.Z2 G (TauCeti.trivialF2 G).V :=
  TauCeti.ContCohomology.cocyclesMap2 G (ZMod 2) G (TauCeti.trivialF2 G).V
    (ContinuousMulEquiv.refl G : G →ₜ* G) (TauCeti.trivialF2Equiv G).symm.toAddMonoidHom
    continuous_of_discreteTopology (trivialF2Equiv_symm_toAddMonoidHom_smul G htriv)
    (toZ2 G (ZMod 2) z)

@[simp] theorem coe_toF2Z1 (z : GQ2.ContCoh.Z1 G (ZMod 2)) :
    (toF2Z1 G htriv z : G → (TauCeti.trivialF2 G).V) =
      fun g => (TauCeti.trivialF2Equiv G).symm (z.1 g) := by
  funext g
  exact TauCeti.ContCohomology.cocyclesMap1_apply G (ZMod 2) G (TauCeti.trivialF2 G).V _ _ _ _
    (toZ1 G (ZMod 2) z) g

@[simp] theorem coe_toF2Z2 (z : GQ2.ContCoh.Z2 G (ZMod 2)) :
    (toF2Z2 G htriv z : G × G → (TauCeti.trivialF2 G).V) =
      fun p => (TauCeti.trivialF2Equiv G).symm (z.1 p) := by
  funext ⟨g, h⟩
  exact TauCeti.ContCohomology.cocyclesMap2_apply G (ZMod 2) G (TauCeti.trivialF2 G).V _ _ _ _
    (toZ2 G (ZMod 2) z) g h

theorem toF2_H1mk (z : GQ2.ContCoh.Z1 G (ZMod 2)) :
    toF2 G htriv (h1Equiv G (ZMod 2) (GQ2.ContCoh.H1mk G (ZMod 2) z)) =
      (toF2Z1 G htriv z : TauCeti.ContCohomology.H1 G (TauCeti.trivialF2 G).V) := by
  rw [h1Equiv_H1mk]
  exact (TauCeti.ContCohomology.explicitMap1Equiv_apply G (ZMod 2) G (TauCeti.trivialF2 G).V
    (ContinuousMulEquiv.refl G) (TauCeti.trivialF2Equiv G).symm continuous_of_discreteTopology
    continuous_of_discreteTopology (trivialF2Equiv_symm_smul G htriv) _).trans
    (TauCeti.ContCohomology.explicitMap1_mk G (ZMod 2) G (TauCeti.trivialF2 G).V _ _
      continuous_of_discreteTopology (trivialF2Equiv_symm_toAddMonoidHom_smul G htriv)
      (toZ1 G (ZMod 2) z))

theorem toF2two_H2mk (z : GQ2.ContCoh.Z2 G (ZMod 2)) :
    toF2two G htriv (h2Equiv G (ZMod 2) (GQ2.ContCoh.H2mk G (ZMod 2) z)) =
      (toF2Z2 G htriv z : TauCeti.ContCohomology.H2 G (TauCeti.trivialF2 G).V) := by
  rw [h2Equiv_H2mk]
  exact (TauCeti.ContCohomology.explicitMap2Equiv_apply G (ZMod 2) G (TauCeti.trivialF2 G).V
    (ContinuousMulEquiv.refl G) (TauCeti.trivialF2Equiv G).symm continuous_of_discreteTopology
    continuous_of_discreteTopology (trivialF2Equiv_symm_smul G htriv) _).trans
    (TauCeti.ContCohomology.explicitMap2_mk G (ZMod 2) G (TauCeti.trivialF2 G).V _ _
      continuous_of_discreteTopology (trivialF2Equiv_symm_toAddMonoidHom_smul G htriv)
      (toZ2 G (ZMod 2) z))

/-- **`H¹(G, 𝔽₂)`**: gq2's `H1 G (ZMod 2)` (trivial action `htriv`) is Mathlib's
`continuousCohomology 1 (trivialF2 G)`.  On elements it is Tau Ceti's composite
`(eqToHom _).hom ∘ explicitH1AddEquivContinuousCohomology` (`cont1F2_apply`, by `rfl`). -/
noncomputable def cont1F2 :
    GQ2.ContCoh.H1 G (ZMod 2) ≃+ continuousCohomology 1 (TauCeti.trivialF2 G) :=
  (((h1Equiv G (ZMod 2)).trans (toF2 G htriv)).trans
    (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology G (TauCeti.trivialF2 G).V)).trans
    (eqToAddEquiv (congrArg (continuousCohomology 1) (TauCeti.ofDiscreteModule_trivialF2 G)))

/-- **`H²(G, 𝔽₂)`** (needs `G` locally compact, as Tau Ceti's degree-two comparison does). -/
noncomputable def cont2F2 [LocallyCompactSpace G] :
    GQ2.ContCoh.H2 G (ZMod 2) ≃+ continuousCohomology 2 (TauCeti.trivialF2 G) :=
  (((h2Equiv G (ZMod 2)).trans (toF2two G htriv)).trans
    (TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology G (TauCeti.trivialF2 G).V)).trans
    (eqToAddEquiv (congrArg (continuousCohomology 2) (TauCeti.ofDiscreteModule_trivialF2 G)))

theorem cont1F2_apply (x : GQ2.ContCoh.H1 G (ZMod 2)) :
    cont1F2 G htriv x =
      (eqToHom (congrArg (continuousCohomology 1) (TauCeti.ofDiscreteModule_trivialF2 G))).hom
        (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology G (TauCeti.trivialF2 G).V
          (toF2 G htriv (h1Equiv G (ZMod 2) x))) := by
  rw [cont1F2, AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.trans_apply,
    eqToAddEquiv_apply]

theorem cont2F2_apply [LocallyCompactSpace G] (x : GQ2.ContCoh.H2 G (ZMod 2)) :
    cont2F2 G htriv x =
      (eqToHom (congrArg (continuousCohomology 2) (TauCeti.ofDiscreteModule_trivialF2 G))).hom
        (TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology G (TauCeti.trivialF2 G).V
          (toF2two G htriv (h2Equiv G (ZMod 2) x))) := by
  rw [cont2F2, AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.trans_apply,
    eqToAddEquiv_apply]

/-- `cont1F2` on the class of a cocycle `z : G → ZMod 2`: the Tau Ceti class of the cocycle
`g ↦ (trivialF2Equiv G).symm (z g)` (`coe_toF2Z1`). -/
theorem cont1F2_H1mk (z : GQ2.ContCoh.Z1 G (ZMod 2)) :
    cont1F2 G htriv (GQ2.ContCoh.H1mk G (ZMod 2) z) =
      (eqToHom (congrArg (continuousCohomology 1) (TauCeti.ofDiscreteModule_trivialF2 G))).hom
        (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology G (TauCeti.trivialF2 G).V
          (toF2Z1 G htriv z : TauCeti.ContCohomology.H1 G (TauCeti.trivialF2 G).V)) := by
  rw [cont1F2_apply, toF2_H1mk]

/-- `cont2F2` on the class of a cocycle. -/
theorem cont2F2_H2mk [LocallyCompactSpace G] (z : GQ2.ContCoh.Z2 G (ZMod 2)) :
    cont2F2 G htriv (GQ2.ContCoh.H2mk G (ZMod 2) z) =
      (eqToHom (congrArg (continuousCohomology 2) (TauCeti.ofDiscreteModule_trivialF2 G))).hom
        (TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology G (TauCeti.trivialF2 G).V
          (toF2Z2 G htriv z : TauCeti.ContCohomology.H2 G (TauCeti.trivialF2 G).V)) := by
  rw [cont2F2_apply, toF2two_H2mk]

/-- **Characters.** The class of a gq2 cocycle `z` whose values are those of a continuous
character `α : G →* Multiplicative (ZMod 2)` is Tau Ceti's `homClass G α hα`.  This is how
`GQ2.kummerClassK` and the Evens–Kahn characters of B9/B11a are read in Tau Ceti. -/
theorem cont1F2_H1mk_eq_homClass (z : GQ2.ContCoh.Z1 G (ZMod 2))
    (α : G →* Multiplicative (ZMod 2)) (hα : Continuous α)
    (hz : ∀ g, z.1 g = Multiplicative.toAdd (α g)) :
    cont1F2 G htriv (GQ2.ContCoh.H1mk G (ZMod 2) z) = TauCeti.ContCohomology.homClass G α hα := by
  have key : toF2Z1 G htriv z = TauCeti.ContCohomology.evensHomCocycle α hα := by
    apply Subtype.ext
    rw [coe_toF2Z1, TauCeti.ContCohomology.coe_evensHomCocycle]
    funext g
    rw [hz g]
  rw [cont1F2_H1mk, TauCeti.ContCohomology.homClass_def, key]

/-- **Cup products.** gq2's `a ⌣[htriv] b` (`GQ2.trivialCupPairing 2 G htriv`) is Tau Ceti's
`(trivialF2TopPairing G).cup 1 1`; the right side lands in degree `1 + 1`, which is `2` by
definitional unfolding. -/
theorem cont2F2_trivialCupPairing [LocallyCompactSpace G] (x y : GQ2.ContCoh.H1 G (ZMod 2)) :
    cont2F2 G htriv (GQ2.trivialCupPairing 2 G htriv x y) =
      (TauCeti.trivialF2TopPairing G).cup 1 1 (cont1F2 G htriv x) (cont1F2 G htriv y) := by
  rw [cont1F2_apply, cont1F2_apply, cont2F2_apply,
    TauCeti.trivialF2TopPairing_cup_one_one_explicitH1]
  congr 2
  rw [GQ2.trivialCupPairing, h2Equiv_cup11]
  simp only [toF2, toF2two, TauCeti.ContCohomology.explicitMap1Equiv_apply,
    TauCeti.ContCohomology.explicitMap2Equiv_apply]
  exact TauCeti.ContCohomology.explicitMap2_explicitCup11 G _ _ _ _ _ _ G _ _ _ _ _ _
    (ContinuousMulEquiv.refl G) _ _ _ _ _ _ _ _ _ (fun m n => by simp)
    (h1Equiv G (ZMod 2) x) (h1Equiv G (ZMod 2) y)

end F2

section F2Naturality

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

attribute [local instance] TopRep.distribMulAction

local instance continuousSMul_trivialF2' (K : Type u) [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] : ContinuousSMul K (TauCeti.trivialF2 K).V :=
  (TauCeti.isSmoothDiscrete_trivialF2 K).continuousSMul

variable (φ : H →ₜ* G)

/-- Tau Ceti's `trivialF2CoeffHom_smul`, in the form `cocyclesMap1`/`eqToHom_comp_trivialF2Map`
expect for a continuous `φ`. -/
theorem trivialF2CoeffHom_smul' (h : H) (m : (TauCeti.trivialF2 G).V) :
    TauCeti.trivialF2CoeffHom (φ h • m) = h • (TauCeti.trivialF2CoeffHom m : (TauCeti.trivialF2 H).V) :=
  TauCeti.trivialF2CoeffHom_smul (φ : H →* G) h m

/-- The coefficient identifications of `ofDiscreteModule_trivialF2` commute with
`trivialF2CoeffHom` (the `hfM` hypothesis of Tau Ceti's `eqToHom_comp_trivialF2Map`). -/
theorem trivialF2Equiv_eqToHom_trivialF2CoeffHom (m : (TauCeti.trivialF2 G).V) :
    TauCeti.trivialF2Equiv H
        ((eqToHom (TauCeti.ofDiscreteModule_trivialF2 H)).hom (TauCeti.trivialF2CoeffHom m)) =
      TauCeti.trivialF2Equiv G ((eqToHom (TauCeti.ofDiscreteModule_trivialF2 G)).hom m) := by
  refine (congrArg (TauCeti.trivialF2Equiv H)
    (TauCeti.eqToHom_ofDiscreteModule_trivialF2_apply H (TauCeti.trivialF2CoeffHom m))).trans
    (Eq.trans ?_ (congrArg (TauCeti.trivialF2Equiv G)
      (TauCeti.eqToHom_ofDiscreteModule_trivialF2_apply G m)).symm)
  rw [TauCeti.trivialF2CoeffHom_apply, AddEquiv.apply_symm_apply]

/-- Tau Ceti's pullback `trivialF2Map φ` on the explicit class of a `1`-cocycle `c` is the
explicit class of `c ∘ φ` (read through `trivialF2CoeffHom`): `eqToHom_comp_trivialF2Map`
composed with the naturality `explicitH1AddEquivContinuousCohomology_map`. -/
theorem trivialF2Map_eqToHom_explicitH1 (c : TauCeti.ContCohomology.Z1 G (TauCeti.trivialF2 G).V) :
    TauCeti.trivialF2Map φ 1
        ((eqToHom (congrArg (continuousCohomology 1) (TauCeti.ofDiscreteModule_trivialF2 G))).hom
          (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology G (TauCeti.trivialF2 G).V
            (c : TauCeti.ContCohomology.H1 G (TauCeti.trivialF2 G).V))) =
      (eqToHom (congrArg (continuousCohomology 1) (TauCeti.ofDiscreteModule_trivialF2 H))).hom
        (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology H (TauCeti.trivialF2 H).V
          (TauCeti.ContCohomology.cocyclesMap1 G (TauCeti.trivialF2 G).V H (TauCeti.trivialF2 H).V
            φ TauCeti.trivialF2CoeffHom continuous_of_discreteTopology
            (trivialF2CoeffHom_smul' φ) c :
              TauCeti.ContCohomology.H1 H (TauCeti.trivialF2 H).V)) := by
  rw [← ConcreteCategory.comp_apply,
    TauCeti.eqToHom_comp_trivialF2Map φ (TauCeti.ofDiscreteModule_trivialF2 G)
      (TauCeti.ofDiscreteModule_trivialF2 H) TauCeti.trivialF2CoeffHom (trivialF2CoeffHom_smul' φ)
      (trivialF2Equiv_eqToHom_trivialF2CoeffHom (G := G) (H := H)) 1,
    ConcreteCategory.comp_apply, TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology_map,
    TauCeti.ContCohomology.explicitMap1_mk]

/-- Degree-two analogue of `trivialF2Map_eqToHom_explicitH1`. -/
theorem trivialF2Map_eqToHom_explicitH2 [LocallyCompactSpace G] [LocallyCompactSpace H]
    (c : TauCeti.ContCohomology.Z2 G (TauCeti.trivialF2 G).V) :
    TauCeti.trivialF2Map φ 2
        ((eqToHom (congrArg (continuousCohomology 2) (TauCeti.ofDiscreteModule_trivialF2 G))).hom
          (TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology G (TauCeti.trivialF2 G).V
            (c : TauCeti.ContCohomology.H2 G (TauCeti.trivialF2 G).V))) =
      (eqToHom (congrArg (continuousCohomology 2) (TauCeti.ofDiscreteModule_trivialF2 H))).hom
        (TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology H (TauCeti.trivialF2 H).V
          (TauCeti.ContCohomology.cocyclesMap2 G (TauCeti.trivialF2 G).V H (TauCeti.trivialF2 H).V
            φ TauCeti.trivialF2CoeffHom continuous_of_discreteTopology
            (trivialF2CoeffHom_smul' φ) c :
              TauCeti.ContCohomology.H2 H (TauCeti.trivialF2 H).V)) := by
  rw [← ConcreteCategory.comp_apply,
    TauCeti.eqToHom_comp_trivialF2Map φ (TauCeti.ofDiscreteModule_trivialF2 G)
      (TauCeti.ofDiscreteModule_trivialF2 H) TauCeti.trivialF2CoeffHom (trivialF2CoeffHom_smul' φ)
      (trivialF2Equiv_eqToHom_trivialF2CoeffHom (G := G) (H := H)) 2,
    ConcreteCategory.comp_apply, TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology_map,
    TauCeti.ContCohomology.explicitMap2_mk]

variable [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
  [DistribMulAction H (ZMod 2)] [ContinuousSMul H (ZMod 2)]
  (htrivG : ∀ (g : G) (m : ZMod 2), g • m = m) (htrivH : ∀ (h : H) (m : ZMod 2), h • m = m)

include htrivG htrivH in
/-- The identity of `ZMod 2` is compatible with any continuous `φ : H →ₜ* G` when both actions
are trivial (the hypothesis of gq2's `H1comap φ (AddMonoidHom.id _)`). -/
theorem id_compat_of_trivial (h : H) (m : ZMod 2) :
    (AddMonoidHom.id (ZMod 2)) (φ h • m) = h • (AddMonoidHom.id (ZMod 2)) m := by
  rw [htrivG, htrivH]

/-- **Naturality of `cont1F2`** along a continuous homomorphism `φ : H →ₜ* G`: Tau Ceti's
`trivialF2Map φ 1` is gq2's pullback `H1comap φ (AddMonoidHom.id _)`. -/
theorem trivialF2Map_cont1F2 (x : GQ2.ContCoh.H1 G (ZMod 2)) :
    TauCeti.trivialF2Map φ 1 (cont1F2 G htrivG x) =
      cont1F2 H htrivH (GQ2.ContCoh.H1comap φ (AddMonoidHom.id (ZMod 2)) continuous_id
        (id_compat_of_trivial φ htrivG htrivH) x) := by
  obtain ⟨z, rfl⟩ := GQ2.ContCoh.H1mk_surjective x
  have key : TauCeti.ContCohomology.cocyclesMap1 G (TauCeti.trivialF2 G).V H
      (TauCeti.trivialF2 H).V φ TauCeti.trivialF2CoeffHom continuous_of_discreteTopology
      (trivialF2CoeffHom_smul' φ) (toF2Z1 G htrivG z) =
      toF2Z1 H htrivH (GQ2.ContCoh.Z1comap φ (AddMonoidHom.id (ZMod 2)) continuous_id
        (id_compat_of_trivial φ htrivG htrivH) z) := by
    apply Subtype.ext
    funext h
    refine (TauCeti.ContCohomology.cocyclesMap1_apply G _ H _ φ _ _ _ _ h).trans ?_
    simp only [TauCeti.trivialF2CoeffHom_apply, coe_toF2Z1, AddEquiv.apply_symm_apply]
    rfl
  rw [H1comap_H1mk, cont1F2_H1mk, cont1F2_H1mk, trivialF2Map_eqToHom_explicitH1, key]

/-- **Naturality of `cont2F2`** along a continuous homomorphism `φ : H →ₜ* G`. -/
theorem trivialF2Map_cont2F2 [LocallyCompactSpace G] [LocallyCompactSpace H]
    (x : GQ2.ContCoh.H2 G (ZMod 2)) :
    TauCeti.trivialF2Map φ 2 (cont2F2 G htrivG x) =
      cont2F2 H htrivH (GQ2.ContCoh.H2comap φ (AddMonoidHom.id (ZMod 2)) continuous_id
        (id_compat_of_trivial φ htrivG htrivH) x) := by
  obtain ⟨z, rfl⟩ := GQ2.ContCoh.H2mk_surjective x
  have key : TauCeti.ContCohomology.cocyclesMap2 G (TauCeti.trivialF2 G).V H
      (TauCeti.trivialF2 H).V φ TauCeti.trivialF2CoeffHom continuous_of_discreteTopology
      (trivialF2CoeffHom_smul' φ) (toF2Z2 G htrivG z) =
      toF2Z2 H htrivH (GQ2.ContCoh.Z2comap φ (AddMonoidHom.id (ZMod 2)) continuous_id
        (id_compat_of_trivial φ htrivG htrivH) z) := by
    apply Subtype.ext
    funext ⟨h, k⟩
    refine (TauCeti.ContCohomology.cocyclesMap2_apply G _ H _ φ _ _ _ _ h k).trans ?_
    simp only [TauCeti.trivialF2CoeffHom_apply, coe_toF2Z2, AddEquiv.apply_symm_apply]
    rfl
  rw [H2comap_H2mk, cont2F2_H2mk, cont2F2_H2mk, trivialF2Map_eqToHom_explicitH2, key]

end F2Naturality

/-! ## The Kummer class, parametric in the Galois dictionary

gq2's `GQ2.kummerClassK k a ∈ H¹(↥k.fixingSubgroup, 𝔽₂)` is the class of
`g ↦ if g • √a = √a then 0 else 1` for the root `sqrtCl a ∈ ℚ̄₂`; Tau Ceti's
`TauCeti.kummerClass a ∈ H¹(Gal(kˢᵉᵖ/k), 𝔽₂)` is the class of the same cocycle for a root in
`SeparableClosure ↥k`.  The comparison is stated for **any** `Φ : ↥k.fixingSubgroup ≃ₜ* Gal(kˢᵉᵖ/k)`
and `↥k`-algebra map `ι : kˢᵉᵖ →ₐ[↥k] ℚ̄₂` with `ι (Φ g x) = g (ι x)`, and then specialized to
A1's pair `(fixingEquivAbsGal k, sepClosureEquiv k)` (`GQ2/TauCeti/GaloisDict.lean`). -/

section KummerGeneric

variable {K : Type u} [Field K] [Invertible (2 : K)]
  {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [DistribMulAction H (ZMod 2)] [ContinuousSMul H (ZMod 2)]
  (htriv : ∀ (h : H) (m : ZMod 2), h • m = m)
  (Φ : H →ₜ* TauCeti.AbsoluteGaloisGroup K)

attribute [local instance] TopRep.distribMulAction

local instance continuousSMul_trivialF2Generic (L : Type u) [Group L] [TopologicalSpace L]
    [IsTopologicalGroup L] : ContinuousSMul L (TauCeti.trivialF2 L).V :=
  (TauCeti.isSmoothDiscrete_trivialF2 L).continuousSMul

open scoped Classical in
/-- **The Kummer class, generically.**  For a field `K` with `2` invertible, a continuous
`Φ : H →ₜ* Gal(Kˢᵉᵖ/K)`, a square root `α ∈ Kˢᵉᵖ` of `a ∈ Kˣ` and a gq2 cocycle
`z : H → ZMod 2` with `z h = if Φ h • α = α then 0 else 1`, Tau Ceti's `kummerClass a` pulled
back along `Φ` is the class of `z` read by `cont1F2`.  Stated over a variable field so that the
instance terms stay small; the dyadic case `K = ↥k` is `trivialF2Map_kummerClass`. -/
theorem trivialF2Map_kummerClass_of_forall (a : Kˣ) (α : (SeparableClosure K)ˣ)
    (hα : α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom a)
    (z : GQ2.ContCoh.Z1 H (ZMod 2)) (hz : ∀ h, z.1 h = if Φ h • α = α then 0 else 1) :
    TauCeti.trivialF2Map Φ 1 (TauCeti.kummerClass a) =
      cont1F2 H htriv (GQ2.ContCoh.H1mk H (ZMod 2) z) := by
  have key : TauCeti.ContCohomology.cocyclesMap1 (TauCeti.AbsoluteGaloisGroup K)
      (TauCeti.trivialF2 (TauCeti.AbsoluteGaloisGroup K)).V H (TauCeti.trivialF2 H).V Φ
      TauCeti.trivialF2CoeffHom continuous_of_discreteTopology (trivialF2CoeffHom_smul' Φ)
      (TauCeti.kummerCocycleModTwo K hα) = toF2Z1 H htriv z := by
    apply Subtype.ext
    funext h
    apply (TauCeti.trivialF2Equiv H).injective
    rw [coe_toF2Z1, AddEquiv.apply_symm_apply, hz h]
    refine (congrArg _ (TauCeti.ContCohomology.cocyclesMap1_apply _ _ _ _ _ _ _ _ _ h)).trans ?_
    rw [TauCeti.trivialF2CoeffHom_apply, AddEquiv.apply_symm_apply,
      TauCeti.kummerCocycleModTwo_apply]
    congr 1
  rw [TauCeti.kummerClass_eq_kummerCocycleModTwoClass_of_sq_eq K a α hα,
    TauCeti.kummerCocycleModTwoClass_def, trivialF2Map_eqToHom_explicitH1, key, cont1F2_H1mk]

end KummerGeneric

section Kummer

variable (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [Invertible (2 : ↥k)]
  (Φ : ↥k.fixingSubgroup ≃ₜ* TauCeti.AbsoluteGaloisGroup ↥k)
  (ι : SeparableClosure ↥k →ₐ[↥k] AlgebraicClosure ℚ_[2])
  (hΦι : ∀ (g : ↥k.fixingSubgroup) (x : SeparableClosure ↥k),
    ι (Φ g x) = (g : GQ2.Kummer.GaloisGroup ℚ_[2]) (ι x))
  (htriv : ∀ (g : ↥k.fixingSubgroup) (m : ZMod 2), g • m = m)

attribute [local instance] TopRep.distribMulAction

local instance continuousSMul_trivialF2'' (K : Type) [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] : ContinuousSMul K (TauCeti.trivialF2 K).V :=
  (TauCeti.isSmoothDiscrete_trivialF2 K).continuousSMul

include hΦι in
/-- For a square root `β ∈ kˢᵉᵖ` of `a`, `Φ g` fixes `β` exactly when `g` fixes gq2's root
`sqrtCl a ∈ ℚ̄₂` (`ι β = ± sqrtCl a`). -/
theorem apply_eq_iff_smul_sqrtCl_eq (a : (↥k)ˣ) {β : SeparableClosure ↥k}
    (hβ : β ^ 2 = algebraMap ↥k (SeparableClosure ↥k) (a : ↥k)) (g : ↥k.fixingSubgroup) :
    Φ g β = β ↔
      (g : GQ2.Kummer.GaloisGroup ℚ_[2]) • GQ2.sqrtCl ((a : ↥k) : AlgebraicClosure ℚ_[2]) =
        GQ2.sqrtCl ((a : ↥k) : AlgebraicClosure ℚ_[2]) := by
  have hι : ι β ^ 2 = GQ2.sqrtCl ((a : ↥k) : AlgebraicClosure ℚ_[2]) ^ 2 := by
    rw [← map_pow, hβ, AlgHom.commutes, GQ2.sqrtCl_sq]
    rfl
  have hinj : Function.Injective ι := ι.toRingHom.injective
  rw [← hinj.eq_iff (a := Φ g β) (b := β), hΦι, ← AlgEquiv.smul_def]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hι with h | h
  · rw [h]
  · rw [h, smul_neg, neg_inj]

/-- The gq2 Kummer cocycle `g ↦ if g • √a = √a then 0 else 1` of `a ∈ kˣ` on `↥k.fixingSubgroup`
(the cocycle underlying `GQ2.kummerClassK k a`, spelled out so that it can be named). -/
noncomputable def kummerCocycleK (a : (↥k)ˣ) : GQ2.ContCoh.Z1 ↥k.fixingSubgroup (ZMod 2) :=
  ⟨fun g ↦ GQ2.Kummer.kummerCocycleFun (GQ2.sqrtCl ((a : ↥k) : AlgebraicClosure ℚ_[2]))
      ((g : ↥k.fixingSubgroup) : GQ2.Kummer.GaloisGroup ℚ_[2]),
    (GQ2.ContCoh.mem_Z1_iff_of_trivial (fun _ _ ↦ rfl)).mpr
      ⟨(GQ2.Kummer.kummerCocycleFun_continuous _).comp continuous_subtype_val,
        fun g h ↦ GQ2.kummerCocycleFun_hom_on (GQ2.sqrtCl_sq _)
          (GQ2.sqrtCl_ne_zero (GQ2.unitCoe_ne_zero k a))
          (fun _ hg' ↦ GQ2.fixingSubgroup_smul k hg' (a : ↥k)) g h⟩⟩

@[simp] theorem coe_kummerCocycleK (a : (↥k)ˣ) :
    (kummerCocycleK k a : ↥k.fixingSubgroup → ZMod 2) = fun g ↦
      GQ2.Kummer.kummerCocycleFun (GQ2.sqrtCl ((a : ↥k) : AlgebraicClosure ℚ_[2]))
        ((g : ↥k.fixingSubgroup) : GQ2.Kummer.GaloisGroup ℚ_[2]) := rfl

/-- `GQ2.kummerClassK k a` is the class of `kummerCocycleK k a` (definitional). -/
theorem kummerClassK_eq_H1mk (a : (↥k)ˣ) :
    GQ2.kummerClassK k a = GQ2.ContCoh.H1mk ↥k.fixingSubgroup (ZMod 2) (kummerCocycleK k a) := rfl

include hΦι in
/-- **The Kummer dictionary.**  Tau Ceti's `kummerClass a`, pulled back along `Φ` by
`trivialF2Map`, is gq2's `kummerClassK k a` read in `continuousCohomology 1 (trivialF2 _)` by
`cont1F2`.  (`trivialF2Map Φ 1 = (trivialF2Iso Φ 1).inv`, by `TauCeti.trivialF2Iso_inv`.) -/
theorem trivialF2Map_kummerClass (a : (↥k)ˣ) :
    TauCeti.trivialF2Map (Φ : ↥k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup ↥k) 1
        (TauCeti.kummerClass a) =
      cont1F2 ↥k.fixingSubgroup htriv (GQ2.kummerClassK k a) := by
  -- a separable square root of `a`
  obtain ⟨β, hβ⟩ := IsSepClosed.exists_pow_nat_eq
    (algebraMap ↥k (SeparableClosure ↥k) (a : ↥k)) 2
  have hβ0 : β ≠ 0 := by
    rintro rfl
    apply a.ne_zero
    apply (map_eq_zero (algebraMap ↥k (SeparableClosure ↥k))).1
    rw [← hβ]
    exact zero_pow two_ne_zero
  have hα : Units.mk0 β hβ0 ^ 2 =
      Units.map (algebraMap ↥k (SeparableClosure ↥k)).toMonoidHom a :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map, hβ]; rfl)
  rw [kummerClassK_eq_H1mk]
  refine trivialF2Map_kummerClass_of_forall htriv
    (Φ : ↥k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup ↥k) a (Units.mk0 β hβ0) hα
    (kummerCocycleK k a) fun g => ?_
  show GQ2.Kummer.kummerCocycleFun _ _ = _
  rw [GQ2.Kummer.kummerCocycleFun]
  congr 1
  refine propext ?_
  rw [Units.ext_iff]
  exact (apply_eq_iff_smul_sqrtCl_eq k Φ ι hΦι a hβ g).symm

include hΦι in
/-- `trivialF2Map_kummerClass` in the `trivialF2Iso` form: the inverse of Tau Ceti's transport
along `Φ` carries `kummerClass a` to `cont1F2 _ htriv (kummerClassK k a)`. -/
theorem trivialF2Iso_inv_kummerClass (a : (↥k)ˣ) :
    (TauCeti.trivialF2Iso Φ 1).inv (TauCeti.kummerClass a) =
      cont1F2 ↥k.fixingSubgroup htriv (GQ2.kummerClassK k a) := by
  rw [TauCeti.trivialF2Iso_inv]
  exact trivialF2Map_kummerClass k Φ ι hΦι htriv a

variable [FiniteDimensional ℚ_[2] ↥k]

/-- **The Kummer dictionary at A1's data** `(fixingEquivAbsGal k, sepClosureEquiv k)`
(`GQ2/TauCeti/GaloisDict.lean`): the form B11a and B9 consume. -/
theorem trivialF2Map_fixingEquivAbsGal_kummerClass (a : (↥k)ˣ) :
    TauCeti.trivialF2Map
        (fixingEquivAbsGal k : ↥k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup ↥k) 1
        (TauCeti.kummerClass a) =
      cont1F2 ↥k.fixingSubgroup htriv (GQ2.kummerClassK k a) :=
  trivialF2Map_kummerClass k (fixingEquivAbsGal k) (sepClosureEquiv k).toAlgHom
    (sepClosureEquiv_fixingEquivAbsGal_apply k) htriv a

/-- `trivialF2Map_fixingEquivAbsGal_kummerClass` in the `trivialF2Iso` form. -/
theorem trivialF2Iso_fixingEquivAbsGal_inv_kummerClass (a : (↥k)ˣ) :
    (TauCeti.trivialF2Iso (fixingEquivAbsGal k) 1).inv (TauCeti.kummerClass a) =
      cont1F2 ↥k.fixingSubgroup htriv (GQ2.kummerClassK k a) :=
  trivialF2Iso_inv_kummerClass k (fixingEquivAbsGal k) (sepClosureEquiv k).toAlgHom
    (sepClosureEquiv_fixingEquivAbsGal_apply k) htriv a

end Kummer

end GQ2.TauCetiBridge
