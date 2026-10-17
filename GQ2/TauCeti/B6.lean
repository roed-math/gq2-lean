/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5.1
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Perfect
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.RootsOfUnity
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.RestrictScalars
public import GQ2.TauCeti.CohomologyDict
public import GQ2.TauCeti.DualizingGroup

@[expose] public section

/-!
# B6: local Tate duality at every finite `k/ℚ₂`, from Tau Ceti

Ticket B6 of the Tau Ceti discharge campaign (`docs/orchestration/tauceti-tickets.md`, recon memo
`docs/orchestration/tauceti-t2-recon.md` §B6).  Everything lives in `GQ2.TauCetiBridge`.

The deliverable is `tateDualityAt_tauceti`, with the type of the field
`GQ2.LiteratureInputs.tateDualityAt`: for a topological group `G` with
`hloc : GQ2.IsLocalDualizingGroup G n`, the bundle `GQ2.TateDualityG G n` (an invariant map
`inv : H²(G, μₙ) ≃+ ℤ/n` and perfectness of the evaluation cup pairings in bidegrees `(0,2)`,
`(1,1)`, `(2,0)` for every finite discrete `n`-torsion `G`-module `M : Type`).

## Route

1. `GQ2/TauCeti/DualizingGroup.lean` turns `hloc` into a finite `K = dualizingField ι`, an
   isomorphism `e = dualizingEquiv ι hι : G ≃ₜ* Field.absoluteGaloisGroup K`, and the equivariant
   coefficient identification `muNEquiv n K : GQ2.MuN n ≃+ (muNRep n K).V`.
2. **Transport** (`section Transport`): for a gq2 module `N` over `G` identified equivariantly
   (along `e.symm`) with the carrier of a discrete `B : GalRep n K`, gq2's `H⁰/H¹/H²(G, N)` are
   Mathlib's `continuousCohomology i B`: A2's dictionary `h{1,2}Equiv`, Tau Ceti's change of group
   and coefficients `explicitMap{0,1,2}`, and Tau Ceti's comparison isomorphisms
   (`transport0`, `transport1`, `transport2`).
3. **The module and its dual** (`section Module`): `M` with the `G_K`-action pulled back along
   `e.symm` is `galRep n K M = ofDiscreteModule (ZMod n) G_K M`, and gq2's `μₙ`-dual
   `GQ2.MuDual n M` is Tau Ceti's `tateDual (galRep n K M)` (`muDualEquiv`, equivariant by
   `muDualEquiv_smul`, which is gq2's conjugation formula against Tau Ceti's
   `tateDualEquiv_ρ_apply`).
4. **The pairings agree** (`tatePairing_transport02/11/20`): the transported gq2 cup pairing,
   read through `inv`, is Tau Ceti's `tateDualityPairing`, by the explicit cup naturality
   `explicitMap2_explicitCup02/11/20` and the explicit-vs-canonical cup comparisons, exactly as in
   Tau Ceti's `Local/Duality/Explicit.lean`.
5. **Perfectness transfers** (`perfect02_of_perfect` etc.): bijectivity of `x ↦ ⟨x, ·⟩` along
   the commuting square of equivalences, from `tateDualityPairing_perfect_mixed`.
6. **Assembly** (`tateDualityOfEquiv`, `tateDualityAt_tauceti`): Tau Ceti's local-field
   package on `↥K` is installed with `letI` (A1's `valuativeRel`, `localTopology`,
   `isNonarchimedeanLocalField`; never global instances), `tr` comes from
   `h2MuEquivZMod_mixed` (any `tr` works, so no normalization is needed), and the per-module
   instances (`AddCommGroup.zmodModule`, `DistribMulAction.compHom`) are installed inside each
   perfectness field.

## Conventions

* `inv` is not normalized (gq2 asserts existence only; see `GQ2/TateDuality.lean`).
* Tau Ceti names are fully qualified; nothing here is a global instance on `↥K`.
* The three Galois facts at `ℚ̄₂` of A1 are local instances here, because instance search for them
  does not terminate under the class-field-theory imports (memo, cross-cutting finding 2).
-/

noncomputable section

namespace GQ2.TauCetiBridge

open CategoryTheory
open GQ2.ContCoh

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

attribute [local instance] isTorsionFree_algebraicClosure isAlgClosure_algebraicClosure
  isGalois_algebraicClosure discreteTopology_muN isTopologicalAddGroup_muN

attribute [local instance] TopRep.distribMulAction

-- The dictionary sections quantify over gq2's full module bundle so that every statement reads
-- on the same typeclass context the assembly has; several individual lemmas use only part of it.
set_option linter.unusedSectionVars false

/-! ### Local instances on `ofDiscreteModule` and `tateDual` (consumed by Tau Ceti's lemmas)

Stated as theorems and made local instances for the whole file (a `local instance` inside the
section would not outlive it). -/

section LocalInstances

variable {R : Type*} [Ring R] [TopologicalSpace R] {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [DiscreteTopology M] [DistribMulAction G M] [SMulCommClass G R M] [ContinuousSMul R M]

/-- The carrier of `ofDiscreteModule R G M` is finite when `M` is. -/
theorem finite_ofDiscreteModule_V [Finite M] : Finite (TauCeti.ofDiscreteModule R G M).V :=
  inferInstanceAs (Finite M)

/-- The derived action on the carrier of `ofDiscreteModule R G M` is continuous when the action on
`M` is (it is the same action). -/
theorem continuousSMul_ofDiscreteModule_V [ContinuousSMul G M] :
    ContinuousSMul G (TauCeti.ofDiscreteModule R G M).V :=
  inferInstanceAs (ContinuousSMul G M)

/-- `ofDiscreteModule R G M` is smooth discrete when the action on `M` is continuous
(`TauCeti.ofDiscreteModule_isSmoothDiscrete`, as a `Fact` for Tau Ceti's duality theorems). -/
theorem fact_isSmoothDiscrete_ofDiscreteModule [ContinuousSMul G M] :
    Fact (TauCeti.IsSmoothDiscrete R (TauCeti.ofDiscreteModule R G M)) :=
  ⟨TauCeti.ofDiscreteModule_isSmoothDiscrete R G M⟩

/-- The derived action on the Tate dual of a finite smooth discrete `A` is continuous. -/
theorem continuousSMul_tateDual_V {n : ℕ} [NeZero n] {F : Type} [Field F]
    (A : TauCeti.ClassFieldTheory.GalRep n F) [DiscreteTopology A.V] [Finite A.V]
    [Fact (TauCeti.IsSmoothDiscrete (ZMod n) A)] :
    ContinuousSMul (Field.absoluteGaloisGroup F) (TauCeti.ClassFieldTheory.tateDual A).V :=
  (Fact.out : TauCeti.IsSmoothDiscrete (ZMod n) (TauCeti.ClassFieldTheory.tateDual A)).continuousSMul

end LocalInstances

attribute [local instance] finite_ofDiscreteModule_V continuousSMul_ofDiscreteModule_V
  fact_isSmoothDiscrete_ofDiscreteModule continuousSMul_tateDual_V

/-! ### Bijectivity packaging -/

/-- Tau Ceti's two-clause perfectness (zero left kernel, every character is a pairing) is
bijectivity of the curried pairing. -/
private theorem bijective_of_perfect {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] {n : ℕ}
    (Φ : X →+ Y →+ ZMod n)
    (h : (∀ x, (∀ y, Φ x y = 0) → x = 0) ∧ ∀ φ : Y →+ ZMod n, ∃ x, ∀ y, Φ x y = φ y) :
    Function.Bijective Φ :=
  ⟨(injective_iff_map_eq_zero Φ).2 fun x hx ↦ h.1 x fun y ↦ DFunLike.congr_fun hx y,
    fun φ ↦ (h.2 φ).imp fun _ hx ↦ AddMonoidHom.ext hx⟩

/-- Precomposition with an additive equivalence is a bijection on characters. -/
private theorem bijective_comp_addEquiv {Y Y' : Type*} [AddCommGroup Y] [AddCommGroup Y'] {n : ℕ}
    (S : Y ≃+ Y') :
    Function.Bijective fun ψ : Y' →+ ZMod n ↦ ψ.comp S.toAddMonoidHom :=
  ⟨fun ψ ψ' h ↦ AddMonoidHom.ext fun y' ↦ by
      obtain ⟨y, rfl⟩ := S.surjective y'
      exact DFunLike.congr_fun h y,
    fun ψ ↦ ⟨ψ.comp S.symm.toAddMonoidHom, AddMonoidHom.ext fun y ↦ by simp⟩⟩

/-- **Bijectivity along a commuting square**: if `F x y = Φ (T x) (S y)` with `T`, `S` additive
equivalences and `Φ` bijective, then `F` is bijective. -/
private theorem bijective_of_comm {X Y X' Y' : Type*} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup X'] [AddCommGroup Y'] {n : ℕ} (F : X → (Y →+ ZMod n)) (T : X ≃+ X')
    (S : Y ≃+ Y') (Φ : X' →+ (Y' →+ ZMod n)) (hΦ : Function.Bijective Φ)
    (hcomm : ∀ x y, F x y = Φ (T x) (S y)) : Function.Bijective F := by
  have hF : F = (fun ψ : Y' →+ ZMod n ↦ ψ.comp S.toAddMonoidHom) ∘ Φ ∘ T :=
    funext fun x ↦ AddMonoidHom.ext fun y ↦ hcomm x y
  rw [hF]
  exact (bijective_comp_addEquiv S).comp (hΦ.comp T.bijective)

/-- Tau Ceti's local Tate-duality pairing, curried as an additive homomorphism into the
Pontryagin dual. -/
def tatePairingHom {n : ℕ} {F : Type} [Field F] (A : TauCeti.ClassFieldTheory.GalRep n F)
    [DiscreteTopology A.V]
    (tr : continuousCohomology 2 (TauCeti.ClassFieldTheory.muNRep n F) ≃+ ZMod n)
    (i j : ℕ) (hij : i + j = 2) :
    continuousCohomology i (TauCeti.ClassFieldTheory.tateDual A) →+
      (continuousCohomology j A →+ ZMod n) :=
  AddMonoidHom.mk'
    (fun x ↦ AddMonoidHom.mk' (fun y ↦ TauCeti.ClassFieldTheory.tateDualityPairing A tr i j hij x y)
      (TauCeti.ClassFieldTheory.tateDualityPairing_add_right A tr i j hij x))
    fun x x' ↦ AddMonoidHom.ext fun y ↦
      TauCeti.ClassFieldTheory.tateDualityPairing_add_left A tr i j hij x x' y

@[simp] theorem tatePairingHom_apply {n : ℕ} {F : Type} [Field F]
    (A : TauCeti.ClassFieldTheory.GalRep n F) [DiscreteTopology A.V]
    (tr : continuousCohomology 2 (TauCeti.ClassFieldTheory.muNRep n F) ≃+ ZMod n)
    (i j : ℕ) (hij : i + j = 2) (x : continuousCohomology i (TauCeti.ClassFieldTheory.tateDual A))
    (y : continuousCohomology j A) :
    tatePairingHom A tr i j hij x y = TauCeti.ClassFieldTheory.tateDualityPairing A tr i j hij x y :=
  rfl

/-! ### Transport of gq2's cohomology over `G` to Mathlib's over `G_K`, along `e : G ≃ₜ* G_K` -/

section Transport

variable (n : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (e : G ≃ₜ* Field.absoluteGaloisGroup K)
  {N : Type} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
  [DistribMulAction G N] [ContinuousSMul G N]
  (B : TauCeti.ClassFieldTheory.GalRep n K) [DiscreteTopology B.V]
  [ContinuousSMul (Field.absoluteGaloisGroup K) B.V]
  (f : N ≃+ B.V) (hf : ∀ (h : Field.absoluteGaloisGroup K) (x : N), f (e.symm h • x) = h • f x)

/-- **Degree `0`**: gq2's invariants of `N` under `G` are `continuousCohomology 0 B`, through
Tau Ceti's `explicitMap0` along `e.symm` (bijective, `explicitMap0_bijective`) and A2's
`cont0Rep`. -/
def transport0 : GQ2.ContCoh.H0 G N ≃+ continuousCohomology 0 B :=
  (AddEquiv.ofBijective
    (TauCeti.ContCohomology.explicitMap0 G N (e.symm : Field.absoluteGaloisGroup K →* G)
      f.toAddMonoidHom hf)
    (TauCeti.ContCohomology.explicitMap0_bijective G N _ e.symm.surjective f hf)).trans
    (cont0Rep B)

theorem transport0_apply (m : GQ2.ContCoh.H0 G N) :
    transport0 n K e B f hf m =
      TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv B 0
        ((TauCeti.ContCohomology.explicitH0IsoContinuousCohomology
          (Field.absoluteGaloisGroup K) B.V).hom
          (TauCeti.ContCohomology.explicitMap0 G N (e.symm : Field.absoluteGaloisGroup K →* G)
            f.toAddMonoidHom hf m)) := rfl

/-- **Degree `1`**: A2's `h1Equiv`, Tau Ceti's `explicitMap1Equiv` along `e.symm` and `f`, and
Tau Ceti's comparison for the discrete `B`. -/
def transport1 : GQ2.ContCoh.H1 G N ≃+ continuousCohomology 1 B :=
  (h1Equiv G N).trans
    ((TauCeti.ContCohomology.explicitMap1Equiv G N (Field.absoluteGaloisGroup K) B.V e.symm f
      continuous_of_discreteTopology continuous_of_discreteTopology hf).trans
      B.explicitH1AddEquivContinuousCohomologyOfDiscrete)

theorem transport1_apply (x : GQ2.ContCoh.H1 G N) :
    transport1 n K e B f hf x =
      B.explicitH1AddEquivContinuousCohomologyOfDiscrete
        (TauCeti.ContCohomology.explicitMap1 G N (Field.absoluteGaloisGroup K) B.V e.symm
          f.toAddMonoidHom continuous_of_discreteTopology hf (h1Equiv G N x)) := by
  rw [transport1, AddEquiv.trans_apply, AddEquiv.trans_apply,
    TauCeti.ContCohomology.explicitMap1Equiv_apply]

/-- **Degree `2`**: A2's `h2Equiv`, Tau Ceti's `explicitMap2Equiv` along `e.symm` and `f`, and
Tau Ceti's comparison for the discrete `B` (`G_K` is compact, hence locally compact). -/
def transport2 : GQ2.ContCoh.H2 G N ≃+ continuousCohomology 2 B :=
  (h2Equiv G N).trans
    ((TauCeti.ContCohomology.explicitMap2Equiv G N (Field.absoluteGaloisGroup K) B.V e.symm f
      continuous_of_discreteTopology continuous_of_discreteTopology hf).trans
      B.explicitH2AddEquivContinuousCohomologyOfDiscrete)

theorem transport2_apply (x : GQ2.ContCoh.H2 G N) :
    transport2 n K e B f hf x =
      B.explicitH2AddEquivContinuousCohomologyOfDiscrete
        (TauCeti.ContCohomology.explicitMap2 G N (Field.absoluteGaloisGroup K) B.V e.symm
          f.toAddMonoidHom continuous_of_discreteTopology hf (h2Equiv G N x)) := by
  rw [transport2, AddEquiv.trans_apply, AddEquiv.trans_apply,
    TauCeti.ContCohomology.explicitMap2Equiv_apply]

end Transport

/-! ### The invariant map -/

section Inv

variable (n : ℕ) [NeZero n] (K : IntermediateField ℚ_[2] ℚ̄₂)
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (GQ2.MuN n)] [ContinuousSMul G (GQ2.MuN n)]
  (e : G ≃ₜ* Field.absoluteGaloisGroup K)
  (he : ∀ (h : Field.absoluteGaloisGroup K) (x : GQ2.MuN n),
    muNEquiv n K (e.symm h • x) = (TauCeti.ClassFieldTheory.muNRep n K).ρ h (muNEquiv n K x))

include he in
/-- `he` in the form Tau Ceti's `explicitMap{1,2}Equiv` expect (`h • ·` is the derived action
`TopRep.distribMulAction`). -/
theorem muNEquiv_smul_of (h : Field.absoluteGaloisGroup K) (x : GQ2.MuN n) :
    muNEquiv n K (e.symm h • x) = h • muNEquiv n K x :=
  (he h x).trans (TopRep.distribMulAction_smul _ h _).symm

/-- **`H²(G, μₙ(ℚ̄₂))` is `H²(G_K, μₙ(Kˢᵉᵖ))`**, Mathlib's continuous cohomology of `muNRep n K`. -/
def h2MuNEquiv : GQ2.ContCoh.H2 G (GQ2.MuN n) ≃+
    continuousCohomology 2 (TauCeti.ClassFieldTheory.muNRep n K) :=
  transport2 n K e (TauCeti.ClassFieldTheory.muNRep n K) (muNEquiv n K) (muNEquiv_smul_of n K e he)

variable (tr : continuousCohomology 2 (TauCeti.ClassFieldTheory.muNRep n K) ≃+ ZMod n)

/-- **The invariant map** of the bundle: `H²(G, μₙ) ≃+ H²(G_K, μₙ(Kˢᵉᵖ)) ≃+ ℤ/n` for a chosen
Tau Ceti invariant `tr`. -/
def invEquiv : GQ2.ContCoh.H2 G (GQ2.MuN n) ≃+ ZMod n := (h2MuNEquiv n K e he).trans tr

theorem invEquiv_apply (x : GQ2.ContCoh.H2 G (GQ2.MuN n)) :
    invEquiv n K e he tr x = tr (h2MuNEquiv n K e he x) := rfl

end Inv

/-! ### A finite `n`-torsion `G`-module as a `GalRep`, and its `μₙ`-dual as the Tate dual -/

section Module

variable (n : ℕ) [NeZero n] (K : IntermediateField ℚ_[2] ℚ̄₂)
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (GQ2.MuN n)] [ContinuousSMul G (GQ2.MuN n)]
  (e : G ≃ₜ* Field.absoluteGaloisGroup K)
  (he : ∀ (h : Field.absoluteGaloisGroup K) (x : GQ2.MuN n),
    muNEquiv n K (e.symm h • x) = (TauCeti.ClassFieldTheory.muNRep n K).ρ h (muNEquiv n K x))
  (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
  [Module (ZMod n) M] [DistribMulAction (Field.absoluteGaloisGroup K) M]
  [ContinuousSMul (Field.absoluteGaloisGroup K) M]
  (hact : ∀ (h : Field.absoluteGaloisGroup K) (m : M), h • m = e.symm h • m)

/-- **The coefficient object** attached to `M`: `ofDiscreteModule (ZMod n) G_K M` for the
`G_K`-action on `M` (in the assembly, the pullback of the `G`-action along `e.symm`). -/
abbrev galRep : TauCeti.ClassFieldTheory.GalRep n K :=
  TauCeti.ofDiscreteModule (ZMod n) (Field.absoluteGaloisGroup K) M

/-- `M` is the carrier of `galRep n K M`. -/
def galRepEquiv : M ≃+ (galRep n K M).V := AddEquiv.refl M

@[simp] theorem galRepEquiv_apply (m : M) : galRepEquiv n K M m = m := rfl

include hact in
/-- `galRepEquiv` is equivariant along `e.symm`: the compatibility hypothesis for Tau Ceti's
`explicitMap{0,1,2}`. -/
theorem galRepEquiv_smul (h : Field.absoluteGaloisGroup K) (m : M) :
    galRepEquiv n K M (e.symm h • m) = h • galRepEquiv n K M m :=
  -- `galRepEquiv` is the identity and `(galRep n K M).ρ h m = h • m` (`ofDiscreteModule_ρ_apply_apply`)
  ((TopRep.distribMulAction_smul (galRep n K M) h (galRepEquiv n K M m)).trans
    ((TauCeti.ofDiscreteModule_ρ_apply_apply (R := ZMod n) h m).trans (hact h m))).symm

/-- `Hom(M, μₙ(ℚ̄₂)) ≃+ Hom(M, μₙ(Kˢᵉᵖ))`, post-composition with `muNEquiv`, with the domain and
codomain spelled as gq2's `MuDual` and the carrier of `galRep n K M`. -/
def muDualHomEquiv :
    GQ2.MuDual n M ≃+ ((galRep n K M).V →+ (TauCeti.ClassFieldTheory.muNRep n K).V) :=
  AddEquiv.addMonoidHomCongrRight (muNEquiv n K)

@[simp] theorem muDualHomEquiv_apply (φ : GQ2.MuDual n M) (m : M) :
    muDualHomEquiv n K M φ (galRepEquiv n K M m) = muNEquiv n K (φ m) := rfl

/-- **gq2's `μₙ`-dual `Hom(M, μₙ(ℚ̄₂))` is Tau Ceti's Tate dual `Hom(M, μₙ(Kˢᵉᵖ))`**, through
`muNEquiv` on the values and `tateDualEquiv`. -/
def muDualEquiv : GQ2.MuDual n M ≃+ (TauCeti.ClassFieldTheory.tateDual (galRep n K M)).V :=
  (muDualHomEquiv n K M).trans (TauCeti.ClassFieldTheory.tateDualEquiv (galRep n K M)).symm

@[simp] theorem tateDualEquiv_muDualEquiv_apply (φ : GQ2.MuDual n M) (m : M) :
    TauCeti.ClassFieldTheory.tateDualEquiv (galRep n K M) (muDualEquiv n K M φ)
        (galRepEquiv n K M m) =
      muNEquiv n K (φ m) := by
  rw [muDualEquiv, AddEquiv.trans_apply, AddEquiv.apply_symm_apply, muDualHomEquiv_apply]

include he hact in
/-- **`muDualEquiv` is equivariant**: gq2's conjugation action `(g • φ) m = g • φ (g⁻¹ • m)` is
Tau Ceti's (`tateDualEquiv_ρ_apply`). -/
theorem muDualEquiv_smul (h : Field.absoluteGaloisGroup K) (φ : GQ2.MuDual n M) :
    muDualEquiv n K M (e.symm h • φ) = h • muDualEquiv n K M φ := by
  apply (TauCeti.ClassFieldTheory.tateDualEquiv (galRep n K M)).injective
  refine AddMonoidHom.ext fun (m : M) ↦ ?_
  -- `h⁻¹` acts on `m` through `e.symm`
  have hinv : (galRep n K M).ρ h⁻¹ (galRepEquiv n K M m) = galRepEquiv n K M ((e.symm h)⁻¹ • m) :=
    (TauCeti.ofDiscreteModule_ρ_apply_apply (R := ZMod n) h⁻¹ m).trans
      ((hact h⁻¹ m).trans (congrArg (· • m) (map_inv e.symm h)))
  calc TauCeti.ClassFieldTheory.tateDualEquiv (galRep n K M) (muDualEquiv n K M (e.symm h • φ))
        (galRepEquiv n K M m)
      = muNEquiv n K (e.symm h • φ ((e.symm h)⁻¹ • m)) :=
        tateDualEquiv_muDualEquiv_apply n K M (e.symm h • φ) m
    _ = (TauCeti.ClassFieldTheory.muNRep n K).ρ h (muNEquiv n K (φ ((e.symm h)⁻¹ • m))) := he h _
    _ = (TauCeti.ClassFieldTheory.muNRep n K).ρ h
          (TauCeti.ClassFieldTheory.tateDualEquiv (galRep n K M) (muDualEquiv n K M φ)
            ((galRep n K M).ρ h⁻¹ (galRepEquiv n K M m))) := by
        rw [hinv, tateDualEquiv_muDualEquiv_apply]
    _ = TauCeti.ClassFieldTheory.tateDualEquiv (galRep n K M)
          ((TauCeti.ClassFieldTheory.tateDual (galRep n K M)).ρ h (muDualEquiv n K M φ))
          (galRepEquiv n K M m) :=
        (TauCeti.ClassFieldTheory.tateDualEquiv_ρ_apply (galRep n K M) h _ _).symm
    _ = TauCeti.ClassFieldTheory.tateDualEquiv (galRep n K M) (h • muDualEquiv n K M φ)
          (galRepEquiv n K M m) := rfl

/-- The pairings match: gq2's evaluation pairing `muDualPairing`, read through `muNEquiv`, is
Tau Ceti's evaluation `tateDualEquiv`. -/
theorem muNEquiv_muDualPairing (φ : GQ2.MuDual n M) (m : M) :
    muNEquiv n K (GQ2.muDualPairing n M φ m) =
      (TauCeti.ClassFieldTheory.tateDualEquiv (galRep n K M)).toAddMonoidHom
        (muDualEquiv n K M φ) (galRepEquiv n K M m) := by
  rw [GQ2.muDualPairing_apply, AddEquiv.coe_toAddMonoidHom, tateDualEquiv_muDualEquiv_apply]

/-- `tateDualEquiv` is the bilinear map of Tau Ceti's `tateEvaluationPairing`. -/
theorem tateDualEquiv_eq_bil (φ : (TauCeti.ClassFieldTheory.tateDual (galRep n K M)).V)
    (a : (galRep n K M).V) :
    (TauCeti.ClassFieldTheory.tateDualEquiv (galRep n K M)).toAddMonoidHom φ a =
      (TauCeti.ClassFieldTheory.tateEvaluationPairing (galRep n K M)).bil φ a :=
  (TauCeti.ClassFieldTheory.tateEvaluationPairing_bil (galRep n K M) φ a).symm

/-- `tateDualEquiv`, as a biadditive map, is `G_K`-equivariant (the `hequiv'` of Tau Ceti's cup
naturality theorems). -/
theorem tateDualEquiv_equivariant (h : Field.absoluteGaloisGroup K)
    (φ : (TauCeti.ClassFieldTheory.tateDual (galRep n K M)).V) (a : (galRep n K M).V) :
    (TauCeti.ClassFieldTheory.tateDualEquiv (galRep n K M)).toAddMonoidHom (h • φ) (h • a) =
      h • (TauCeti.ClassFieldTheory.tateDualEquiv (galRep n K M)).toAddMonoidHom φ a :=
  TauCeti.TopPairing.equivariant_of_eq _ _ (tateDualEquiv_eq_bil n K M) h φ a

/-! #### The transported classes -/

/-- gq2's `H⁰(G, Hom(M, μₙ))` as `continuousCohomology 0 (tateDual (galRep n K M))`. -/
def dualTransport0 :
    GQ2.ContCoh.H0 G (GQ2.MuDual n M) ≃+
      continuousCohomology 0 (TauCeti.ClassFieldTheory.tateDual (galRep n K M)) :=
  transport0 n K e _ (muDualEquiv n K M) (muDualEquiv_smul n K e he M hact)

/-- gq2's `H¹(G, Hom(M, μₙ))` as `continuousCohomology 1 (tateDual (galRep n K M))`. -/
def dualTransport1 :
    GQ2.ContCoh.H1 G (GQ2.MuDual n M) ≃+
      continuousCohomology 1 (TauCeti.ClassFieldTheory.tateDual (galRep n K M)) :=
  transport1 n K e _ (muDualEquiv n K M) (muDualEquiv_smul n K e he M hact)

/-- gq2's `H²(G, Hom(M, μₙ))` as `continuousCohomology 2 (tateDual (galRep n K M))`. -/
def dualTransport2 :
    GQ2.ContCoh.H2 G (GQ2.MuDual n M) ≃+
      continuousCohomology 2 (TauCeti.ClassFieldTheory.tateDual (galRep n K M)) :=
  transport2 n K e _ (muDualEquiv n K M) (muDualEquiv_smul n K e he M hact)

/-- gq2's `H⁰(G, M)` as `continuousCohomology 0 (galRep n K M)`. -/
def modTransport0 : GQ2.ContCoh.H0 G M ≃+ continuousCohomology 0 (galRep n K M) :=
  transport0 n K e _ (galRepEquiv n K M) (galRepEquiv_smul n K e M hact)

/-- gq2's `H¹(G, M)` as `continuousCohomology 1 (galRep n K M)`. -/
def modTransport1 : GQ2.ContCoh.H1 G M ≃+ continuousCohomology 1 (galRep n K M) :=
  transport1 n K e _ (galRepEquiv n K M) (galRepEquiv_smul n K e M hact)

/-- gq2's `H²(G, M)` as `continuousCohomology 2 (galRep n K M)`. -/
def modTransport2 : GQ2.ContCoh.H2 G M ≃+ continuousCohomology 2 (galRep n K M) :=
  transport2 n K e _ (galRepEquiv n K M) (galRepEquiv_smul n K e M hact)

/-! #### The pairings agree -/

variable (tr : continuousCohomology 2 (TauCeti.ClassFieldTheory.muNRep n K) ≃+ ZMod n)

/-- **Bidegree `(1,1)`**: Tau Ceti's Tate pairing of the transported classes is the transported
gq2 cup pairing, read through `tr`.  (Assembled as a term, as in Tau Ceti's
`Local/Duality/Explicit.lean`: `rw` with the comparison isomorphisms makes the motive check
unfold the cohomology groups and time out.) -/
theorem tatePairing_transport11 (x : GQ2.ContCoh.H1 G (GQ2.MuDual n M)) (y : GQ2.ContCoh.H1 G M) :
    TauCeti.ClassFieldTheory.tateDualityPairing (galRep n K M) tr 1 1 rfl
        (dualTransport1 n K e he M hact x) (modTransport1 n K e M hact y) =
      invEquiv n K e he tr
        (GQ2.ContCoh.cup11 (GQ2.muDualPairing n M) (GQ2.muDualPairing_equivariant n M) x y) := by
  refine (TauCeti.ClassFieldTheory.tateDualityPairing_def (galRep n K M) tr 1 1 rfl _ _).trans
    (Eq.trans (congrArg tr ?_) (invEquiv_apply n K e he tr _).symm)
  -- `rfl ▸ ·` is the identity; unfold the two degree-one transports
  refine (congrArg₂ (fun a b ↦ (TauCeti.ClassFieldTheory.tateEvaluationPairing (galRep n K M)).cup
    1 1 a b) (transport1_apply n K e _ (muDualEquiv n K M) (muDualEquiv_smul n K e he M hact) x)
    (transport1_apply n K e _ (galRepEquiv n K M) (galRepEquiv_smul n K e M hact) y)).trans ?_
  -- the canonical cup of the pairing is the explicit cup of `tateDualEquiv`
  refine (TauCeti.TopPairing.cup_one_one_explicitH1AddEquivContinuousCohomologyOfDiscrete _ _
    (tateDualEquiv_eq_bil n K M) _ _).trans ?_
  -- naturality of the explicit cup along `e.symm` and the coefficient identifications
  refine (congrArg (TauCeti.ClassFieldTheory.muNRep n K).explicitH2AddEquivContinuousCohomologyOfDiscrete
    (TauCeti.ContCohomology.explicitMap2_explicitCup11 (G := G) (M := GQ2.MuDual n M) (N := M)
      (P := GQ2.MuN n) (μ := GQ2.muDualPairing n M) (hμ := continuous_of_discreteTopology)
      (hequiv := GQ2.muDualPairing_equivariant n M) (H := Field.absoluteGaloisGroup K)
      (M' := (TauCeti.ClassFieldTheory.tateDual (galRep n K M)).V) (N' := (galRep n K M).V)
      (P' := (TauCeti.ClassFieldTheory.muNRep n K).V)
      (μ' := (TauCeti.ClassFieldTheory.tateDualEquiv (galRep n K M)).toAddMonoidHom)
      (hμ' := continuous_of_discreteTopology) (hequiv' := tateDualEquiv_equivariant n K M)
      (φ := e.symm) (fM := (muDualEquiv n K M).toAddMonoidHom)
      (fN := (galRepEquiv n K M).toAddMonoidHom) (fP := (muNEquiv n K).toAddMonoidHom)
      (hcM := continuous_of_discreteTopology) (hcN := continuous_of_discreteTopology)
      (hcP := continuous_of_discreteTopology)
      (hfM := muDualEquiv_smul n K e he M hact) (hfN := galRepEquiv_smul n K e M hact)
      (hfP := muNEquiv_smul_of n K e he) (hpair := muNEquiv_muDualPairing n K M)
      (a := h1Equiv G (GQ2.MuDual n M) x) (b := h1Equiv G M y)).symm).trans ?_
  -- A2's cup dictionary, then fold the degree-two transport
  exact (congrArg (fun z ↦
      (TauCeti.ClassFieldTheory.muNRep n K).explicitH2AddEquivContinuousCohomologyOfDiscrete
        (TauCeti.ContCohomology.explicitMap2 G (GQ2.MuN n) (Field.absoluteGaloisGroup K)
          (TauCeti.ClassFieldTheory.muNRep n K).V e.symm (muNEquiv n K).toAddMonoidHom
          continuous_of_discreteTopology (muNEquiv_smul_of n K e he) z))
    (h2Equiv_cup11 (GQ2.muDualPairing n M) (GQ2.muDualPairing_equivariant n M) x y).symm).trans
    (transport2_apply n K e _ (muNEquiv n K) (muNEquiv_smul_of n K e he) _).symm

/-- **Bidegree `(0,2)`**. -/
theorem tatePairing_transport02 (m : GQ2.ContCoh.H0 G (GQ2.MuDual n M)) (y : GQ2.ContCoh.H2 G M) :
    TauCeti.ClassFieldTheory.tateDualityPairing (galRep n K M) tr 0 2 rfl
        (dualTransport0 n K e he M hact m) (modTransport2 n K e M hact y) =
      invEquiv n K e he tr
        (GQ2.ContCoh.cup02 (GQ2.muDualPairing n M) (GQ2.muDualPairing_equivariant n M) m y) := by
  refine (TauCeti.ClassFieldTheory.tateDualityPairing_def (galRep n K M) tr 0 2 rfl _ _).trans
    (Eq.trans (congrArg tr ?_) (invEquiv_apply n K e he tr _).symm)
  -- unfold the two transports; in degree two also the discrete comparison
  refine (congrArg₂ (fun a b ↦ (TauCeti.ClassFieldTheory.tateEvaluationPairing (galRep n K M)).cup
    0 2 a b) (transport0_apply n K e _ (muDualEquiv n K M) (muDualEquiv_smul n K e he M hact) m)
    ((transport2_apply n K e _ (galRepEquiv n K M) (galRepEquiv_smul n K e M hact) y).trans
      (TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete_apply (galRep n K M) _))).trans ?_
  -- the canonical cup over `ZMod n` is the cup of the `ℤ`-pairing of `tateDualEquiv`
  refine (TauCeti.TopPairing.cup_zero_two_ofDiscreteModuleRestrictScalarsInt _ _
    (tateDualEquiv_eq_bil n K M) _ _).symm.trans ?_
  -- which is the explicit cup
  refine (congrArg (TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv
    (TauCeti.ClassFieldTheory.muNRep n K) (0 + 2))
    (TauCeti.ContCohomology.explicitAddEquiv_cup02 (Field.absoluteGaloisGroup K) _ _ _
      (TauCeti.ClassFieldTheory.tateDualEquiv (galRep n K M)).toAddMonoidHom
      (tateDualEquiv_equivariant n K M) _ _)).trans ?_
  -- naturality of the explicit cup along `e.symm` and the coefficient identifications
  refine (congrArg (fun z ↦ TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv
      (TauCeti.ClassFieldTheory.muNRep n K) (0 + 2)
      (TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology (Field.absoluteGaloisGroup K)
        (TauCeti.ClassFieldTheory.muNRep n K).V z))
    (TauCeti.ContCohomology.explicitMap2_explicitCup02 (G := G) (M := GQ2.MuDual n M) (N := M)
      (P := GQ2.MuN n) (μ := GQ2.muDualPairing n M) (hμ := continuous_of_discreteTopology)
      (hequiv := GQ2.muDualPairing_equivariant n M) (H := Field.absoluteGaloisGroup K)
      (M' := (TauCeti.ClassFieldTheory.tateDual (galRep n K M)).V) (N' := (galRep n K M).V)
      (P' := (TauCeti.ClassFieldTheory.muNRep n K).V)
      (μ' := (TauCeti.ClassFieldTheory.tateDualEquiv (galRep n K M)).toAddMonoidHom)
      (hμ' := continuous_of_discreteTopology) (hequiv' := tateDualEquiv_equivariant n K M)
      (φ := e.symm) (fM := (muDualEquiv n K M).toAddMonoidHom)
      (fN := (galRepEquiv n K M).toAddMonoidHom) (fP := (muNEquiv n K).toAddMonoidHom)
      (hcN := continuous_of_discreteTopology) (hcP := continuous_of_discreteTopology)
      (hfM := muDualEquiv_smul n K e he M hact) (hfN := galRepEquiv_smul n K e M hact)
      (hfP := muNEquiv_smul_of n K e he) (hpair := muNEquiv_muDualPairing n K M)
      (m := m) (b := h2Equiv G M y)).symm).trans ?_
  -- A2's cup dictionary, then fold the degree-two transport
  exact (congrArg (fun z ↦ TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv
      (TauCeti.ClassFieldTheory.muNRep n K) (0 + 2)
      (TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology (Field.absoluteGaloisGroup K)
        (TauCeti.ClassFieldTheory.muNRep n K).V
        (TauCeti.ContCohomology.explicitMap2 G (GQ2.MuN n) (Field.absoluteGaloisGroup K)
          (TauCeti.ClassFieldTheory.muNRep n K).V e.symm (muNEquiv n K).toAddMonoidHom
          continuous_of_discreteTopology (muNEquiv_smul_of n K e he) z)))
    (h2Equiv_cup02 (GQ2.muDualPairing n M) (GQ2.muDualPairing_equivariant n M) m y).symm).trans
    ((transport2_apply n K e _ (muNEquiv n K) (muNEquiv_smul_of n K e he) _).trans
      (TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete_apply
        (TauCeti.ClassFieldTheory.muNRep n K) _)).symm

/-- **Bidegree `(2,0)`**. -/
theorem tatePairing_transport20 (x : GQ2.ContCoh.H2 G (GQ2.MuDual n M)) (m : GQ2.ContCoh.H0 G M) :
    TauCeti.ClassFieldTheory.tateDualityPairing (galRep n K M) tr 2 0 rfl
        (dualTransport2 n K e he M hact x) (modTransport0 n K e M hact m) =
      invEquiv n K e he tr
        (GQ2.ContCoh.cup20 (GQ2.muDualPairing n M) (GQ2.muDualPairing_equivariant n M) x m) := by
  refine (TauCeti.ClassFieldTheory.tateDualityPairing_def (galRep n K M) tr 2 0 rfl _ _).trans
    (Eq.trans (congrArg tr ?_) (invEquiv_apply n K e he tr _).symm)
  refine (congrArg₂ (fun a b ↦ (TauCeti.ClassFieldTheory.tateEvaluationPairing (galRep n K M)).cup
    2 0 a b)
    ((transport2_apply n K e _ (muDualEquiv n K M) (muDualEquiv_smul n K e he M hact) x).trans
      (TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete_apply
        (TauCeti.ClassFieldTheory.tateDual (galRep n K M)) _))
    (transport0_apply n K e _ (galRepEquiv n K M) (galRepEquiv_smul n K e M hact) m)).trans ?_
  refine (TauCeti.TopPairing.cup_two_zero_ofDiscreteModuleRestrictScalarsInt _ _
    (tateDualEquiv_eq_bil n K M) _ _).symm.trans ?_
  refine (congrArg (TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv
    (TauCeti.ClassFieldTheory.muNRep n K) (2 + 0))
    (TauCeti.ContCohomology.explicitAddEquiv_cup20 (Field.absoluteGaloisGroup K) _ _ _
      (TauCeti.ClassFieldTheory.tateDualEquiv (galRep n K M)).toAddMonoidHom
      (tateDualEquiv_equivariant n K M) _ _)).trans ?_
  refine (congrArg (fun z ↦ TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv
      (TauCeti.ClassFieldTheory.muNRep n K) (2 + 0)
      (TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology (Field.absoluteGaloisGroup K)
        (TauCeti.ClassFieldTheory.muNRep n K).V z))
    (TauCeti.ContCohomology.explicitMap2_explicitCup20 (G := G) (M := GQ2.MuDual n M) (N := M)
      (P := GQ2.MuN n) (μ := GQ2.muDualPairing n M) (hμ := continuous_of_discreteTopology)
      (hequiv := GQ2.muDualPairing_equivariant n M) (H := Field.absoluteGaloisGroup K)
      (M' := (TauCeti.ClassFieldTheory.tateDual (galRep n K M)).V) (N' := (galRep n K M).V)
      (P' := (TauCeti.ClassFieldTheory.muNRep n K).V)
      (μ' := (TauCeti.ClassFieldTheory.tateDualEquiv (galRep n K M)).toAddMonoidHom)
      (hμ' := continuous_of_discreteTopology) (hequiv' := tateDualEquiv_equivariant n K M)
      (φ := e.symm) (fM := (muDualEquiv n K M).toAddMonoidHom)
      (fN := (galRepEquiv n K M).toAddMonoidHom) (fP := (muNEquiv n K).toAddMonoidHom)
      (hcM := continuous_of_discreteTopology) (hcP := continuous_of_discreteTopology)
      (hfM := muDualEquiv_smul n K e he M hact) (hfN := galRepEquiv_smul n K e M hact)
      (hfP := muNEquiv_smul_of n K e he) (hpair := muNEquiv_muDualPairing n K M)
      (a := h2Equiv G (GQ2.MuDual n M) x) (n := m)).symm).trans ?_
  exact (congrArg (fun z ↦ TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv
      (TauCeti.ClassFieldTheory.muNRep n K) (2 + 0)
      (TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology (Field.absoluteGaloisGroup K)
        (TauCeti.ClassFieldTheory.muNRep n K).V
        (TauCeti.ContCohomology.explicitMap2 G (GQ2.MuN n) (Field.absoluteGaloisGroup K)
          (TauCeti.ClassFieldTheory.muNRep n K).V e.symm (muNEquiv n K).toAddMonoidHom
          continuous_of_discreteTopology (muNEquiv_smul_of n K e he) z)))
    (h2Equiv_cup20 (GQ2.muDualPairing n M) (GQ2.muDualPairing_equivariant n M) x m).symm).trans
    ((transport2_apply n K e _ (muNEquiv n K) (muNEquiv_smul_of n K e he) _).trans
      (TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete_apply
        (TauCeti.ClassFieldTheory.muNRep n K) _)).symm

/-! #### Perfectness transfers -/

include hact in
/-- **`(1,1)`**: gq2's perfectness clause from Tau Ceti's two-clause perfectness at
`galRep n K M`. -/
theorem perfect11_of_perfect
    (hperf : (∀ x, (∀ y, TauCeti.ClassFieldTheory.tateDualityPairing (galRep n K M) tr 1 1 rfl x y
        = 0) → x = 0) ∧
      ∀ φ : continuousCohomology 1 (galRep n K M) →+ ZMod n,
        ∃ x, ∀ y, TauCeti.ClassFieldTheory.tateDualityPairing (galRep n K M) tr 1 1 rfl x y = φ y) :
    Function.Bijective fun c : GQ2.ContCoh.H1 G (GQ2.MuDual n M) ↦
      (invEquiv n K e he tr).toAddMonoidHom.comp
        (GQ2.ContCoh.cup11 (GQ2.muDualPairing n M) (GQ2.muDualPairing_equivariant n M) c) :=
  bijective_of_comm _ (dualTransport1 n K e he M hact) (modTransport1 n K e M hact)
    (tatePairingHom (galRep n K M) tr 1 1 rfl) (bijective_of_perfect _ hperf)
    fun x y ↦ (tatePairing_transport11 n K e he M hact tr x y).symm

include hact in
/-- **`(0,2)`**. -/
theorem perfect02_of_perfect
    (hperf : (∀ x, (∀ y, TauCeti.ClassFieldTheory.tateDualityPairing (galRep n K M) tr 0 2 rfl x y
        = 0) → x = 0) ∧
      ∀ φ : continuousCohomology 2 (galRep n K M) →+ ZMod n,
        ∃ x, ∀ y, TauCeti.ClassFieldTheory.tateDualityPairing (galRep n K M) tr 0 2 rfl x y = φ y) :
    Function.Bijective fun c : GQ2.ContCoh.H0 G (GQ2.MuDual n M) ↦
      (invEquiv n K e he tr).toAddMonoidHom.comp
        (GQ2.ContCoh.cup02 (GQ2.muDualPairing n M) (GQ2.muDualPairing_equivariant n M) c) :=
  bijective_of_comm _ (dualTransport0 n K e he M hact) (modTransport2 n K e M hact)
    (tatePairingHom (galRep n K M) tr 0 2 rfl) (bijective_of_perfect _ hperf)
    fun x y ↦ (tatePairing_transport02 n K e he M hact tr x y).symm

include hact in
/-- **`(2,0)`**. -/
theorem perfect20_of_perfect
    (hperf : (∀ x, (∀ y, TauCeti.ClassFieldTheory.tateDualityPairing (galRep n K M) tr 2 0 rfl x y
        = 0) → x = 0) ∧
      ∀ φ : continuousCohomology 0 (galRep n K M) →+ ZMod n,
        ∃ x, ∀ y, TauCeti.ClassFieldTheory.tateDualityPairing (galRep n K M) tr 2 0 rfl x y = φ y) :
    Function.Bijective fun c : GQ2.ContCoh.H2 G (GQ2.MuDual n M) ↦
      (invEquiv n K e he tr).toAddMonoidHom.comp
        (GQ2.ContCoh.cup20 (GQ2.muDualPairing n M) (GQ2.muDualPairing_equivariant n M) c) :=
  bijective_of_comm _ (dualTransport2 n K e he M hact) (modTransport0 n K e M hact)
    (tatePairingHom (galRep n K M) tr 2 0 rfl) (bijective_of_perfect _ hperf)
    fun x y ↦ (tatePairing_transport20 n K e he M hact tr x y).symm

end Module

/-! ### Assembly -/

section Assembly

variable (n : ℕ) [NeZero n] (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (GQ2.MuN n)] [ContinuousSMul G (GQ2.MuN n)]
  (e : G ≃ₜ* Field.absoluteGaloisGroup K)
  (he : ∀ (h : Field.absoluteGaloisGroup K) (x : GQ2.MuN n),
    muNEquiv n K (e.symm h • x) = (TauCeti.ClassFieldTheory.muNRep n K).ρ h (muNEquiv n K x))

/-- Tau Ceti's invariant `H²(G_K, μₙ(Kˢᵉᵖ)) ≃+ ℤ/n`, with Tau Ceti's local-field package on
`↥K` installed locally (`h2MuEquivZMod_mixed`; any such equivalence serves). -/
def tauCetiInv : continuousCohomology 2 (TauCeti.ClassFieldTheory.muNRep n K) ≃+ ZMod n :=
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  (TauCeti.ClassFieldTheory.h2MuEquivZMod_mixed K n (NeZero.ne n)).some

/-- Tau Ceti's perfectness at `galRep n K M`, for a `G_K`-module structure on `M` given as
instances, with the local-field package on `↥K` installed locally. -/
theorem perfect_galRep (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [Finite M] [Module (ZMod n) M] [DistribMulAction (Field.absoluteGaloisGroup K) M]
    [ContinuousSMul (Field.absoluteGaloisGroup K) M] (i j : ℕ) (hij : i + j = 2) :
    (∀ x, (∀ y, TauCeti.ClassFieldTheory.tateDualityPairing (galRep n K M) (tauCetiInv n K) i j hij
        x y = 0) → x = 0) ∧
      ∀ φ : continuousCohomology j (galRep n K M) →+ ZMod n,
        ∃ x, ∀ y, TauCeti.ClassFieldTheory.tateDualityPairing (galRep n K M) (tauCetiInv n K) i j
          hij x y = φ y :=
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  @TauCeti.ClassFieldTheory.tateDualityPairing_perfect_mixed K _ _ _ _ (isNonarchimedeanLocalField K)
    n (NeZero.ne n) (galRep n K M) (tauCetiInv n K) inferInstance _ _ i j hij

/-- **The duality bundle for `G ≃ₜ* G_K`**, `K/ℚ₂` finite, with `e` compatible with the actions on
`μₙ`. -/
def tateDualityOfEquiv : GQ2.TateDualityG G n where
  inv := invEquiv n K e he (tauCetiInv n K)
  perfect02 M _ _ _ _ _ _ htor := by
    let _ : Module (ZMod n) M := AddCommGroup.zmodModule htor
    let _ : DistribMulAction (Field.absoluteGaloisGroup K) M :=
      DistribMulAction.compHom M (e.symm : Field.absoluteGaloisGroup K →* G)
    have _ : ContinuousSMul (Field.absoluteGaloisGroup K) M :=
      MulAction.continuousSMul_compHom e.symm.continuous
    exact perfect02_of_perfect n K e he M (fun _ _ ↦ rfl) (tauCetiInv n K)
      (perfect_galRep n K M 0 2 rfl)
  perfect11 M _ _ _ _ _ _ htor := by
    let _ : Module (ZMod n) M := AddCommGroup.zmodModule htor
    let _ : DistribMulAction (Field.absoluteGaloisGroup K) M :=
      DistribMulAction.compHom M (e.symm : Field.absoluteGaloisGroup K →* G)
    have _ : ContinuousSMul (Field.absoluteGaloisGroup K) M :=
      MulAction.continuousSMul_compHom e.symm.continuous
    exact perfect11_of_perfect n K e he M (fun _ _ ↦ rfl) (tauCetiInv n K)
      (perfect_galRep n K M 1 1 rfl)
  perfect20 M _ _ _ _ _ _ htor := by
    let _ : Module (ZMod n) M := AddCommGroup.zmodModule htor
    let _ : DistribMulAction (Field.absoluteGaloisGroup K) M :=
      DistribMulAction.compHom M (e.symm : Field.absoluteGaloisGroup K →* G)
    have _ : ContinuousSMul (Field.absoluteGaloisGroup K) M :=
      MulAction.continuousSMul_compHom e.symm.continuous
    exact perfect20_of_perfect n K e he M (fun _ _ ↦ rfl) (tauCetiInv n K)
      (perfect_galRep n K M 2 0 rfl)

end Assembly

/-- **B6 (local Tate duality at every finite `k/ℚ₂`), from Tau Ceti.**  The type is that of the
field `GQ2.LiteratureInputs.tateDualityAt`: for a local dualizing group `G` (an open embedding
`ι : G →* G_ℚ₂` compatible with the action on `μₙ`), the bundle `GQ2.TateDualityG G n`.  `G` is
identified with `Field.absoluteGaloisGroup K` for `K = dualizingField ι` (finite over `ℚ₂`), and
the bundle is `tateDualityOfEquiv` there. -/
def tateDualityAt_tauceti (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) [NeZero n] [DistribMulAction G (MuN n)] [ContinuousSMul G (MuN n)]
    (hloc : IsLocalDualizingGroup G n) : TateDualityG G n :=
  haveI := finiteDimensional_dualizingField hloc.choose hloc.choose_spec.1
  tateDualityOfEquiv n (dualizingField hloc.choose)
    (dualizingEquiv hloc.choose hloc.choose_spec.1)
    (muNEquiv_dualizingEquiv_symm_smul n hloc.choose hloc.choose_spec.1 hloc.choose_spec.2.2)

end GQ2.TauCetiBridge
