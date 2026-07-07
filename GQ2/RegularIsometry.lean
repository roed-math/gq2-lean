/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GQ2.KappaNormalForm
import GQ2.OrbitDecomp

/-!
# P-15f2b: the isometric regular embedding

The `C`-equivariant **split embedding** of a ramified simple faithful quadratic `𝔽₂[C]`-module
`(V, q)` into a regular module `W = PermW C N = 𝔽₂[C]^N`, carrying the pulled-back form
`Q_W := q ∘ r` (`r` the equivariant retraction) together with an equivariant factor-set datum
for it.  This upgrades `RegularSummand.lemma_6_11` (a pure module embedding) to an **isometry**
`Q_W ∘ ι = q`, and supplies an equivariant `FactorSet` on `W` — the datum-side input of the §6.2
orbit route to `SectionSix.lemma_6_17_vanish`.

## What `regular_isometric_embedding` delivers

From `lemma_6_11` we obtain `N`, the equivariant embedding `ι : V →+ W`, the equivariant
retraction `r : W →+ V`, and `r ∘ ι = id`.  Setting `Q_W := q ∘ r`:

* the **isometry** `Q_W (ι v) = q v` is immediate from `r (ι v) = v`;
* `Q_W` is `C`-invariant and `𝔽₂`-quadratic (`r` additive + equivariant, `q` invariant/quadratic);
* `exists_datum_of_invariant_quadratic` (the permutation-module normal form) supplies an
  equivariant factor-set datum `datW` for `Q_W`.

The two equivariances are re-expressed in the `PermW` `DistribMulAction` form
`ι (h • v) = h • ι v` and `r (h • F) = h • r F` — the shape `RepIndependence.lemma_6_14` consumes.

This mirrors the ramified branch of `KappaNormalForm.kappa0_exists_tame`, but **exposes** `ι`, `r`,
`datW` and the isometry instead of immediately collapsing them to `∃ dat, IsEquivariantFactorSet q
dat` on `V`.  The exposed package is what the §6.3 orbit computation (Lemmas 6.14–6.17) transports
through.

## Relation to the full f2b interface / the remaining core

The full f2b deliverable additionally asks for `datW = sumDatum (orbit datums)` — the §6.2
**orbit decomposition** of `Q_W` into square/free/involution orbit polynomials ((75)/(76)/Lemma
6.2), whose per-orbit equivariance is banked (`isEquivariantFactorSet_{square,free,inv}OrbitDatum`
in `SectionNine`/`InvolutionDatum`).  The banked normal form `exists_datum_of_invariant_quadratic`
deliberately takes the *single* invariant-biadditive `β`-refinement route
(`docs/p17e-kappa0-scoping.md`), so it produces `datW` but **not** its orbit-sum form; recovering
the latter is the remaining combinatorial core of the orbit route.  This file delivers the
datum-independent isometric-embedding infrastructure that either route (the orbit route or the
flagged `β`-route of `docs/p15f2-subtickets.md`) consumes.

No axioms; `Ax = ∅` (std-3 throughout, inheriting `lemma_6_11`'s `sorry`-free status).
-/

namespace GQ2

open QuadraticFp2

/-- **The isometric regular embedding** (P-15f2b, P1 + the β-datum): a ramified simple faithful
2-torsion quadratic `𝔽₂[C]`-module `(V, q)` embeds `C`-equivariantly as a split summand of a
regular module `W = 𝔽₂[C]^N`, carrying the pulled-back form `Q_W := q ∘ r` and an equivariant
factor-set datum for it, so that `ι` is an **isometry** `Q_W (ι v) = q v`.

Everything is extracted from `lemma_6_11`'s module split (equivariance, retraction) plus the
permutation-module normal form `exists_datum_of_invariant_quadratic`; the isometry is free from
`r (ι v) = v`. -/
theorem regular_isometric_embedding {C : Type} [Group C] [TopologicalSpace C] [Finite C]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    (c : ContinuousMonoidHom Ttame C)
    (hgen : Subgroup.closure {c tameSigma, c tameTau} = ⊤)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hinv : IsInvariant C q)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v) :
    ∃ (N : ℕ) (ι : V →+ PermW C N) (r : PermW C N →+ V) (datW : FactorSet C (PermW C N)),
      IsEquivariantFactorSet (fun F => q (r F)) datW ∧
      (∀ v : V, q (r (ι v)) = q v) ∧
      (∀ (h : C) (v : V), ι (h • v) = h • ι v) ∧
      (∀ (h : C) (F : PermW C N), r (h • F) = h • r F) ∧
      (∀ v : V, r (ι v) = v) := by
  obtain ⟨N, ι, r, hι, hr, hri⟩ := lemma_6_11 c hgen hV2 hfaith hsimple hram
  -- recast the two equivariances into the `PermW` `DistribMulAction` form
  have hιsmul : ∀ (h : C) (v : V), ι (h • v) = h • ι v := by
    intro h v
    funext n x
    rw [hι h v n x]
    rfl
  have hrsmul : ∀ (h : C) (F : PermW C N), r (h • F) = h • r F := by
    intro h F
    show r (fun n x => F n (h⁻¹ * x)) = h • r F
    exact hr h F
  -- the pulled-back form `Q_W = q ∘ r`
  set qW : PermW C N → ZMod 2 := fun F => q (r F) with hqW
  have hqWquad : IsQuadraticFp2 qW := by
    constructor
    · show q (r 0) = 0
      rw [map_zero, hq.map_zero]
    · intro a b d
      show polar _ _ _ = polar _ _ _ + polar _ _ _
      simp only [hqW, polar, map_add]
      exact hq.polar_add_left (r a) (r b) (r d)
    · intro a b d
      show polar _ _ _ = polar _ _ _ + polar _ _ _
      simp only [hqW, polar, map_add]
      exact hq.polar_add_right (r a) (r b) (r d)
  have hqWinv : IsInvariant C qW := by
    intro cc F
    simp only [hqW]
    rw [hrsmul cc F]
    exact hinv cc (r F)
  obtain ⟨datW, hdatW⟩ := exists_datum_of_invariant_quadratic qW hqWquad hqWinv
  rw [hqW] at hdatW
  exact ⟨N, ι, r, datW, hdatW, fun v => by rw [hri v], hιsmul, hrsmul, hri⟩

/-! ## P-15f2b capstone: the orbit-sum isometric embedding

Reindex the foundation's regular summand `𝔽₂[C]` to `RegRep N` along `e : C ≃* G ⧸ N`, then
apply the §6.2 orbit decomposition (`OrbitDecomp.isEquivariantFactorSet_orbitSumDatum`) to the
pulled-back form.  The `C ≅ AbsGalQ2 ⧸ ker ρ` instantiation of `e` stays with f2c/f2d. -/

section OrbitCapstone

open OrbitVanish (sumDatum)

variable {C : Type} [Group C]
variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

/-- Reindex a single regular summand `𝔽₂[C]` to `RegRep N` along `e : C ≃* G ⧸ N`. -/
def reSummand (e : C ≃* G ⧸ N) : (C → ZMod 2) ≃+ RegRep N where
  toFun f := fun h => f (e.symm h)
  invFun g := fun c => g (e c)
  left_inv f := by funext c; show f (e.symm (e c)) = f c; rw [MulEquiv.symm_apply_apply]
  right_inv g := by funext h; show g (e (e.symm h)) = g h; rw [MulEquiv.apply_symm_apply]
  map_add' _ _ := rfl

theorem reSummand_smul (e : C ≃* G ⧸ N) (c : C) (f : C → ZMod 2) :
    reSummand N e (fun x => f (c⁻¹ * x)) = e c • reSummand N e f := by
  funext h
  show f (c⁻¹ * e.symm h) = reSummand N e f ((e c)⁻¹ * h)
  show f (c⁻¹ * e.symm h) = f (e.symm ((e c)⁻¹ * h))
  rw [map_mul, map_inv, MulEquiv.symm_apply_apply]

/-- The blockwise reindex `𝔽₂[C]^K ≃+ (Fin K → RegRep N)`. -/
def reBlock (e : C ≃* G ⧸ N) (K : ℕ) : (Fin K → C → ZMod 2) ≃+ (Fin K → RegRep N) :=
  AddEquiv.piCongrRight (fun _ => reSummand N e)

theorem reBlock_apply (e : C ≃* G ⧸ N) {K : ℕ} (F : Fin K → C → ZMod 2) (k : Fin K) :
    reBlock N e K F k = reSummand N e (F k) := rfl

theorem reBlock_smul (e : C ≃* G ⧸ N) {K : ℕ} (c : C) (F : PermW C K) :
    reBlock N e K (c • F) = e c • reBlock N e K F := by
  funext k
  show reSummand N e (fun x => F k (c⁻¹ * x)) = e c • reBlock N e K F k
  rw [reBlock_apply, reSummand_smul]

theorem reBlock_symm_smul (e : C ≃* G ⧸ N) {K : ℕ} (d : G ⧸ N) (Y : Fin K → RegRep N) :
    (reBlock N e K).symm (d • Y) = e.symm d • (reBlock N e K).symm Y := by
  apply (reBlock N e K).injective
  rw [AddEquiv.apply_symm_apply, reBlock_smul, AddEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]

/-- **The orbit-sum isometric embedding** (P-15f2b): a ramified simple faithful quadratic
`𝔽₂[C]`-module `(V, q)` embeds `C`-equivariantly (through `e : C ≃* G ⧸ N`) as a split summand of
`Fin K → RegRep N`, carrying the pulled-back form `Q_W := q ∘ r` together with the **§6.2
orbit-sum datum** `sumDatum (orbitIndexSet Q_W) orbitDatum` for it, an isometry.  This is the full
P-15f2b interface with `datW` *definitionally* the orbit sum — the shape
`OrbitVanish.Q0loc_vanish_of_datum_decomp` consumes. -/
theorem regular_isometric_embedding_orbit
    [TopologicalSpace C] [Finite C] [Fintype (G ⧸ N)]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    (e : C ≃* G ⧸ N)
    (cT : ContinuousMonoidHom Ttame C)
    (hgen : Subgroup.closure {cT tameSigma, cT tameTau} = ⊤)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hinv : IsInvariant C q)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, cT tameTau • v ≠ v) :
    ∃ (K : ℕ) (ι : V →+ (Fin K → RegRep N)) (r : (Fin K → RegRep N) →+ V),
      IsEquivariantFactorSet (fun F => q (r F))
        (sumDatum (orbitIndexSet N (fun F => q (r F))) (orbitDatum N)) ∧
      (∀ v : V, q (r (ι v)) = q v) ∧
      (∀ (a : C) (v : V), ι (a • v) = e a • ι v) ∧
      (∀ v : V, r (ι v) = v) := by
  haveI : Finite (G ⧸ N) := Finite.of_fintype _
  obtain ⟨K, ι₀, r₀, _, _, _, hιsmul, hrsmul, hri⟩ :=
    regular_isometric_embedding cT hgen q hq hinv hV2 hfaith hsimple hram
  set ι : V →+ (Fin K → RegRep N) := (reBlock N e K).toAddMonoidHom.comp ι₀ with hι
  set r : (Fin K → RegRep N) →+ V := r₀.comp (reBlock N e K).symm.toAddMonoidHom with hr
  -- retraction
  have hretr : ∀ v : V, r (ι v) = v := by
    intro v
    show r₀ ((reBlock N e K).symm (reBlock N e K (ι₀ v))) = v
    rw [AddEquiv.symm_apply_apply, hri]
  -- equivariance of `r` in the `G ⧸ N` action
  have hrsmul' : ∀ (d : G ⧸ N) (F : Fin K → RegRep N), r (d • F) = e.symm d • r F := by
    intro d F
    show r₀ ((reBlock N e K).symm (d • F)) = e.symm d • r₀ ((reBlock N e K).symm F)
    rw [reBlock_symm_smul, hrsmul]
  -- the pulled-back form is invariant and quadratic
  have hqWinv : IsInvariant (G ⧸ N) (fun F => q (r F)) := by
    intro d F
    show q (r (d • F)) = q (r F)
    rw [hrsmul' d F, hinv]
  have hqWquad : IsQuadraticFp2 (fun F : Fin K → RegRep N => q (r F)) := by
    constructor
    · show q (r 0) = 0
      rw [map_zero, hq.map_zero]
    · intro A B D
      show polar _ _ _ = polar _ _ _ + polar _ _ _
      simp only [polar, map_add]
      exact hq.polar_add_left (r A) (r B) (r D)
    · intro A B D
      show polar _ _ _ = polar _ _ _ + polar _ _ _
      simp only [polar, map_add]
      exact hq.polar_add_right (r A) (r B) (r D)
  refine ⟨K, ι, r, isEquivariantFactorSet_orbitSumDatum N hqWquad hqWinv, ?_, ?_, hretr⟩
  · intro v; rw [hretr v]
  · intro a v
    show reBlock N e K (ι₀ (a • v)) = e a • reBlock N e K (ι₀ v)
    rw [hιsmul, reBlock_smul]

end OrbitCapstone

end GQ2
