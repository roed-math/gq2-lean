/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GQ2.KappaNormalForm

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

end GQ2
