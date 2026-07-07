import GQ2.ShapiroDeepness
import GQ2.RegularIsometry
import GQ2.OrbitDecomp

/-!
# P-15f2d: final assembly of `lemma_6_17_vanish` — wiring bricks

The capstone composing f2a (datum-independence) + Lemma 6.14 (`RepIndependence.lemma_6_14`) + f2b
(the orbit decomposition `regular_isometric_embedding_orbit`) + f2c (`hcoh`/`hvanish`) through
`OrbitVanish.Q0loc_vanish_of_datum_decomp`, then the SectionSix statement-move.

This file begins with the **mechanical wiring bricks** — independent of the open f2a/f2c1/f2c2
mathematics, buildable now.  f2b's orbit datum lives over `G ⧸ N` while the ambient `Q0loc` /
Lemma-6.14 transport is over `C`; the assembly reindexes the datum along `e : C ≃* G ⧸ N` (the
`FactorSet.reindexHom`/`Q0loc_reindexHom` bridge landed in `ShapiroDeepness`).  These two bricks
say `reindexHom` distributes over `sumDatum` and preserves equivariance under the `φ`-pullback
action — the two facts needed to feed the reindexed orbit sum into the reducer.
-/

namespace GQ2

namespace VanishClose

open OrbitVanish (sumDatum)

variable {C C' V : Type*} [Group C] [Group C'] [AddCommGroup V]
  [DistribMulAction C V] [DistribMulAction C' V]

/-- **`reindexHom` distributes over `sumDatum`** (P-15f2d wiring): reindexing a datum sum's acting
group along `φ` is the sum of the reindexed per-orbit data.  Both sides have the same factor set
(`f` is untouched by `reindexHom`) and the same corrections (`m` pre-composes `φ` inside each
summand), so this is definitional. -/
theorem reindexHom_sumDatum {ι : Type*} (s : Finset ι) (datf : ι → FactorSet C V) (φ : C' → C) :
    (sumDatum s datf).reindexHom φ = sumDatum s (fun o => (datf o).reindexHom φ) := rfl

/-- **Equivariance is preserved under `reindexHom`** (P-15f2d wiring): if `dat` is an equivariant
factor set for `q` over `C`, `φ : C' →* C` is a group hom, and the `C'`-action on `V` is the
`φ`-pullback of the `C`-action (`hφ`), then `dat.reindexHom φ` is an equivariant factor set for `q`
over `C'`.  The factor-set clauses are inherited verbatim (`f` unchanged); the correction clauses
(59)/(60) transport by `φ`'s multiplicativity and the `hφ` action identity. -/
theorem isEquivariantFactorSet_reindexHom {q : V → ZMod 2} {dat : FactorSet C V}
    (h : IsEquivariantFactorSet q dat) (φ : C' →* C)
    (hφ : ∀ (c' : C') (v : V), c' • v = φ c' • v) :
    IsEquivariantFactorSet q (dat.reindexHom φ) where
  f_cocycle := h.f_cocycle
  f_diag := h.f_diag
  f_polar := h.f_polar
  f_zero_left := h.f_zero_left
  f_zero_right := h.f_zero_right
  m_quad c' v w := by
    show dat.m (φ c') (v + w) + dat.m (φ c') v + dat.m (φ c') w
        = dat.f (c' • v) (c' • w) + dat.f v w
    rw [hφ c' v, hφ c' w]
    exact h.m_quad (φ c') v w
  m_mul c' d' v := by
    show dat.m (φ (c' * d')) v = dat.m (φ c') (d' • v) + dat.m (φ d') v
    rw [map_mul, hφ d' v]
    exact h.m_mul (φ c') (φ d') v
  m_one v := by
    show dat.m (φ 1) v = 0
    rw [map_one]
    exact h.m_one v

/-! ## The classifying equivalence `e : C ≃* AbsGalQ2 ⧸ ker ρ` -/

section ETower

variable {C : Type} [Group C] [TopologicalSpace C]

/-- **The classifying equivalence** `e : C ≃* AbsGalQ2 ⧸ ker ρ` (P-15f2d): for a surjective `ρ`,
the inverse of the first-isomorphism `AbsGalQ2 ⧸ ker ρ ≃* C`.  It is what f2b's
`regular_isometric_embedding_orbit` consumes to give the regular module `W = Fin K → RegRep (ker ρ)`
its `C`-view (the `e`-pullback of the canonical `G ⧸ N`-action). -/
noncomputable def eOfSurj (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρsurj : Function.Surjective ρ) :
    C ≃* AbsGalQ2 ⧸ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) :=
  (QuotientGroup.quotientKerEquivOfSurjective ρ.toMonoidHom hρsurj).symm

/-- **`e ∘ ρ = mk'`** (P-15f2d): the classifying equivalence sends `ρ g` back to its coset, so
`e` composed with `ρ` is the quotient map.  This is the identity that turns the `C`-level reindexed
pullback into the `mk' N`-level orbit map (where `lemma_6_15_*` are stated) and supplies the
`Q0loc`/reducer compatibility `hρW : g • w = ρ g • w` on `W`. -/
theorem eOfSurj_rho (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρsurj : Function.Surjective ρ)
    (g : AbsGalQ2) :
    eOfSurj ρ hρsurj (ρ g) = QuotientGroup.mk g := by
  have he : QuotientGroup.quotientKerEquivOfSurjective ρ.toMonoidHom hρsurj (QuotientGroup.mk g)
      = ρ g := QuotientGroup.kerLift_mk _ g
  exact (QuotientGroup.quotientKerEquivOfSurjective ρ.toMonoidHom hρsurj).symm_apply_eq.mpr he.symm

end ETower

end VanishClose

end GQ2
