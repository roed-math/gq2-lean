/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5.5
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.CupNorm
public import GQ2.TauCeti.CohomologyDict

@[expose] public section

/-!
# B11a from Tau Ceti: the Hilbert-symbol norm criterion over finite dyadic bases

Ticket B11a of the Tau Ceti discharge campaign (`docs/orchestration/tauceti-tickets.md`, recon memo
`docs/orchestration/tauceti-t2-recon.md` §B11a).  This file provides
`hilbertSymbol_normCriterion_finiteDyadic_tauceti`, whose statement is the
`hilbertSymbol_normCriterion_finiteDyadic` field of `GQ2.LiteratureInputs` verbatim: for a finite
`k : IntermediateField ℚ_[2] ℚ̄₂` and `a b ∈ kˣ`, the cup product `[a] ⌣ [b]` of gq2's Kummer
classes vanishes in `H²(G_k, 𝔽₂)` iff `b = x² - a y²` for some `x y ∈ k`.

It is Tau Ceti's `cup_kummerClass_eq_zero_iff` at `K = ↥k` (which holds for any field with `2`
invertible; no local hypothesis), carried across by the dictionaries: A2's `cont2F2` (an additive
equivalence, so it reflects `0`), its cup rule `cont2F2_trivialCupPairing` and Kummer rule
`trivialF2Map_fixingEquivAbsGal_kummerClass` (at A1's `fixingEquivAbsGal k`), Tau Ceti's
`trivialF2Map_cup`, and injectivity of `trivialF2Map` in degree `2` (it is the inverse of
`trivialF2Iso`).  `Invertible (2 : ↥k)` is not found by instance search and is supplied by
`invertibleOfNonzero`; `LocallyCompactSpace ↥k.fixingSubgroup` is A1's instance.
-/

namespace GQ2.TauCetiBridge

open CategoryTheory GQ2.ContCoh

/-- **B11a from Tau Ceti**: the Hilbert-symbol norm criterion over finite dyadic bases.  The
statement is the type of the `hilbertSymbol_normCriterion_finiteDyadic` field of
`GQ2.LiteratureInputs`. -/
theorem hilbertSymbol_normCriterion_finiteDyadic_tauceti
    (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m) :
    ∀ a b : (↥k)ˣ,
      kummerClassK k a ⌣[htriv] kummerClassK k b = 0 ↔
        ∃ x y : ↥k, (b : ↥k) = x ^ 2 - (a : ↥k) * y ^ 2 := by
  intro a b
  let : Invertible (2 : ↥k) := invertibleOfNonzero two_ne_zero
  have hinj : Function.Injective (TauCeti.trivialF2Map
      (fixingEquivAbsGal k : ↥k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup ↥k) 2) := by
    rw [← TauCeti.trivialF2Iso_inv (fixingEquivAbsGal k) 2]
    exact (ConcreteCategory.bijective_of_isIso _).1
  rw [← (cont2F2 ↥k.fixingSubgroup htriv).map_eq_zero_iff, cont2F2_trivialCupPairing,
    ← trivialF2Map_fixingEquivAbsGal_kummerClass k htriv a,
    ← trivialF2Map_fixingEquivAbsGal_kummerClass k htriv b, ← TauCeti.trivialF2Map_cup,
    ← TauCeti.cup_kummerClass_eq_zero_iff a b]
  exact ⟨fun h => hinj (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩

end GQ2.TauCetiBridge
