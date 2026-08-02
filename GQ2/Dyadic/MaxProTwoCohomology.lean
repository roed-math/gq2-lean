/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex GPT-5
-/
import GQ2.Dyadic.Instances.KSupply
import GQ2.MaxProPCohomology

/-!
# Mod-2 `H¹` on `G_K(2)`

This file specializes the general degree-one maximal-pro-`p` comparison to
`G_K → G_K(2)` and `𝔽₂`.  It is the first cohomological transfer needed to reuse the field-side
dyadic data on the maximal pro-2 quotient.

The quotient-side action is left as an instance argument because the continuous-cohomology type
records it through typeclass synthesis.  Every such action on `ZMod 2` is automatically trivial,
so the resulting equivalence is independent of any mathematical choice of action.
-/

namespace GQ2.Dyadic

open ContCoh Count

noncomputable section

variable {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
variable [DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2)]
  [ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2)]

/-- `Multiplicative 𝔽₂` is a pro-2 group. -/
theorem isProPTwo_multiplicativeZModTwo : IsProP 2 (Multiplicative (ZMod 2)) :=
  isProP_of_isPGroup (IsPGroup.of_card (p := 2) (n := 1)
    (by rw [Nat.card_eq_fintype_card]; decide))

/-- Inflation identifies mod-2 `H¹` of `G_K(2)` with mod-2 `H¹` of `G_K`. -/
def h1MaxProTwoEquivGalK :
    H1 (maxProPQuotient 2 (GalK K)) (ZMod 2) ≃+ H1 (GalK K) (ZMod 2) :=
  maxProPH1EquivOfTrivial isProPTwo_multiplicativeZModTwo (htriv_galK K) smul_zmod2

omit [FiniteDimensional ℚ_[2] K]
  [ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2)] in
/-- The forward map of `h1MaxProTwoEquivGalK` is inflation along `G_K → G_K(2)`. -/
theorem h1MaxProTwoEquivGalK_apply (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) :
    h1MaxProTwoEquivGalK (K := K) x =
      inf1 (maxProPMk 2 (GalK K))
        (fun g m => (smul_zmod2 (maxProPMk 2 (GalK K) g) m).trans
          (htriv_galK K g m).symm) x :=
  maxProPH1EquivOfTrivial_apply isProPTwo_multiplicativeZModTwo (htriv_galK K) smul_zmod2 x

omit [ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2)] in
/-- The field-side computation of the size of mod-2 `H¹`, transported to `G_K(2)`. -/
theorem card_H1_zmodTwo_maxProTwoGalK :
    Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) =
      2 ^ (Module.finrank ℚ_[2] K + 2) := by
  rw [Nat.card_congr (h1MaxProTwoEquivGalK (K := K)).toEquiv]
  exact FieldData.card_H1_zmodTwo K

omit [FiniteDimensional ℚ_[2] K] in
/-- Inflation along `G_K → G_K(2)` respects the mod-2 cup product. -/
theorem inf2_trivialCupPairing_maxProPMk_galK
    (x y : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) :
    inf2 (maxProPMk 2 (GalK K))
        (fun g m => (smul_zmod2 (maxProPMk 2 (GalK K) g) m).trans
          (htriv_galK K g m).symm)
        (trivialCupPairing 2 (maxProPQuotient 2 (GalK K)) smul_zmod2 x y) =
      trivialCupPairing 2 (GalK K) (htriv_galK K)
        (h1MaxProTwoEquivGalK (K := K) x) (h1MaxProTwoEquivGalK (K := K) y) := by
  obtain ⟨a, rfl⟩ := H1mk_surjective x
  obtain ⟨b, rfl⟩ := H1mk_surjective y
  rw [h1MaxProTwoEquivGalK_apply, h1MaxProTwoEquivGalK_apply]
  simp only [trivialCupPairing, cup11_mk_mk]
  rw [inf2_H2mk, inf1_H1mk, inf1_H1mk, cup11_mk_mk]
  congr 1
  apply Subtype.ext
  funext p
  change a.1 (maxProPMk 2 (GalK K) p.1) *
      (maxProPMk 2 (GalK K) p.1 • b.1 (maxProPMk 2 (GalK K) p.2)) =
    a.1 (maxProPMk 2 (GalK K) p.1) * (p.1 • b.1 (maxProPMk 2 (GalK K) p.2))
  rw [smul_zmod2, htriv_galK]

end


end GQ2.Dyadic
