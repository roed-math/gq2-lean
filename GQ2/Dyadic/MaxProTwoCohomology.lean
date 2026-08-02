/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex GPT-5
-/
import GQ2.Dyadic.Instances.KSupply
import GQ2.MaxProPCohomology

/-!
# Mod-2 cohomology on `G_K(2)`

This file specializes the maximal-pro-`p` cohomology comparison to `G_K → G_K(2)` and
`𝔽₂`.  Inflation is an equivalence in degree one and injective in degree two.  Field-side local
duality and cup-product nondegeneracy then make the degree-two map an equivalence and prove that
`G_K(2)` is a Demushkin group of rank `[K : ℚ₂] + 2`.

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

omit [FiniteDimensional ℚ_[2] K]
  [ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2)] in
/-- Degree-two inflation from `G_K(2)` to `G_K`. -/
def h2InflationGalK :
    H2 (maxProPQuotient 2 (GalK K)) (ZMod 2) →+
      H2 (GalK K) (ZMod 2) :=
  inf2 (maxProPMk 2 (GalK K))
    (fun g m => (smul_zmod2 (maxProPMk 2 (GalK K) g) m).trans
      (htriv_galK K g m).symm)

omit [FiniteDimensional ℚ_[2] K] in
/-- Degree-two inflation from `G_K(2)` to `G_K` is injective. -/
theorem h2InflationGalK_injective : Function.Injective (h2InflationGalK (K := K)) :=
  injective_inf2_maxProPMk_zmodTwo (htriv_galK K) smul_zmod2

/-- The mod-2 cup product on `G_K(2)` is nondegenerate in the left slot. -/
theorem trivialCupPairing_maxProTwoGalK_nondeg_left
    (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) (hx : x ≠ 0) :
    ∃ y, trivialCupPairing 2 (maxProPQuotient 2 (GalK K)) smul_zmod2 x y ≠ 0 := by
  let e := h1MaxProTwoEquivGalK (K := K)
  have hex : e x ≠ 0 := by
    intro he
    apply hx
    apply e.injective
    simpa using he
  obtain ⟨y, hy⟩ := exists_trivialCupPairing_ne_zero_galK K (e x) hex
  refine ⟨e.symm y, ?_⟩
  intro hzero
  apply hy
  rw [← e.apply_symm_apply y]
  rw [← inf2_trivialCupPairing_maxProPMk_galK x (e.symm y)]
  rw [hzero, map_zero]

/-- The mod-2 cup product on `G_K(2)` is nondegenerate in the right slot. -/
theorem trivialCupPairing_maxProTwoGalK_nondeg_right
    (y : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) (hy : y ≠ 0) :
    ∃ x, trivialCupPairing 2 (maxProPQuotient 2 (GalK K)) smul_zmod2 x y ≠ 0 := by
  obtain ⟨x, hx⟩ := trivialCupPairing_maxProTwoGalK_nondeg_left (K := K) y hy
  refine ⟨x, ?_⟩
  rw [trivialCupPairing_comm smul_zmod2]
  exact hx

/-- There is a nonzero mod-2 degree-two class on `G_K(2)`: cup any nonzero degree-one class
with a class supplied by nondegeneracy. -/
theorem exists_ne_zero_H2_maxProTwoGalK :
    ∃ z : H2 (maxProPQuotient 2 (GalK K)) (ZMod 2), z ≠ 0 := by
  let Q := maxProPQuotient 2 (GalK K)
  have hcard := card_H1_zmodTwo_maxProTwoGalK (K := K)
  letI : Finite (H1 Q (ZMod 2)) := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    positivity)
  haveI : Nontrivial (H1 Q (ZMod 2)) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hcard]
    apply Nat.one_lt_two_pow
    omega)
  obtain ⟨x, hx⟩ := exists_ne (0 : H1 Q (ZMod 2))
  obtain ⟨y, hy⟩ := trivialCupPairing_maxProTwoGalK_nondeg_left (K := K) x hx
  exact ⟨trivialCupPairing 2 Q smul_zmod2 x y, hy⟩

/-- The mod-2 degree-two cohomology of `G_K(2)` has two elements. -/
theorem card_H2_zmodTwo_maxProTwoGalK :
    Nat.card (H2 (maxProPQuotient 2 (GalK K)) (ZMod 2)) = 2 := by
  let Q := maxProPQuotient 2 (GalK K)
  let f := h2InflationGalK (K := K)
  have hinj : Function.Injective f := h2InflationGalK_injective (K := K)
  have htarget : Nat.card (H2 (GalK K) (ZMod 2)) = 2 :=
    card_H2_zmodTwo_galK K
  letI : Finite (H2 (GalK K) (ZMod 2)) := Nat.finite_of_card_ne_zero (by
    rw [htarget]
    decide)
  letI : Finite (H2 Q (ZMod 2)) := Finite.of_injective f hinj
  obtain ⟨z, hz⟩ := exists_ne_zero_H2_maxProTwoGalK (K := K)
  letI : Nontrivial (H2 Q (ZMod 2)) := ⟨⟨z, 0, hz⟩⟩
  have hlow : 1 < Nat.card (H2 Q (ZMod 2)) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hhigh : Nat.card (H2 Q (ZMod 2)) ≤ 2 :=
    (Nat.card_le_card_of_injective f hinj).trans_eq htarget
  dsimp [Q] at hlow hhigh ⊢
  omega

/-- Inflation identifies mod-2 `H²` of `G_K(2)` with mod-2 `H²` of `G_K`. -/
noncomputable def h2MaxProTwoEquivGalK :
    H2 (maxProPQuotient 2 (GalK K)) (ZMod 2) ≃+ H2 (GalK K) (ZMod 2) := by
  let f := h2InflationGalK (K := K)
  have hinj : Function.Injective f := h2InflationGalK_injective (K := K)
  have htarget : Nat.card (H2 (GalK K) (ZMod 2)) = 2 :=
    card_H2_zmodTwo_galK K
  have hsource : Nat.card (H2 (maxProPQuotient 2 (GalK K)) (ZMod 2)) = 2 :=
    card_H2_zmodTwo_maxProTwoGalK (K := K)
  haveI : Finite (H2 (GalK K) (ZMod 2)) := Nat.finite_of_card_ne_zero (by
    rw [htarget]
    decide)
  exact AddEquiv.ofBijective f
    ((Nat.bijective_iff_injective_and_card f).mpr
      ⟨hinj, hsource.trans htarget.symm⟩)

/-- The forward map of `h2MaxProTwoEquivGalK` is degree-two inflation. -/
theorem h2MaxProTwoEquivGalK_apply
    (z : H2 (maxProPQuotient 2 (GalK K)) (ZMod 2)) :
    h2MaxProTwoEquivGalK (K := K) z =
      inf2 (maxProPMk 2 (GalK K))
        (fun g m => (smul_zmod2 (maxProPMk 2 (GalK K) g) m).trans
          (htriv_galK K g m).symm) z := rfl

/-- The maximal pro-2 quotient of the absolute Galois group of a finite dyadic field is a
Demushkin group. -/
theorem isDemushkin_maxProTwoGalK :
    IsDemushkin 2 (maxProPQuotient 2 (GalK K)) where
  smul_trivial := smul_zmod2
  isProP := isProP_maxProPQuotient
  finiteH1 := Nat.finite_of_card_ne_zero (by
    rw [card_H1_zmodTwo_maxProTwoGalK (K := K)]
    positivity)
  cardH2 := card_H2_zmodTwo_maxProTwoGalK (K := K)
  nondegen_left := trivialCupPairing_maxProTwoGalK_nondeg_left (K := K)
  nondegen_right := trivialCupPairing_maxProTwoGalK_nondeg_right (K := K)

omit [ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2)] in
/-- The Demushkin rank of `G_K(2)` is `[K : ℚ₂] + 2`. -/
theorem demushkinRank_maxProTwoGalK :
    demushkinRank 2 (maxProPQuotient 2 (GalK K)) = Module.finrank ℚ_[2] K + 2 :=
  demushkinRank_eq_of_card (card_H1_zmodTwo_maxProTwoGalK (K := K))

end


end GQ2.Dyadic
