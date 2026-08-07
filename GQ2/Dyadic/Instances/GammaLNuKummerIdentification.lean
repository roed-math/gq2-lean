/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLUnramifiedHilbertValue
import GQ2.Dyadic.OddDegreeRamifiedI
import GQ2.UnitNormIndex

/-!
# `ν̄ = [−3]` — the Artin ⟷ Kummer identification of the unramified class

`GammaLUnramifiedHilbertValue` reduced the `𝔽₂` number `NuUrOmegaCupOne B` (the cup value
`b_K([2], ν̄) = 1` the marked Frattini frame costs) to a single `def`-shaped `Prop`,
`NuUrUnramifiedKummerClass B`: that the mod-two unramified character `ν̄` of the bundle *is* the
Kummer class of a unit cutting out an unramified quadratic extension.  This file proves that
`Prop` for **every odd-degree `K`**, with `u = −3`, and therefore closes `NuUrOmegaCupOne` at the
level-`L` row `r = 0` (`nuUrOmegaCupOne_of_odd`).

The route is the one the residual docstring of that file records, executed in four steps.  None
of them needs the finite-layer norm-residue clause `(a_K)` that `MarkedRecip` deliberately omits,
and none of them needs `ModTwoTateKummerArtinCompatibility`: the norm-residue theorem is used
only at the **base**, where B5 carries it.

## What is proved

* **§1 `−3` is a nonsquare** (`sq_ne_neg_three_padic`, `sq_ne_neg_three_of_odd`).  Over `ℚ₂`
  this is `−3 ≡ 5 (mod 8)` read in `ZMod 8`; over an odd-degree `K` a square root would generate
  a quadratic subextension, and `2 ∤ [K : ℚ₂]`.
* **§2 `K(√−3)/K` is unramified** (`hasEqualNormValueGroups_of_sq_eq_neg_three`) — the one
  genuinely new analytic obligation, discharged in the repository's `HasEqualNormValueGroups`
  norm vocabulary, with no residue-field interface.  Writing `z = x + y√−3`, the ultrametric
  estimate settles `‖z‖` outright unless `‖x‖ = ‖y‖`, where `‖z‖² = ‖t² + 3‖` for the unit
  `t = x/y`; and `‖t² + 3‖ ∈ {1, ‖4‖, ‖t−1‖²}` in every case, the last branch (`‖t−1‖ = ‖2‖`,
  `t − 1 = 2c`) resting on **`‖c² + c + 1‖ = 1`** (`norm_cubeCyclotomic_eq_one`): the residue
  field of an odd-degree `K` has no primitive cube root of unity, because otherwise `2c + 1` is a
  square root of `−3` to Hensel depth and `GQ2.sq_of_near_one` upgrades it to an honest one,
  contradicting §1.  This is also exactly what "`−3` is a nonsquare in `K`" costs, so §§1–2 are
  one package.
* **§3 the descent** (`redTwo_nuUr_restrict`).  `MarkedRecip.norm_compat` plus B5 clause (b) give
  `ν_ur(incl∗ rec_K x) = ofAdd(−f·v_K(x))`, while clause `(b_K)` gives
  `ν_ur^K(rec_K x) = ofAdd(−v_K(x))`; density of the `rec_K`-image upgrades this to
  `ν_ur ∘ incl∗ = f · ν_ur^K` on all of `G_K^{ab}` (`toAdd_nuUr_incl`).  The valuation input is
  `e · v₂(N x) = n · v_K(x)`, i.e. `UnitNormIndex.e_mul_val_norm` widened off `[IsGalois]` by
  `norm_algebra_eq_norm_pow_finrank` (`e_mul_val_norm_of_finrank`).  In odd degree `n = e·f`
  makes `f` odd, so the two mod-two shadows coincide.
* **§4 the base case** (`redTwo_nuUr_eq_kummerCocycle`).  `L = ℚ₂(√−3)`; the kernel of the Kummer
  character `[−3]` is `L.fixingSubgroup` (`ker_kummerNegThree`), which is therefore open and
  normal, so `L/ℚ₂` is finite Galois with abelian group (`isGalois_layer`, `comm_layer`) and
  **B5 clause (a)** applies: `ker([−3] ∘ rec) = N(Lˣ)`.  §2 at the odd-degree field `⊥` (through
  the coordinate lemma `exists_coords_base`) shows `v₂(N(Lˣ))` is even, so
  `ker([−3] ∘ rec) ⊆ {v₂ even} = ker(ν̄ ∘ rec)`; since the uniformizer misses the larger kernel,
  two characters into the two-element group with nested kernels are *equal*
  (`nuBar_eq_kummerNegThreeAb`), and `denseRange_recip` carries it to all of `G_{ℚ₂}^{ab}`.
  Note that only *one* inclusion of norm groups is needed — B11b is never invoked.
* **§5 the identification** (`nuUrUnramifiedKummerClass_of_odd`).  `kummerClassK` is `H1mk` of
  the same `Kummer.kummerCocycleFun` at every base field, so `[−3]_K` is literally `[−3]_{ℚ₂}`
  restricted, and §§3–4 compose pointwise.  `nuUrOmegaCupOne_of_odd` is the one-line consumer,
  and `sqMarkedForwardSupply_of_presentation` /
  `nonempty_markedCoreCertificate_of_presentation` restate the frame file's §6 endpoints with
  the cup hypothesis gone: the `L`-row certificate now costs exactly one residual,
  `SqCupAdaptedFramePresentation K`.

## Axioms

Everything through §5's `nuUrUnramifiedKummerClass_of_odd` is **std-3**: the file is
parametrized over `R : LocalReciprocity` and `B : MarkedRecip R K`, so neither B5 nor B5-K
appears, and B13 has been a `def` since the 2026-07-24 flip.  Only the final consumer
`nuUrOmegaCupOne_of_odd` picks up `hilbertSymbol_normCriterion_finiteDyadic` (**B11a**) and
`tateDualityAt` (**B6**), inherited verbatim from `GammaLUnramifiedHilbertValue` §§1–3; the two
frame endpoints add `absGalQ2_isTopologicallyFinitelyGenerated` (**B1**) and
`absGalQ2_localEulerCharacteristic` (**B7**), the footprint of the frame file's §5–§6.  The
`#print axioms` block at the end of the file is the record.  No `sorry`, no new axiom, no
`native_decide`.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 ContCoh
open FrattiniFrameSupply

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

namespace NuKummer

/-! ## §1 `−3` is a nonsquare, and `K(√−3)/K` is unramified, in odd degree -/

section NonSquare

/-- `‖−3‖ = 1` in `ℚ₂`: `3` is a `2`-adic unit. -/
theorem norm_neg_three_padic : ‖(-3 : ℚ_[2])‖ = 1 := by
  have hne : (-3 : ℚ_[2]) ≠ 0 := by norm_num
  have hval : (-3 : ℚ_[2]).valuation = 0 := by
    rw [show (-3 : ℚ_[2]) = ((-3 : ℤ) : ℚ_[2]) by push_cast; ring, Padic.valuation_intCast]
    simp [padicValInt]
  rw [Padic.norm_eq_zpow_neg_valuation hne, hval]
  norm_num

/-- `‖−3‖ = 1` in `ℚ̄₂`. -/
theorem norm_neg_three : ‖(-3 : ℚ̄₂)‖ = 1 := by
  rw [show (-3 : ℚ̄₂) = algebraMap ℚ_[2] ℚ̄₂ (-3) by rw [map_neg, map_ofNat],
    norm_algebraMap' (𝕜' := ℚ̄₂), norm_neg_three_padic]

/-- Any square root of `−3` has norm one. -/
theorem norm_eq_one_of_sq_eq_neg_three {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) : ‖δ‖ = 1 := by
  have hsq : ‖δ‖ ^ 2 = 1 := by rw [← norm_pow, hδ, norm_neg_three]
  nlinarith [norm_nonneg δ]

/-- **`−3` is not a square in `ℚ₂`** (`−3 ≡ 5 (mod 8)` and every square of a `2`-adic integer is
`0, 1` or `4` mod `8`). -/
theorem sq_ne_neg_three_padic (v : ℚ_[2]) : v ^ 2 ≠ -3 := by
  intro hv
  have hvn : ‖v‖ = 1 := by
    have hsq : ‖v‖ ^ 2 = 1 := by rw [← norm_pow, hv, norm_neg_three_padic]
    nlinarith [norm_nonneg v]
  let z : ℤ_[2] := ⟨v, hvn.le⟩
  have hz : z ^ 2 = -3 := by
    apply Subtype.ext
    show v ^ 2 = ((-3 : ℤ_[2]) : ℚ_[2])
    rw [hv, show ((-3 : ℤ_[2]) : ℚ_[2]) = algebraMap ℤ_[2] ℚ_[2] (-3) from rfl, map_neg, map_ofNat]
  have hmod := congrArg (PadicInt.toZModPow (p := 2) 3) hz
  rw [map_pow, map_neg, map_ofNat] at hmod
  revert hmod
  generalize (PadicInt.toZModPow (p := 2) 3 z) = a
  revert a
  decide

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]

/-- **`−3` stays a nonsquare in odd degree.**  A square root would generate a quadratic
subextension, and `2 ∤ [K : ℚ₂]`. -/
theorem sq_ne_neg_three_of_odd (hodd : Odd (Module.finrank ℚ_[2] K)) (v : ↥K) : v ^ 2 ≠ -3 := by
  intro hv
  have hint : IsIntegral ℚ_[2] v := (Algebra.IsIntegral.isIntegral (R := ℚ_[2]) v)
  have hdvd : minpoly ℚ_[2] v ∣ (Polynomial.X ^ 2 + Polynomial.C 3 : Polynomial ℚ_[2]) := by
    apply minpoly.dvd
    simp only [map_add, map_pow, Polynomial.aeval_X, hv, map_ofNat]
    ring
  have hpne : (Polynomial.X ^ 2 + Polynomial.C 3 : Polynomial ℚ_[2]) ≠ 0 := by
    intro h
    have := congrArg (fun p => Polynomial.coeff p 2) h
    simp at this
  have hle : (minpoly ℚ_[2] v).natDegree ≤ 2 := by
    have hd := Polynomial.natDegree_le_of_dvd hdvd hpne
    have : (Polynomial.X ^ 2 + Polynomial.C 3 : Polynomial ℚ_[2]).natDegree = 2 := by
      compute_degree!
    omega
  have hne1 : (minpoly ℚ_[2] v).natDegree ≠ 1 := by
    intro h1
    have hmem : v ∈ (⊥ : IntermediateField ℚ_[2] ↥K) := by
      apply IntermediateField.finrank_adjoin_simple_eq_one_iff.mp
      rw [IntermediateField.adjoin.finrank hint, h1]
    obtain ⟨w, hw⟩ := IntermediateField.mem_bot.mp hmem
    refine sq_ne_neg_three_padic w ?_
    have hcast : algebraMap ℚ_[2] ↥K (w ^ 2) = algebraMap ℚ_[2] ↥K (-3) := by
      rw [map_pow, hw, hv, map_neg, map_ofNat]
    exact (algebraMap ℚ_[2] ↥K).injective hcast
  have hne0 : (minpoly ℚ_[2] v).natDegree ≠ 0 := by
    have := minpoly.natDegree_pos hint
    omega
  have hdeg : (minpoly ℚ_[2] v).natDegree = 2 := by omega
  have hrank : Module.finrank ℚ_[2] ↥(IntermediateField.adjoin ℚ_[2] {v}) = 2 := by
    rw [IntermediateField.adjoin.finrank hint, hdeg]
  have htower : Module.finrank ℚ_[2] ↥(IntermediateField.adjoin ℚ_[2] {v}) *
      Module.finrank ↥(IntermediateField.adjoin ℚ_[2] {v}) ↥K = Module.finrank ℚ_[2] ↥K :=
    Module.finrank_mul_finrank _ _ _
  rw [hrank] at htower
  obtain ⟨j, hj⟩ := hodd
  omega

/-- The chosen square root of `−3` does not lie in an odd-degree `K`. -/
theorem notMem_of_sq_eq_neg_three (hodd : Odd (Module.finrank ℚ_[2] K)) {δ : ℚ̄₂}
    (hδ : δ ^ 2 = -3) : δ ∉ K := by
  intro hmem
  refine sq_ne_neg_three_of_odd hodd ⟨δ, hmem⟩ ?_
  apply Subtype.ext
  show δ ^ 2 = ((-3 : ↥K) : ℚ̄₂)
  rw [hδ, show ((-3 : ↥K) : ℚ̄₂) = algebraMap (↥K) ℚ̄₂ (-3) from rfl, map_neg, map_ofNat]

end NonSquare

/-! ## §2 `K(√−3)/K` is unramified in odd degree

The value group does not grow: `‖x + y√−3‖` is always the norm of an element of `K`.  The only
case where the ultrametric estimate does not settle it on the spot is `‖x‖ = ‖y‖` with
`t = x/y ≡ 1` to depth exactly `‖2‖`, and there the value is `‖2‖·‖c² + c + 1‖^{1/2}` with `c` a
unit; `‖c² + c + 1‖ < 1` would make `2c + 1` a square root of `−3` to Hensel depth, which the
local square theorem upgrades to an honest one — impossible in odd degree by §1. -/

section Unramified

/-- `‖3‖ = 1` in any normed `ℚ₂`-algebra. -/
theorem norm_three_algebra {F : Type*} [NormedField F] [NormedAlgebra ℚ_[2] F] :
    ‖(3 : F)‖ = 1 := by
  rw [show (3 : F) = algebraMap ℚ_[2] F 3 from (map_ofNat _ 3).symm,
    norm_algebraMap' (𝕜' := F) (3 : ℚ_[2]), ← norm_neg]
  exact norm_neg_three_padic

/-- Ultrametric domination: a strictly smaller summand does not move the norm. -/
theorem norm_add_of_norm_lt {F : Type*} [NormedField F] [IsUltrametricDist F] {a b : F}
    (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt h), max_eq_left h.le]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]

/-- **No primitive cube root of unity in the residue field of an odd-degree `K`**, phrased in
the repository's norm vocabulary: `‖c² + c + 1‖ = 1` for every `c` of norm one.

If instead `‖c² + c + 1‖ < 1`, then `d = 2c + 1` satisfies `d² + 3 = 4(c² + c + 1)`, so
`−d²/3` is within `< ‖4‖` of `1`; the local square theorem (`GQ2.sq_of_near_one`) makes it a
square `w²`, and `d/w` is an honest square root of `−3` in `K`. -/
theorem norm_cubeCyclotomic_eq_one (hodd : Odd (Module.finrank ℚ_[2] K)) {c : ↥K}
    (hc : ‖c‖ = 1) : ‖c ^ 2 + c + 1‖ = 1 := by
  have h2lt : ‖(2 : ↥K)‖ < 1 := GQ2.norm_two_lt_one'
  have h3 : ‖(3 : ↥K)‖ = 1 := norm_three_algebra
  have h4 : ‖(4 : ↥K)‖ = ‖(2 : ↥K)‖ * ‖(2 : ↥K)‖ := by
    rw [show (4 : ↥K) = 2 * 2 by norm_num, norm_mul]
  have h2pos : (0 : ℝ) < ‖(2 : ↥K)‖ := norm_pos_iff.mpr two_ne_zero
  have h4pos : (0 : ℝ) < ‖(4 : ↥K)‖ := by rw [h4]; exact mul_pos h2pos h2pos
  have h4lt : ‖(4 : ↥K)‖ < 1 := by
    rw [h4]; nlinarith [norm_nonneg (2 : ↥K)]
  have hle : ‖c ^ 2 + c + 1‖ ≤ 1 := by
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ (le_of_eq norm_one))
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ (le_of_eq hc))
    rw [norm_pow, hc, one_pow]
  rcases eq_or_lt_of_le hle with h | hlt
  · exact h
  exfalso
  set B : ↥K := c ^ 2 + c + 1 with hB
  set q : ↥K := -(2 * c + 1) ^ 2 / 3 with hq
  have h30 : (3 : ↥K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at h3
    exact absurd h3.symm one_ne_zero
  have hqsub : q - 1 = -(4 * B) / 3 := by
    rw [hq, hB]
    field_simp
    ring
  have hqnorm : ‖q - 1‖ < ‖(4 : ↥K)‖ := by
    rw [hqsub, norm_div, norm_neg, norm_mul, h3, div_one]
    nlinarith
  have hq1 : ‖q‖ = 1 := by
    rw [show q = (1 : ↥K) + (q - 1) by ring,
      norm_add_of_norm_lt (a := (1 : ↥K)) (b := q - 1)
        (by rw [norm_one]; exact lt_trans hqnorm h4lt), norm_one]
  obtain ⟨w, hw⟩ := GQ2.sq_of_near_one K q hqnorm
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at hw
    rw [← hw, norm_zero] at hq1
    exact absurd hq1 zero_ne_one
  refine sq_ne_neg_three_of_odd hodd ((2 * c + 1) * w⁻¹) ?_
  have hd2 : (2 * c + 1) ^ 2 = -3 * w ^ 2 := by
    rw [hw, hq]
    field_simp
  field_simp
  linear_combination hd2

/-- **The norm-form value is a square in the value group.**  For a unit `t`, `‖t² + 3‖` is
`‖w‖²` for an explicit `w ∈ {1, 2, t − 1}`. -/
theorem exists_norm_sq_eq_sq_add_three (hodd : Odd (Module.finrank ℚ_[2] K)) {t : ↥K}
    (ht : ‖t‖ = 1) : ∃ w : ↥K, w ≠ 0 ∧ ‖t ^ 2 + 3‖ = ‖w‖ ^ 2 := by
  have h2lt : ‖(2 : ↥K)‖ < 1 := GQ2.norm_two_lt_one'
  have h2pos : (0 : ℝ) < ‖(2 : ↥K)‖ := norm_pos_iff.mpr two_ne_zero
  have h4 : ‖(4 : ↥K)‖ = ‖(2 : ↥K)‖ ^ 2 := by
    rw [show (4 : ↥K) = 2 * 2 by norm_num, norm_mul, sq]
  set s : ↥K := t - 1 with hs
  have hsle : ‖s‖ ≤ 1 := by
    rw [hs, sub_eq_add_neg]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le (le_of_eq ht) ?_)
    rw [norm_neg, norm_one]
  rcases eq_or_lt_of_le hsle with hs1 | hslt
  · -- `t ≢ 1`: the value is a unit
    refine ⟨1, one_ne_zero, ?_⟩
    have hfac : t ^ 2 + 3 = s * (s + 2) + 4 := by rw [hs]; ring
    have hs2 : ‖s + 2‖ = ‖s‖ := norm_add_of_norm_lt (by rw [hs1]; exact h2lt)
    have hprod : ‖s * (s + 2)‖ = 1 := by rw [norm_mul, hs2, hs1, one_mul]
    rw [hfac, norm_add_of_norm_lt (a := s * (s + 2)) (b := (4 : ↥K)) (by
      rw [hprod, h4]; nlinarith), hprod, norm_one, one_pow]
  · -- `t ≡ 1`: split on the depth of `s = t − 1`
    have hexp : t ^ 2 + 3 = s ^ 2 + 2 * s + 4 := by rw [hs]; ring
    rcases lt_trichotomy ‖s‖ ‖(2 : ↥K)‖ with hcase | hcase | hcase
    · refine ⟨2, two_ne_zero, ?_⟩
      have hsmall : ‖s ^ 2 + 2 * s‖ < ‖(4 : ↥K)‖ := by
        refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
        · rw [norm_pow, h4]; nlinarith [norm_nonneg s]
        · rw [norm_mul, h4]; nlinarith
      rw [hexp, show s ^ 2 + 2 * s + 4 = (4 : ↥K) + (s ^ 2 + 2 * s) by ring,
        norm_add_of_norm_lt hsmall, h4]
    · refine ⟨2, two_ne_zero, ?_⟩
      have hc0 : (2 : ↥K) ≠ 0 := two_ne_zero
      set c : ↥K := s / 2 with hcdef
      have hcnorm : ‖c‖ = 1 := by
        rw [hcdef, norm_div, hcase, div_self (ne_of_gt h2pos)]
      have hcube : ‖c ^ 2 + c + 1‖ = 1 := norm_cubeCyclotomic_eq_one hodd hcnorm
      have hfac : t ^ 2 + 3 = 4 * (c ^ 2 + c + 1) := by
        rw [hexp, hcdef]
        field_simp
        ring
      rw [hfac, norm_mul, hcube, mul_one, h4]
    · refine ⟨s, ?_, ?_⟩
      · intro h
        rw [h, norm_zero] at hcase
        exact absurd hcase (not_lt.mpr h2pos.le)
      · have hsmall : ‖2 * s + 4‖ < ‖s ^ 2‖ := by
          rw [norm_pow]
          refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
          · rw [norm_mul]; nlinarith
          · rw [h4]; nlinarith
        rw [hexp, show s ^ 2 + 2 * s + 4 = s ^ 2 + (2 * s + 4) by ring,
          norm_add_of_norm_lt hsmall, norm_pow]

/-- **The analytic obligation, discharged.**  For odd `[K : ℚ₂]`, adjoining a square root of
`−3` does not enlarge the value group: `K(√−3)/K` is unramified in the repository's
`HasEqualNormValueGroups` convention. -/
theorem hasEqualNormValueGroups_of_sq_eq_neg_three (hodd : Odd (Module.finrank ℚ_[2] K))
    {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) : HasEqualNormValueGroups K δ := by
  have hδnorm : ‖δ‖ = 1 := norm_eq_one_of_sq_eq_neg_three hδ
  have hδK : δ ∉ K := notMem_of_sq_eq_neg_three hodd hδ
  have hδcoe : δ ^ 2 = (((-3 : ↥K) : ↥K) : ℚ̄₂) := by
    rw [hδ, show ((-3 : ↥K) : ℚ̄₂) = algebraMap (↥K) ℚ̄₂ (-3) from rfl, map_neg, map_ofNat]
  obtain ⟨σ, hσ⟩ := UnramifiedQuadraticNorms.exists_conj hδcoe hδK
  rintro z hz0 ⟨x, y, rfl⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · refine ⟨x, ?_, by rw [ZeroMemClass.coe_zero, zero_mul, add_zero]⟩
    intro h
    exact hz0 (by rw [h, ZeroMemClass.coe_zero, zero_mul, add_zero])
  have hycoe : ((y : ↥K) : ℚ̄₂) ≠ 0 := fun h => hy0 (by exact_mod_cast h)
  rcases eq_or_ne x 0 with rfl | hx0
  · refine ⟨y, hy0, ?_⟩
    rw [ZeroMemClass.coe_zero, zero_add, norm_mul, hδnorm, mul_one]
  have hxcoe : ((x : ↥K) : ℚ̄₂) ≠ 0 := fun h => hx0 (by exact_mod_cast h)
  rcases eq_or_ne ‖((x : ↥K) : ℚ̄₂)‖ ‖((y : ↥K) : ℚ̄₂)‖ with heq | hne
  · -- the interesting case: rescale by `y` and use the norm-form value
    set t : ↥K := x / y with hts
    have htnorm : ‖t‖ = 1 := by
      show ‖((x / y : ↥K) : ℚ̄₂)‖ = 1
      rw [show ((x / y : ↥K) : ℚ̄₂) = ((x : ↥K) : ℚ̄₂) / ((y : ↥K) : ℚ̄₂) from rfl, norm_div, heq,
        div_self (norm_ne_zero_iff.mpr hycoe)]
    have hsplit : ((x : ↥K) : ℚ̄₂) + ((y : ↥K) : ℚ̄₂) * δ
        = ((y : ↥K) : ℚ̄₂) * (((t : ↥K) : ℚ̄₂) + δ) := by
      rw [show ((t : ↥K) : ℚ̄₂) = ((x : ↥K) : ℚ̄₂) / ((y : ↥K) : ℚ̄₂) from rfl]
      field_simp
    have hconj : ‖σ (((t : ↥K) : ℚ̄₂) + ((1 : ↥K) : ℚ̄₂) * δ)‖
        = ‖((t : ↥K) : ℚ̄₂) + ((1 : ↥K) : ℚ̄₂) * δ‖ :=
      UnramifiedQuadraticNorms.norm_conj_eq K σ _
    rw [UnramifiedQuadraticNorms.conj_apply hσ] at hconj
    have hone : ((1 : ↥K) : ℚ̄₂) = 1 := rfl
    rw [hone, one_mul] at hconj
    have hprod : ‖((t : ↥K) : ℚ̄₂) + δ‖ ^ 2 = ‖((t ^ 2 + 3 : ↥K) : ℚ̄₂)‖ := by
      have hmul : (((t : ↥K) : ℚ̄₂) + δ) * (((t : ↥K) : ℚ̄₂) - δ)
          = ((t ^ 2 + 3 : ↥K) : ℚ̄₂) := by
        have hc : ((t ^ 2 + 3 : ↥K) : ℚ̄₂) = ((t : ↥K) : ℚ̄₂) ^ 2 + 3 := by
          show ((t : ↥K) : ℚ̄₂) ^ 2 + ((3 : ↥K) : ℚ̄₂) = _
          rw [show ((3 : ↥K) : ℚ̄₂) = algebraMap (↥K) ℚ̄₂ 3 from rfl, map_ofNat]
        rw [hc]
        linear_combination -hδ
      rw [← hmul, norm_mul, hconj, sq]
    obtain ⟨w, hw0, hw⟩ := exists_norm_sq_eq_sq_add_three hodd htnorm
    have hval : ‖((t : ↥K) : ℚ̄₂) + δ‖ = ‖((w : ↥K) : ℚ̄₂)‖ := by
      have hsq : ‖((t : ↥K) : ℚ̄₂) + δ‖ ^ 2 = ‖((w : ↥K) : ℚ̄₂)‖ ^ 2 := by
        rw [hprod]; exact hw
      nlinarith [norm_nonneg (((t : ↥K) : ℚ̄₂) + δ), norm_nonneg (((w : ↥K) : ℚ̄₂)),
        norm_nonneg ((y : ↥K) : ℚ̄₂)]
    refine ⟨y * w, mul_ne_zero hy0 hw0, ?_⟩
    rw [hsplit, norm_mul, hval,
      show ((y * w : ↥K) : ℚ̄₂) = ((y : ↥K) : ℚ̄₂) * ((w : ↥K) : ℚ̄₂) from rfl, norm_mul]
  · -- unequal coordinate norms: the ultrametric equality settles it
    have hyδ : ‖((y : ↥K) : ℚ̄₂) * δ‖ = ‖((y : ↥K) : ℚ̄₂)‖ := by
      rw [norm_mul, hδnorm, mul_one]
    have hmax : ‖((x : ↥K) : ℚ̄₂) + ((y : ↥K) : ℚ̄₂) * δ‖
        = max ‖((x : ↥K) : ℚ̄₂)‖ ‖((y : ↥K) : ℚ̄₂)‖ := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hyδ]; exact hne), hyδ]
    rcases le_total ‖((x : ↥K) : ℚ̄₂)‖ ‖((y : ↥K) : ℚ̄₂)‖ with hle | hle
    · exact ⟨y, hy0, by rw [hmax, max_eq_right hle]⟩
    · exact ⟨x, hx0, by rw [hmax, max_eq_left hle]⟩

end Unramified

/-! ## §3 Descent: `ν̄_K` is the restriction of `ν̄_{ℚ₂}`

`norm_compat` reads `ν_ur ∘ incl∗ ∘ rec_K = ν_ur ∘ rec ∘ N_{K/ℚ₂} = −v₂ ∘ N`, and
`v₂(N x) = f · v_K(x)`; the `K`-side clause `(b_K)` reads `ν_ur^K ∘ rec_K = −v_K`.  So
`ν_ur ∘ incl∗ = f · ν_ur^K` on the `rec_K`-image, hence everywhere by density.  In odd degree
`f` is odd, so the two characters have the *same* mod-two shadow. -/

section Descent

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]

/-- **`e · v₂(N y) = n · m` without a Galois hypothesis.**  This is
`UnitNormIndex.e_mul_val_norm` with `norm_algebra_eq_norm_pow_finrank` (the all-embeddings form)
in place of `UnitNormIndex.norm_val`; nothing else in that proof used `IsGalois`. -/
theorem e_mul_val_norm_of_finrank (FF : DyadicUnitFiltration K) (y : ↥K) (hy : y ≠ 0) (m : ℤ)
    (hm : ‖(y : ℚ̄₂)‖ = ‖FF.π‖ ^ m) :
    (FF.e : ℤ) * (Algebra.norm ℚ_[2] y).valuation = (Module.finrank ℚ_[2] K : ℤ) * m := by
  have hny : (Algebra.norm ℚ_[2] y : ℚ_[2]) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hy
  have hN2 : ‖(Algebra.norm ℚ_[2] y : ℚ_[2])‖ = (2 : ℝ) ^ (-(Algebra.norm ℚ_[2] y).valuation) := by
    rw [Padic.norm_eq_zpow_neg_valuation hny]; norm_num
  have hBe : ‖FF.π‖ ^ (FF.e : ℤ) = (2 : ℝ) ^ (-1 : ℤ) := by
    rw [zpow_natCast, ← FF.he, show (2 : ℚ̄₂) = algebraMap ℚ_[2] ℚ̄₂ 2 from (map_ofNat _ 2).symm,
      norm_algebraMap' (𝕜' := ℚ̄₂), UnitNormIndex.norm_two]
  have hNB : ‖(Algebra.norm ℚ_[2] y : ℚ_[2])‖ = ‖FF.π‖ ^ ((Module.finrank ℚ_[2] K : ℤ) * m) := by
    rw [norm_algebra_eq_norm_pow_finrank K y, hm,
      ← zpow_natCast (‖FF.π‖ ^ m) (Module.finrank ℚ_[2] K), ← zpow_mul, mul_comm]
  have hcombine : (2 : ℝ) ^ (-(Algebra.norm ℚ_[2] y).valuation * (FF.e : ℤ))
      = (2 : ℝ) ^ (-((Module.finrank ℚ_[2] K : ℤ) * m)) := by
    calc (2 : ℝ) ^ (-(Algebra.norm ℚ_[2] y).valuation * (FF.e : ℤ))
        = ((2 : ℝ) ^ (-(Algebra.norm ℚ_[2] y).valuation)) ^ (FF.e : ℤ) := by rw [← zpow_mul]
      _ = ‖(Algebra.norm ℚ_[2] y : ℚ_[2])‖ ^ (FF.e : ℤ) := by rw [← hN2]
      _ = (‖FF.π‖ ^ ((Module.finrank ℚ_[2] K : ℤ) * m)) ^ (FF.e : ℤ) := by rw [hNB]
      _ = (‖FF.π‖ ^ (FF.e : ℤ)) ^ ((Module.finrank ℚ_[2] K : ℤ) * m) := by
            rw [← zpow_mul, ← zpow_mul, mul_comm]
      _ = ((2 : ℝ) ^ (-1 : ℤ)) ^ ((Module.finrank ℚ_[2] K : ℤ) * m) := by rw [hBe]
      _ = (2 : ℝ) ^ (-((Module.finrank ℚ_[2] K : ℤ) * m)) := by rw [← zpow_mul]; ring_nf
  have hinj := zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    hcombine
  linarith [hinj]

/-- The filtration uniformizer as a unit of `K` (the `IsGalois`-free copy of
`UnitNormIndex.piUnit`). -/
def piUnitK (FF : DyadicUnitFiltration K) : (↥K)ˣ :=
  Units.mk0 ⟨FF.π, FF.hπ_mem⟩ fun h => FF.hπ_ne (by simpa using congrArg Subtype.val h)

omit [FiniteDimensional ℚ_[2] K] in
@[simp] theorem piUnitK_coe (FF : DyadicUnitFiltration K) :
    (((piUnitK FF : (↥K)ˣ) : ↥K) : ℚ̄₂) = FF.π := rfl

omit [FiniteDimensional ℚ_[2] K] in
theorem norm_piUnitK_pos (FF : DyadicUnitFiltration K) : (0 : ℝ) < ‖FF.π‖ :=
  norm_pos_iff.mpr FF.hπ_ne

/-- **The `K`-side value of `ν_ur^K` on `rec_K`.**  If `‖x‖ = ‖π‖^m` then
`ν_ur^K(rec_K x) = ofAdd(−m)`: clause `(b_K)` on the decomposition `x = (x π^{−m}) · π^m`. -/
theorem nuUrK_recip_eq (B : MarkedRecip R K) (FF : DyadicUnitFiltration K) (x : (↥K)ˣ) (m : ℤ)
    (hm : ‖((x : ↥K) : ℚ̄₂)‖ = ‖FF.π‖ ^ m) :
    B.nu_ur (B.recip x) = Multiplicative.ofAdd ((-m : ℤ) : ℤ_[2]) := by
  have hπ0 : ‖FF.π‖ ≠ 0 := (norm_piUnitK_pos FF).ne'
  refine MarkedRecip.nu_ur_recip_of_decomp B x (x * (piUnitK FF) ^ (-m)) (piUnitK FF) m ?_ ?_
    FF.hπ_lt (fun z hz0 hz1 => FF.hπ_max (z : ℚ̄₂) z.2 hz1)
  · rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  · show ‖((x * (piUnitK FF) ^ (-m) : (↥K)ˣ) : ↥K)‖ = 1
    rw [Units.val_mul, norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow]
    show ‖((x : ↥K) : ℚ̄₂)‖ * ‖FF.π‖ ^ (-m) = 1
    rw [hm, ← zpow_add₀ hπ0, add_neg_cancel, zpow_zero]

/-- **The `ℚ₂`-side value of `ν_ur` on the pushed-forward `rec_K`.**  `norm_compat` plus B5
clause (b): `ν_ur(incl∗ rec_K x) = ofAdd(−f·m)`, the residue degree entering through
`e · v₂(N x) = n · m = e · f · m`. -/
theorem nuUrQ_incl_recip_eq (B : MarkedRecip R K) (FF : DyadicUnitFiltration K) (x : (↥K)ˣ)
    (m : ℤ) (hm : ‖((x : ↥K) : ℚ̄₂)‖ = ‖FF.π‖ ^ m) :
    R.nu_ur (inclAbK K (B.recip x)) = Multiplicative.ofAdd ((-((FF.f : ℤ) * m) : ℤ) : ℤ_[2]) := by
  have hval : v2 (normUnitsK K x) = (FF.f : ℤ) * m := by
    have hkey := e_mul_val_norm_of_finrank FF (x : ↥K) (Units.ne_zero x) m hm
    have hef : (Module.finrank ℚ_[2] K : ℤ) = (FF.e : ℤ) * (FF.f : ℤ) := by
      rw [SpectralLocalField.field_finrank_eq_e_mul_f (K := K) (FF := FF)]; push_cast; ring
    have hene : (FF.e : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp FF.he_pos)
    have hv2 : v2 (normUnitsK K x) = (Algebra.norm ℚ_[2] ((x : ↥K))).valuation := rfl
    rw [hv2]
    refine mul_left_cancel₀ hene ?_
    rw [hkey, hef]
    ring
  rw [B.norm_compat x, R.nu_ur_recip, hval]

/-- **The descent identity.**  `ν_ur ∘ incl∗ = f · ν_ur^K` on all of `G_K^{ab}`, by density of
the `rec_K`-image. -/
theorem toAdd_nuUr_incl (B : MarkedRecip R K) (FF : DyadicUnitFiltration K) (g : GalKab K) :
    Multiplicative.toAdd (R.nu_ur (inclAbK K g))
      = (FF.f : ℤ_[2]) * Multiplicative.toAdd (B.nu_ur g) := by
  have hext : (fun g : GalKab K => Multiplicative.toAdd (R.nu_ur (inclAbK K g)))
      = fun g : GalKab K => (FF.f : ℤ_[2]) * Multiplicative.toAdd (B.nu_ur g) := by
    refine Continuous.ext_on B.denseRange_recip
      (continuous_toAdd.comp (R.continuous_nu_ur.comp (continuous_inclAbK K)))
      (continuous_const.mul (continuous_toAdd.comp B.continuous_nu_ur)) ?_
    rintro _ ⟨x, rfl⟩
    obtain ⟨m, hm⟩ := UnramifiedNorm.norm_eq_zpow FF (SetLike.coe_mem (x : ↥K))
      (fun h => (Units.ne_zero x) (by exact_mod_cast h))
    show Multiplicative.toAdd (R.nu_ur (inclAbK K (B.recip x)))
        = (FF.f : ℤ_[2]) * Multiplicative.toAdd (B.nu_ur (B.recip x))
    rw [nuUrQ_incl_recip_eq B FF x m hm, nuUrK_recip_eq B FF x m hm]
    show ((-((FF.f : ℤ) * m) : ℤ) : ℤ_[2]) = (FF.f : ℤ_[2]) * ((-m : ℤ) : ℤ_[2])
    push_cast
    ring
  exact congrFun hext g

/-- Mod-two reduction of an odd natural number is `1`. -/
theorem redTwo_natCast_of_odd {n : ℕ} (hn : Odd n) : MarkedFrame.redTwo (n : ℤ_[2]) = 1 := by
  show (PadicInt.toZModPow (p := 2) 1) (n : ℤ_[2]) = 1
  rw [map_natCast]
  have : (n : ZMod (2 ^ 1)) = ((n % 2 : ℕ) : ZMod (2 ^ 1)) := by
    conv_lhs => rw [← Nat.div_add_mod n 2]
    push_cast
    show ((2 : ZMod (2 ^ 1)) * (n / 2 : ℕ) + (n % 2 : ℕ) : ZMod (2 ^ 1)) = _
    rw [show (2 : ZMod (2 ^ 1)) = 0 by decide, zero_mul, zero_add]
  rw [this, Nat.odd_iff.mp hn]
  rfl

/-- **The mod-two descent.**  In odd degree the residue degree `f` is odd, so the mod-two
shadow of `ν_ur` restricted to `G_K` *is* the mod-two shadow of `ν_ur^K`. -/
theorem redTwo_nuUr_restrict (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) (g : GalK K) :
    MarkedFrame.redTwo (Multiplicative.toAdd (R.nu_ur (toAb (g : AbsGalQ2))))
      = MarkedFrame.redTwo (Multiplicative.toAdd (B.nu_ur (toAbK K g))) := by
  have hf : Odd FF.f := by
    rw [SpectralLocalField.field_finrank_eq_e_mul_f (K := K) (FF := FF)] at hodd
    exact (Nat.odd_mul.mp hodd).2
  rw [← inclAbK_toAbK K g, toAdd_nuUr_incl B FF (toAbK K g), map_mul,
    redTwo_natCast_of_odd hf, one_mul]

end Descent

/-! ## §4 The base case at `ℚ₂`

`L = ℚ₂(√−3)` is the unramified quadratic layer.  B5 clause (a) identifies the kernel of
`rec` followed by restriction to `L` with the norm group `N(Lˣ)`; §2 (at the odd-degree field
`⊥`) shows every norm from `L` has even valuation, and that inclusion of kernels is already
enough: two characters of `ℚ₂ˣ` into the two-element group with one kernel inside the other, the
larger one missing the uniformizer, are equal. -/

section BaseCase

open IntermediateField

/-- The quadratic layer `ℚ₂(√−3) ⊂ ℚ̄₂`. -/
abbrev layer (δ : ℚ̄₂) : IntermediateField ℚ_[2] ℚ̄₂ := IntermediateField.adjoin ℚ_[2] {δ}

theorem isIntegral_of_algClosure (δ : ℚ̄₂) : IsIntegral ℚ_[2] δ :=
  Algebra.IsIntegral.isIntegral δ

instance finiteDimensional_layer (δ : ℚ̄₂) : FiniteDimensional ℚ_[2] ↥(layer δ) :=
  IntermediateField.adjoin.finiteDimensional (isIntegral_of_algClosure δ)

/-- The minimal polynomial of a square root of `−3` over `ℚ₂` is quadratic. -/
theorem minpoly_natDegree_sqrt_neg_three {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) :
    (minpoly ℚ_[2] δ).natDegree = 2 := by
  have hint : IsIntegral ℚ_[2] δ := isIntegral_of_algClosure δ
  have hdvd : minpoly ℚ_[2] δ ∣ (Polynomial.X ^ 2 + Polynomial.C 3 : Polynomial ℚ_[2]) := by
    apply minpoly.dvd
    simp only [map_add, map_pow, Polynomial.aeval_X, hδ, map_ofNat]
    ring
  have hpne : (Polynomial.X ^ 2 + Polynomial.C 3 : Polynomial ℚ_[2]) ≠ 0 := by
    intro h
    have := congrArg (fun p => Polynomial.coeff p 2) h
    simp at this
  have hle : (minpoly ℚ_[2] δ).natDegree ≤ 2 := by
    have hd := Polynomial.natDegree_le_of_dvd hdvd hpne
    have : (Polynomial.X ^ 2 + Polynomial.C 3 : Polynomial ℚ_[2]).natDegree = 2 := by
      compute_degree!
    omega
  have hne1 : (minpoly ℚ_[2] δ).natDegree ≠ 1 := by
    intro h1
    have hmem : δ ∈ (⊥ : IntermediateField ℚ_[2] ℚ̄₂) := by
      apply IntermediateField.finrank_adjoin_simple_eq_one_iff.mp
      rw [IntermediateField.adjoin.finrank hint, h1]
    obtain ⟨w, hw⟩ := IntermediateField.mem_bot.mp hmem
    refine sq_ne_neg_three_padic w ?_
    have hcast : algebraMap ℚ_[2] ℚ̄₂ (w ^ 2) = algebraMap ℚ_[2] ℚ̄₂ (-3) := by
      rw [map_pow, hw, hδ, map_neg, map_ofNat]
    exact (algebraMap ℚ_[2] ℚ̄₂).injective hcast
  have hne0 : (minpoly ℚ_[2] δ).natDegree ≠ 0 := by
    have := minpoly.natDegree_pos hint
    omega
  omega

theorem finrank_layer {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) : Module.finrank ℚ_[2] ↥(layer δ) = 2 := by
  rw [IntermediateField.adjoin.finrank (isIntegral_of_algClosure δ),
    minpoly_natDegree_sqrt_neg_three hδ]

/-- **Coordinates over the base**: every element of `ℚ₂(√−3)` is `a + b√−3` with `a, b ∈ ℚ₂`
(the `k = ℚ₂` port of `UnramifiedQuadraticNorms.exists_coords`). -/
theorem exists_coords_base {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) {z : ℚ̄₂} (hz : z ∈ layer δ) :
    ∃ a b : ℚ_[2], z = algebraMap ℚ_[2] ℚ̄₂ a + algebraMap ℚ_[2] ℚ̄₂ b * δ := by
  have hint : IsIntegral ℚ_[2] δ := isIntegral_of_algClosure δ
  have hqdeg : (minpoly ℚ_[2] δ).natDegree = 2 := minpoly_natDegree_sqrt_neg_three hδ
  have hzalg : z ∈ Algebra.adjoin ℚ_[2] ({δ} : Set ℚ̄₂) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[2]) δ)]
    exact hz
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hzalg
  obtain ⟨p, hp⟩ := hzalg
  have hmne1 : minpoly ℚ_[2] δ ≠ 1 := by
    intro h; rw [h, Polynomial.natDegree_one] at hqdeg; exact absurd hqdeg (by norm_num)
  set r := p %ₘ minpoly ℚ_[2] δ with hr
  have hzr : (Polynomial.aeval δ) r = z := by
    have hsplit : r + minpoly ℚ_[2] δ * (p /ₘ minpoly ℚ_[2] δ) = p :=
      Polynomial.modByMonic_add_div p (minpoly ℚ_[2] δ)
    calc (Polynomial.aeval δ) r
        = (Polynomial.aeval δ) r + (Polynomial.aeval δ) (minpoly ℚ_[2] δ)
            * (Polynomial.aeval δ) (p /ₘ minpoly ℚ_[2] δ) := by
          rw [minpoly.aeval, zero_mul, add_zero]
      _ = (Polynomial.aeval δ) p := by rw [← map_mul, ← map_add, hsplit]
      _ = z := hp
  have hrdeg : r.natDegree ≤ 1 := by
    have hlt : r.natDegree < (minpoly ℚ_[2] δ).natDegree :=
      Polynomial.natDegree_modByMonic_lt p (minpoly.monic hint) hmne1
    omega
  refine ⟨r.coeff 0, r.coeff 1, ?_⟩
  rw [← hzr, Polynomial.aeval_eq_sum_range' (n := 2) (by omega) δ,
    Finset.sum_range_succ, Finset.sum_range_one]
  simp [Algebra.smul_def]

/-- **The layer is unramified over `ℚ₂`**, in the norm form §2 supplies at the odd-degree
field `⊥`: every nonzero element of `ℚ₂(√−3)` has the norm of a nonzero element of `ℚ₂`. -/
theorem exists_padic_norm_eq {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) {z : ℚ̄₂} (hz : z ∈ layer δ)
    (hz0 : z ≠ 0) : ∃ w : ℚ_[2], w ≠ 0 ∧ ‖z‖ = ‖w‖ := by
  obtain ⟨a, b, rfl⟩ := exists_coords_base hδ hz
  have hbot : Odd (Module.finrank ℚ_[2] ↥(⊥ : IntermediateField ℚ_[2] ℚ̄₂)) := by
    rw [IntermediateField.finrank_bot]; exact odd_one
  obtain ⟨w, hw0, hw⟩ := hasEqualNormValueGroups_of_sq_eq_neg_three hbot hδ _ hz0
    ⟨⟨algebraMap ℚ_[2] ℚ̄₂ a, IntermediateField.algebraMap_mem _ a⟩,
      ⟨algebraMap ℚ_[2] ℚ̄₂ b, IntermediateField.algebraMap_mem _ b⟩, rfl⟩
  obtain ⟨w', hw'⟩ := IntermediateField.mem_bot.mp w.2
  refine ⟨w', ?_, ?_⟩
  · intro h
    refine hw0 (Subtype.ext ?_)
    rw [← hw', h, map_zero]
    rfl
  · rw [hw, ← hw', norm_algebraMap' (𝕜' := ℚ̄₂)]

/-- **Norms from the layer have even valuation.**  `‖N y‖ = ‖y‖²` and `‖y‖ = ‖w‖` for a `w ∈ ℚ₂`,
so `v₂(N y) = 2 v₂(w)`. -/
theorem even_v2_of_mem_normSubgroup {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) {x : ℚ_[2]ˣ}
    (hx : x ∈ normSubgroup (layer δ)) : Even (v2 x) := by
  obtain ⟨y, rfl⟩ := hx
  have hy0 : ((y : ↥(layer δ)) : ℚ̄₂) ≠ 0 := fun h => (Units.ne_zero y) (by exact_mod_cast h)
  obtain ⟨w, hw0, hw⟩ := exists_padic_norm_eq hδ (SetLike.coe_mem (y : ↥(layer δ))) hy0
  have hN0 : (Algebra.norm ℚ_[2] ((y : ↥(layer δ))) : ℚ_[2]) ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr (Units.ne_zero y)
  have hnorm : ((2 : ℕ) : ℝ) ^ (-(Algebra.norm ℚ_[2] ((y : ↥(layer δ)))).valuation)
      = (((2 : ℕ) : ℝ) ^ (-w.valuation)) ^ (2 : ℕ) := by
    rw [← Padic.norm_eq_zpow_neg_valuation hN0, ← Padic.norm_eq_zpow_neg_valuation hw0,
      norm_algebra_eq_norm_pow_finrank (layer δ) (y : ↥(layer δ)), finrank_layer hδ, hw]
  rw [← zpow_natCast (((2 : ℕ) : ℝ) ^ (-w.valuation)) 2, ← zpow_mul] at hnorm
  have hexp := zpow_right_injective₀ (by norm_num : (0 : ℝ) < ((2 : ℕ) : ℝ))
    (by norm_num : ((2 : ℕ) : ℝ) ≠ 1) hnorm
  push_cast at hexp
  refine ⟨w.valuation, ?_⟩
  show (Algebra.norm ℚ_[2] ((y : ↥(layer δ)))).valuation = _
  linarith

/-! ### The Kummer character of `−3` and its kernel -/

/-- `δ² = −3` in the `algebraMap`-of-a-unit shape the Kummer API consumes. -/
theorem sq_eq_algebraMap_uNeg3 {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) :
    δ ^ 2 = algebraMap ℚ_[2] ℚ̄₂ ((uNeg3 : ℚ_[2]ˣ) : ℚ_[2]) := by
  rw [hδ]
  show (-3 : ℚ̄₂) = algebraMap ℚ_[2] ℚ̄₂ (-3)
  rw [map_neg, map_ofNat]

/-- **The Kummer character `[−3] : G_{ℚ₂} → 𝔽₂`**, as a monoid homomorphism. -/
def kummerNegThree {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) : AbsGalQ2 →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (Kummer.kummerCocycleFun δ g)
  map_one' := congrArg Multiplicative.ofAdd (Kummer.kummerCocycleFun_eq0 (one_smul _ δ))
  map_mul' _ _ := congrArg Multiplicative.ofAdd
    (Kummer.kummerCocycleFun_hom (sq_eq_algebraMap_uNeg3 hδ) _ _)

@[simp] theorem kummerNegThree_apply {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) (g : AbsGalQ2) :
    Multiplicative.toAdd (kummerNegThree hδ g) = Kummer.kummerCocycleFun δ g := rfl

theorem continuous_kummerNegThree {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) : Continuous (kummerNegThree hδ) :=
  continuous_ofAdd.comp (Kummer.kummerCocycleFun_continuous δ)

/-- The Kummer cocycle vanishes exactly on the stabilizer of the chosen root. -/
theorem kummerCocycleFun_eq_zero_iff (δ : ℚ̄₂) (g : Kummer.GaloisGroup ℚ_[2]) :
    Kummer.kummerCocycleFun δ g = 0 ↔ g ∈ MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ := by
  rw [MulAction.mem_stabilizer_iff]
  simp [Kummer.kummerCocycleFun]

/-- The kernel of `[−3]` is the fixing subgroup of the layer. -/
theorem ker_kummerNegThree {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) :
    ((kummerNegThree hδ).ker : Subgroup AbsGalQ2) = (layer δ).fixingSubgroup := by
  ext g
  have hiff : g ∈ (kummerNegThree hδ).ker ↔ Kummer.kummerCocycleFun δ g = 0 := by
    rw [MonoidHom.mem_ker]
    exact ofAdd_eq_one
  rw [hiff, GQ2.QuadraticAdjoin.fixingSubgroup_adjoin_simple]
  exact kummerCocycleFun_eq_zero_iff δ g

/-- The layer is a Galois extension of `ℚ₂`: its fixing subgroup is the (open, normal) kernel
of `[−3]`. -/
theorem isGalois_layer {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) : IsGalois ℚ_[2] ↥(layer δ) := by
  have hnormal : (layer δ).fixingSubgroup.Normal := by
    rw [← ker_kummerNegThree hδ]
    exact MonoidHom.normal_ker _
  exact ((InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois (layer δ)).mp
    ⟨IntermediateField.fixingSubgroup_isOpen (layer δ), hnormal⟩).2

/-- Restriction to the layer kills `[−3]`'s kernel. -/
theorem restrictHom_layer_eq_one {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) [IsGalois ℚ_[2] ↥(layer δ)]
    (u : AbsGalQ2) (hu : kummerNegThree hδ u = 1) : restrictHom (layer δ) u = 1 := by
  have hu' : u ∈ (kummerNegThree hδ).ker := hu
  rw [ker_kummerNegThree hδ, ← IntermediateField.restrictNormalHom_ker (layer δ)] at hu'
  exact hu'

/-- The restriction of `G_{ℚ₂}` to the layer has abelian image: `[−3]`'s kernel contains every
commutator, and it *is* the kernel of the restriction. -/
theorem restrictHom_layer_comm {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) [IsGalois ℚ_[2] ↥(layer δ)]
    (g h : AbsGalQ2) :
    restrictHom (layer δ) g * restrictHom (layer δ) h
      = restrictHom (layer δ) h * restrictHom (layer δ) g := by
  have hcomm : kummerNegThree hδ (g * h * (h * g)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul,
      mul_comm (kummerNegThree hδ h) (kummerNegThree hδ g), mul_inv_cancel]
  have h1 := restrictHom_layer_eq_one hδ _ hcomm
  rw [map_mul, map_inv, map_mul, map_mul, mul_inv_eq_one] at h1
  exact h1

/-- `Gal(L/ℚ₂)` is abelian. -/
theorem comm_layer {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) :
    ∀ σ τ : (↥(layer δ) ≃ₐ[ℚ_[2]] ↥(layer δ)), σ * τ = τ * σ := by
  haveI := isGalois_layer hδ
  intro σ τ
  obtain ⟨g, rfl⟩ :=
    AlgEquiv.restrictNormalHom_surjective (F := ℚ_[2]) (K₁ := ↥(layer δ)) (E := ℚ̄₂) σ
  obtain ⟨h, rfl⟩ :=
    AlgEquiv.restrictNormalHom_surjective (F := ℚ_[2]) (K₁ := ↥(layer δ)) (E := ℚ̄₂) τ
  exact restrictHom_layer_comm hδ g h

/-! ### The two characters of `ℚ₂ˣ` -/

/-- Mod-two reduction of an integer, read through `ℤ₂`. -/
theorem redTwo_intCast_eq_zero_iff (n : ℤ) : MarkedFrame.redTwo ((n : ℤ) : ℤ_[2]) = 0 ↔ Even n := by
  show (PadicInt.toZModPow (p := 2) 1) ((n : ℤ) : ℤ_[2]) = 0 ↔ _
  rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd n 2]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by push_cast at hk; omega⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by push_cast; omega⟩

/-- **The `ν̄` side.**  `ν̄(rec x) = 0` exactly when `v₂(x)` is even. -/
theorem nuBar_recip_eq_one_iff (R : LocalReciprocity) (x : ℚ_[2]ˣ) :
    MarkedFrame.redTwoChar (R.nu_ur (R.recip x)) = 1 ↔ Even (v2 x) := by
  rw [R.nu_ur_recip]
  show Multiplicative.ofAdd (MarkedFrame.redTwo ((-(v2 x) : ℤ) : ℤ_[2])) = 1 ↔ _
  rw [ofAdd_eq_one, redTwo_intCast_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨-k, by omega⟩
  · rintro ⟨k, hk⟩; exact ⟨-k, by omega⟩

/-- `[−3]` kills the closed commutator subgroup (Hausdorff abelian target), so it factors through
`G_{ℚ₂}^{ab}`. -/
theorem commClosure_le_ker_kummerNegThree {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) :
    commClosure ≤ (kummerNegThree hδ).ker := by
  apply Subgroup.topologicalClosure_minimal _
    (Abelianization.commutator_subset_ker (kummerNegThree hδ))
  rw [MonoidHom.coe_ker]
  exact isClosed_singleton.preimage (continuous_kummerNegThree hδ)

/-- `[−3]` as a character of `G_{ℚ₂}^{ab}`. -/
def kummerNegThreeAb {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) : AbsGalQ2ab →* Multiplicative (ZMod 2) :=
  QuotientGroup.lift commClosure (kummerNegThree hδ)
    (fun _ hx => MonoidHom.mem_ker.mp (commClosure_le_ker_kummerNegThree hδ hx))

@[simp] theorem kummerNegThreeAb_toAb {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) (g : AbsGalQ2) :
    kummerNegThreeAb hδ (toAb g) = kummerNegThree hδ g := rfl

theorem continuous_kummerNegThreeAb {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) :
    Continuous (kummerNegThreeAb hδ) :=
  continuous_quot_lift _ (continuous_kummerNegThree hδ)

/-- `[−3](g) = 0` exactly when `g` restricts trivially to the layer. -/
theorem kummerNegThree_eq_one_iff_restrict {δ : ℚ̄₂} (hδ : δ ^ 2 = -3)
    [IsGalois ℚ_[2] ↥(layer δ)] (g : AbsGalQ2) :
    kummerNegThree hδ g = 1 ↔ restrictHom (layer δ) g = 1 := by
  refine ⟨restrictHom_layer_eq_one hδ g, fun hg => ?_⟩
  have hg' : g ∈ (AlgEquiv.restrictNormalHom (↥(layer δ))).ker := hg
  rw [IntermediateField.restrictNormalHom_ker (layer δ), ← ker_kummerNegThree hδ] at hg'
  exact hg'

/-- **B5 clause (a) at the layer.**  `[−3](rec x) = 0` exactly when `x` is a norm from
`ℚ₂(√−3)`. -/
theorem kummerNegThreeAb_recip_eq_one_iff {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) (R : LocalReciprocity)
    (x : ℚ_[2]ˣ) :
    kummerNegThreeAb hδ (R.recip x) = 1 ↔ x ∈ normSubgroup (layer δ) := by
  haveI := isGalois_layer hδ
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective commClosure (R.recip x)
  have hkey : kummerNegThreeAb hδ (R.recip x) = 1 ↔
      restrictAb (layer δ) (comm_layer hδ) (R.recip x) = 1 := by
    rw [← hg]
    exact kummerNegThree_eq_one_iff_restrict hδ g
  rw [hkey, ← (R.norm_reciprocity (layer δ) (comm_layer hδ)).2]
  exact MonoidHom.mem_ker.symm

/-- A `𝔽₂`-character value is determined by being nontrivial. -/
theorem eq_of_ne_one (a b : Multiplicative (ZMod 2)) (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  revert ha hb
  revert a b
  decide

/-- **The base identification.**  `ν̄ = [−3]` as characters of `G_{ℚ₂}^{ab}`: on the dense
`rec`-image both vanish exactly on the even-valuation subgroup. -/
theorem nuBar_eq_kummerNegThreeAb {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) (R : LocalReciprocity)
    (a : AbsGalQ2ab) :
    MarkedFrame.redTwoChar (R.nu_ur a) = kummerNegThreeAb hδ a := by
  have hsub : ∀ x : ℚ_[2]ˣ, kummerNegThreeAb hδ (R.recip x) = 1 → Even (v2 x) := fun x hx =>
    even_v2_of_mem_normSubgroup hδ ((kummerNegThreeAb_recip_eq_one_iff hδ R x).mp hx)
  have hodd2 : ¬ Even (v2 uniformizer) := by
    rw [UnitNormIndex.v2_uniformizer]
    rintro ⟨k, hk⟩
    omega
  have hk2 : kummerNegThreeAb hδ (R.recip uniformizer) ≠ 1 := fun h => hodd2 (hsub _ h)
  have hval : ∀ x : ℚ_[2]ˣ,
      MarkedFrame.redTwoChar (R.nu_ur (R.recip x)) = kummerNegThreeAb hδ (R.recip x) := by
    intro x
    by_cases hx : kummerNegThreeAb hδ (R.recip x) = 1
    · rw [hx, nuBar_recip_eq_one_iff]
      exact hsub x hx
    · have hnotev : ¬ Even (v2 x) := by
        intro hev
        have heq : kummerNegThreeAb hδ (R.recip x)
            = kummerNegThreeAb hδ (R.recip uniformizer) := eq_of_ne_one _ _ hx hk2
        have hone : kummerNegThreeAb hδ (R.recip (x * uniformizer⁻¹)) = 1 := by
          rw [map_mul R.recip, map_inv R.recip, map_mul (kummerNegThreeAb hδ),
            map_inv (kummerNegThreeAb hδ), heq, mul_inv_cancel]
        have hev2 := hsub _ hone
        rw [UnitNormIndex.v2_mul, UnitNormIndex.v2_inv, UnitNormIndex.v2_uniformizer] at hev2
        obtain ⟨j, hj⟩ := hev
        obtain ⟨k, hk⟩ := hev2
        omega
      have hnn : MarkedFrame.redTwoChar (R.nu_ur (R.recip x)) ≠ 1 := fun hcon =>
        hnotev ((nuBar_recip_eq_one_iff R x).mp hcon)
      exact eq_of_ne_one _ _ hnn hx
  have hext : (fun a : AbsGalQ2ab => MarkedFrame.redTwoChar (R.nu_ur a))
      = fun a : AbsGalQ2ab => kummerNegThreeAb hδ a :=
    Continuous.ext_on R.denseRange_recip
      ((map_continuous MarkedFrame.redTwoChar).comp R.continuous_nu_ur)
      (continuous_kummerNegThreeAb hδ) (by rintro _ ⟨x, rfl⟩; exact hval x)
  exact congrFun hext a

/-- **The base case, pointwise.**  The mod-two unramified character of `G_{ℚ₂}` is the Kummer
cocycle of `−3`. -/
theorem redTwo_nuUr_eq_kummerCocycle {δ : ℚ̄₂} (hδ : δ ^ 2 = -3) (R : LocalReciprocity)
    (g : AbsGalQ2) :
    MarkedFrame.redTwo (Multiplicative.toAdd (R.nu_ur (toAb g)))
      = Kummer.kummerCocycleFun δ g := by
  have h := congrArg Multiplicative.toAdd (nuBar_eq_kummerNegThreeAb hδ R (toAb g))
  simpa using h

end BaseCase

/-! ## §5 The identification, and the cup value it discharges -/

section Assembly

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- `−3` as a unit of `K`. -/
def negThreeUnit (K : IntermediateField ℚ_[2] ℚ̄₂) : (↥K)ˣ :=
  Units.mk0 (-3 : ↥K) (by norm_num)

theorem negThreeUnit_coe (K : IntermediateField ℚ_[2] ℚ̄₂) :
    (((negThreeUnit K : (↥K)ˣ) : ↥K) : ℚ̄₂) = -3 := by
  show ((-3 : ↥K) : ℚ̄₂) = -3
  rw [show ((-3 : ↥K) : ℚ̄₂) = algebraMap (↥K) ℚ̄₂ (-3) from rfl, map_neg, map_ofNat]

theorem sq_sqrtCl_negThreeUnit (K : IntermediateField ℚ_[2] ℚ̄₂) :
    (sqrtCl (((negThreeUnit K : (↥K)ˣ) : ↥K) : ℚ̄₂)) ^ 2 = -3 := by
  rw [sqrtCl_sq, negThreeUnit_coe]

/-- **The residual `Prop` of `GammaLUnramifiedHilbertValue` §3, discharged.**  For every
odd-degree `K` the mod-two unramified class of a marked bundle is the Kummer class of `−3`,
whose square root generates the unramified quadratic extension of `K`. -/
theorem nuUrUnramifiedKummerClass_of_odd (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) : MarkedFrame.NuUrUnramifiedKummerClass B := by
  have hδ3 : (sqrtCl (((negThreeUnit K : (↥K)ˣ) : ↥K) : ℚ̄₂)) ^ 2 = -3 :=
    sq_sqrtCl_negThreeUnit K
  refine ⟨negThreeUnit K, sqrtCl (((negThreeUnit K : (↥K)ˣ) : ↥K) : ℚ̄₂), sqrtCl_sq _,
    hasEqualNormValueGroups_of_sq_eq_neg_three hodd hδ3, ?_⟩
  rw [h1MaxProTwoEquivGalK_apply]
  unfold MarkedFrame.nuUrModTwoClassKTwo SqCyclotomicFrattiniFrame.characterClass kummerClassK
  rw [inf1_H1mk]
  congr 1
  apply Subtype.ext
  funext g
  show MarkedFrame.redTwo (Multiplicative.toAdd (nuUrKTwo B (maxProPMk 2 (GalK K) g)))
      = Kummer.kummerCocycleFun _ _
  rw [nuUrKTwo_maxProPMk]
  exact (redTwo_nuUr_restrict B (dyadicUnitFiltration K) hodd g).symm.trans
    (redTwo_nuUr_eq_kummerCocycle hδ3 R (g : AbsGalQ2))

/-- **The `𝔽₂` cup value `b_K([2], ν̄) = 1`, unconditionally in odd degree at the level-`L` row.**
This closes the `ν`-side residual of the marked Frattini frame. -/
theorem nuUrOmegaCupOne_of_odd (B : MarkedRecip R K) (hodd : Odd (Module.finrank ℚ_[2] K))
    (hr : B.r = 0) : MarkedFrame.NuUrOmegaCupOne B :=
  MarkedFrame.nuUrOmegaCupOne_of_nuUrUnramifiedKummerClass B hodd hr
    (nuUrUnramifiedKummerClass_of_odd B hodd)

/-- **The `ν`-side collapsed.**  `oddDegreeGalKSqMarkedForwardSupply` with its cup hypothesis
discharged: the marked forward supply now costs only the stage-lane residual
`SqCupAdaptedFramePresentation K`. -/
theorem sqMarkedForwardSupply_of_presentation (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) (hr : B.r = 0)
    (hpres : MarkedFrame.SqCupAdaptedFramePresentation K) :
    SqMarkedForwardSupply B ((Module.finrank ℚ_[2] K - 1) / 2) :=
  MarkedFrame.oddDegreeGalKSqMarkedForwardSupply B hodd hr
    (nuUrOmegaCupOne_of_odd B hodd hr) hpres

/-- The `L`-row marked-core certificate over the single remaining residual. -/
theorem nonempty_markedCoreCertificate_of_presentation (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) (hr : B.r = 0) (c : ℤ_[2])
    (hMix : SqCore.SqHandleMixFixesCore ((Module.finrank ℚ_[2] K - 1) / 2) c)
    (hpres : MarkedFrame.SqCupAdaptedFramePresentation K) :
    Nonempty (MarkedCoreCertificateKTwoSq B ((Module.finrank ℚ_[2] K - 1) / 2)) :=
  MarkedFrame.nonempty_markedCoreCertificate_of_cupOne_of_presentation B hodd hr c hMix
    (nuUrOmegaCupOne_of_odd B hodd hr) hpres

end Assembly

end NuKummer

end

#print axioms NuKummer.sq_ne_neg_three_padic
#print axioms NuKummer.sq_ne_neg_three_of_odd
#print axioms NuKummer.notMem_of_sq_eq_neg_three
#print axioms NuKummer.norm_cubeCyclotomic_eq_one
#print axioms NuKummer.exists_norm_sq_eq_sq_add_three
#print axioms NuKummer.hasEqualNormValueGroups_of_sq_eq_neg_three
#print axioms NuKummer.e_mul_val_norm_of_finrank
#print axioms NuKummer.nuUrK_recip_eq
#print axioms NuKummer.nuUrQ_incl_recip_eq
#print axioms NuKummer.toAdd_nuUr_incl
#print axioms NuKummer.redTwo_nuUr_restrict
#print axioms NuKummer.minpoly_natDegree_sqrt_neg_three
#print axioms NuKummer.exists_coords_base
#print axioms NuKummer.exists_padic_norm_eq
#print axioms NuKummer.even_v2_of_mem_normSubgroup
#print axioms NuKummer.ker_kummerNegThree
#print axioms NuKummer.isGalois_layer
#print axioms NuKummer.comm_layer
#print axioms NuKummer.kummerNegThreeAb_recip_eq_one_iff
#print axioms NuKummer.nuBar_eq_kummerNegThreeAb
#print axioms NuKummer.redTwo_nuUr_eq_kummerCocycle
#print axioms NuKummer.nuUrUnramifiedKummerClass_of_odd
#print axioms NuKummer.nuUrOmegaCupOne_of_odd
#print axioms NuKummer.sqMarkedForwardSupply_of_presentation
#print axioms NuKummer.nonempty_markedCoreCertificate_of_presentation

end GQ2.Dyadic.LSquare
