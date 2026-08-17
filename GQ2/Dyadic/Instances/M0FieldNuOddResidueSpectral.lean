/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/

import GQ2.Dyadic.Instances.M0FieldNuOddResidue
import GQ2.Dyadic.RamificationInertiaBridge

/-!
# The unramified square class in odd residue degree

For a dyadic field with odd residue degree, the finite residue field has cardinality
`2^f` with odd `f`, so it has no nontrivial cube root of unity.  Reducing `c^2+c+1` proves
the norm-one identity needed by the explicit `K(√-3)` value-group calculation.  This replaces
the older odd-total-degree premise by its sharp residue-degree premise and closes the selected
compact-M unramified-character input.
-/

namespace GQ2.Dyadic.LSquare.NuKummer

noncomputable section

open GQ2
open GQ2.Dyadic.SpectralLocalField

variable {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])}
  [FiniteDimensional ℚ_[2] K]

theorem norm_cubeCyclotomic_eq_one_of_odd_residueDegree
    (FF : DyadicUnitFiltration K) (hf : Odd FF.f) {c : K}
    (hc : ‖c‖ = 1) : ‖c ^ 2 + c + 1‖ = 1 := by
  letI := normValuation_hasExtension K
  letI := integer_finite K
  let O := ExtensionInteger K
  let k := IsLocalRing.ResidueField O
  have hbaseFinite : Finite (IsLocalRing.ResidueField BaseInteger) :=
    Finite.of_injective baseIntegerResidueEquivZMod baseIntegerResidueEquivZMod.injective
  letI : Finite (IsLocalRing.ResidueField BaseInteger) := hbaseFinite
  letI : Finite k := IsLocalRing.ResidueField.finite_of_finite
    (R := BaseInteger) (S := O) hbaseFinite
  letI : Fintype k := Fintype.ofFinite k
  have hkcard : Fintype.card k = 2 ^ FF.f := by
    rw [← Nat.card_eq_fintype_card]
    exact normInteger_residueField_card_eq_pow_f K FF
  letI : CharP k 2 := charP_of_card_eq_prime_pow hkcard
  have hle : ‖c ^ 2 + c + 1‖ ≤ 1 := by
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ (le_of_eq norm_one))
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ (le_of_eq hc))
    rw [norm_pow, hc, one_pow]
  rcases eq_or_lt_of_le hle with h | hlt
  · exact h
  exfalso
  let cO : O := ⟨c, by
    change ‖c‖₊ ≤ 1
    exact_mod_cast hc.le⟩
  let r : k := IsLocalRing.residue O cO
  have hrpoly : r ^ 2 + r + 1 = 0 := by
    change IsLocalRing.residue O (cO ^ 2 + cO + 1) = 0
    rw [IsLocalRing.residue_eq_zero_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    change ‖c ^ 2 + c + 1‖₊ < 1
    exact_mod_cast hlt
  have hr3 : r ^ 3 = 1 := by
    linear_combination (r - 1) * hrpoly
  have hrne : r ≠ 1 := by
    intro hr
    rw [hr] at hrpoly
    have hrpoly' : (3 : k) = 0 := by
      calc
        (3 : k) = 1 ^ 2 + 1 + 1 := by norm_num
        _ = 0 := hrpoly
    have hthree : (3 : k) = 1 := by
      have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
      calc
        (3 : k) = (2 : k) + 1 := by norm_num
        _ = 0 + 1 := congrArg (fun z : k ↦ z + 1) htwo
        _ = 1 := zero_add 1
    exact one_ne_zero (hthree.symm.trans hrpoly')
  have hr0 : r ≠ 0 := by
    intro hr
    rw [hr, zero_pow (by omega : 3 ≠ 0)] at hr3
    exact zero_ne_one hr3
  let u : kˣ := Units.mk0 r hr0
  have hu3 : u ^ 3 = 1 := by
    apply Units.ext
    exact hr3
  have hune : u ≠ 1 := by
    intro hu
    exact hrne (congrArg Units.val hu)
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hune
  have hdvd : 3 ∣ Nat.card kˣ := by
    rw [← hord]
    exact orderOf_dvd_natCard u
  rw [Nat.card_units, normInteger_residueField_card_eq_pow_f K FF] at hdvd
  obtain ⟨j, hj⟩ := hf
  have hmod : 2 ^ FF.f % 3 = 2 := by
    rw [hj, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  obtain ⟨d, hd⟩ := hdvd
  have hdecomp := Nat.mod_add_div (2 ^ FF.f) 3
  rw [hmod] at hdecomp
  omega

theorem exists_norm_sq_eq_sq_add_three_of_odd_residueDegree
    (FF : DyadicUnitFiltration K) (hf : Odd FF.f) {t : K}
    (ht : ‖t‖ = 1) : ∃ w : K, w ≠ 0 ∧ ‖t ^ 2 + 3‖ = ‖w‖ ^ 2 := by
  have h2lt : ‖(2 : K)‖ < 1 := GQ2.norm_two_lt_one'
  have h2pos : (0 : ℝ) < ‖(2 : K)‖ := norm_pos_iff.mpr two_ne_zero
  have h4 : ‖(4 : K)‖ = ‖(2 : K)‖ ^ 2 := by
    rw [show (4 : K) = 2 * 2 by norm_num, norm_mul, sq]
  set s : K := t - 1 with hs
  have hsle : ‖s‖ ≤ 1 := by
    rw [hs, sub_eq_add_neg]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _)
      (max_le (le_of_eq ht) ?_)
    rw [norm_neg, norm_one]
  rcases eq_or_lt_of_le hsle with hs1 | hslt
  · refine ⟨1, one_ne_zero, ?_⟩
    have hfac : t ^ 2 + 3 = s * (s + 2) + 4 := by rw [hs]; ring
    have hs2 : ‖s + 2‖ = ‖s‖ :=
      norm_add_of_norm_lt (by rw [hs1]; exact h2lt)
    have hprod : ‖s * (s + 2)‖ = 1 := by
      rw [norm_mul, hs2, hs1, one_mul]
    rw [hfac, norm_add_of_norm_lt (a := s * (s + 2)) (b := (4 : K))
      (by rw [hprod, h4]; nlinarith), hprod, norm_one, one_pow]
  · have hexp : t ^ 2 + 3 = s ^ 2 + 2 * s + 4 := by rw [hs]; ring
    rcases lt_trichotomy ‖s‖ ‖(2 : K)‖ with hcase | hcase | hcase
    · refine ⟨2, two_ne_zero, ?_⟩
      have hsmall : ‖s ^ 2 + 2 * s‖ < ‖(4 : K)‖ := by
        refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
          (max_lt ?_ ?_)
        · rw [norm_pow, h4]
          nlinarith [norm_nonneg s]
        · rw [norm_mul, h4]
          nlinarith
      rw [hexp, show s ^ 2 + 2 * s + 4 = (4 : K) + (s ^ 2 + 2 * s) by ring,
        norm_add_of_norm_lt hsmall, h4]
    · refine ⟨2, two_ne_zero, ?_⟩
      set c : K := s / 2 with hcdef
      have hcnorm : ‖c‖ = 1 := by
        rw [hcdef, norm_div, hcase, div_self (ne_of_gt h2pos)]
      have hcube : ‖c ^ 2 + c + 1‖ = 1 :=
        norm_cubeCyclotomic_eq_one_of_odd_residueDegree FF hf hcnorm
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
          refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
            (max_lt ?_ ?_)
          · rw [norm_mul]
            nlinarith
          · rw [h4]
            nlinarith
        rw [hexp, show s ^ 2 + 2 * s + 4 = s ^ 2 + (2 * s + 4) by ring,
          norm_add_of_norm_lt hsmall, norm_pow]

theorem hasEqualNormValueGroups_of_sq_eq_neg_three_of_odd_residueDegree
    (FF : DyadicUnitFiltration K) (hf : Odd FF.f)
    {δ : AlgebraicClosure ℚ_[2]} (hδ : δ ^ 2 = -3) :
    HasEqualNormValueGroups K δ := by
  by_cases hδK : δ ∈ K
  · rintro z hz0 ⟨x, y, rfl⟩
    let d : K := ⟨δ, hδK⟩
    refine ⟨x + y * d, ?_, rfl⟩
    intro hw
    apply hz0
    have hw' := congrArg (fun w : K ↦ (w : AlgebraicClosure ℚ_[2])) hw
    simpa [d] using hw'
  have hδnorm : ‖δ‖ = 1 := norm_eq_one_of_sq_eq_neg_three hδ
  have hδcoe : δ ^ 2 = (((-3 : K) : K) : AlgebraicClosure ℚ_[2]) := by
    rw [hδ, show ((-3 : K) : AlgebraicClosure ℚ_[2]) =
      algebraMap K (AlgebraicClosure ℚ_[2]) (-3) from rfl, map_neg, map_ofNat]
  obtain ⟨σ, hσ⟩ := UnramifiedQuadraticNorms.exists_conj hδcoe hδK
  rintro z hz0 ⟨x, y, rfl⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · refine ⟨x, ?_, by rw [ZeroMemClass.coe_zero, zero_mul, add_zero]⟩
    intro h
    exact hz0 (by rw [h, ZeroMemClass.coe_zero, zero_mul, add_zero])
  have hycoe : ((y : K) : AlgebraicClosure ℚ_[2]) ≠ 0 :=
    fun h ↦ hy0 (by exact_mod_cast h)
  rcases eq_or_ne x 0 with rfl | hx0
  · refine ⟨y, hy0, ?_⟩
    rw [ZeroMemClass.coe_zero, zero_add, norm_mul, hδnorm, mul_one]
  have hxcoe : ((x : K) : AlgebraicClosure ℚ_[2]) ≠ 0 :=
    fun h ↦ hx0 (by exact_mod_cast h)
  rcases eq_or_ne ‖((x : K) : AlgebraicClosure ℚ_[2])‖
    ‖((y : K) : AlgebraicClosure ℚ_[2])‖ with heq | hne
  · set t : K := x / y with hts
    have htnorm : ‖t‖ = 1 := by
      show ‖((x / y : K) : AlgebraicClosure ℚ_[2])‖ = 1
      rw [show ((x / y : K) : AlgebraicClosure ℚ_[2]) =
        ((x : K) : AlgebraicClosure ℚ_[2]) /
          ((y : K) : AlgebraicClosure ℚ_[2]) from rfl,
        norm_div, heq, div_self (norm_ne_zero_iff.mpr hycoe)]
    have hsplit : ((x : K) : AlgebraicClosure ℚ_[2]) +
        ((y : K) : AlgebraicClosure ℚ_[2]) * δ =
      ((y : K) : AlgebraicClosure ℚ_[2]) *
        (((t : K) : AlgebraicClosure ℚ_[2]) + δ) := by
      rw [show ((t : K) : AlgebraicClosure ℚ_[2]) =
        ((x : K) : AlgebraicClosure ℚ_[2]) /
          ((y : K) : AlgebraicClosure ℚ_[2]) from rfl]
      field_simp
    have hconj :
        ‖σ (((t : K) : AlgebraicClosure ℚ_[2]) +
          ((1 : K) : AlgebraicClosure ℚ_[2]) * δ)‖ =
        ‖((t : K) : AlgebraicClosure ℚ_[2]) +
          ((1 : K) : AlgebraicClosure ℚ_[2]) * δ‖ :=
      UnramifiedQuadraticNorms.norm_conj_eq K σ _
    rw [UnramifiedQuadraticNorms.conj_apply hσ] at hconj
    have hone : ((1 : K) : AlgebraicClosure ℚ_[2]) = 1 := rfl
    rw [hone, one_mul] at hconj
    have hprod :
        ‖((t : K) : AlgebraicClosure ℚ_[2]) + δ‖ ^ 2 =
          ‖((t ^ 2 + 3 : K) : AlgebraicClosure ℚ_[2])‖ := by
      have hmul :
          (((t : K) : AlgebraicClosure ℚ_[2]) + δ) *
            (((t : K) : AlgebraicClosure ℚ_[2]) - δ) =
          ((t ^ 2 + 3 : K) : AlgebraicClosure ℚ_[2]) := by
        have hc : ((t ^ 2 + 3 : K) : AlgebraicClosure ℚ_[2]) =
            ((t : K) : AlgebraicClosure ℚ_[2]) ^ 2 + 3 := by
          show ((t : K) : AlgebraicClosure ℚ_[2]) ^ 2 +
            ((3 : K) : AlgebraicClosure ℚ_[2]) = _
          rw [show ((3 : K) : AlgebraicClosure ℚ_[2]) =
            algebraMap K (AlgebraicClosure ℚ_[2]) 3 from rfl, map_ofNat]
        rw [hc]
        linear_combination -hδ
      rw [← hmul, norm_mul, hconj, sq]
    obtain ⟨w, hw0, hw⟩ :=
      exists_norm_sq_eq_sq_add_three_of_odd_residueDegree FF hf htnorm
    have hval :
        ‖((t : K) : AlgebraicClosure ℚ_[2]) + δ‖ =
          ‖((w : K) : AlgebraicClosure ℚ_[2])‖ := by
      have hsq :
          ‖((t : K) : AlgebraicClosure ℚ_[2]) + δ‖ ^ 2 =
            ‖((w : K) : AlgebraicClosure ℚ_[2])‖ ^ 2 := by
        rw [hprod]
        exact hw
      nlinarith [norm_nonneg (((t : K) : AlgebraicClosure ℚ_[2]) + δ),
        norm_nonneg (((w : K) : AlgebraicClosure ℚ_[2])),
        norm_nonneg ((y : K) : AlgebraicClosure ℚ_[2])]
    refine ⟨y * w, mul_ne_zero hy0 hw0, ?_⟩
    rw [hsplit, norm_mul, hval,
      show ((y * w : K) : AlgebraicClosure ℚ_[2]) =
        ((y : K) : AlgebraicClosure ℚ_[2]) *
          ((w : K) : AlgebraicClosure ℚ_[2]) from rfl,
      norm_mul]
  · have hyδ :
        ‖((y : K) : AlgebraicClosure ℚ_[2]) * δ‖ =
          ‖((y : K) : AlgebraicClosure ℚ_[2])‖ := by
      rw [norm_mul, hδnorm, mul_one]
    have hmax :
        ‖((x : K) : AlgebraicClosure ℚ_[2]) +
          ((y : K) : AlgebraicClosure ℚ_[2]) * δ‖ =
        max ‖((x : K) : AlgebraicClosure ℚ_[2])‖
          ‖((y : K) : AlgebraicClosure ℚ_[2])‖ := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (by rw [hyδ]; exact hne), hyδ]
    rcases le_total ‖((x : K) : AlgebraicClosure ℚ_[2])‖
      ‖((y : K) : AlgebraicClosure ℚ_[2])‖ with hle | hle
    · exact ⟨y, hy0, by rw [hmax, max_eq_right hle]⟩
    · exact ⟨x, hx0, by rw [hmax, max_eq_left hle]⟩

end
end GQ2.Dyadic.LSquare.NuKummer


namespace GQ2.Dyadic.Instances.M0FieldNuOddResidueSpectral

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.M0FieldNuOddResidue
open GQ2.Dyadic.Instances.M0FieldUniformizerDInvariant
open GQ2.Dyadic.LSquare.NuKummer

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])}
  [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] [CompactSpace AbsGalQ2]
  [TotallyDisconnectedSpace AbsGalQ2]

/-- Odd residue degree constructs the unramified square class of `-3` and leaves only the
intrinsic distinguished-D placement in the selected compact-M corrected-RN consumer. -/
theorem m0RowResidualRN_of_familySelection_of_oddResidueDegree
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K) (hf : Odd FF.f)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha : ℕ} (hbranch : S.branch = .M0 alpha)
    (Hplace : M0UniformizerDPlacement FF alpha (handleCount FP (.M0 alpha))) :
    ∃ G : GenAsmBranch K B,
      G.pres = .M0 alpha (handleCount FP (.M0 alpha)) ∧
        Nonempty (GenAsmRowResidualRN (FF := FF) G) :=
  m0RowResidualRN_of_familySelection_of_oddResidue_negThree
    B FF hf S hbranch Hplace
      (hasEqualNormValueGroups_of_sq_eq_neg_three_of_odd_residueDegree
        FF hf (sq_sqrtCl_negThreeUnit K))

#print axioms
  GQ2.Dyadic.LSquare.NuKummer.norm_cubeCyclotomic_eq_one_of_odd_residueDegree
#print axioms
  GQ2.Dyadic.LSquare.NuKummer.exists_norm_sq_eq_sq_add_three_of_odd_residueDegree
#print axioms
  GQ2.Dyadic.LSquare.NuKummer.hasEqualNormValueGroups_of_sq_eq_neg_three_of_odd_residueDegree
#print axioms m0RowResidualRN_of_familySelection_of_oddResidueDegree

end
end GQ2.Dyadic.Instances.M0FieldNuOddResidueSpectral
