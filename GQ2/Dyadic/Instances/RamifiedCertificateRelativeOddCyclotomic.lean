/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateOddCyclotomicRamification
import GQ2.GaloisCosetNorm
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Relative odd-cyclotomic extensions are unramified

For arbitrary finite dyadic fields `K ≤ L`, the actual relative residue action is constructed
and proved base-linear. If an odd root generates `L/K`, reduction is faithful. Comparing the
field-degree tower with the residue-degree tower forces `e(L/K)=1`.

The concrete endpoint discharges relative normality and generation for `K(ζ)/K`, and constructs
equal norm-value witnesses for every element of `K ⊔ Q₂(ζ)`. No normality of `K/Q₂`, no
reciprocity law, and no presentation-family or handle-count restriction is used.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 SpectralLocalField
open scoped NNReal Pointwise
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

section Relative
variable (K L : IntermediateField ℚ_[2] ℚ̄₂)
  [FiniteDimensional ℚ_[2] L]
  [Algebra K L] [IsScalarTower ℚ_[2] K L] [IsScalarTower K L ℚ̄₂]

omit [IsScalarTower K L ℚ̄₂] in
/-- Relative automorphisms preserve the inherited spectral norm, without absolute normality. -/
theorem relativeFiniteGalois_norm_eq (g : L ≃ₐ[K] L) (x : L) : ‖g x‖ = ‖x‖ := by
  rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[2],
    NormedAlgebra.norm_eq_spectralNorm ℚ_[2]]
  exact (spectralNorm_eq_of_equiv (g.restrictScalars ℚ_[2]) x).symm

omit [FiniteDimensional ℚ_[2] L] [IsScalarTower ℚ_[2] K L] in
/-- The norm valuations in an embedded field tower are compatible. -/
theorem relativeNormValuation_hasExtension :
    (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := by
  constructor
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  simp only [Valuation.comap_apply, NormedField.valuation_apply]
  have hn : ‖algebraMap K L x‖ = ‖x‖ := by
    change ‖algebraMap L ℚ̄₂ (algebraMap K L x)‖ = ‖algebraMap K ℚ̄₂ x‖
    rw [← IsScalarTower.algebraMap_apply]
  exact_mod_cast (show ‖x‖ ≤ 1 ↔ ‖algebraMap K L x‖ ≤ 1 by rw [hn])

/-- Every relative automorphism preserves the upper field's norm valuation ring. -/
theorem relativeFiniteGalois_mem_normInteger_decomposition (g : L ≃ₐ[K] L) :
    g ∈ (finiteNormInteger L).decompositionSubgroup K := by
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  change ‖g⁻¹ x‖₊ ≤ 1 ↔ ‖x‖₊ ≤ 1
  rw [← NNReal.coe_le_coe, ← NNReal.coe_le_coe]
  simp only [NNReal.coe_one, coe_nnnorm, relativeFiniteGalois_norm_eq]

/-- The relative Galois group as a group of norm-ring-preserving automorphisms. -/
def relativeFiniteGaloisNormDecomposition : (L ≃ₐ[K] L) →*
    (finiteNormInteger L).decompositionSubgroup K where
  toFun g := ⟨g, relativeFiniteGalois_mem_normInteger_decomposition K L g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The actual relative action on the upper residue field. -/
def relativeFiniteGaloisResidueAction : (L ≃ₐ[K] L) →*
    RingAut (IsLocalRing.ResidueField (finiteNormInteger L)) :=
  (MulSemiringAction.toRingAut ((finiteNormInteger L).decompositionSubgroup K)
    (IsLocalRing.ResidueField (finiteNormInteger L))).comp
      (relativeFiniteGaloisNormDecomposition K L)

/-- The relative residue action is induced by reduction of the field action. -/
theorem relativeFiniteGaloisResidueAction_residue (g : L ≃ₐ[K] L)
    (x : finiteNormInteger L) :
    relativeFiniteGaloisResidueAction K L g (IsLocalRing.residue (finiteNormInteger L) x) =
      IsLocalRing.residue (finiteNormInteger L)
        (relativeFiniteGaloisNormDecomposition K L g • x) :=
  (IsLocalRing.ResidueField.residue_smul ((finiteNormInteger L).decompositionSubgroup K)
    (relativeFiniteGaloisNormDecomposition K L g) x).symm

local instance : (NormedField.valuation (K := K)).HasExtension
    (NormedField.valuation (K := L)) := relativeNormValuation_hasExtension K L
local instance : Algebra (finiteNormInteger K) (finiteNormInteger L) :=
  Valuation.HasExtension.instAlgebra_valuationSubring
    (NormedField.valuation (K := K)) (NormedField.valuation (K := L))
set_option synthInstance.maxHeartbeats 40000 in
local instance : IsLocalHom (algebraMap (finiteNormInteger K) (finiteNormInteger L)) :=
  Valuation.HasExtension.instIsLocalHomValuationInteger

/-- Relative residue automorphisms fix the lower residue field. -/
theorem relativeFiniteGaloisResidueAction_commutes_base (g : L ≃ₐ[K] L)
    (a : IsLocalRing.ResidueField (finiteNormInteger K)) :
    relativeFiniteGaloisResidueAction K L g
        (algebraMap (IsLocalRing.ResidueField (finiteNormInteger K))
          (IsLocalRing.ResidueField (finiteNormInteger L)) a) =
      algebraMap (IsLocalRing.ResidueField (finiteNormInteger K))
        (IsLocalRing.ResidueField (finiteNormInteger L)) a := by
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
  change relativeFiniteGaloisResidueAction K L g
      (IsLocalRing.residue (finiteNormInteger L)
        (algebraMap (finiteNormInteger K) (finiteNormInteger L) b)) =
    IsLocalRing.residue (finiteNormInteger L)
      (algebraMap (finiteNormInteger K) (finiteNormInteger L) b)
  rw [relativeFiniteGaloisResidueAction_residue]
  congr 1
  apply Subtype.ext
  change g (algebraMap K L (b : K)) = algebraMap K L (b : K)
  exact g.commutes _

/-- The relative residue action, linear over the lower residue field. -/
def relativeFiniteGaloisResidueAlgAction : (L ≃ₐ[K] L) →*
    Gal(IsLocalRing.ResidueField (finiteNormInteger L)/
      IsLocalRing.ResidueField (finiteNormInteger K)) where
  toFun g :=
    { relativeFiniteGaloisResidueAction K L g with
      commutes' := relativeFiniteGaloisResidueAction_commutes_base K L g }
  map_one' := by
    ext x
    change relativeFiniteGaloisResidueAction K L 1 x = x
    rw [map_one]
    rfl
  map_mul' g h := by
    ext x
    change relativeFiniteGaloisResidueAction K L (g * h) x =
      relativeFiniteGaloisResidueAction K L g (relativeFiniteGaloisResidueAction K L h x)
    rw [map_mul]
    rfl

omit [FiniteDimensional ℚ_[2] L] in
private theorem relative_residue_norm_sub_lt_one
    (x y : finiteNormInteger L)
    (hxy : IsLocalRing.residue (finiteNormInteger L) x =
      IsLocalRing.residue (finiteNormInteger L) y) :
    ‖(x : L) - (y : L)‖ < 1 := by
  have hz : IsLocalRing.residue (finiteNormInteger L) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff] at hz
  change ‖(x : L) - (y : L)‖₊ < 1 at hz
  exact_mod_cast hz

/-- Odd roots remain distinct after reduction; a relative odd-root generator makes the
relative residue action faithful. -/
theorem relativeFiniteGaloisResidueAlgAction_injective_of_odd_root
    (m : ℕ) (hm : Odd m) (x : L) (hx : x ^ m = 1)
    (hgen : Algebra.adjoin K {x} = ⊤) :
    Function.Injective (relativeFiniteGaloisResidueAlgAction K L) := by
  intro g h hgh
  have hnorm : ‖x‖ = 1 :=
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm.pos, hx⟩).norm_eq_one
  let xO : finiteNormInteger L := ⟨x, by
    change ‖x‖₊ ≤ 1
    exact_mod_cast hnorm.le⟩
  have hres : IsLocalRing.residue (finiteNormInteger L)
        (relativeFiniteGaloisNormDecomposition K L g • xO) =
      IsLocalRing.residue (finiteNormInteger L)
        (relativeFiniteGaloisNormDecomposition K L h • xO) := by
    rw [← relativeFiniteGaloisResidueAction_residue,
      ← relativeFiniteGaloisResidueAction_residue]
    exact DFunLike.congr_fun hgh _
  have hclose := relative_residue_norm_sub_lt_one L _ _ hres
  change ‖g x - h x‖ < 1 at hclose
  have heq : g x = h x := by
    by_contra hne
    have hgroot : ((g x : L) : ℚ̄₂) ^ m = 1 := by
      exact_mod_cast (show (g x) ^ m = 1 by rw [← map_pow, hx, map_one])
    have hhroot : ((h x : L) : ℚ̄₂) ^ m = 1 := by
      exact_mod_cast (show (h x) ^ m = 1 by rw [← map_pow, hx, map_one])
    have hsep := TeichmullerLift.norm_sub_eq_one_of_pow_eq_one hm hgroot hhroot
      (fun hc ↦ hne (Subtype.ext hc))
    change ‖((g x : L) : ℚ̄₂) - ((h x : L) : ℚ̄₂)‖ < 1 at hclose
    rw [hsep] at hclose
    exact lt_irrefl 1 hclose
  have hhom : g.toAlgHom = h.toAlgHom := AlgHom.ext_of_adjoin_eq_top hgen (by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact heq)
  apply AlgEquiv.ext
  intro z
  exact congrArg (fun f : L →ₐ[K] L ↦ f z) hhom

/-- A faithful relative residue action forces relative ramification index one. The proof
uses both field and residue degree towers and does not require either field to be normal over
`Q₂`. -/
theorem relE_eq_one_of_relativeResidueAction_injective
    [FiniteDimensional ℚ_[2] K] [IsGalois K L]
    (FK : DyadicUnitFiltration K) (FL : DyadicUnitFiltration L) (hKL : K ≤ L)
    (hinj : Function.Injective (relativeFiniteGaloisResidueAlgAction K L)) :
    GaloisCosetNorm.relE FK FL hKL = 1 := by
  letI : FiniteDimensional K L := FiniteDimensional.right ℚ_[2] K L
  let kK := IsLocalRing.ResidueField (finiteNormInteger K)
  let kL := IsLocalRing.ResidueField (finiteNormInteger L)
  have hcardK : Nat.card kK = 2 ^ FK.f := normInteger_residueField_card_eq_pow_f K FK
  have hcardL : Nat.card kL = 2 ^ FL.f := normInteger_residueField_card_eq_pow_f L FL
  letI : Finite kK := (Nat.card_ne_zero.mp (by rw [hcardK]; positivity)).2
  letI : Finite kL := (Nat.card_ne_zero.mp (by rw [hcardL]; positivity)).2
  have hdim : FL.f = FK.f * Module.finrank kK kL := by
    apply Nat.pow_right_injective (le_refl 2)
    have hc := Module.natCard_eq_pow_finrank (K := kK) (V := kL)
    rw [hcardK, hcardL, ← pow_mul] at hc
    exact hc
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank] at hle
  have hdeg := Module.finrank_mul_finrank ℚ_[2] K L
  rw [field_finrank_eq_e_mul_f (FF := FK),
    field_finrank_eq_e_mul_f (FF := FL), hdim] at hdeg
  have he : FL.e ≤ FK.e := by
    have hk := FK.hf_pos
    have hd : 0 < Module.finrank kK kL := Module.finrank_pos
    nlinarith [Nat.mul_le_mul_left (FK.e * FK.f) hle]
  have ht := GaloisCosetNorm.e_eq_relE_mul FK FL hKL
  have hp := GaloisCosetNorm.relE_pos FK FL hKL
  have hk : 0 < (FK.e : ℤ) := by exact_mod_cast FK.he_pos
  have he' : (FL.e : ℤ) ≤ FK.e := by exact_mod_cast he
  nlinarith

/-- A finite relative Galois extension generated by an odd root is unramified. -/
theorem relE_eq_one_of_relative_odd_root
    [FiniteDimensional ℚ_[2] K] [IsGalois K L]
    (FK : DyadicUnitFiltration K) (FL : DyadicUnitFiltration L) (hKL : K ≤ L)
    (m : ℕ) (hm : Odd m) (x : L) (hx : x ^ m = 1)
    (hgen : Algebra.adjoin K {x} = ⊤) :
    GaloisCosetNorm.relE FK FL hKL = 1 :=
  relE_eq_one_of_relativeResidueAction_injective K L FK FL hKL
    (relativeFiniteGaloisResidueAlgAction_injective_of_odd_root K L m hm x hx hgen)

end Relative

section Adjoin
variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]

/-- Adjoining an odd primitive root to any finite dyadic field adds no ramification.
Relative normality and generation are proved from the cyclotomic presentation. -/
theorem relativeOddCyclotomic_relE_eq_one
    (FK : DyadicUnitFiltration K) (m : ℕ) (hm : Odd m)
    (ζ : ℚ̄₂) (hζ : IsPrimitiveRoot ζ m)
    (FL : DyadicUnitFiltration ((IntermediateField.adjoin K {ζ}).restrictScalars ℚ_[2])) :
    GaloisCosetNorm.relE FK FL
      (show K ≤ (IntermediateField.adjoin K {ζ}).restrictScalars ℚ_[2] from
        fun x hx ↦ (IntermediateField.adjoin K {ζ}).algebraMap_mem ⟨x, hx⟩) = 1 := by
  let J := IntermediateField.adjoin K {ζ}
  letI : NeZero m := ⟨hm.pos.ne'⟩
  letI : Algebra.IsAlgebraic K ℚ̄₂ := Algebra.IsAlgebraic.tower_top (K := ℚ_[2]) K
  letI : IsCyclotomicExtension {m} K J :=
    hζ.intermediateField_adjoin_isCyclotomicExtension (K := K)
  letI : IsGalois K J := IsCyclotomicExtension.isGalois {m} K J
  letI : FiniteDimensional K J := IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral ζ)
  letI : FiniteDimensional ℚ_[2] J := Module.Finite.trans K J
  letI : FiniteDimensional ℚ_[2] (J.restrictScalars ℚ_[2]) :=
    inferInstanceAs (FiniteDimensional ℚ_[2] J)
  letI : Algebra K (J.restrictScalars ℚ_[2]) := inferInstanceAs (Algebra K J)
  letI : IsScalarTower ℚ_[2] K (J.restrictScalars ℚ_[2]) :=
    inferInstanceAs (IsScalarTower ℚ_[2] K J)
  letI : IsScalarTower K (J.restrictScalars ℚ_[2]) ℚ̄₂ :=
    inferInstanceAs (IsScalarTower K J ℚ̄₂)
  letI : IsGalois K (J.restrictScalars ℚ_[2]) := inferInstanceAs (IsGalois K J)
  let x : J := ⟨ζ, IntermediateField.mem_adjoin_simple_self K ζ⟩
  have hx : x ^ m = 1 := by
    apply Subtype.ext
    exact hζ.pow_eq_one
  have hgen : Algebra.adjoin K {x} = ⊤ := by
    exact (IntermediateField.adjoin.powerBasis
      (Algebra.IsIntegral.isIntegral ζ)).adjoin_gen_eq_top
  exact relE_eq_one_of_relative_odd_root K (J.restrictScalars ℚ_[2]) FK FL _ m hm x hx hgen

/-- Every nonzero element of an odd-cyclotomic compositum has the norm of a nonzero base-field
element. The upper filtration is constructed, not assumed. -/
theorem exists_same_norm_mem_base_of_mem_odd_cyclotomic
    (FK : DyadicUnitFiltration K) (m : ℕ) (hm : Odd m)
    (ζ : ℚ̄₂) (hζ : IsPrimitiveRoot ζ m) {x : ℚ̄₂} (hx0 : x ≠ 0)
    (hx : x ∈ K ⊔ IntermediateField.adjoin ℚ_[2] {ζ}) :
    ∃ y : ℚ̄₂, y ≠ 0 ∧ y ∈ K ∧ ‖x‖ = ‖y‖ := by
  let J := IntermediateField.adjoin K {ζ}
  let L := J.restrictScalars ℚ_[2]
  letI : Algebra.IsAlgebraic K ℚ̄₂ := Algebra.IsAlgebraic.tower_top (K := ℚ_[2]) K
  letI : FiniteDimensional K J := IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral ζ)
  letI : FiniteDimensional ℚ_[2] J := Module.Finite.trans K J
  letI : FiniteDimensional ℚ_[2] L := inferInstanceAs (FiniteDimensional ℚ_[2] J)
  let FL := dyadicUnitFiltration' L
  have hKL : K ≤ L := fun y hy ↦ J.algebraMap_mem ⟨y, hy⟩
  have he : GaloisCosetNorm.relE FK FL hKL = 1 :=
    relativeOddCyclotomic_relE_eq_one K FK m hm ζ hζ FL
  have hπ := GaloisCosetNorm.relE_spec FK FL hKL
  rw [he, zpow_one] at hπ
  apply UnramifiedNorm.hunram_of_uniformizer_norm_eq FK FL hπ.symm x hx0
  change x ∈ (IntermediateField.adjoin K {ζ}).restrictScalars ℚ_[2]
  rwa [IntermediateField.restrictScalars_adjoin_eq_sup]

end Adjoin

#print axioms relativeFiniteGalois_norm_eq
#print axioms relativeNormValuation_hasExtension
#print axioms relativeFiniteGalois_mem_normInteger_decomposition
#print axioms relativeFiniteGaloisNormDecomposition
#print axioms relativeFiniteGaloisResidueAction
#print axioms relativeFiniteGaloisResidueAction_residue
#print axioms relativeFiniteGaloisResidueAction_commutes_base
#print axioms relativeFiniteGaloisResidueAlgAction
#print axioms relativeFiniteGaloisResidueAlgAction_injective_of_odd_root
#print axioms relE_eq_one_of_relativeResidueAction_injective
#print axioms relE_eq_one_of_relative_odd_root
#print axioms relativeOddCyclotomic_relE_eq_one
#print axioms exists_same_norm_mem_base_of_mem_odd_cyclotomic
end
end GQ2.Dyadic

