/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateAbsoluteResidueExactSequence
import GQ2.Dyadic.Instances.RamifiedCertificateResidueReciprocity

/-!
# The single Frobenius lift behind the absolute residue exact sequence

The finite-level lifting condition isolated by the absolute-residue exact-sequence module is
equivalent to one much smaller input: an absolute Galois element inducing square Frobenius on the
entire absolute residue field. Finite-field cyclicity shows that powers of this single element
lift every automorphism at every finite normal residue level.

The same input has a concrete Teichmuller form. An absolute Galois element induces square
Frobenius if and only if it squares every odd-order root of unity. Odd-root approximation detects
all residue classes, while odd-root separation upgrades equality of reductions to equality of
the roots themselves.

Thus the exact remaining field theorem is existence of one absolute Frobenius element, equivalently
one element that squares all prime-to-two roots of unity. No such existence assertion is made here.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open SpectralLocalField

local notation "k₀" => IsLocalRing.ResidueField BaseInteger
local notation "k̄₂" => IsLocalRing.ResidueField absoluteNormInteger

local instance : Algebra BaseInteger absoluteNormInteger := absoluteNormIntegerAlgebra
local instance : IsLocalHom (algebraMap BaseInteger absoluteNormInteger) :=
  absoluteNormInteger_algebraMap_isLocalHom
local instance : Algebra k₀ k̄₂ := absoluteResidueFieldAlgebra
local instance : Algebra.IsAlgebraic k₀ k̄₂ := absoluteResidueField_isAlgebraic
local instance : Finite k₀ := baseResidueField_finite
local instance : Fintype k₀ := Fintype.ofFinite k₀
local instance : IsAlgClosed k̄₂ := absoluteResidueField_isAlgClosed
local instance : Normal k₀ k̄₂ := absoluteResidueField_normal

/-- A lift of square Frobenius through the canonical absolute residue action. -/
def AbsoluteResidueFrobeniusLift : Prop :=
  ∃ g : Kummer.GaloisGroup ℚ_[2],
    absoluteResidueAlgAction g = absoluteResidueFrobenius

private theorem absoluteResidueFrobenius_pow_apply (n : ℕ) (x : k̄₂) :
    (absoluteResidueFrobenius ^ n) x = x ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      simp only [AlgEquiv.mul_apply]
      rw [ih]
      rw [absoluteResidueFrobenius_apply]
      rw [show 2 ^ (n + 1) = 2 ^ n * 2 by rw [pow_succ]]
      exact (pow_mul x (2 ^ n) 2).symm

/-- One absolute lift of square Frobenius supplies all finite normal residue lifts. -/
theorem absoluteResidueAlgAction_surjective_of_frobeniusLift
    (H : AbsoluteResidueFrobeniusLift) :
    Function.Surjective absoluteResidueAlgAction := by
  rw [absoluteResidueAlgAction_surjective_iff_finite_lifts]
  intro E hEfin hEnormal sigma
  letI : FiniteDimensional k₀ E := hEfin
  letI : Normal k₀ E := hEnormal
  letI : Finite E := Module.finite_of_finite k₀
  letI : IsScalarTower k₀ E k̄₂ :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      have hx : x = 0 ∨ x = 1 := by
        rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1)
          (baseIntegerResidueEquivZMod x) with h | h
        · exact Or.inl (baseIntegerResidueEquivZMod.injective (by simpa using h))
        · exact Or.inr (baseIntegerResidueEquivZMod.injective (by simpa using h))
      rcases hx with rfl | rfl <;> simp)
  let sigmaE : Gal(E/k₀) := sigma.restrictNormal E
  obtain ⟨n, hn⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k₀ E).2 sigmaE
  obtain ⟨g, hg⟩ := H
  refine ⟨g ^ n.1, fun x => ?_⟩
  rw [map_pow, hg, absoluteResidueFrobenius_pow_apply]
  have hn_apply := DFunLike.congr_fun hn x
  have hfrobE :
      (FiniteField.frobeniusAlgEquivOfAlgebraic k₀ E ^ n.1) x =
        x ^ (2 ^ n.1) := by
    rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
      baseResidueField_fintype_card]
  calc
    (x : k̄₂) ^ (2 ^ n.1) =
      algebraMap E k̄₂ (x ^ (2 ^ n.1)) :=
        (map_pow (algebraMap E k̄₂) x (2 ^ n.1)).symm
    _ = algebraMap E k̄₂
        ((FiniteField.frobeniusAlgEquivOfAlgebraic k₀ E ^ n.1) x) :=
          congrArg (algebraMap E k̄₂) hfrobE.symm
    _ = algebraMap E k̄₂ (sigmaE x) := congrArg (algebraMap E k̄₂) hn_apply
    _ = sigma (x : k̄₂) := sigma.restrictNormal_commutes E x

/-- Residue-action surjectivity is equivalent to one absolute lift of square Frobenius. -/
theorem absoluteResidueAlgAction_surjective_iff_frobeniusLift :
    Function.Surjective absoluteResidueAlgAction ↔
      AbsoluteResidueFrobeniusLift := by
  constructor
  · intro hsurj
    obtain ⟨g, hg⟩ := hsurj absoluteResidueFrobenius
    exact ⟨g, hg⟩
  · exact absoluteResidueAlgAction_surjective_of_frobeniusLift

/-- An absolute Galois element acts as arithmetic Frobenius on every odd-order Teichmuller
representative. -/
def SquaresOddRootsOfUnity (g : Kummer.GaloisGroup ℚ_[2]) : Prop :=
  ∀ (m : ℕ) (zeta : AlgebraicClosure ℚ_[2]),
    Odd m → zeta ^ m = 1 → g • zeta = zeta ^ 2

private theorem absoluteResidue_eq_of_norm_sub_lt_one
    (x y : absoluteNormInteger)
    (hxy : ‖(x : AlgebraicClosure ℚ_[2]) - (y : AlgebraicClosure ℚ_[2])‖ < 1) :
    IsLocalRing.residue absoluteNormInteger x =
      IsLocalRing.residue absoluteNormInteger y := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (absoluteResidue_zero_iff_norm_lt_one _).mpr
  exact hxy

private theorem absoluteResidue_norm_sub_lt_one_of_eq
    (x y : absoluteNormInteger)
    (hxy : IsLocalRing.residue absoluteNormInteger x =
      IsLocalRing.residue absoluteNormInteger y) :
    ‖(x : AlgebraicClosure ℚ_[2]) - (y : AlgebraicClosure ℚ_[2])‖ < 1 := by
  apply (absoluteResidue_zero_iff_norm_lt_one (x - y)).mp
  rw [map_sub, hxy, sub_self]

private theorem sq_pow_eq_one_of_pow_eq_one
    {zeta : AlgebraicClosure ℚ_[2]} {m : ℕ} (hzeta : zeta ^ m = 1) :
    (zeta ^ 2) ^ m = 1 := by
  calc
    (zeta ^ 2) ^ m = zeta ^ (2 * m) := (pow_mul zeta 2 m).symm
    _ = zeta ^ (m * 2) := congrArg (zeta ^ ·) (Nat.mul_comm 2 m)
    _ = (zeta ^ m) ^ 2 := pow_mul zeta m 2
    _ = 1 := by rw [hzeta, one_pow]

/-- Squaring all odd-order roots of unity is exactly lifting square Frobenius on the residue
field. -/
theorem squaresOddRootsOfUnity_iff_residueFrobenius
    (g : Kummer.GaloisGroup ℚ_[2]) :
    SquaresOddRootsOfUnity g ↔
      absoluteResidueAlgAction g = absoluteResidueFrobenius := by
  constructor
  · intro hroots
    apply AlgEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    have hxle : ‖(x : AlgebraicClosure ℚ_[2])‖ ≤ 1 := by
      have hx := x.property
      change ‖(x : AlgebraicClosure ℚ_[2])‖₊ ≤ 1 at hx
      exact_mod_cast hx
    rcases lt_or_eq_of_le hxle with hxlt | hxeq
    · have hxzero : IsLocalRing.residue absoluteNormInteger x = 0 :=
        (absoluteResidue_zero_iff_norm_lt_one x).mpr hxlt
      rw [hxzero, map_zero, map_zero]
    · obtain ⟨m, zeta, hmodd, hzeta, hnear⟩ :=
        exists_odd_rootOfUnity_near (x : AlgebraicClosure ℚ_[2]) hxeq
      have hzetanorm : ‖zeta‖ = 1 :=
        (isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hmodd.pos, hzeta⟩).norm_eq_one
      let zetaA : absoluteNormInteger := ⟨zeta, by
        change ‖zeta‖₊ ≤ 1
        exact_mod_cast hzetanorm.le⟩
      have hxzeta : IsLocalRing.residue absoluteNormInteger x =
          IsLocalRing.residue absoluteNormInteger zetaA :=
        absoluteResidue_eq_of_norm_sub_lt_one x zetaA hnear
      calc
        absoluteResidueAlgAction g (IsLocalRing.residue absoluteNormInteger x) =
            absoluteResidueAlgAction g
              (IsLocalRing.residue absoluteNormInteger zetaA) := congrArg _ hxzeta
        _ = IsLocalRing.residue absoluteNormInteger (absoluteDecomposition g • zetaA) :=
          absoluteResidueAction_residue g zetaA
        _ = IsLocalRing.residue absoluteNormInteger (zetaA ^ 2) := by
          congr 1
          apply Subtype.ext
          exact hroots m zeta hmodd hzeta
        _ = (IsLocalRing.residue absoluteNormInteger zetaA) ^ 2 := by rw [map_pow]
        _ = (IsLocalRing.residue absoluteNormInteger x) ^ 2 := by rw [hxzeta]
        _ = absoluteResidueFrobenius
            (IsLocalRing.residue absoluteNormInteger x) :=
          (absoluteResidueFrobenius_apply _).symm
  · intro hres m zeta hmodd hzeta
    have hzetanorm : ‖zeta‖ = 1 :=
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hmodd.pos, hzeta⟩).norm_eq_one
    let zetaA : absoluteNormInteger := ⟨zeta, by
      change ‖zeta‖₊ ≤ 1
      exact_mod_cast hzetanorm.le⟩
    have hresEq : IsLocalRing.residue absoluteNormInteger
          (absoluteDecomposition g • zetaA) =
        IsLocalRing.residue absoluteNormInteger (zetaA ^ 2) := by
      calc
        IsLocalRing.residue absoluteNormInteger (absoluteDecomposition g • zetaA) =
            absoluteResidueAlgAction g
              (IsLocalRing.residue absoluteNormInteger zetaA) :=
          (absoluteResidueAction_residue g zetaA).symm
        _ = absoluteResidueFrobenius
              (IsLocalRing.residue absoluteNormInteger zetaA) :=
          DFunLike.congr_fun hres _
        _ = (IsLocalRing.residue absoluteNormInteger zetaA) ^ 2 :=
          absoluteResidueFrobenius_apply _
        _ = IsLocalRing.residue absoluteNormInteger (zetaA ^ 2) := by rw [map_pow]
    have hclose : ‖g • zeta - zeta ^ 2‖ < 1 := by
      have hcloseA := absoluteResidue_norm_sub_lt_one_of_eq
        (absoluteDecomposition g • zetaA) (zetaA ^ 2) hresEq
      have hcoe1 :
          (((absoluteDecomposition g • zetaA : absoluteNormInteger) :
            AlgebraicClosure ℚ_[2])) = g • zeta := rfl
      have hcoe2 :
          (((zetaA ^ 2 : absoluteNormInteger) : AlgebraicClosure ℚ_[2])) = zeta ^ 2 := rfl
      rw [hcoe1, hcoe2] at hcloseA
      exact hcloseA
    have hgzeta : (g • zeta) ^ m = 1 := by
      rw [AlgEquiv.smul_def, ← map_pow, hzeta, map_one]
    have hzeta2 : (zeta ^ 2) ^ m = 1 := sq_pow_eq_one_of_pow_eq_one hzeta
    by_contra hne
    have hsep := TeichmullerLift.norm_sub_eq_one_of_pow_eq_one
      hmodd hgzeta hzeta2 hne
    rw [hsep] at hclose
    exact lt_irrefl 1 hclose

/-- The exact finite lifting condition is one Galois element squaring every odd-order root of
unity. -/
theorem absoluteResidueAlgAction_surjective_iff_exists_squaresOddRoots :
    Function.Surjective absoluteResidueAlgAction ↔
      ∃ g : Kummer.GaloisGroup ℚ_[2], SquaresOddRootsOfUnity g := by
  rw [absoluteResidueAlgAction_surjective_iff_frobeniusLift]
  unfold AbsoluteResidueFrobeniusLift
  exact exists_congr fun g => (squaresOddRootsOfUnity_iff_residueFrobenius g).symm

#print axioms AbsoluteResidueFrobeniusLift
#print axioms absoluteResidueAlgAction_surjective_of_frobeniusLift
#print axioms absoluteResidueAlgAction_surjective_iff_frobeniusLift
#print axioms SquaresOddRootsOfUnity
#print axioms squaresOddRootsOfUnity_iff_residueFrobenius
#print axioms absoluteResidueAlgAction_surjective_iff_exists_squaresOddRoots

end

end GQ2.Dyadic
