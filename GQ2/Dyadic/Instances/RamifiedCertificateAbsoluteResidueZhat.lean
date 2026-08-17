/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateOddRootLocalConjugacy
import GQ2.Dyadic.Instances.RamifiedCertificateQurZhatFrobeniusComparison
import Mathlib.FieldTheory.Galois.Profinite

/-!
# The absolute residue Galois group is procyclic

Square Frobenius topologically generates the Galois group of the absolute residue field over the
base residue field.  Surjectivity follows from finite-field Frobenius generation and the Krull
neighborhood basis.  Injectivity is checked against every finite quotient in the profinite
completion defining Zhat.  This yields a square-Frobenius-normalized continuous equivalence
between the absolute residue Galois group and Zhat.

Combining that equivalence with the now-surjective canonical absolute residue action also
identifies the quotient of Gal(AlgebraicClosure Q2/Q2) by absolute inertia with Zhat.
This closes the absolute residue-field Galois seam.  For a general finite extension K/Q2, the
remaining campaign input is the commuting comparison between its oriented abstract tame quotient
and this canonical absolute Frobenius coordinate.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open SpectralLocalField

local notation "k₀" => IsLocalRing.ResidueField BaseInteger
local notation "k̄₂" => IsLocalRing.ResidueField absoluteNormInteger

local instance : Algebra k₀ k̄₂ := absoluteResidueFieldAlgebra
local instance : Algebra.IsAlgebraic k₀ k̄₂ := absoluteResidueField_isAlgebraic
local instance : Finite k₀ := baseResidueField_finite
local instance : Fintype k₀ := Fintype.ofFinite k₀
local instance : IsAlgClosed k̄₂ := absoluteResidueField_isAlgClosed
local instance : Normal k₀ k̄₂ := absoluteResidueField_normal
local instance : CharP k₀ 2 :=
  RingHom.charP baseIntegerResidueEquivZMod.toRingHom
    baseIntegerResidueEquivZMod.injective 2
local instance : Algebra.IsSeparable k₀ k̄₂ := inferInstance
local instance : IsGalois k₀ k̄₂ where

private instance finiteIndexNormal_index_neZero
    (H : FiniteIndexNormalSubgroup (GrpCat.of (Multiplicative ℤ))) :
    NeZero H.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩

/-- Profinite exponentiation of square Frobenius on the absolute residue field. -/
def zhatToAbsoluteResidueGal : ContinuousMonoidHom Zhat Gal(k̄₂/k₀) :=
  (zpowHatHom absoluteResidueFrobenius).hom

@[simp] theorem zhatToAbsoluteResidueGal_ofInt (n : ℤ) :
    zhatToAbsoluteResidueGal (Zhat.ofInt n) = absoluteResidueFrobenius ^ n :=
  zpowHat_ofInt absoluteResidueFrobenius n

private theorem absoluteResidueFrobenius_pow_apply_nat (n : ℕ) (x : k̄₂) :
    (absoluteResidueFrobenius ^ n) x = x ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      simp only [AlgEquiv.mul_apply]
      rw [ih, absoluteResidueFrobenius_apply]
      rw [show 2 ^ (n + 1) = 2 ^ n * 2 by rw [pow_succ]]
      exact (pow_mul x (2 ^ n) 2).symm

/-- Square Frobenius topologically generates the full absolute residue Galois group. -/
theorem zhatToAbsoluteResidueGal_surjective :
    Function.Surjective zhatToAbsoluteResidueGal := by
  have hdense : DenseRange zhatToAbsoluteResidueGal := by
    intro sigma
    rw [mem_closure_iff_nhds_one]
    intro U hU
    rw [krullTopology_mem_nhds_one_iff_of_normal] at hU
    obtain ⟨E, hEfin, hEnormal, hEU⟩ := hU
    letI : FiniteDimensional k₀ E := hEfin
    letI : Normal k₀ E := hEnormal
    letI : Finite E := Module.finite_of_finite k₀
    let sigmaE : Gal(E/k₀) := sigma.restrictNormal E
    obtain ⟨n, hn⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k₀ E).2 sigmaE
    refine ⟨zhatToAbsoluteResidueGal (Zhat.ofInt (n.1 : ℤ)),
      ⟨Zhat.ofInt (n.1 : ℤ), rfl⟩, hEU ?_⟩
    apply (IntermediateField.mem_fixingSubgroup_iff E _).mpr
    intro x hx
    have hx' : sigma.symm x ∈ E := by
      rw [← (IntermediateField.normal_iff_forall_map_eq'.mp hEnormal sigma.symm)]
      exact (E.map_mem_map sigma.symm.toAlgHom).mpr hx
    let xx : E := ⟨sigma.symm x, hx'⟩
    have hn_apply := DFunLike.congr_fun hn xx
    have hfrobE :
        (FiniteField.frobeniusAlgEquivOfAlgebraic k₀ E ^ n.1) xx =
          xx ^ (2 ^ n.1) := by
      rw [AlgEquiv.coe_pow,
        FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
        baseResidueField_fintype_card]
    rw [div_eq_mul_inv, zhatToAbsoluteResidueGal_ofInt]
    change (absoluteResidueFrobenius ^ n.1) (sigma.symm x) = x
    rw [absoluteResidueFrobenius_pow_apply_nat]
    calc
      (sigma.symm x : k̄₂) ^ (2 ^ n.1) =
          algebraMap E k̄₂ (xx ^ (2 ^ n.1)) := by
            rw [map_pow]
            rfl
      _ = algebraMap E k̄₂
          ((FiniteField.frobeniusAlgEquivOfAlgebraic k₀ E ^ n.1) xx) :=
            congrArg (algebraMap E k̄₂) hfrobE.symm
      _ = algebraMap E k̄₂ (sigmaE xx) :=
            congrArg (algebraMap E k̄₂) hn_apply
      _ = x := by simp [sigmaE, xx]
  intro sigma
  have hclosed : IsClosed (Set.range fun z : Zhat => zhatToAbsoluteResidueGal z) :=
    (isCompact_range (zhatToAbsoluteResidueGal).continuous_toFun).isClosed
  have hsigma : sigma ∈ closure (Set.range fun z : Zhat =>
      zhatToAbsoluteResidueGal z) := hdense sigma
  rw [hclosed.closure_eq] at hsigma
  exact hsigma

private noncomputable def finiteResidueLevel (n : ℕ) [NeZero n] :
    IntermediateField k₀ k̄₂ :=
  (IsAlgClosed.lift : FiniteField.Extension k₀ 2 n →ₐ[k₀] k̄₂).fieldRange

private theorem finiteResidueLevel_finrank (n : ℕ) [NeZero n] :
    Module.finrank k₀ (finiteResidueLevel n) = n := by
  let i : FiniteField.Extension k₀ 2 n →ₐ[k₀] k̄₂ := IsAlgClosed.lift
  let e : FiniteField.Extension k₀ 2 n ≃ₐ[k₀] finiteResidueLevel n :=
    AlgEquiv.ofInjectiveField i
  rw [← e.toLinearEquiv.finrank_eq]
  exact FiniteField.finrank_extension k₀ 2 n

private noncomputable instance finiteResidueLevel_finiteDimensional
    (n : ℕ) [NeZero n] : FiniteDimensional k₀ (finiteResidueLevel n) :=
  Module.finite_of_finrank_pos (by
    rw [finiteResidueLevel_finrank]
    exact NeZero.pos n)

private noncomputable instance finiteResidueLevel_finite
    (n : ℕ) [NeZero n] : Finite (finiteResidueLevel n) :=
  Module.finite_of_finite k₀

private noncomputable instance finiteResidueLevel_normal
    (n : ℕ) [NeZero n] : Normal k₀ (finiteResidueLevel n) := inferInstance

private theorem finiteResidueLevel_frobenius_restrict (n : ℕ) [NeZero n] :
    absoluteResidueFrobenius.restrictNormal (finiteResidueLevel n) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k₀ (finiteResidueLevel n) := by
  ext x
  rw [AlgEquiv.restrictNormal_apply, absoluteResidueFrobenius_apply]
  change (x : k̄₂) ^ 2 = ((x ^ Fintype.card k₀ : finiteResidueLevel n) : k̄₂)
  rw [baseResidueField_fintype_card]
  rfl

private theorem finiteResidueLevel_frobenius_generates (n : ℕ) [NeZero n] :
    ∀ g : Gal(finiteResidueLevel n/k₀),
      g ∈ Subgroup.zpowers
        (FiniteField.frobeniusAlgEquivOfAlgebraic k₀ (finiteResidueLevel n)) := by
  intro g
  obtain ⟨j, hj⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k₀
      (finiteResidueLevel n)).2 g
  exact Subgroup.mem_zpowers_iff.mpr ⟨(j.1 : ℤ), by simpa using hj⟩

private theorem quotient_generator_generates (H :
    FiniteIndexNormalSubgroup
      (GrpCat.of (Multiplicative ℤ))) :
    ∀ g : Multiplicative ℤ ⧸ H.toSubgroup,
      g ∈ Subgroup.zpowers
        ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) :
          Multiplicative ℤ ⧸ H.toSubgroup) := by
  intro g
  induction g using QuotientGroup.induction_on with
  | H x =>
    exact Subgroup.mem_zpowers_iff.mpr ⟨x.toAdd, by
      rw [← QuotientGroup.mk_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one,
        ofAdd_toAdd]⟩

private noncomputable def quotientToFiniteResidueGal
    (H : FiniteIndexNormalSubgroup
      (GrpCat.of (Multiplicative ℤ))) :
    (Multiplicative ℤ ⧸ H.toSubgroup) ≃*
      Gal(finiteResidueLevel H.index/k₀) := by
  let qgen : Multiplicative ℤ ⧸ H.toSubgroup :=
    ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) :
      Multiplicative ℤ ⧸ H.toSubgroup)
  let fgen : Gal(finiteResidueLevel H.index/k₀) :=
    FiniteField.frobeniusAlgEquivOfAlgebraic k₀
      (finiteResidueLevel H.index)
  let eQ := zmodMulEquivOfGenerator (quotient_generator_generates H)
    (by rw [← Subgroup.index_eq_card])
  let eF := zmodMulEquivOfGenerator
    (finiteResidueLevel_frobenius_generates H.index)
    (by
      rw [IsGalois.card_aut_eq_finrank, finiteResidueLevel_finrank])
  exact eQ.symm.trans eF

private theorem quotientToFiniteResidueGal_generator
    (H : FiniteIndexNormalSubgroup
      (GrpCat.of (Multiplicative ℤ))) :
    quotientToFiniteResidueGal H
        ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) :
          Multiplicative ℤ ⧸ H.toSubgroup) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k₀
        (finiteResidueLevel H.index) := by
  simp [quotientToFiniteResidueGal, zmodMulEquivOfGenerator_apply_ofAdd_one]

private noncomputable def quotientToFiniteResidueGalHom
    (H : FiniteIndexNormalSubgroup (GrpCat.of (Multiplicative ℤ))) :
    ContinuousMonoidHom
      ↑((ProfiniteGrp.ProfiniteCompletion.diagram
        (GrpCat.of (Multiplicative ℤ))).obj H).toProfinite.toTop
      Gal(finiteResidueLevel H.index/k₀) := by
  letI : Finite
      ↑((ProfiniteGrp.ProfiniteCompletion.diagram
        (GrpCat.of (Multiplicative ℤ))).obj H).toProfinite.toTop :=
    by
      change Finite (Multiplicative ℤ ⧸ H.toSubgroup)
      infer_instance
  letI : DiscreteTopology
      ↑((ProfiniteGrp.ProfiniteCompletion.diagram
        (GrpCat.of (Multiplicative ℤ))).obj H).toProfinite.toTop :=
    Finite.instDiscreteTopology
  refine ⟨?_, continuous_of_discreteTopology⟩
  change (Multiplicative ℤ ⧸ H.toSubgroup) →*
    Gal(finiteResidueLevel H.index/k₀)
  exact (quotientToFiniteResidueGal H).toMonoidHom

private theorem zhat_finiteResidue_component
    (H : FiniteIndexNormalSubgroup
      (GrpCat.of (Multiplicative ℤ))) (z : Zhat) :
    (AlgEquiv.restrictNormalHom (finiteResidueLevel H.index))
        (zhatToAbsoluteResidueGal z) =
      quotientToFiniteResidueGal H (z.1 H) := by
  have hproj : Continuous (fun w : Zhat => w.1 H) := by
    exact continuous_apply H |>.comp continuous_subtype_val
  apply congrFun (Zhat.funext_ofInt (X :=
    Gal(finiteResidueLevel H.index/k₀))
      ((InfiniteGalois.restrictNormalHom_continuous
        (finiteResidueLevel H.index)).comp
          (zhatToAbsoluteResidueGal).continuous_toFun)
      ((quotientToFiniteResidueGalHom H).continuous_toFun.comp hproj) ?_) z
  intro n
  change (AlgEquiv.restrictNormalHom (finiteResidueLevel H.index))
      (zhatToAbsoluteResidueGal (Zhat.ofInt n)) =
    quotientToFiniteResidueGal H ((Zhat.ofInt n).1 H)
  rw [zhatToAbsoluteResidueGal_ofInt, map_zpow]
  change (absoluteResidueFrobenius.restrictNormal
      (finiteResidueLevel H.index)) ^ n = quotientToFiniteResidueGal H
    (QuotientGroup.mk (Multiplicative.ofAdd n))
  rw [finiteResidueLevel_frobenius_restrict]
  rw [show QuotientGroup.mk (Multiplicative.ofAdd n) =
      (((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) :
        Multiplicative ℤ ⧸ H.toSubgroup) ^ n) by
    rw [← QuotientGroup.mk_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]]
  rw [map_zpow, quotientToFiniteResidueGal_generator]

theorem zhatToAbsoluteResidueGal_injective :
    Function.Injective zhatToAbsoluteResidueGal := by
  intro a b hab
  apply Subtype.ext
  funext H
  apply (quotientToFiniteResidueGal H).injective
  rw [← zhat_finiteResidue_component, ← zhat_finiteResidue_component, hab]

/-- The normalized continuous equivalence from `Zhat` to the absolute residue Galois group. -/
noncomputable def zhatEquivAbsoluteResidueGal :
    ContinuousMulEquiv Zhat Gal(k̄₂/k₀) := by
  let e : Zhat ≃* Gal(k̄₂/k₀) :=
    MulEquiv.ofBijective zhatToAbsoluteResidueGal.toMonoidHom
      ⟨zhatToAbsoluteResidueGal_injective,
        zhatToAbsoluteResidueGal_surjective⟩
  have he_cont : Continuous e := zhatToAbsoluteResidueGal.continuous_toFun
  have he_home : IsHomeomorph e :=
    isHomeomorph_iff_continuous_bijective.mpr ⟨he_cont, e.bijective⟩
  have he_inv_cont : Continuous e.symm :=
    (Equiv.isHomeomorph_iff e.toEquiv).mp he_home |>.2
  exact
    { e with
      continuous_toFun := he_cont
      continuous_invFun := he_inv_cont }

@[simp] theorem zhatEquivAbsoluteResidueGal_ofInt (n : ℤ) :
    zhatEquivAbsoluteResidueGal (Zhat.ofInt n) =
      absoluteResidueFrobenius ^ n :=
  zhatToAbsoluteResidueGal_ofInt n

/-- The square-Frobenius-normalized coordinate on the absolute residue Galois group. -/
noncomputable def absoluteResidueGalEquivZhat :
    ContinuousMulEquiv Gal(k̄₂/k₀) Zhat :=
  zhatEquivAbsoluteResidueGal.symm

@[simp] theorem absoluteResidueGalEquivZhat_frobenius :
    absoluteResidueGalEquivZhat absoluteResidueFrobenius = Zhat.ofInt 1 := by
  change zhatEquivAbsoluteResidueGal.symm absoluteResidueFrobenius =
    Zhat.ofInt 1
  apply zhatEquivAbsoluteResidueGal.injective
  rw [zhatEquivAbsoluteResidueGal.apply_symm_apply]
  exact (zhatEquivAbsoluteResidueGal_ofInt 1).symm

/-- The absolute unramified quotient is the full absolute residue Galois group. -/
noncomputable def absoluteInertiaQuotientEquivResidueGal :
    (Kummer.GaloisGroup ℚ_[2] ⧸ absoluteInertiaSubgroup) ≃ₜ*
      Gal(k̄₂/k₀) := by
  let e : (Kummer.GaloisGroup ℚ_[2] ⧸ absoluteInertiaSubgroup) ≃*
      Gal(k̄₂/k₀) :=
    (QuotientGroup.quotientMulEquivOfEq absoluteResidueAlgAction_ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective absoluteResidueAlgAction
        absoluteResidueAlgAction_surjective)
  have he_cont : Continuous e := by
    apply (QuotientGroup.isQuotientMap_mk absoluteInertiaSubgroup).continuous_iff.mpr
    exact absoluteResidueAlgAction_continuous
  have he_home : IsHomeomorph e :=
    isHomeomorph_iff_continuous_bijective.mpr ⟨he_cont, e.bijective⟩
  have he_inv_cont : Continuous e.symm :=
    (Equiv.isHomeomorph_iff e.toEquiv).mp he_home |>.2
  exact
    { e with
      continuous_toFun := he_cont
      continuous_invFun := he_inv_cont }

@[simp] theorem absoluteInertiaQuotientEquivResidueGal_mk
    (g : Kummer.GaloisGroup ℚ_[2]) :
    absoluteInertiaQuotientEquivResidueGal (QuotientGroup.mk g) =
      absoluteResidueAlgAction g := rfl

/-- The canonical square-Frobenius coordinate on the absolute unramified quotient of
`Gal(AlgebraicClosure Q2/Q2)`. -/
noncomputable def absoluteInertiaQuotientEquivZhat :
    (Kummer.GaloisGroup ℚ_[2] ⧸ absoluteInertiaSubgroup) ≃ₜ* Zhat :=
  absoluteInertiaQuotientEquivResidueGal.trans absoluteResidueGalEquivZhat

@[simp] theorem absoluteInertiaQuotientEquivZhat_mk
    (g : Kummer.GaloisGroup ℚ_[2]) :
    absoluteInertiaQuotientEquivZhat (QuotientGroup.mk g) =
      absoluteResidueGalEquivZhat (absoluteResidueAlgAction g) := rfl

#print axioms zhatToAbsoluteResidueGal
#print axioms zhatToAbsoluteResidueGal_ofInt
#print axioms zhatToAbsoluteResidueGal_surjective
#print axioms zhatToAbsoluteResidueGal_injective
#print axioms zhatEquivAbsoluteResidueGal
#print axioms zhatEquivAbsoluteResidueGal_ofInt
#print axioms absoluteResidueGalEquivZhat
#print axioms absoluteResidueGalEquivZhat_frobenius
#print axioms absoluteInertiaQuotientEquivResidueGal
#print axioms absoluteInertiaQuotientEquivResidueGal_mk
#print axioms absoluteInertiaQuotientEquivZhat
#print axioms absoluteInertiaQuotientEquivZhat_mk

end
end GQ2.Dyadic

