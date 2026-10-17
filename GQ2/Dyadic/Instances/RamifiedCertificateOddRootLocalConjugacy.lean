/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateOddRootFrobeniusConjugacy
import GQ2.Dyadic.Instances.RamifiedCertificateAbsoluteResidueAlgebraicClosure
import Mathlib.RingTheory.Henselian

/-!
# Odd cyclotomic local conjugacy and the absolute residue Frobenius lift

The valuation ring of the absolute `2`-adic algebraic closure is Henselian.  The proof is direct:
a monic polynomial splits in the algebraic closure, each root is integral, and a product with norm
less than one has a factor with norm less than one.

For an odd primitive root `zeta`, reduce its integral minimal polynomial to the residue field.
Square Frobenius preserves the reduced polynomial and separability makes the derivative nonzero at
the squared residue.  Hensel lifting then produces a root close to `zeta ^ 2`; separation of
distinct odd roots forces equality.  Hence `zeta` and `zeta ^ 2` are conjugate over `Q_2`.

The W182--W183 compactness equivalences assemble these finite local conjugacies into one absolute
Galois element squaring every odd root of unity.  Equivalently, the canonical action on the
absolute residue field is surjective.  Thus the residue-lifting half of the compatible ramified
analysis is reduced to the normalized unramified coordinate and its oriented-tame comparison;
finite residue lifting and action surjectivity themselves are no longer open.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open SpectralLocalField
open Polynomial

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]
local notation "k₀" => IsLocalRing.ResidueField BaseInteger
local notation "k̄₂" => IsLocalRing.ResidueField absoluteNormInteger

local instance : Algebra BaseInteger absoluteNormInteger := absoluteNormIntegerAlgebra
local instance : IsLocalHom (algebraMap BaseInteger absoluteNormInteger) :=
  absoluteNormInteger_algebraMap_isLocalHom
local instance : Algebra k₀ k̄₂ := absoluteResidueFieldAlgebra
local instance : Finite k₀ := baseResidueField_finite
local instance : Fintype k₀ := Fintype.ofFinite k₀
local instance : Algebra.IsAlgebraic k₀ k̄₂ := absoluteResidueField_isAlgebraic
local instance : IsAlgClosed k̄₂ := absoluteResidueField_isAlgClosed

private theorem baseResidue_natCast_ne_zero_of_odd {m : ℕ} (hm : Odd m) :
    (m : k₀) ≠ 0 := by
  intro hzero
  have hzmod : (m : ZMod 2) = 0 := by
    simpa using congrArg baseIntegerResidueEquivZMod hzero
  exact (ZMod.natCast_ne_zero_iff_odd.mpr hm) hzmod

private theorem absoluteResidue_eval_square (P : k₀[X]) (x : k̄₂) :
    P.eval₂ (algebraMap k₀ k̄₂) (x ^ 2) =
      (P.eval₂ (algebraMap k₀ k̄₂) x) ^ 2 := by
  calc
    P.eval₂ (algebraMap k₀ k̄₂) (x ^ 2) =
        P.eval₂ (algebraMap k₀ k̄₂) (absoluteResidueFrobenius x) := by
          rw [absoluteResidueFrobenius_apply]
    _ = absoluteResidueFrobenius
        (P.eval₂ (algebraMap k₀ k̄₂) x) :=
      (algHom_eval₂_algebraMap P absoluteResidueFrobenius.toAlgHom x).symm
    _ = (P.eval₂ (algebraMap k₀ k̄₂) x) ^ 2 :=
      absoluteResidueFrobenius_apply _

theorem absoluteNormInteger_henselianLocalRing :
    HenselianLocalRing absoluteNormInteger := by
  constructor
  intro f hf a₀ hfa hderiv
  let F : ℚ̄₂[X] := f.map (algebraMap absoluteNormInteger ℚ̄₂)
  have hFmonic : F.Monic := hf.map _
  have hFsplit : F.Splits := IsAlgClosed.splits F
  have hFne : F ≠ 0 := hFmonic.ne_zero
  have hsmall : ‖F.eval (a₀ : ℚ̄₂)‖ < 1 := by
    have hres : IsLocalRing.residue absoluteNormInteger (f.eval a₀) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hfa
    have hnorm := (absoluteResidue_zero_iff_norm_lt_one (f.eval a₀)).mp hres
    calc
      ‖F.eval (a₀ : ℚ̄₂)‖ =
          ‖algebraMap absoluteNormInteger ℚ̄₂ (f.eval a₀)‖ := by
            change ‖(f.map (algebraMap absoluteNormInteger ℚ̄₂)).eval
              (algebraMap absoluteNormInteger ℚ̄₂ a₀)‖ = _
            rw [eval_map_apply]
      _ = ‖((f.eval a₀ : absoluteNormInteger) : ℚ̄₂)‖ := rfl
      _ < 1 := hnorm
  have hroot : ∃ r ∈ F.roots, ‖(a₀ : ℚ̄₂) - r‖ < 1 := by
    by_contra h
    push Not at h
    have hnorm_one : ∀ r ∈ F.roots, ‖(a₀ : ℚ̄₂) - r‖ = 1 := by
      intro r hr
      have hrroot : F.eval r = 0 := (mem_roots hFne).mp hr
      have hrint : IsIntegral absoluteNormInteger r := by
        refine ⟨f, hf, ?_⟩
        simpa [F, eval_map] using hrroot
      obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hrint
      have hrnorm : ‖r‖ ≤ 1 := by
        rw [← hb]
        exact_mod_cast b.2
      have hdiff : ‖(a₀ : ℚ̄₂) - r‖ ≤ 1 := by
        rw [sub_eq_add_neg]
        refine le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_
        rw [norm_neg]
        exact max_le (by exact_mod_cast a₀.2) hrnorm
      exact le_antisymm hdiff (h r hr)
    have heval := hFsplit.eval_eq_prod_roots_of_monic hFmonic (a₀ : ℚ̄₂)
    have hprod : ‖(F.roots.map fun r => (a₀ : ℚ̄₂) - r).prod‖ = 1 := by
      have haux : ∀ s : Multiset ℚ̄₂,
          (∀ r ∈ s, ‖(a₀ : ℚ̄₂) - r‖ = 1) →
            ‖(s.map fun r => (a₀ : ℚ̄₂) - r).prod‖ = 1 := by
        intro s hs
        induction s using Multiset.induction_on with
        | empty => simp
        | @cons r s ih =>
            rw [Multiset.map_cons, Multiset.prod_cons, norm_mul,
              hs r (Multiset.mem_cons_self r s),
              ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx)), one_mul]
      exact haux F.roots hnorm_one
    rw [heval, hprod] at hsmall
    exact lt_irrefl 1 hsmall
  obtain ⟨r, hr, hrclose⟩ := hroot
  have hrroot : F.eval r = 0 := (mem_roots hFne).mp hr
  have hrint : IsIntegral absoluteNormInteger r := by
    refine ⟨f, hf, ?_⟩
    simpa [F, eval_map] using hrroot
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hrint
  refine ⟨a, ?_, ?_⟩
  · apply Subtype.ext
    change algebraMap absoluteNormInteger ℚ̄₂ (f.eval a) = 0
    calc
      algebraMap absoluteNormInteger ℚ̄₂ (f.eval a) =
          F.eval (algebraMap absoluteNormInteger ℚ̄₂ a) := by
            change algebraMap absoluteNormInteger ℚ̄₂ (f.eval a) =
              (f.map (algebraMap absoluteNormInteger ℚ̄₂)).eval
                (algebraMap absoluteNormInteger ℚ̄₂ a)
            rw [eval_map_apply]
      _ = F.eval r := by rw [ha]
      _ = 0 := hrroot
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (absoluteResidue_zero_iff_norm_lt_one (a - a₀)).mpr
    change ‖(a : ℚ̄₂) - (a₀ : ℚ̄₂)‖ < 1
    rw [show ((a : absoluteNormInteger) : ℚ̄₂) = r by exact ha, norm_sub_rev]
    exact hrclose

theorem primitiveOddRoot_isConjRoot_square {m : ℕ} (hm : Odd m)
    {zeta : ℚ̄₂} (hzeta : IsPrimitiveRoot zeta m) :
    IsConjRoot ℚ_[2] zeta (zeta ^ 2) := by
  letI : HenselianLocalRing absoluteNormInteger :=
    absoluteNormInteger_henselianLocalRing
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hzpow : zeta ^ m = 1 := hzeta.pow_eq_one
  have hzint : IsIntegral BaseInteger zeta := by
    refine ⟨X ^ m - C 1, monic_X_pow_sub_C (1 : BaseInteger) hm0, ?_⟩
    simp [hzpow]
  let zetaI : integralClosure BaseInteger ℚ̄₂ := ⟨zeta, hzint⟩
  let p₀ : BaseInteger[X] := minpoly BaseInteger zetaI
  let p : absoluteNormInteger[X] :=
    p₀.map (algebraMap BaseInteger absoluteNormInteger)
  let zetaA : absoluteNormInteger := ⟨zeta, by
    change ‖zeta‖₊ ≤ 1
    exact_mod_cast ((hzeta.isOfFinOrder hm0).norm_eq_one.le)⟩
  let zetaSqA : absoluteNormInteger := zetaA ^ 2
  let P₀ : k₀[X] := p₀.map (IsLocalRing.residue BaseInteger)
  let x : k̄₂ := IsLocalRing.residue absoluteNormInteger zetaA
  have hp₀monic : p₀.Monic :=
    minpoly.monic (Algebra.IsIntegral.isIntegral zetaI)
  have hpmonic : p.Monic := hp₀monic.map _
  have hp₀zeta : Polynomial.aeval zetaI p₀ = 0 := minpoly.aeval BaseInteger zetaI
  have hp₀zetaQ :
      p₀.eval₂ (algebraMap BaseInteger ℚ̄₂) zeta = 0 := by
    calc
      p₀.eval₂ (algebraMap BaseInteger ℚ̄₂) zeta =
          (Subalgebra.val (integralClosure BaseInteger ℚ̄₂))
            (p₀.eval₂ (algebraMap BaseInteger
              (integralClosure BaseInteger ℚ̄₂)) zetaI) := by
                symm
                exact algHom_eval₂_algebraMap p₀
                  (Subalgebra.val (integralClosure BaseInteger ℚ̄₂)) zetaI
      _ = 0 := by rw [← aeval_def, hp₀zeta, map_zero]
  have hBaseComp :
      (algebraMap absoluteNormInteger ℚ̄₂).comp
          (algebraMap BaseInteger absoluteNormInteger) =
        algebraMap BaseInteger ℚ̄₂ := by
    ext a
    rfl
  have hpzeta : p.eval zetaA = 0 := by
    apply Subtype.ext
    change algebraMap absoluteNormInteger ℚ̄₂ (p.eval zetaA) = 0
    rw [show p = p₀.map (algebraMap BaseInteger absoluteNormInteger) by rfl,
      eval_map]
    rw [Polynomial.hom_eval₂, hBaseComp]
    exact hp₀zetaQ
  have hcomp :
      (IsLocalRing.residue absoluteNormInteger).comp
          (algebraMap BaseInteger absoluteNormInteger) =
        (algebraMap k₀ k̄₂).comp (IsLocalRing.residue BaseInteger) := by
    rfl
  have hresP : p.map (IsLocalRing.residue absoluteNormInteger) =
      P₀.map (algebraMap k₀ k̄₂) := by
    change (p₀.map (algebraMap BaseInteger absoluteNormInteger)).map
        (IsLocalRing.residue absoluteNormInteger) =
      (p₀.map (IsLocalRing.residue BaseInteger)).map (algebraMap k₀ k̄₂)
    rw [map_map, map_map, hcomp]
  have hP₀x : P₀.eval₂ (algebraMap k₀ k̄₂) x = 0 := by
    have h := congrArg (IsLocalRing.residue absoluteNormInteger) hpzeta
    rw [map_zero, ← eval_map_apply, hresP] at h
    simpa [eval₂_eq_eval_map] using h
  have hP₀x2 : P₀.eval₂ (algebraMap k₀ k̄₂) (x ^ 2) = 0 := by
    rw [absoluteResidue_eval_square, hP₀x, zero_pow (by norm_num)]
  have hp₀dvd : p₀ ∣ X ^ m - 1 := by
    haveI : Module.IsTorsionFree BaseInteger ℚ̄₂ :=
      Module.IsTorsionFree.trans_faithfulSMul BaseInteger ℚ_[2] ℚ̄₂
    apply minpoly.isIntegrallyClosed_dvd (Algebra.IsIntegral.isIntegral zetaI)
    apply Subtype.ext
    simpa [zetaI, sub_eq_zero] using hzpow
  have hP₀dvd : P₀ ∣ (X ^ m - 1 : k₀[X]) := by
    apply Polynomial.map_dvd (IsLocalRing.residue BaseInteger) at hp₀dvd
    simpa [P₀] using hp₀dvd
  have hP₀sep : P₀.Separable := by
    exact (separable_X_pow_sub_C (1 : k₀)
      (baseResidue_natCast_ne_zero_of_odd hm) one_ne_zero).of_dvd hP₀dvd
  have hP₀deriv :
      P₀.derivative.eval₂ (algebraMap k₀ k̄₂) (x ^ 2) ≠ 0 :=
    hP₀sep.eval₂_derivative_ne_zero (algebraMap k₀ k̄₂) hP₀x2
  have hpzetaSq_mem : p.eval zetaSqA ∈ IsLocalRing.maximalIdeal absoluteNormInteger := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h : IsLocalRing.residue absoluteNormInteger (p.eval zetaSqA) = 0 := by
      rw [← eval_map_apply, hresP]
      rw [show IsLocalRing.residue absoluteNormInteger zetaSqA = x ^ 2 by
        simp [zetaSqA, x]]
      simpa [eval₂_eq_eval_map] using hP₀x2
    exact h
  have hpderiv_unit : IsUnit (p.derivative.eval zetaSqA) := by
    have hresPderiv : p.derivative.map (IsLocalRing.residue absoluteNormInteger) =
        P₀.derivative.map (algebraMap k₀ k̄₂) := by
      rw [← derivative_map, ← derivative_map]
      exact congrArg derivative hresP
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    have h : IsLocalRing.residue absoluteNormInteger
        (p.derivative.eval zetaSqA) ≠ 0 := by
      rw [← eval_map_apply, hresPderiv]
      rw [show IsLocalRing.residue absoluteNormInteger zetaSqA = x ^ 2 by
        simp [zetaSqA, x]]
      simpa [eval₂_eq_eval_map] using hP₀deriv
    exact h
  obtain ⟨y, hypy, hycong⟩ := HenselianLocalRing.is_henselian
    p hpmonic zetaSqA hpzetaSq_mem hpderiv_unit
  have hyclose : ‖(y : ℚ̄₂) - zeta ^ 2‖ < 1 := by
    apply (absoluteResidue_zero_iff_norm_lt_one (y - zetaSqA)).mp
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hycong
  have hyp₀y : p₀.eval₂ (algebraMap BaseInteger ℚ̄₂) (y : ℚ̄₂) = 0 := by
    have hy := congrArg (fun a : absoluteNormInteger => (a : ℚ̄₂)) hypy
    change algebraMap absoluteNormInteger ℚ̄₂ (p.eval y) = 0 at hy
    rw [show p = p₀.map (algebraMap BaseInteger absoluteNormInteger) by rfl,
      eval_map] at hy
    rw [Polynomial.hom_eval₂, hBaseComp] at hy
    exact hy
  have hyroot : (y : ℚ̄₂) ^ m = 1 := by
    obtain ⟨q, hq⟩ := hp₀dvd
    have hmap := congrArg
      (fun Q : BaseInteger[X] => Q.eval₂ (algebraMap BaseInteger ℚ̄₂) (y : ℚ̄₂)) hq
    simp only [eval₂_mul, hyp₀y, zero_mul, eval₂_sub, eval₂_pow, eval₂_X,
      eval₂_one, sub_eq_zero] at hmap
    exact hmap
  have hzsqroot : (zeta ^ 2) ^ m = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hzpow, one_pow]
  have hyeq : (y : ℚ̄₂) = zeta ^ 2 := by
    by_contra hne
    have hsep := TeichmullerLift.norm_sub_eq_one_of_pow_eq_one hm hyroot hzsqroot hne
    rw [hsep] at hyclose
    exact lt_irrefl 1 hyclose
  apply (isConjRoot_iff_aeval_eq_zero (Algebra.IsIntegral.isIntegral zeta)).mpr
  have hminpoly :
      p₀.map (algebraMap BaseInteger ℚ_[2]) = minpoly ℚ_[2] zeta := by
    exact minpoly.ofSubring (A := BaseInteger) zetaI
  have hymin : (minpoly ℚ_[2] zeta).eval₂
      (algebraMap ℚ_[2] ℚ̄₂) (y : ℚ̄₂) = 0 := by
    rw [← hminpoly, eval₂_map]
    exact hyp₀y
  simpa [aeval_def, hyeq] using hymin

/-- One absolute Galois element simultaneously induces square Frobenius on all odd roots. -/
theorem exists_squaresOddRootsOfUnity :
    ∃ g : Kummer.GaloisGroup ℚ_[2], SquaresOddRootsOfUnity g := by
  rw [exists_squaresOddRoots_iff_primitive_conjugacy]
  exact fun _m hm _zeta hzeta => primitiveOddRoot_isConjRoot_square hm hzeta

/-- The canonical absolute residue action is surjective. -/
theorem absoluteResidueAlgAction_surjective :
    Function.Surjective absoluteResidueAlgAction :=
  absoluteResidueAlgAction_surjective_iff_exists_squaresOddRoots.mpr
    exists_squaresOddRootsOfUnity

#print axioms primitiveOddRoot_isConjRoot_square
#print axioms absoluteNormInteger_henselianLocalRing
#print axioms exists_squaresOddRootsOfUnity
#print axioms absoluteResidueAlgAction_surjective

end
end GQ2.Dyadic
