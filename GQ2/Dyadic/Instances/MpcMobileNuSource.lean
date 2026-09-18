/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcCoreUnit
import GQ2.Dyadic.Instances.GammaRCorePresentationNuNormalize
import GQ2.Dyadic.MarkedCore.CoVDischarge
import GQ2.Dyadic.Instances.EvenMHeadHandlePairTame
import GQ2.Dyadic.Instances.TameInertiaPrimeToTwoCorrection

/-!
# A normalized procyclic M core using the actual unramified D-coordinate

At positive selected level, the D-coordinate is congruent to a unit modulo `2^r`; hence its
actual value is a unit. Use that unit in the arbitrary-unit Mpc dictionary, whose head is
`D^(etaD⁻¹)`, and simultaneously shear the wild letters to kill their unramified coordinates.
This constructs a complete normalized pro-2 presentation without a distinguished C pivot or
a unit-valued handle. The untouched character is the character on the original `DM alpha h`;
we make no additional claim that the changed generator marking has the old canonical rows.

The structural tame defect is in full inertia, as proved through finite quotients of the
full profinite unramified coordinate, and a prime-to-two tau correction removes it. These are
structural core and tame-specialization results only: analytic supply, pro-2 tame-kernel
claims, and the final field identification are not asserted here.
-/

namespace GQ2.Dyadic.Instances.MpcMobileNuSource

noncomputable section

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Count.PilotN GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Instances.MProcyclicCore
open GQ2.Dyadic.Instances.GammaRCorePresentationNuNormalize
open GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate
open GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalize
open GQ2.Dyadic.PadicOmegaProTwo
open Multiplicative

/-- The actual unit D-coordinate gives a unit-normalized procyclic head. -/
theorem mpcCorePresentationUnit_nu_sigma
    {alpha r p h : ℕ} (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hD : ztwoIota (nuP (dmD alpha h)) = ofAdd (eta : ℤ_[2])) :
    nuP ((mpcCorePresentationUnit alpha r p eta h halpha).mark .sigma) =
      ztwoOne := by
  apply ztwoIota.injective
  let nu' : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]) :=
    (ztwoIota : ContinuousMonoidHom Ztwo (Multiplicative ℤ_[2])).comp nuP
  change nu' (zpowZtwo (isProP_DM alpha h) (dmGen alpha h 3)
    ((eta⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) = ztwoIota ztwoOne
  rw [map_zpowZtwo (isProP_DM alpha h) PropOneOne.isProP_two_multPadicInt]
  change zpowZtwo PropOneOne.isProP_two_multPadicInt
    (ztwoIota (nuP (dmD alpha h))) ((eta⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = _
  rw [hD, SectionThree.zpowZtwo_ofAdd, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, ztwoIota_ztwoOne]

/-- The original Mpc word with all wild rows normalized simultaneously. -/
def mpcMobileNormalizedW (alpha r p h : ℕ) (eta : ℤ_[2]ˣ)
    (halpha : 1 ≤ alpha) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    PWord (Generator (2 + 2 * h)) :=
  PWord.subst
    (wildShearNielsen
      (wildNuCoefficient nuP (mpcCorePresentationUnit alpha r p eta h halpha).mark)).backward
    (mpcWUnit alpha r p eta h)

/-- A complete normalized core; no C-pivot or handle condition is required. -/
def mpcMobileNormalizedCore (alpha r p h : ℕ) (eta : ℤ_[2]ˣ)
    (halpha : 1 ≤ alpha) (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hD : ztwoIota (nuP (dmD alpha h)) = ofAdd (eta : ℤ_[2])) :
    FlexibleCoreLeavesRN (2 + 2 * h)
      (mpcMobileNormalizedW alpha r p h eta halpha nuP) (DM alpha h) nuP :=
  normalizedFlexibleCoreLeaves
    (mpcCorePresentationUnit alpha r p eta h halpha) nuP
    (mpcCorePresentationUnit_nu_sigma eta halpha nuP hD)

/-- The torsion relation forces the zeroth shear coefficient to vanish. -/
theorem mpcCore_wildNuCoefficient_zero
    {alpha r p h : ℕ} (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    wildNuCoefficient nuP (mpcCorePresentationUnit alpha r p eta h halpha).mark
      ⟨0, by omega⟩ = 0 := by
  change toAdd (ztwoIota (nuP
    (mpcUnitUntwist (isProP_DM alpha h) alpha r p eta h
      (dmGen alpha h) 0))) = 0
  rw [mpcUnitUntwist_zero, map_inv, map_mul, map_pow,
    map_inv, map_mul, map_pow, toAdd_inv, toAdd_mul, toAdd_pow]
  let nu' : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]) :=
    (ztwoIota : ContinuousMonoidHom Ztwo (Multiplicative ℤ_[2])).comp nuP
  have hA := nu_dmA_eq alpha h halpha nu'
  change toAdd (ztwoIota (nuP (dmGen alpha h 0))) =
    -(2 : ℤ_[2]) ^ (alpha - 1) * toAdd (ztwoIota (nuP (dmGen alpha h 2))) at hA
  rw [hA, nsmul_eq_mul]
  simp only [m, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- A positive-level perturbation of a unit remains a unit. -/
theorem isUnit_of_unit_add_positive_two_pow
    {r : ℕ} (hr : 0 < r) (eta : ℤ_[2]ˣ) (w : ℤ_[2]) :
    IsUnit ((eta : ℤ_[2]) + 2 ^ r * w) := by
  apply mIsUnit_of_parity_one
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [pow_succ, mul_comm (2 ^ k) 2, mul_assoc, mParityZ_add,
    mParityZ_two_mul, add_zero]
  exact mParityZ_of_isUnit eta.isUnit

/-- The first wild shear coefficient is the discrepancy in the B-row. -/
theorem mpcCore_wildNuCoefficient_one
    {alpha r p h : ℕ} (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hD : ztwoIota (nuP (dmD alpha h)) = ofAdd (eta : ℤ_[2])) :
    wildNuCoefficient nuP (mpcCorePresentationUnit alpha r p eta h halpha).mark
      ⟨1, by omega⟩ = toAdd (ztwoIota (nuP (dmB alpha h))) - p := by
  have hsig := mpcCorePresentationUnit_nu_sigma (r := r) (p := p) eta halpha nuP hD
  change nuP (zpowZtwo (isProP_DM alpha h) (dmGen alpha h 3)
    ((eta⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) = ztwoOne at hsig
  change toAdd (ztwoIota (nuP
    (mpcUnitUntwist (isProP_DM alpha h) alpha r p eta h
      (dmGen alpha h) (nWildIdx h ⟨1, by omega⟩)))) = _
  rw [show nWildIdx h ⟨1, by omega⟩ = 1 by
    apply Fin.ext
    rw [coreVal_one]
    rfl]
  rw [mpcUnitUntwist_one, map_mul, map_zpow, hsig, map_mul, map_zpow,
    ztwoIota_ztwoOne, toAdd_mul, toAdd_zpow]
  simp only [toAdd_ofAdd, zsmul_eq_mul, Int.cast_neg, Int.cast_natCast, mul_one]
  change _ + -(p : ℤ_[2]) = _ - (p : ℤ_[2])
  rw [sub_eq_add_neg]
  rfl

/-- The second wild shear coefficient is the discrepancy in the C-row. -/
theorem mpcCore_wildNuCoefficient_two
    {alpha r p h : ℕ} (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hD : ztwoIota (nuP (dmD alpha h)) = ofAdd (eta : ℤ_[2])) :
    wildNuCoefficient nuP (mpcCorePresentationUnit alpha r p eta h halpha).mark
      ⟨2, by omega⟩ = toAdd (ztwoIota (nuP (dmC alpha h))) - 2 ^ r := by
  have hsig := mpcCorePresentationUnit_nu_sigma (r := r) (p := p) eta halpha nuP hD
  change nuP (zpowZtwo (isProP_DM alpha h) (dmGen alpha h 3)
    ((eta⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) = ztwoOne at hsig
  change toAdd (ztwoIota (nuP
    (mpcUnitUntwist (isProP_DM alpha h) alpha r p eta h
      (dmGen alpha h) (nWildIdx h ⟨2, by omega⟩)))) = _
  rw [show nWildIdx h ⟨2, by omega⟩ = 3 by
    apply Fin.ext
    rw [coreVal_three]
    rfl]
  rw [mpcUnitUntwist_three, map_mul, map_zpow, hsig, map_mul, map_zpow,
    ztwoIota_ztwoOne, toAdd_mul, toAdd_zpow]
  simp only [toAdd_ofAdd, zsmul_eq_mul, Int.cast_neg, mul_one, s]
  simp only [Int.cast_pow, Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat, sub_eq_add_neg]
  rfl

/-- The selected positive-level D residue suffices to construct normalized structural leaves.
The new unit is the actual D-row and retains the selected residue modulo `2^r`. -/
theorem exists_mpcMobileNormalizedCore_of_D_residue
    {alpha r p h : ℕ} (halpha : 1 ≤ alpha) (hr : 0 < r)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (eta : ℤ_[2]ˣ)
    (hD : ∃ w : ℤ_[2], toAdd (ztwoIota (nuP (dmD alpha h))) =
      (eta : ℤ_[2]) + 2 ^ r * w) :
    ∃ etaD : ℤ_[2]ˣ,
      (etaD : ℤ_[2]) = toAdd (ztwoIota (nuP (dmD alpha h))) ∧
      (∃ w : ℤ_[2], (etaD : ℤ_[2]) = (eta : ℤ_[2]) + 2 ^ r * w) ∧
      Nonempty (FlexibleCoreLeavesRN (2 + 2 * h)
        (mpcMobileNormalizedW alpha r p h etaD halpha nuP) (DM alpha h) nuP) := by
  obtain ⟨w, hw⟩ := hD
  have hunit : IsUnit (toAdd (ztwoIota (nuP (dmD alpha h)))) := by
    rw [hw]
    exact isUnit_of_unit_add_positive_two_pow hr eta w
  refine ⟨hunit.unit, hunit.unit_spec, ⟨w, hunit.unit_spec.trans hw⟩, ?_⟩
  refine ⟨mpcMobileNormalizedCore alpha r p h hunit.unit halpha nuP ?_⟩
  rw [hunit.unit_spec]
  rfl

/-- In a commutative target the Mpc word dies when its core wild rows are pro-2 and x0 is one.
No assumption on the full sigma action or the supplied D-word is needed. -/
theorem eval_mpcWAt_eq_one_of_commutative_omegaFixed
    {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {alpha r p h : ℕ} (halpha : 1 ≤ alpha) (t : Marking (2 + 2 * h) G)
    (D : PWord (Generator (2 + 2 * h)))
    (htau : t.τ = 1) (hx0 : t (coreLetter h 0) = 1)
    (hcore : ∀ i : Fin 3, t (coreLetter h i) ^ᶻ omega2 = t (coreLetter h i)) :
    t.eval (mpcWAt alpha r p h D) = 1 := by
  have hdelta (i : Fin 3) : t.eval (dW h i) = 1 := by
    simp only [dW, uW, PWord.prodList_cons, PWord.prodList_nil, Marking.eval_mul,
      Marking.eval_one, meval_omega2Pow, Marking.eval_gen, Marking.eval_inv, mul_one]
    rw [Marking.apply_tau, htau, mul_one, hcore, mul_inv_cancel]
  have he01 (a b : ℕ) : t.eval (e01W h a b) = 1 := by
    simp [e01W, hdelta]
  have hz : t.eval (zW h p) = 1 := by
    cases p with
    | zero => simp [zW, hdelta]
    | succ p => simp [zW, hdelta]
  have he2 : t.eval (e2W h (s r) (m alpha) p) = 1 := by
    have horbit (u : G) (k : ℕ) : orbitNorm u 1 k = 1 := by
      induction k with
      | zero => rfl
      | succ k ih => simp [orbitNorm_succ, ih]
    simp [e2W, hdelta, eval_orbitNormFactors, hz, horbit]
  have hhandle : ((handleTailW h).map (t.eval ·)).prod = 1 := by
    rw [List.prod_eq_one]
    intro x hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
    obtain rfl := eq_handlesW_of_mem_handleTail hw
    rw [eval_handlesW, handleWord, List.prod_eq_one]
    intro x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    simp [commP]
  have hbalance (x : G) : (x ^ (-(m alpha : ℤ))) ^ (2 : ℤ) *
      x ^ ((2 ^ alpha : ℕ) : ℤ) = 1 := by
    rw [← zpow_mul, ← zpow_add]
    have H : (2 : ℤ) * m alpha = (2 ^ alpha : ℕ) := by
      exact_mod_cast two_mul_m halpha
    rw [show -(m alpha : ℤ) * 2 + (2 ^ alpha : ℕ) = 0 by omega, zpow_zero]
  have hcomm (x y : G) : commR x y = 1 := commR_eq_one_iff.mpr (Commute.all _ _)
  rw [mpcWAt, eval_prodListM]
  simp only [List.map_append, List.prod_append, hhandle, mul_one,
    linFactorsAt, hatFactorsAt, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, meval_zpow, meval_comm, he01, he2, hdelta,
    hcomm, one_zpow, one_mul, mul_one, Nat.cast_ofNat]
  have ha : t.eval (aW h (s r) (m alpha)) =
      t.eval (c0W h (s r)) ^ (-(m alpha : ℤ)) := by simp [aW, hx0]
  have hahat : t.eval (aHatW h (s r) (m alpha)) =
      t.eval (c0HatW h (s r)) ^ (-(m alpha : ℤ)) := by simp [aHatW, hdelta]
  rw [ha, hahat, hbalance, hbalance, one_mul]

/-- The normalized word has trivial value in every finite unramified quotient. -/
theorem eval_mpcMobileNormalized_of_proTwoWild
    {P : Type} [CommGroup P] [TopologicalSpace P] [DiscreteTopology P] [Finite P]
    {alpha r p h : ℕ} (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) (b : P) :
    let t : Marking (2 + 2 * h) P :=
      ⟨fun g ↦ match g with
        | .sigma => b
        | .tau => 1
        | .wild _ => 1⟩
    t.eval (mpcMobileNormalizedW alpha r p h eta halpha nuP) = 1 := by
  let k := wildNuCoefficient nuP (mpcCorePresentationUnit alpha r p eta h halpha).mark
  let t : Marking (2 + 2 * h) P :=
    ⟨fun g ↦ match g with
      | .sigma => b
      | .tau => 1
      | .wild _ => 1⟩
  let u := (wildShearNielsen k).backwardMark t
  change t.eval (PWord.subst (wildShearNielsen k).backward (mpcWUnit alpha r p eta h)) = 1
  rw [← (wildShearNielsen k).backwardMark_eval]
  apply eval_mpcWAt_eq_one_of_commutative_omegaFixed halpha u
  · rfl
  · change (1 : P) * b ^ᶻ padicOmega2 (k ⟨0, by omega⟩) = 1
    have hk0 : k ⟨0, by omega⟩ = 0 := mpcCore_wildNuCoefficient_zero eta halpha nuP
    rw [hk0]
    simp
  · intro i
    change ((1 : P) * b ^ᶻ padicOmega2 (k ⟨i, by have := i.isLt; omega⟩)) ^ᶻ omega2 =
      (1 : P) * b ^ᶻ padicOmega2 (k ⟨i, by have := i.isLt; omega⟩)
    simpa using omega2_fixed_zpowHat_padicOmega2 b (k ⟨i, by have := i.isLt; omega⟩)

/-- The normalized word's tame defect lies in full inertia, not merely in `ker nuTq`. -/
theorem tame_eval_mpcMobileNormalized_mem_inertia
    {alpha r p h q : ℕ} (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    (tameMarking (2 + 2 * h) q).eval
        (mpcMobileNormalizedW alpha r p h eta halpha nuP) ∈ inertiaPartQ q := by
  rw [mem_inertiaPartQ_iff_tqToZhat_eq_one]
  apply eq_one_of_forall_mem_openNormalSubgroup
  intro U
  let pi : ContinuousMonoidHom Zhat (Zhat ⧸ U.toSubgroup) :=
    ⟨QuotientGroup.mk' U.toSubgroup, QuotientGroup.continuous_mk⟩
  haveI : DiscreteTopology (Zhat ⧸ U.toSubgroup) := by
    refine discreteTopology_of_isOpen_singleton_one ?_
    have hpre : (QuotientGroup.mk : Zhat → Zhat ⧸ U.toSubgroup) ⁻¹' {1} =
        (U.toSubgroup : Set Zhat) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
        QuotientGroup.eq_one_iff]
    rw [← (QuotientGroup.isQuotientMap_mk U.toSubgroup).isOpen_preimage, hpre]
    exact U.isOpen'
  haveI : Finite (Zhat ⧸ U.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ U.isOpen'
  letI : CommGroup (Zhat ⧸ U.toSubgroup) :=
    { (inferInstance : Group (Zhat ⧸ U.toSubgroup)) with
      mul_comm := by
        intro a b
        induction a using QuotientGroup.induction_on with | _ a =>
        induction b using QuotientGroup.induction_on with | _ b =>
        change QuotientGroup.mk' U.toSubgroup (a * b) =
          QuotientGroup.mk' U.toSubgroup (b * a)
        exact congrArg (QuotientGroup.mk' U.toSubgroup) (zhat_mul_comm a b) }
  let f : ContinuousMonoidHom (Tq q) (Zhat ⧸ U.toSubgroup) := pi.comp (tqToZhat q)
  let t0 : Marking (2 + 2 * h) (Zhat ⧸ U.toSubgroup) :=
    ⟨fun g ↦ match g with
      | .sigma => pi (Zhat.ofInt 1)
      | .tau => 1
      | .wild _ => 1⟩
  have hmark : (tameMarking (2 + 2 * h) q).map ⇑f = t0 := by
    ext g
    cases g with
    | sigma =>
      change pi (tqToZhat q (tqSigma q)) = pi (Zhat.ofInt 1)
      rw [tqToZhat_tqSigma]
    | tau =>
      change pi (tqToZhat q (tqTau q)) = 1
      rw [tqToZhat_tqTau, map_one]
    | wild i =>
      change pi (tqToZhat q 1) = 1
      simp
  apply (QuotientGroup.eq_one_iff _).mp
  change pi (tqToZhat q ((tameMarking (2 + 2 * h) q).eval
    (mpcMobileNormalizedW alpha r p h eta halpha nuP))) = 1
  calc
    pi (tqToZhat q ((tameMarking (2 + 2 * h) q).eval
        (mpcMobileNormalizedW alpha r p h eta halpha nuP))) =
        ((tameMarking (2 + 2 * h) q).map ⇑f).eval
          (mpcMobileNormalizedW alpha r p h eta halpha nuP) :=
      Marking.map_eval f (tameMarking (2 + 2 * h) q)
        (mpcMobileNormalizedW alpha r p h eta halpha nuP)
    _ = t0.eval (mpcMobileNormalizedW alpha r p h eta halpha nuP) := by rw [hmark]
    _ = 1 := eval_mpcMobileNormalized_of_proTwoWild eta halpha nuP (pi (Zhat.ofInt 1))

/-- Remove the normalized word's full tame defect with a prime-to-two tau-power. -/
def mpcMobileTameCorrectedW {q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    (alpha r p h : ℕ) (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    PWord (Generator (2 + 2 * h)) :=
  tamePrimeToTwoCorrectedWord hq0 hqe
    (mpcMobileNormalizedW alpha r p h eta halpha nuP)
    (tame_eval_mpcMobileNormalized_mem_inertia eta halpha nuP)

/-- The corrected word has the ordinary canonical tame specialization. -/
theorem mpcMobileTameCorrectedW_specializes
    {alpha r p h q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    TameSpec.TameSpecializes (2 + 2 * h) q
      (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP) :=
  tamePrimeToTwoCorrectedWord_specializes hq0 hqe _ _

/-- The tame-corrected word retains the complete normalized pro-2 core. -/
def mpcMobileTameCorrectedCore {q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    (alpha r p h : ℕ) (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hD : ztwoIota (nuP (dmD alpha h)) = ofAdd (eta : ℤ_[2])) :
    FlexibleCoreLeavesRN (2 + 2 * h)
      (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP) (DM alpha h) nuP := by
  let C := mpcMobileNormalizedCore alpha r p h eta halpha nuP hD
  exact
    { presentation := CorePresentation.ofPrimeToTwoTameCorrection C.presentation hq0 hqe
        (tame_eval_mpcMobileNormalized_mem_inertia eta halpha nuP)
      nu_sigma := C.nu_sigma
      nu_wild := C.nu_wild }

#print axioms mpcCorePresentationUnit_nu_sigma
#print axioms mpcMobileNormalizedCore
#print axioms mpcCore_wildNuCoefficient_zero
#print axioms mpcCore_wildNuCoefficient_one
#print axioms mpcCore_wildNuCoefficient_two
#print axioms exists_mpcMobileNormalizedCore_of_D_residue
#print axioms eval_mpcWAt_eq_one_of_commutative_omegaFixed
#print axioms tame_eval_mpcMobileNormalized_mem_inertia
#print axioms mpcMobileTameCorrectedW_specializes
#print axioms mpcMobileTameCorrectedCore

end
end GQ2.Dyadic.Instances.MpcMobileNuSource
