/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.TameInertiaProcyclic
import GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalize
import GQ2.Dyadic.Instances.RamifiedCertificateQurZhatFrobeniusComparison
import GQ2.TameSimple

/-!
# Tame correction for the uniformly normalized even-M source

The simultaneous wild shear used by the strict-handle construction preserves the pro-`2`
presentation but may introduce a tame defect.  This module computes the defect in the full
unramified coordinate, proves that it lies in actual tame inertia, and removes it using the
rank-generic profinite `tau` correction.

The result is uniform in the rank and handle count.  It gives one corrected word with both an
ordinary tame specialization and complete normalized `FlexibleCoreLeavesRN`; no nilpotency
class or frozen field row occurs.
-/

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalize

noncomputable section

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Words
open GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Instances.EvenMHeadHandleSource
open GQ2.Dyadic.Instances.EvenMHeadHandlePairSource
open GQ2.Dyadic.Instances.EvenMHeadHandlePairCore
open GQ2.Dyadic.Instances.GammaRCorePresentationNuNormalize
open GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate

theorem headHandlePairSwap_coreZero {h : ℕ} (j : Fin h) :
    headHandlePairSwap j (.wild ⟨0, by omega⟩) =
      (.wild ⟨0, by omega⟩ : Generator (2 + 2 * h)) := by
  have hhead : headHandleSwap j (.wild ⟨0, by omega⟩) =
      (.wild ⟨0, by omega⟩ : Generator (2 + 2 * h)) := by
    apply Equiv.swap_apply_of_ne_of_ne
    · simp
    · intro H
      have E := congrArg (Generator.equivFin (2 + 2 * h)) H
      simp [handleU, Generator.equivFin] at E
  have htail : tailHandleSwap j (.wild ⟨0, by omega⟩) =
      (.wild ⟨0, by omega⟩ : Generator (2 + 2 * h)) := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro H
      have E := congrArg (Generator.equivFin (2 + 2 * h)) H
      simp [coreLetter, Generator.equivFin] at E
    · intro H
      have E := congrArg (Generator.equivFin (2 + 2 * h)) H
      simp [handleV, Generator.equivFin] at E
  rw [headHandlePairSwap]
  change tailHandleSwap j (headHandleSwap j (.wild ⟨0, by omega⟩)) = _
  rw [hhead]
  exact htail

theorem headHandlePairCorePresentation_mark_coreZero
    (alpha h : ℕ) (halpha : 1 ≤ alpha) (j : Fin h) :
    (headHandlePairCorePresentation alpha h halpha j).mark
      (.wild ⟨0, by omega⟩) = MCompactCore.mUntwist alpha h (dmGen alpha h) 0 := by
  rw [headHandlePairCorePresentation_mark, headHandlePairSwap_coreZero,
    MCompactCore.mCorePresentation_mark_wild]
  congr 2

theorem headHandlePair_wildNuCoefficient_coreZero
    {alpha h : ℕ} (halpha : 1 ≤ alpha) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    wildNuCoefficient nuP
      (headHandlePairCorePresentation alpha h halpha j).mark
      ⟨0, by omega⟩ = 0 := by
  rw [wildNuCoefficient, headHandlePairCorePresentation_mark_coreZero,
    MCompactCore.mUntwist_zero, map_inv, map_mul, map_zpow]
  rw [map_inv, map_mul, map_zpow]
  rw [toAdd_inv, toAdd_mul, toAdd_zpow]
  let nu' : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]) :=
    (ztwoIota : ContinuousMonoidHom Ztwo (Multiplicative ℤ_[2])).comp nuP
  have hA := nu_dmA_eq alpha h halpha nu'
  change Multiplicative.toAdd (ztwoIota (nuP (dmA alpha h))) =
    -(2 : ℤ_[2]) ^ (alpha - 1) *
      Multiplicative.toAdd (ztwoIota (nuP (dmC alpha h))) at hA
  rw [show dmGen alpha h 0 = dmA alpha h from rfl,
    show dmGen alpha h 2 = dmC alpha h from rfl, hA]
  rw [zsmul_eq_mul, Int.cast_natCast]
  rw [show (mOf alpha : ℤ_[2]) = (2 : ℤ_[2]) ^ (alpha - 1) by
    simp [mOf, Nat.cast_pow]]
  ring

/-- Every finite image of a `2`-adic shear exponent is fixed by `omega2`. -/
theorem omega2_fixed_zpowHat_padicOmega2
    {P : Type} [Group P] [TopologicalSpace P] [DiscreteTopology P] [Finite P]
    (x : P) (u : ℤ_[2]) :
    (x ^ᶻ padicOmega2 u) ^ᶻ omega2 = x ^ᶻ padicOmega2 u := by
  rw [zpowHat_omega2]
  have hmem : x ^ᶻ padicOmega2 u ∈ Subgroup.zpowers (powOmega2 x) := by
    rw [zpowHat_padicOmega2, padicOmega2Exp]
    rw [mul_comm, pow_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  obtain ⟨k, hk⟩ :=
    (IsPGroup.iff_orderOf.mp (GQ2.FoxH.isPGroup_zpowers_powOmega2 x)) ⟨_, hmem⟩
  exact powOmega2_eq_self_of_orderOf_two_pow ((orderOf_submonoid _).trans hk)

/-- The compact-M word dies in a commutative target when its relevant rows are `omega2`-fixed. -/
theorem eval_mCompact_eq_one_of_commutative_omegaFixed
    {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {alpha h : ℕ} (t : Marking (2 + 2 * h) G)
    (htau : t.τ = 1)
    (hx0 : t (coreLetter h 0) = 1)
    (hsigma : t.σ ^ᶻ omega2 = t.σ)
    (hcore : ∀ i : Fin 3,
      t (coreLetter h i) ^ᶻ omega2 = t (coreLetter h i)) :
    t.eval (mCompactW alpha h) = 1 := by
  have hhandle : t.eval (handlesW h) = 1 := by
    rw [eval_handlesW, MarkedCore.handleWord, List.prod_eq_one]
    intro x hx
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    simp [commP]
  have hdelta : ∀ i : Fin 3,
      t.eval (GQ2.Dyadic.Words.MCompact.deltaC h i) = 1 := by
    intro i
    rw [eval_deltaC, htau, mul_one, hcore, mul_inv_cancel]
  have hE := eval_eRevW_eq_eBlock (α := alpha) t
  rw [hdelta, hdelta] at hE
  rw [eval_mCompact_factors, hhandle, mul_one, Marking.eval_def, mFactors,
    PWord.eval_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    PWord.eval_zpow, PWord.eval_comm, PWord.eval_inv, PWord.eval_conj,
    PWord.eval_gen, PWord.eval_prodList, PWord.eval_omega2PowHat,
    ← Marking.eval_def, eval_sigma2W, hE, a0W, j2W, hx0, hcore, hsigma,
    htau, Marking.apply_tau, inv_one, one_mul, mul_one]
  rw [commR_eq_one_iff.mpr (Commute.all _ _), one_mul,
    conjR_eq_self_of_comm]
  rw [show eBlock (t.σ ^ (mOf alpha : ℤ)) (t.σ ^ (mOf alpha : ℤ)) 1 1 = 1 by
    simp [eBlock]]
  rw [← zpow_mul, ← mul_assoc, ← zpow_add,
    show (-(mOf alpha : ℤ) * 2 + 2 * (mOf alpha : ℤ)) = 0 by ring,
    zpow_zero, one_mul]
  simp

theorem eval_headHandlePairNormalized_of_proTwoHead
    {P : Type} [CommGroup P] [TopologicalSpace P] [DiscreteTopology P] [Finite P]
    {alpha h : ℕ} (halpha : 1 ≤ alpha) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) (b : P) :
    let t : Marking (2 + 2 * h) P :=
      ⟨fun g ↦ match g with
        | .sigma => b
        | .tau => 1
        | .wild _ => 1⟩
    t.eval (headHandlePairNormalizedW alpha h halpha j nuP) = 1 := by
  let k := wildNuCoefficient nuP
    (headHandlePairCorePresentation alpha h halpha j).mark
  let t : Marking (2 + 2 * h) P :=
    ⟨fun g ↦ match g with
      | .sigma => b
      | .tau => 1
      | .wild _ => 1⟩
  let u := (wildShearNielsen k).backwardMark t
  let s := (headHandlePairNielsen j).backwardMark u
  have hs_apply (g : Generator (2 + 2 * h)) :
      s g = t.eval ((wildShearNielsen k).backward (headHandlePairSwap j g)) := by
    change t.eval ((wildShearNielsen k).backward
      ((headHandlePairSwap j).symm g)) = _
    rw [headHandlePairSwap_symm]
  change t.eval (PWord.subst (wildShearNielsen k).backward
    (headHandlePairCompactW alpha j)) = 1
  rw [← (wildShearNielsen k).backwardMark_eval]
  change u.eval (headHandlePairCompactW alpha j) = 1
  rw [headHandlePairCompactW_eq_nielsenBackward,
    ← (headHandlePairNielsen j).backwardMark_eval]
  change s.eval (mCompactW alpha h) = 1
  apply eval_mCompact_eq_one_of_commutative_omegaFixed s
  · rfl
  · rw [hs_apply]
    rw [show headHandlePairSwap j (coreLetter h 0) = coreLetter h 0 by
      simpa [coreLetter] using headHandlePairSwap_coreZero j]
    change (1 : P) * b ^ᶻ padicOmega2 (k ⟨0, by omega⟩) = 1
    have hk0 : k ⟨0, by omega⟩ = 0 := by
      dsimp [k]
      have H := headHandlePair_wildNuCoefficient_coreZero halpha j nuP
      rw [show (0 : Fin (2 + 2 * h + 1)) = ⟨0, by omega⟩ by
        apply Fin.ext
        rfl]
      exact H
    rw [hk0]
    simp
  · change s .sigma ^ᶻ omega2 = s .sigma
    rw [hs_apply]
    rw [headHandlePairSwap_sigma]
    change ((1 : P) * b ^ᶻ padicOmega2 (k _)) ^ᶻ omega2 =
      (1 : P) * b ^ᶻ padicOmega2 (k _)
    simpa using omega2_fixed_zpowHat_padicOmega2 b (k _)
  · intro i
    rw [hs_apply]
    obtain ⟨l, hl⟩ : ∃ l : Fin (2 + 2 * h + 1),
        headHandlePairSwap j (coreLetter h i) = .wild l := by
      fin_cases i
      · refine ⟨⟨0, by omega⟩, ?_⟩
        change headHandlePairSwap j (coreLetter h 0) = coreLetter h 0
        rw [headHandlePairSwap]
        change tailHandleSwap j (headHandleSwap j (coreLetter h 0)) = coreLetter h 0
        rw [headHandleSwap_coreLetter, tailHandleSwap_coreZero]
      · refine ⟨⟨1, by omega⟩, ?_⟩
        change headHandlePairSwap j (coreLetter h 1) = coreLetter h 1
        rw [headHandlePairSwap]
        change tailHandleSwap j (headHandleSwap j (coreLetter h 1)) = coreLetter h 1
        rw [headHandleSwap_coreLetter, tailHandleSwap_coreOne]
      · refine ⟨⟨4 + 2 * (j : ℕ), by have := j.isLt; omega⟩, ?_⟩
        change headHandlePairSwap j (coreLetter h 2) = handleV j
        exact headHandlePairSwap_coreTwo j
    rw [hl]
    change ((1 : P) * b ^ᶻ padicOmega2 (k l)) ^ᶻ omega2 =
      (1 : P) * b ^ᶻ padicOmega2 (k l)
    simpa using omega2_fixed_zpowHat_padicOmega2 b (k l)

/-- Full tame inertia is exactly the kernel of the full profinite unramified coordinate. -/
theorem mem_inertiaPartQ_iff_tqToZhat_eq_one {q : ℕ} {x : Tq q} :
    x ∈ inertiaPartQ q ↔ tqToZhat q x = 1 := by
  rw [← quotientMk_eq_one_iff (N := inertiaPartQ q)]
  constructor
  · intro hx
    have H := congrArg (qurQEquivZhat q) hx
    change qurQToZhat q (qMkQ q x) = qurQToZhat q 1 at H
    rw [qurQToZhat_qMkQ, map_one] at H
    exact H
  · intro hx
    apply (qurQEquivZhat q).injective
    change qurQToZhat q (qMkQ q x) = qurQToZhat q 1
    rw [qurQToZhat_qMkQ, map_one]
    exact hx

/-- The normalized all-rank word has no full unramified tame defect. -/
theorem tame_eval_headHandlePairNormalized_mem_inertia
    {alpha h q : ℕ} (halpha : 1 ≤ alpha) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    (tameMarking (2 + 2 * h) q).eval
        (headHandlePairNormalizedW alpha h halpha j nuP) ∈ inertiaPartQ q := by
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
        exact congrArg (QuotientGroup.mk' U.toSubgroup)
          (GQ2.Dyadic.Words.Mpc.zhat_mul_comm a b) }
  let f : ContinuousMonoidHom (Tq q) (Zhat ⧸ U.toSubgroup) :=
    pi.comp (tqToZhat q)
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
    (headHandlePairNormalizedW alpha h halpha j nuP))) = 1
  calc
    pi (tqToZhat q ((tameMarking (2 + 2 * h) q).eval
        (headHandlePairNormalizedW alpha h halpha j nuP))) =
        ((tameMarking (2 + 2 * h) q).map ⇑f).eval
          (headHandlePairNormalizedW alpha h halpha j nuP) :=
      Marking.map_eval f (tameMarking (2 + 2 * h) q)
        (headHandlePairNormalizedW alpha h halpha j nuP)
    _ = t0.eval (headHandlePairNormalizedW alpha h halpha j nuP) := by rw [hmark]
    _ = 1 := eval_headHandlePairNormalized_of_proTwoHead halpha j nuP
      (pi (Zhat.ofInt 1))

/-- The normalized strict-handle word with its full tame-inertia defect removed. -/
noncomputable def headHandlePairTameCorrectedW
    (alpha h q : ℕ) (halpha : 1 ≤ alpha) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    PWord (Generator (2 + 2 * h)) :=
  tameCorrectedWord (q := q) (headHandlePairNormalizedW alpha h halpha j nuP)
    (tame_eval_headHandlePairNormalized_mem_inertia (q := q) halpha j nuP)

theorem headHandlePairTameCorrectedW_specializes
    (alpha h q : ℕ) (halpha : 1 ≤ alpha) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    TameSpec.TameSpecializes (2 + 2 * h) q
      (headHandlePairTameCorrectedW alpha h q halpha j nuP) := by
  unfold headHandlePairTameCorrectedW
  exact tameCorrectedWord_specializes _ _

/-- Tame correction preserves the normalized complete pro-`2` presentation and its rows. -/
noncomputable def headHandlePairTameCorrectedFlexibleCore
    {alpha h q : ℕ} (halpha : 1 ≤ alpha) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hU : nuP (dmGen alpha h (handleIdxU j)) = ztwoOne) :
    FlexibleCoreLeavesRN (2 + 2 * h)
      (headHandlePairTameCorrectedW alpha h q halpha j nuP)
      (DM alpha h) nuP := by
  let C := headHandlePairNormalizedFlexibleCore halpha j nuP hU
  change FlexibleCoreLeavesRN (2 + 2 * h)
    (tameCorrectedWord (q := q) (headHandlePairNormalizedW alpha h halpha j nuP)
      (tame_eval_headHandlePairNormalized_mem_inertia (q := q) halpha j nuP))
    (DM alpha h) nuP
  refine
    { presentation := CorePresentation.ofTameCorrection C.presentation
        (tame_eval_headHandlePairNormalized_mem_inertia (q := q) halpha j nuP)
      nu_sigma := ?_
      nu_wild := ?_ }
  · exact C.nu_sigma
  · exact C.nu_wild

#print axioms headHandlePair_wildNuCoefficient_coreZero
#print axioms omega2_fixed_zpowHat_padicOmega2
#print axioms eval_mCompact_eq_one_of_commutative_omegaFixed
#print axioms eval_headHandlePairNormalized_of_proTwoHead
#print axioms mem_inertiaPartQ_iff_tqToZhat_eq_one
#print axioms tame_eval_headHandlePairNormalized_mem_inertia
#print axioms headHandlePairTameCorrectedW
#print axioms headHandlePairTameCorrectedW_specializes
#print axioms headHandlePairTameCorrectedFlexibleCore

end

end GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalize
