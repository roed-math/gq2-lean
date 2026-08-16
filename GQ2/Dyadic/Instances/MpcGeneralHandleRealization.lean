/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.CertificateSupplyRN
import GQ2.Dyadic.Instances.MpcCertificate

/-!
# General-h marked realizations for procyclic M rows

The level condition makes every handle value divisible by the scaled `C` pivot.  Consequently
the existing Eichler handle moves clear the handle plane without requiring that pivot to be a
unit.  Thus handle clearing is not an invariant obstruction.  The module also packages the
general corrected-equivalence premise into a tied realization at any selected display.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralHandleRealization

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcCert GQ2.Dyadic.Instances.NuWitness
open GQ2.Dyadic.FieldUnimod
open GQ2.Dyadic.SelectedCoreLeavesRN GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc

noncomputable section

/-- The level condition on a general-h M core. -/
def MpcChiKerLevelH (alpha r h : ℕ)
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2])) : Prop :=
  ∀ z, chiM alpha h z = 1 → ∃ y : ℤ_[2], toAdd (nu z) = 2 ^ r * y

/-- The three rank-four residue conditions for the general Mpc target. -/
def MpcMarkedDataH (alpha r pp h : ℕ) (eta : ℤ_[2]ˣ)
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2])) : Prop :=
  (∃ gamma : ℤ_[2]ˣ,
      toAdd (nu (dmC alpha h)) = (gamma : ℤ_[2]) * 2 ^ r) ∧
    (∃ w : ℤ_[2], toAdd (nu (dmD alpha h)) = (eta : ℤ_[2]) + 2 ^ r * w) ∧
      ∃ w : ℤ_[2], toAdd (nu (dmB alpha h)) = (pp : ℤ_[2]) + 2 ^ r * w

/-- A chi-preserving change of variables changes a marking only by a level-divisible value. -/
theorem shift_mem_of_level {alpha r h : ℕ}
    {nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2])}
    (hlev : MpcChiKerLevelH alpha r h nu)
    {Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type)}
    (hPsi : ∀ x, chiM alpha h (Psi x) = chiM alpha h x) (g : DM alpha h) :
    ∃ y : ℤ_[2], toAdd (nu (Psi g)) = toAdd (nu g) + 2 ^ r * y := by
  obtain ⟨y, hy⟩ := hlev (Psi g * g⁻¹) (by rw [map_mul, map_inv, hPsi, mul_inv_cancel])
  refine ⟨y, ?_⟩
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv] at hy
  linear_combination hy

/-- Once the pivot is normalized to `2^r`, the level condition supplies exactly the two
divisibility families consumed by scaled handle clearing. -/
theorem handle_dvd_of_level_and_pivot {alpha r h : ℕ}
    {nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2])}
    (hlev : MpcChiKerLevelH alpha r h nu)
    {Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type)}
    (hPsi : ∀ x, chiM alpha h (Psi x) = chiM alpha h x)
    (hpivot : toAdd (nu (Psi (dmC alpha h))) = 2 ^ r) :
    (∀ j : Fin h, ∃ a, toAdd (nu (Psi (dmGen alpha h (handleIdxU j)))) =
      toAdd (nu (Psi (dmC alpha h))) * a) ∧
      ∀ j : Fin h, ∃ b, toAdd (nu (Psi (dmGen alpha h (handleIdxV j)))) =
        toAdd (nu (Psi (dmC alpha h))) * b := by
  constructor
  · intro j
    obtain ⟨a, ha⟩ := hlev (Psi (dmGen alpha h (handleIdxU j))) (by rw [hPsi, chiM_handleU])
    exact ⟨a, by rw [hpivot]; exact ha⟩
  · intro j
    obtain ⟨b, hb⟩ := hlev (Psi (dmGen alpha h (handleIdxV j))) (by rw [hPsi, chiM_handleV])
    exact ⟨b, by rw [hpivot]; exact hb⟩

/-- One handle can be cleared when both coordinates are multiples of the pivot. -/
theorem exists_frameClear_one_of_dvd {h : ℕ} (j : Fin h)
    (v : Fin (coreRank h) → ℤ_[2]) (a b : ℤ_[2])
    (ha : v (handleIdxU j) = v 2 * a) (hb : v (handleIdxV j) = v 2 * b) :
    ∃ phi ∈ Submonoid.closure (frameClearGens h),
      phi v (handleIdxU j) = 0 ∧ phi v (handleIdxV j) = 0 ∧ phi v 2 = v 2 ∧
        (∀ i : Fin h, i ≠ j → phi v (handleIdxU i) = v (handleIdxU i)) ∧
          ∀ i : Fin h, i ≠ j → phi v (handleIdxV i) = v (handleIdxV i) := by
  refine ⟨frameEnd (frameEichlerV j (-b)) * frameEnd (frameEichlerU j (-a)),
    mul_mem (frameEichlerV_mem_clearGens _ _) (frameEichlerU_mem_clearGens _ _),
    ?_, ?_, ?_, ?_, ?_⟩
  · show frameEichlerV j (-b) (frameEichlerU j (-a) v) (handleIdxU j) = 0
    rw [frameEichlerV_handleU, frameEichlerU_handleU_self, ha, smul_eq_mul]
    ring
  · show frameEichlerV j (-b) (frameEichlerU j (-a) v) (handleIdxV j) = 0
    rw [frameEichlerV_handleV_self, frameEichlerU_handleV, frameEichlerU_two, hb,
      smul_eq_mul]
    ring
  · change frameEichlerV j (-b) (frameEichlerU j (-a) v) 2 = v 2
    rw [frameEichlerV_two, frameEichlerU_two]
  · intro i hij
    change frameEichlerV j (-b) (frameEichlerU j (-a) v) (handleIdxU i) = _
    rw [frameEichlerV_handleU, frameEichlerU_handleU_of_ne _ _ _ hij]
  · intro i hij
    change frameEichlerV j (-b) (frameEichlerU j (-a) v) (handleIdxV i) = _
    rw [frameEichlerV_of_ne _ _ _ (fun hc => hij (handleIdxV_injective hc))
      (handleIdxV_ne_three i), frameEichlerU_handleV]

/-- Clear every handle when all handle values lie in the pivot ideal. -/
theorem exists_frameClear_of_dvd {h : ℕ} (v : Fin (coreRank h) → ℤ_[2])
    (hU : ∀ j : Fin h, ∃ a, v (handleIdxU j) = v 2 * a)
    (hV : ∀ j : Fin h, ∃ b, v (handleIdxV j) = v 2 * b) :
    ∃ phi ∈ Submonoid.closure (frameClearGens h),
      (∀ j : Fin h, phi v (handleIdxU j) = 0) ∧
        (∀ j : Fin h, phi v (handleIdxV j) = 0) ∧ phi v 2 = v 2 := by
  let step : (n : ℕ) → ∃ phi ∈ Submonoid.closure (frameClearGens h),
      (∀ j : Fin h, (j : ℕ) < n →
        phi v (handleIdxU j) = 0 ∧ phi v (handleIdxV j) = 0) ∧
      (∀ j : Fin h, n ≤ (j : ℕ) →
        phi v (handleIdxU j) = v (handleIdxU j) ∧
          phi v (handleIdxV j) = v (handleIdxV j)) ∧ phi v 2 = v 2 := by
    intro n
    induction n with
    | zero =>
      exact ⟨1, one_mem _, fun j hj => absurd hj (by omega),
        fun _ _ => ⟨rfl, rfl⟩, rfl⟩
    | succ n ih =>
      obtain ⟨phi, hphi, hclear, hrest, htwo⟩ := ih
      by_cases hn : n < h
      · let j : Fin h := ⟨n, hn⟩
        obtain ⟨a, ha⟩ := hU j
        obtain ⟨b, hb⟩ := hV j
        have hjrest := hrest j (by simp only [j]; omega)
        obtain ⟨psi, hpsi, hu, hv, htwo', hune, hvne⟩ :=
          exists_frameClear_one_of_dvd j (phi v) a b
            (by rw [hjrest.1, ha, htwo]) (by rw [hjrest.2, hb, htwo])
        refine ⟨psi * phi, mul_mem hpsi hphi, ?_, ?_, ?_⟩
        · intro i hi
          by_cases hin : (i : ℕ) = n
          · have hieq : i = j := Fin.ext hin
            subst hieq
            exact ⟨hu, hv⟩
          · have hne : i ≠ j := fun hc => hin (by rw [hc])
            obtain ⟨hiu, hiv⟩ := hclear i (by omega)
            exact ⟨(hune i hne).trans hiu, (hvne i hne).trans hiv⟩
        · intro i hi
          have hne : i ≠ j := fun hc => by rw [hc] at hi; simp only [j] at hi; omega
          have hirest := hrest i (by omega)
          change psi (phi v) (handleIdxU i) = v (handleIdxU i) ∧
            psi (phi v) (handleIdxV i) = v (handleIdxV i)
          exact ⟨(hune i hne).trans hirest.1, (hvne i hne).trans hirest.2⟩
        · change psi (phi v) 2 = v 2
          rw [htwo', htwo]
      · exact ⟨phi, hphi, fun j hj => hclear j (by have := j.isLt; omega),
          fun j hj => (absurd (show (j : ℕ) < h from j.isLt) (by omega)), htwo⟩
  obtain ⟨phi, hphi, hclear, _, htwo⟩ := step h
  exact ⟨phi, hphi, fun j => (hclear j j.isLt).1,
    fun j => (hclear j j.isLt).2, htwo⟩

/-- Core-level scaled handle clearing, realized by continuous chi-preserving automorphisms. -/
theorem exists_dmClear_nu_of_dvd {alpha h : ℕ}
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (hU : ∀ j : Fin h, ∃ a, toAdd (nu (dmGen alpha h (handleIdxU j))) =
      toAdd (nu (dmC alpha h)) * a)
    (hV : ∀ j : Fin h, ∃ b, toAdd (nu (dmGen alpha h (handleIdxV j))) =
      toAdd (nu (dmC alpha h)) * b) :
    ∃ Psi : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (Psi x) = chiM alpha h x) ∧
        (∀ j : Fin h, nu (Psi (dmGen alpha h (handleIdxU j))) = 1) ∧
          (∀ j : Fin h, nu (Psi (dmGen alpha h (handleIdxV j))) = 1) ∧
            nu (Psi (dmC alpha h)) = nu (dmC alpha h) := by
  obtain ⟨phi, hphi, hu, hv, hc⟩ := exists_frameClear_of_dvd
    (nuFrame nu (dmGen alpha h))
    (fun j => by change ∃ a, _ = toAdd (nu (dmC alpha h)) * a; exact hU j)
    (fun j => by change ∃ b, _ = toAdd (nu (dmC alpha h)) * b; exact hV j)
  obtain ⟨Psi, hmem, hbridge⟩ := exists_dmRealizes alpha h hphi
  refine ⟨Psi, chiM_of_mem_dmClearAuts alpha h hmem, fun j => ?_, fun j => ?_, ?_⟩
  · apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    exact congrFun (hbridge nu) (handleIdxU j) |>.trans (hu j)
  · apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    exact congrFun (hbridge nu) (handleIdxV j) |>.trans (hv j)
  · apply Multiplicative.toAdd.injective
    exact (congrFun (hbridge nu) 2).trans hc

/-- With the general scaling face supplied explicitly, level plus the pivot row normalize `C`
and clear every handle.  This isolates `MScalingHypothesis` as the only non-structural premise
needed before the already exact `D` and `B` transvections can finish the rank-four block. -/
theorem exists_scaled_handle_correction {alpha r h : ℕ}
    (hscale : MScalingHypothesis alpha h)
    (nu : ContinuousMonoidHom (DM alpha h : Type) (Multiplicative ℤ_[2]))
    (hlev : MpcChiKerLevelH alpha r h nu)
    (hpivot : ∃ gamma : ℤ_[2]ˣ,
      toAdd (nu (dmC alpha h)) = (gamma : ℤ_[2]) * 2 ^ r) :
    ∃ u : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type),
      (∀ x, chiM alpha h (u x) = chiM alpha h x) ∧
        toAdd (nu (u (dmC alpha h))) = 2 ^ r ∧
          (∀ j : Fin h, nu (u (dmGen alpha h (handleIdxU j))) = 1) ∧
            ∀ j : Fin h, nu (u (dmGen alpha h (handleIdxV j))) = 1 := by
  obtain ⟨gamma, hgamma⟩ := hpivot
  obtain ⟨Ps, hsChi, hsC⟩ := hscale gamma⁻¹
  let nu2 := nu.comp (autHom Ps)
  have hc2 : toAdd (nu2 (dmC alpha h)) = 2 ^ r := by
    show toAdd (nu (Ps (dmC alpha h))) = _
    rw [hsC nu, hgamma, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_mul]
  obtain ⟨hU, hV⟩ := handle_dvd_of_level_and_pivot hlev hsChi hc2
  obtain ⟨Ph, hhChi, hhU, hhV, hhC⟩ := exists_dmClear_nu_of_dvd nu2 hU hV
  refine ⟨Ph.trans Ps, fun x => ?_, ?_, ?_, ?_⟩
  · show chiM alpha h (Ps (Ph x)) = chiM alpha h x
    rw [hsChi, hhChi]
  · change toAdd (nu2 (Ph (dmC alpha h))) = _
    rw [hhC, hc2]
  · intro j
    exact hhU j
  · intro j
    exact hhV j

/-- General procyclic-M marked-core certificate.  The remaining field-facing premise is exactly
this corrected equivalence; scaled handle clearing itself is discharged above. -/
structure Certificate {G : Type} [Group G] [TopologicalSpace G]
    (alpha r pp h : ℕ) (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha)
    (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2]) where
  abstractEquiv : ContinuousMulEquiv (DM alpha h : Type) G
  orientation : ∀ x, chiG (abstractEquiv x) = chiM alpha h x
  correction : ContinuousMulEquiv (DM alpha h : Type) (DM alpha h : Type)
  correction_chi : ∀ x, chiM alpha h (correction x) = chiM alpha h x
  correction_nu : ∀ x, nuG (abstractEquiv (correction x)) =
    mpcNuPadic alpha r pp h eta halpha x

section Field

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- Turn the general certificate into a realization at the canonical arbitrary-unit marking. -/
def realization {B : MarkedRecip Rec K} {alpha r pp h : ℕ} {eta : ℤ_[2]ˣ}
    {halpha : 1 ≤ alpha}
    (C : Certificate alpha r pp h eta halpha
      (chiCycKTwo (K := K)).toMonoidHom (nuUrKTwo B).toMonoidHom) :
    MarkedCoreRealization (K := K) (B := B) (DM alpha h)
      (SelectedCoreLeavesRN.mpcNu alpha r pp h eta halpha) where
  equiv := C.correction.trans C.abstractEquiv
  nu_equiv := fun x => by
    change ztwoIota (ztwoIota.symm (mpcNuPadic alpha r pp h eta halpha x)) = _
    rw [ztwoIota.apply_symm_apply]
    exact (C.correction_nu x).symm

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The canonical arbitrary-unit marking is surjective at every handle count. -/
theorem mpcNu_surjective (alpha r pp h : ℕ) (eta : ℤ_[2]ˣ) (halpha : 1 ≤ alpha) :
    Function.Surjective (SelectedCoreLeavesRN.mpcNu alpha r pp h eta halpha) :=
  surjective_of_ztwoOne_mem_range _
    ⟨(GQ2.Dyadic.Instances.MProcyclicCore.mpcCorePresentationUnit
      alpha r pp eta h halpha).mark .sigma,
      SelectedCoreLeavesRN.mpcNu_sigma alpha r pp h eta halpha⟩

/-- A tied general-h branch at any selected display, from the exact general certificate. -/
theorem genAsmBranch_of_certificate {B : MarkedRecip Rec K} {alpha r pp h : ℕ}
    {eta : ℤ_[2]ˣ} {halpha : 1 ≤ alpha} (epsilon : Bool) (display : EtaDisplay)
    (hdeg : Module.finrank ℚ_[2] K =
      (SelectedPresentation.Mpc alpha r epsilon display h).degree)
    (C : Certificate alpha r pp h eta halpha
      (chiCycKTwo (K := K)).toMonoidHom (nuUrKTwo B).toMonoidHom) :
    ∃ G : GenAsmBranch K B,
      G.pres = .Mpc alpha r epsilon display h ∧
        HEq G.nuP (SelectedCoreLeavesRN.mpcNu alpha r pp h eta halpha) := by
  exact ⟨{ pres := .Mpc alpha r epsilon display h
           hdeg := hdeg
           nuP := SelectedCoreLeavesRN.mpcNu alpha r pp h eta halpha
           hnuP := mpcNu_surjective alpha r pp h eta halpha
           realization := realization C }, rfl, HEq.rfl⟩

end Field

#print axioms MpcChiKerLevelH
#print axioms MpcMarkedDataH
#print axioms shift_mem_of_level
#print axioms handle_dvd_of_level_and_pivot
#print axioms exists_frameClear_one_of_dvd
#print axioms exists_frameClear_of_dvd
#print axioms exists_dmClear_nu_of_dvd
#print axioms exists_scaled_handle_correction
#print axioms Certificate
#print axioms realization
#print axioms mpcNu_surjective
#print axioms genAsmBranch_of_certificate

end

end GQ2.Dyadic.Instances.MpcGeneralHandleRealization
