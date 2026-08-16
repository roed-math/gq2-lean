/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.NpcPlanePrimitive
import GQ2.Dyadic.Instances.FieldBranchIdentificationTied

/-!
# General-handle compact-N realization at level zero

The existing compact-N level-zero certificate was stated only at handle count zero. At a
general handle count, the exact level witness need not be primitive on the original
`(sigma, x2)` plane: its unit coordinate may lie on a handle. `NpcPlanePrimitive` supplies the
missing frame step, moving such a coordinate into `x2` through a chi-preserving Eichler
automorphism.

After that correction, the existing arbitrary-handle compact-N marked certificate applies
directly. This module records both the resulting certificate and its adaptation to the common
`MarkedCoreRealization` at the canonical `nNuZtwo` marking. No additional frame or
unimodularity hypothesis remains.
-/

namespace GQ2.Dyadic.Instances.N0GeneralLevelZero

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.Instances.NpcCert
open GQ2.Dyadic.Instances.NpcCertificateLevel
open GQ2.Dyadic.Instances.NpcPlanePrimitive
open scoped GQ2.SectionThree.TopAbInstances

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- Level zero at any handle count supplies the compact-N marked certificate. -/
theorem marked_matching_certificate_KTwoN_of_level_zero_general
    (B : MarkedRecip Rec K) {alpha h : ℕ} (halpha : 2 ≤ alpha) (hr : B.r = 0)
    (e : OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) :
    Nonempty (MarkedCoreCertificateKTwoN B alpha h) := by
  let nu' : ContinuousMonoidHom (DN alpha h : Type) (Multiplicative ℤ_[2]) :=
    npcCert_transport (nuUrKTwo B).toMonoidHom e.1
      ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun)
  have hlev : NpcChiKerLevel alpha 0 h nu' := by
    exact npcChiKerLevel_of_level B hr e
  obtain ⟨gbar, hgchi, hgnu⟩ := B.nu_ker_chi_ge 1
  obtain ⟨g, rfl⟩ := surjective_toAbK K gbar
  let q : maxProPQuotient 2 (GalK K) := maxProPMk 2 (GalK K) g
  let x : (DN alpha h : Type) := e.1.symm q
  have hxchi : chiN alpha h x = 1 := by
    calc
      chiN alpha h x = chiCycKTwo (K := K) (e.1 x) := (e.2 x).symm
      _ = chiCycKTwo (K := K) (e.1 (e.1.symm q)) := rfl
      _ = chiCycKTwo (K := K) (maxProPMk 2 (GalK K) g) := by
        rw [e.1.apply_symm_apply]
      _ = chiCycKAb K (toAbK K g) := by rw [chiCycKAb_toAbK, chiCycKTwo_maxProPMk]
      _ = 1 := hgchi
  have hxnu : toAdd (nu' x) = 2 ^ (0 : ℕ) := by
    change toAdd (nuUrKTwo B (e.1 (e.1.symm q))) = 1
    rw [e.1.apply_symm_apply]
    change toAdd (nuUrKTwo B (maxProPMk 2 (GalK K) g)) = 1
    rw [nuUrKTwo_maxProPMk, hgnu, hr, pow_zero, one_mul]
  obtain ⟨Psi, hchi, a, b, ha, hb, hab⟩ :=
    exists_dnPlanePrimitive_of_level_exact halpha nu' hlev x hxchi hxnu
  let e' : OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K)) :=
    ⟨Psi.trans e.1, fun z ↦ (e.2 (Psi z)).trans (hchi z)⟩
  apply marked_matching_certificate_KTwoN B alpha h e'.1 e'.2
  have ha' : toAdd (nu' (Psi (dnSigma alpha h))) = a := by simpa using ha
  have hb' : toAdd (nu' (Psi (dnX2 alpha h))) = b := by simpa using hb
  change IsUnit (toAdd (nu' (Psi (dnSigma alpha h)))) ∨
    IsUnit (toAdd (nu' (Psi (dnX2 alpha h))))
  exact ha' ▸ hb' ▸ hab

/-- General-handle compact-N field realization from level zero and an oriented equivalence. -/
theorem markedCoreRealizationN_of_level_zero_general
    (B : MarkedRecip Rec K) {alpha h : ℕ} (halpha : 2 ≤ alpha) (hr : B.r = 0)
    (e : OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) :
    Nonempty (MarkedCoreRealization (K := K) (B := B) (DN alpha h)
      (nNuZtwo alpha h)) := by
  obtain ⟨C⟩ := marked_matching_certificate_KTwoN_of_level_zero_general B halpha hr e
  exact ⟨MarkedCoreRealization.ofCertificateN (nNuZtwo alpha h)
    (GQ2.Dyadic.FieldBranchId.fieldId_ztwoIota_nNuZtwo alpha h) C⟩

#print axioms marked_matching_certificate_KTwoN_of_level_zero_general
#print axioms markedCoreRealizationN_of_level_zero_general

end
end GQ2.Dyadic.Instances.N0GeneralLevelZero
