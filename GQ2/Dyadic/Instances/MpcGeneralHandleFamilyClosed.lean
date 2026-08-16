/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcHandleDeterminant
import GQ2.Dyadic.Instances.MpcGeneralHandleFamilyFinal

namespace GQ2.Dyadic.Instances.MpcGeneralHandleFamilyClosed

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.Instances.MProcyclicCore
open GQ2.Dyadic.Instances.MpcGeneralHandleCertificate
open GQ2.Dyadic.Instances.MpcGeneralHandleFamilyFinal
open GQ2.Dyadic.Instances.MpcHandleDeterminant
open GQ2.Dyadic.TameSpec

/-- The canonical displayed arbitrary-h Mpc core has its affine determinant unconditionally. -/
theorem mpcAffineDeterminantCertificate_display
    (alpha r q : ℕ) (epsilon : Bool) (h : ℕ) {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) (halpha : 2 ≤ alpha) (hr : 1 ≤ r)
    (hq0 : q ≠ 0) (hqe : Even q) :
    let C := mpcCorePresentationDisplay alpha r (p epsilon r) h d (by omega)
    let nuP := mpcNu alpha r (p epsilon r) h eta (by omega)
    AffineDeterminantCertificate
      (GammaR (2 + 2 * h) q (mpcW alpha r (p epsilon r) d.display h))
      (2 + 2 * h) q (DM alpha h) nuP (standardNumerics (2 + 2 * h))
      (tameOfSpec (2 + 2 * h) q (mpcW alpha r (p epsilon r) d.display h)
        (Count.tameSpecializes_mpcW hq0 hqe (by omega)
          r (p epsilon r) d.display h))
      (C.coreHom hq0 hqe)
      (C.nu_compat_coreHom hq0 hqe
        (Count.tameSpecializes_mpcW hq0 hqe (by omega)
          r (p epsilon r) d.display h)
        nuP (mpcNu_sigma alpha r (p epsilon r) h eta (by omega))
        (mpcNu_wild alpha r (p epsilon r) h eta (by omega)))
      (scalarActionZmodTwo _) := by
  let C := mpcCorePresentationDisplay alpha r (p epsilon r) h d (by omega)
  let nuP := mpcNu alpha r (p epsilon r) h eta (by omega)
  let tame := Count.tameSpecializes_mpcW hq0 hqe (by omega : 1 ≤ alpha)
    r (p epsilon r) d.display h
  let tameHom := tameOfSpec (2 + 2 * h) q
    (mpcW alpha r (p epsilon r) d.display h) tame
  let pro2 := C.coreHom hq0 hqe
  let compat := C.nu_compat_coreHom hq0 hqe tame nuP
    (mpcNu_sigma alpha r (p epsilon r) h eta (by omega))
    (mpcNu_wild alpha r (p epsilon r) h eta (by omega))
  apply RecordBlocks.recBl_determinant_standard_congr
    (n := 2 * h + 2) (m := 2 + 2 * h) (by omega)
  apply mpcAffineDeterminantCertificate_handles d halpha hr hqe
    nuP tameHom pro2 compat
  · exact TameSpec.tameOfSpec_gammaGen _ .sigma
  · exact TameSpec.tameOfSpec_gammaGen _ .tau
  · exact fun i ↦ TameSpec.tameOfSpec_gammaGen _ (.wild i)

/-- The arbitrary-display, arbitrary-h corrected Mpc word certificate has no analytic premise. -/
noncomputable def mpcWordCertificateRN_of_display
    (alpha r q : ℕ) (epsilon : Bool) (h : ℕ) {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) (halpha : 2 ≤ alpha) (hr : 1 ≤ r)
    (hq0 : q ≠ 0) (hqe : Even q) :
    WordCertificateRN (2 + 2 * h) q (mpcW alpha r (p epsilon r) d.display h)
      (DM alpha h) (isProP_DM alpha h)
      (mpcNu alpha r (p epsilon r) h eta (by omega))
      (standardNumerics (2 + 2 * h)) :=
  mpcWordCertificateRN_of_display_determinant alpha r q epsilon h d halpha hr hq0 hqe
    (mpcAffineDeterminantCertificate_display alpha r q epsilon h d
      halpha hr hq0 hqe)

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

omit [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- A tied displayed general-h Mpc branch acquires its corrected residual unconditionally. -/
theorem mpcRowResidualRN_of_tied_display
    (B : MarkedRecip Rec K) {FF : DyadicUnitFiltration K}
    (G : GenAsmBranch K B) {alpha r h : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) (halpha : 2 ≤ alpha) (hr : 1 ≤ r)
    (hp : G.pres = .Mpc alpha r epsilon d.display h)
    (hnu : HEq G.nuP (mpcNu alpha r (p epsilon r) h eta (by omega))) :
    Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  apply mpcRowResidualRN_of_tied_display_determinant B G d halpha hr hp hnu
  exact mpcAffineDeterminantCertificate_display alpha r (qOf K FF) epsilon h d
    halpha hr (qOf_ne_zero K FF) (even_qOf K FF)

/-- The family-selected arbitrary-display Mpc row retains only the honest field premises. -/
theorem mpcRowResidualRN_of_familySelection_closed
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    {FP : FieldParameters} {W : FamilyFieldBranchWitness FP (B.fieldMarkedPair FF)}
    (S : FamilyFieldBranchSelection K FP (B.fieldMarkedPair FF) W)
    {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (hbranch : S.branch = .Mpc alpha r epsilon eta)
    (e : OrientedContinuousMulEquiv
      (chiM alpha (handleCount FP (.Mpc alpha r epsilon eta)))
      (chiCycKTwo (K := K)))
    (hscale : MScalingHypothesis alpha
      (handleCount FP (.Mpc alpha r epsilon eta)))
    (hpivot : ∃ gamma : ℤ_[2]ˣ,
      Multiplicative.toAdd (transport (nuUrKTwo B).toMonoidHom e.1
        ((nuUrKTwo B).continuous_toFun.comp e.1.continuous_toFun)
          (dmC alpha (handleCount FP (.Mpc alpha r epsilon eta)))) =
        (gamma : ℤ_[2]) * 2 ^ r) :
    let d : MpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    ∃ G : GenAsmBranch K B,
      G.pres = .Mpc alpha r epsilon d.display
        (handleCount FP (.Mpc alpha r epsilon eta)) ∧
      Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  let d : MpcDisplayFor eta :=
    Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
  have hvalid := S.valid
  rw [hbranch] at hvalid
  obtain ⟨G, hp, hnu⟩ := mpcGenAsmBranch_of_familySelection_tied
    B FF S hbranch e hscale hpivot
  refine ⟨G, hp, ?_⟩
  exact mpcRowResidualRN_of_tied_display B G d hvalid.1 hvalid.2 hp hnu

#print axioms mpcAffineDeterminantCertificate_display
#print axioms mpcWordCertificateRN_of_display
#print axioms mpcRowResidualRN_of_tied_display
#print axioms mpcRowResidualRN_of_familySelection_closed

end
end GQ2.Dyadic.Instances.MpcGeneralHandleFamilyClosed
