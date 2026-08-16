/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcGeneralHandleFamily
import GQ2.Dyadic.Instances.MpcCandidateStokes
import GQ2.Dyadic.Instances.MpcCandidateScalar
import GQ2.Dyadic.GeneralAssembly

/-!
# General-h procyclic-M family consumers

The corrected family realization is packaged as a tied displayed branch.  The corresponding
corrected word certificate works at every handle count and every honest `MpcDisplayFor`; its
sole analytic premise is the affine determinant.  The family endpoint therefore retains
exactly the oriented equivalence, explicit scaling hypothesis, transported `C` pivot, and
determinant.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralHandleFamilyFinal

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.SelectedCoreLeavesRN
open GQ2.Dyadic.Instances.MProcyclicCore
open GQ2.Dyadic.Instances.MpcCandidateScalar
open GQ2.Dyadic.Instances.MpcCandidateStokes
open GQ2.Dyadic.Instances.MpcGeneralHandleCertificate
open GQ2.Dyadic.Instances.MpcGeneralHandleRealization
open GQ2.Dyadic.Instances.MpcGeneralHandleFamily
open GQ2.Dyadic.TameSpec

private noncomputable def corePresentationOfProTwoEvalEq
    {n : ℕ} {R S : PWord (Generator n)} {P : ProfiniteGrp}
    (C : CorePresentation n R P)
    (heval : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking n G),
        t.eval (pro2 R) = t.eval (pro2 S)) :
    CorePresentation n S P where
  isProP := C.isProP
  mark := C.mark
  mark_tau := C.mark_tau
  rel := by
    rw [← heval]
    exact C.rel
  liftHom := fun hQ t ht hrel ↦ C.liftHom hQ t ht ((heval _ t).trans hrel)
  liftHom_mark := fun hQ t ht hrel g ↦
    C.liftHom_mark hQ t ht ((heval _ t).trans hrel) g
  hom_ext := C.hom_ext

/-- The arbitrary-unit core presentation transported to any compatible displayed Mpc word. -/
noncomputable def mpcCorePresentationDisplay
    (alpha r pp h : ℕ) {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta) (halpha : 1 ≤ alpha) :
    CorePresentation (2 + 2 * h) (mpcW alpha r pp d.display h) (DM alpha h) :=
  corePresentationOfProTwoEvalEq
    (mpcCorePresentationUnit alpha r pp eta h halpha) (by
      intro G _ _ _ _ _ t
      rw [eval_pro2_mpcWUnit halpha, eval_pro2_mpcW halpha, d.represents])

/-- The general-h, arbitrary-display corrected Mpc word certificate.  Exact lifting, Stokes,
and scalar count are theorems; only the affine determinant remains an input. -/
noncomputable def mpcWordCertificateRN_of_display_determinant
    (alpha r q : ℕ) (epsilon : Bool) (h : ℕ) {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) (halpha : 2 ≤ alpha) (hr : 1 ≤ r)
    (hq0 : q ≠ 0) (hqe : Even q)
    (determinant :
      let C := mpcCorePresentationDisplay alpha r (p epsilon r) h d (by omega)
      let nuP := mpcNu alpha r (p epsilon r) h eta (by omega)
      AffineDeterminantCertificate
        (GammaR (2 + 2 * h) q (mpcW alpha r (p epsilon r) d.display h))
        (2 + 2 * h) q (DM alpha h) nuP (standardNumerics (2 + 2 * h))
        (tameOfSpec (2 + 2 * h) q (mpcW alpha r (p epsilon r) d.display h)
          (Count.tameSpecializes_mpcW hq0 hqe (by omega) r (p epsilon r) d.display h))
        (C.coreHom hq0 hqe)
        (C.nu_compat_coreHom hq0 hqe
          (Count.tameSpecializes_mpcW hq0 hqe (by omega) r (p epsilon r) d.display h)
          nuP (mpcNu_sigma alpha r (p epsilon r) h eta (by omega))
          (mpcNu_wild alpha r (p epsilon r) h eta (by omega)))
        (scalarActionZmodTwo _)) :
    WordCertificateRN (2 + 2 * h) q (mpcW alpha r (p epsilon r) d.display h)
      (DM alpha h) (isProP_DM alpha h)
      (mpcNu alpha r (p epsilon r) h eta (by omega))
      (standardNumerics (2 + 2 * h)) := by
  let C := mpcCorePresentationDisplay alpha r (p epsilon r) h d (by omega)
  let nuP := mpcNu alpha r (p epsilon r) h eta (by omega)
  let tame := Count.tameSpecializes_mpcW hq0 hqe (by omega : 1 ≤ alpha)
    r (p epsilon r) d.display h
  have hnuSigma : nuP (C.mark .sigma) = ztwoOne :=
    mpcNu_sigma alpha r (p epsilon r) h eta (by omega)
  have hnuWild : ∀ j : Fin (2 + 2 * h + 1), nuP (C.mark (.wild j)) = 1 :=
    mpcNu_wild alpha r (p epsilon r) h eta (by omega)
  refine
    { tameSpecialization := tame
      coreRel := fun G _ _ _ _ _ t ↦ t.eval (pro2 (mpcW alpha r (p epsilon r) d.display h))
      proTwoWord := fun _ _ _ _ _ _ _ ↦ rfl
      pro2 := C.coreHom hq0 hqe
      ker_pro2 := C.ker_coreHom hq0 hqe
      hpro2 := C.coreHom_surjective hq0 hqe
      compat := C.nu_compat_coreHom hq0 hqe tame nuP hnuSigma hnuWild
      tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
      smulZmod2 := scalarActionZmodTwo _
      contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
      htriv := scalarActionZmodTwo_triv _
      exactLifting := ?_
      stokes := ?_
      scalar := ?_
      determinant := determinant
      htame := Count.htame_of_tameSpecializes tame
      hwild := Count.hwild_of_tameSpecializes tame }
  · have H := RecordBlocks.recBl_mpc_exactLiftingRN
      (alpha := alpha) (r := r) (h := h) (q := q) (epsilon := epsilon)
      d halpha hr hqe nuP
    rw [MProcyclicExact.gamma_sign_eq_display alpha r h q epsilon d] at H
    exact NProcyclic.exactLiftingRN_standard_congr (by omega) H
  · apply RecordBlocks.recBl_stokes_standard_congr
      (n := 2 * h + 2) (m := 2 + 2 * h) (by omega)
    exact mpcCand_stokes_displayed
      (alpha := alpha) (r := r) (pp := p epsilon r) (h := h) (q := q)
      d halpha hr hqe (P := DM alpha h) (nuP := nuP)
  · exact mpcCandidate_scalar d halpha hr hqe

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

omit [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- A displayed general-h Mpc branch tied to the canonical arbitrary-unit marking acquires
the corrected residual from its exact affine determinant. -/
theorem mpcRowResidualRN_of_tied_display_determinant
    (B : MarkedRecip Rec K) {FF : DyadicUnitFiltration K}
    (G : GenAsmBranch K B) {alpha r h : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) (halpha : 2 ≤ alpha) (hr : 1 ≤ r)
    (hp : G.pres = .Mpc alpha r epsilon d.display h)
    (hnu : HEq G.nuP (mpcNu alpha r (p epsilon r) h eta (by omega)))
    (determinant :
      let C := mpcCorePresentationDisplay alpha r (p epsilon r) h d (by omega)
      let nuP := mpcNu alpha r (p epsilon r) h eta (by omega)
      AffineDeterminantCertificate
        (GammaR (2 + 2 * h) (qOf K FF)
          (mpcW alpha r (p epsilon r) d.display h))
        (2 + 2 * h) (qOf K FF) (DM alpha h) nuP
        (standardNumerics (2 + 2 * h))
        (tameOfSpec (2 + 2 * h) (qOf K FF)
          (mpcW alpha r (p epsilon r) d.display h)
          (Count.tameSpecializes_mpcW (qOf_ne_zero K FF) (even_qOf K FF)
            (by omega) r (p epsilon r) d.display h))
        (C.coreHom (qOf_ne_zero K FF) (even_qOf K FF))
        (C.nu_compat_coreHom (qOf_ne_zero K FF) (even_qOf K FF)
          (Count.tameSpecializes_mpcW (qOf_ne_zero K FF) (even_qOf K FF)
            (by omega) r (p epsilon r) d.display h)
          nuP (mpcNu_sigma alpha r (p epsilon r) h eta (by omega))
          (mpcNu_wild alpha r (p epsilon r) h eta (by omega)))
        (scalarActionZmodTwo _)) :
    Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  obtain ⟨pres, hdeg, nu, hnuP, realization⟩ := G
  subst hp
  obtain rfl : nu = mpcNu alpha r (p epsilon r) h eta (by omega) := eq_of_heq hnu
  exact ⟨⟨mpcWordCertificateRN_of_display_determinant
    alpha r (qOf K FF) epsilon h d halpha hr
    (qOf_ne_zero K FF) (even_qOf K FF) determinant⟩⟩

/-- Package the family-selected general-h realization as a displayed tied branch. -/
theorem mpcGenAsmBranch_of_familySelection_tied
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
      HEq G.nuP (mpcNu alpha r (p epsilon r)
        (handleCount FP (.Mpc alpha r epsilon eta)) eta (by
          have hv := S.valid
          rw [hbranch] at hv
          exact le_trans (by decide) hv.1)) := by
  let d : MpcDisplayFor eta :=
    Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
  let h := handleCount FP (.Mpc alpha r epsilon eta)
  have halpha : 1 ≤ alpha := by
    have hv := S.valid
    rw [hbranch] at hv
    exact le_trans (by decide) hv.1
  obtain ⟨M⟩ := realization_of_familySelection B FF S hbranch e hscale hpivot
  have hdeg : Module.finrank ℚ_[2] K =
      (SelectedPresentation.Mpc alpha r epsilon d.display h).degree := by
    have hd := S.degree_eq_field
    rw [hbranch] at hd
    exact hd.symm
  exact ⟨{ pres := .Mpc alpha r epsilon d.display h
           hdeg := hdeg
           nuP := mpcNu alpha r (p epsilon r) h eta halpha
           hnuP := mpcNu_surjective alpha r (p epsilon r) h eta halpha
           realization := M }, rfl, HEq.rfl⟩

/-- The family-selected arbitrary-display Mpc row, including its tied branch and corrected RN
residual.  The premise list is exactly orientation, scaling, transported `C` pivot, and the
displayed affine determinant. -/
theorem mpcRowResidualRN_of_familySelection
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
        (gamma : ℤ_[2]) * 2 ^ r)
    (determinant :
      let d : MpcDisplayFor eta :=
        Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
      let h := handleCount FP (.Mpc alpha r epsilon eta)
      let C := mpcCorePresentationDisplay alpha r (p epsilon r) h d (by
        have hv := S.valid
        rw [hbranch] at hv
        exact le_trans (by decide) hv.1)
      let nuP := mpcNu alpha r (p epsilon r) h eta (by
        have hv := S.valid
        rw [hbranch] at hv
        exact le_trans (by decide) hv.1)
      AffineDeterminantCertificate
        (GammaR (2 + 2 * h) (qOf K FF)
          (mpcW alpha r (p epsilon r) d.display h))
        (2 + 2 * h) (qOf K FF) (DM alpha h) nuP
        (standardNumerics (2 + 2 * h))
        (tameOfSpec (2 + 2 * h) (qOf K FF)
          (mpcW alpha r (p epsilon r) d.display h)
          (Count.tameSpecializes_mpcW (qOf_ne_zero K FF) (even_qOf K FF)
            (by
              have hv := S.valid
              rw [hbranch] at hv
              exact le_trans (by decide) hv.1)
            r (p epsilon r) d.display h))
        (C.coreHom (qOf_ne_zero K FF) (even_qOf K FF))
        (C.nu_compat_coreHom (qOf_ne_zero K FF) (even_qOf K FF)
          (Count.tameSpecializes_mpcW (qOf_ne_zero K FF) (even_qOf K FF)
            (by
              have hv := S.valid
              rw [hbranch] at hv
              exact le_trans (by decide) hv.1)
            r (p epsilon r) d.display h)
          nuP
          (mpcNu_sigma alpha r (p epsilon r) h eta (by
            have hv := S.valid
            rw [hbranch] at hv
            exact le_trans (by decide) hv.1))
          (mpcNu_wild alpha r (p epsilon r) h eta (by
            have hv := S.valid
            rw [hbranch] at hv
            exact le_trans (by decide) hv.1)))
        (scalarActionZmodTwo _)) :
    let d : MpcDisplayFor eta :=
      Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
    ∃ G : GenAsmBranch K B,
      G.pres = .Mpc alpha r epsilon d.display
        (handleCount FP (.Mpc alpha r epsilon eta)) ∧
      Nonempty (GenAsmRowResidualRN (FF := FF) G) := by
  let d : MpcDisplayFor eta :=
    Eq.mp (congrArg BranchData.DisplayFor hbranch) S.display
  let h := handleCount FP (.Mpc alpha r epsilon eta)
  have hvalid := S.valid
  rw [hbranch] at hvalid
  obtain ⟨G, hp, hnu⟩ := mpcGenAsmBranch_of_familySelection_tied
    B FF S hbranch e hscale hpivot
  refine ⟨G, hp, ?_⟩
  exact mpcRowResidualRN_of_tied_display_determinant
    B G d hvalid.1 hvalid.2 hp hnu determinant

#print axioms mpcCorePresentationDisplay
#print axioms mpcWordCertificateRN_of_display_determinant
#print axioms mpcRowResidualRN_of_tied_display_determinant
#print axioms mpcGenAsmBranch_of_familySelection_tied
#print axioms mpcRowResidualRN_of_familySelection

end
end GQ2.Dyadic.Instances.MpcGeneralHandleFamilyFinal
