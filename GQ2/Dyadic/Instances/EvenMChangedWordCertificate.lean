/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.MCompactFlexibleCertificate
import GQ2.Dyadic.Instances.MpcFlexibleCertificate
import GQ2.Dyadic.WordCertificateRNTransport

/-!
# Corrected even-M certificates after a word change

The unchanged compact-M word can retain the distinguished-pivot obstruction.  This module
moves the word as well as the core.  First, the compact-M and displayed Mpc analytic arguments
are packaged over an arbitrary exact pro-2 boundary map.  Then a normalized presentation of
any tame-compatible equivalent word supplies that boundary map by transport.

Thus the remaining even-M problem is purely a presentation theorem: construct an adapted word,
a normalized field-core presentation, and the candidate-group equivalence.  No determinant,
Gauss-sum, or canonical-pivot premise remains.
-/

namespace GQ2.Dyadic.Instances.EvenMChangedWordCertificate

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words
open GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate
open GQ2.Dyadic.Instances.WordPhase
open GQ2.Dyadic.Instances.WordPhaseCompactMHandleBoundary
open GQ2.Dyadic.Instances.MCompactCore
open GQ2.Dyadic.Instances.MpcCandidateScalar
open GQ2.Dyadic.Instances.MpcCandidateStokes
open GQ2.Dyadic.Instances.MpcHandleDeterminant
open GQ2.Dyadic.MProcyclicExact
open GQ2.Dyadic.MCompact GQ2.Dyadic.Words.MCompact
open GQ2.Dyadic.Words.Mpc
open TameSpec

/-- The compact-M analysis only needs an exact pro-2 boundary map, not a canonical core. -/
noncomputable def mCompactWordCertificateRN_of_boundary
    {alpha h q : ℕ} (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} (hP : IsProP 2 P) {nuP : ContinuousMonoidHom P Ztwo}
    (pro2G : ContinuousMonoidHom
      ((GammaR (2 + 2 * h) q (mCompactW alpha h)) : Type) P)
    (hker : pro2G.toMonoidHom.ker =
      proPKernel 2 ((GammaR (2 + 2 * h) q (mCompactW alpha h)) : Type))
    (hpro2 : Function.Surjective pro2G)
    (compat : ∀ g, nuTq q
      (tameOfSpec (2 + 2 * h) q (mCompactW alpha h)
        (mTameSpecializes alpha h q hq0 hqe) g) = nuP (pro2G g)) :
    WordCertificateRN (2 + 2 * h) q (mCompactW alpha h) P hP nuP
      (standardNumerics (2 + 2 * h)) where
  tameSpecialization := mTameSpecializes alpha h q hq0 hqe
  coreRel := fun G _ _ _ _ _ t => t.eval (pro2 (mCompactW alpha h))
  proTwoWord := fun _ _ _ _ _ _ _ => rfl
  pro2 := pro2G
  ker_pro2 := hker
  hpro2 := hpro2
  compat := compat
  tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
  smulZmod2 := scalarActionZmodTwo _
  contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
  htriv := scalarActionZmodTwo_triv _
  exactLifting := RowClauses.rowCl_mCand_exactLiftingRN halpha hq0 hqe nuP
  stokes := RecordBlocks.recBl_mCand_stokes halpha hq0 hqe
  scalar := RowClauses.rowCl_mCand_scalar halpha hq0 hqe
  determinant := by
    apply RecordBlocks.recBl_determinant_standard_congr
      (n := 2 * h + 2) (m := 2 + 2 * h) (by omega)
    apply RecordBlocks.recBl_mCand_determinant_of_wordPhaseSupply halpha
    apply wPh_recBlWordPhaseSupply_of_branchFree
    exact wPcM_branchFreeSupply_handles nuP
      (tameOfSpec (2 + 2 * h) q (mCompactW alpha h)
        (mTameSpecializes alpha h q hq0 hqe))
      pro2G compat
      (TameSpec.tameOfSpec_gammaGen _ .sigma)
      (TameSpec.tameOfSpec_gammaGen _ .tau)
      (fun i => TameSpec.tameOfSpec_gammaGen _ (.wild i)) halpha
  htame := Count.htame_of_tameSpecializes _
  hwild := Count.hwild_of_tameSpecializes _

/-- A normalized presentation of any word equivalent to compact M inherits the full
corrected certificate. -/
noncomputable def mCompactWordCertificateRN_of_wordEquiv
    {alpha h q : ℕ} (halpha : 2 ≤ alpha) (hq0 : q ≠ 0) (hqe : Even q)
    {R : PWord (Generator (2 + 2 * h))}
    {P : ProfiniteGrp} (hP : IsProP 2 P) {nuP : ContinuousMonoidHom P Ztwo}
    (C : FlexibleCoreLeavesRN (2 + 2 * h) R P nuP)
    (hspec : TameSpecializes (2 + 2 * h) q R)
    (e : ContinuousMulEquiv
      ((GammaR (2 + 2 * h) q R) : Type)
      ((GammaR (2 + 2 * h) q (mCompactW alpha h)) : Type))
    (htame : tameOfSpec (2 + 2 * h) q R hspec =
      (tameOfSpec (2 + 2 * h) q (mCompactW alpha h)
        (mTameSpecializes alpha h q hq0 hqe)).comp
        (e : ContinuousMonoidHom _ _)) :
    WordCertificateRN (2 + 2 * h) q R P hP nuP
      (standardNumerics (2 + 2 * h)) := by
  let p1 := C.pro2 hq0 hqe
  let p0 : ContinuousMonoidHom
      ((GammaR (2 + 2 * h) q (mCompactW alpha h)) : Type) P :=
    p1.comp (e.symm : ContinuousMonoidHom _ _)
  have hcompat0 : ∀ g, nuTq q
      (tameOfSpec (2 + 2 * h) q (mCompactW alpha h)
        (mTameSpecializes alpha h q hq0 hqe) g) = nuP (p0 g) := by
    intro g
    have hg := C.compat hq0 hqe hspec (e.symm g)
    rw [DFunLike.congr_fun htame (e.symm g)] at hg
    simpa [p0, p1] using hg
  let W0 := mCompactWordCertificateRN_of_boundary halpha hq0 hqe hP p0
    (ker_comp_continuousMulEquiv e.symm p1 (C.ker_pro2 hq0 hqe))
    ((C.hpro2 hq0 hqe).comp e.symm.surjective) hcompat0
  have hq2 : 2 ≤ q := by
    obtain ⟨k, hk⟩ := hqe
    omega
  exact W0.transportWordEquiv hq2 hqe hspec e htame

/-- The displayed Mpc analysis also only needs an exact pro-2 boundary map. -/
noncomputable def mpcWordCertificateRN_of_boundary
    {alpha r h q : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} (hP : IsProP 2 P) {nuP : ContinuousMonoidHom P Ztwo}
    (pro2G : ContinuousMonoidHom
      ((GammaR (2 + 2 * h) q
        (mpcW alpha r (p epsilon r) d.display h)) : Type) P)
    (hker : pro2G.toMonoidHom.ker = proPKernel 2
      ((GammaR (2 + 2 * h) q
        (mpcW alpha r (p epsilon r) d.display h)) : Type))
    (hpro2 : Function.Surjective pro2G)
    (compat : ∀ g, nuTq q
      (tameOfSpec (2 + 2 * h) q
        (mpcW alpha r (p epsilon r) d.display h)
        (Count.tameSpecializes_mpcW hq0 hqe (by omega)
          r (p epsilon r) d.display h) g) = nuP (pro2G g)) :
    WordCertificateRN (2 + 2 * h) q
      (mpcW alpha r (p epsilon r) d.display h) P hP nuP
      (standardNumerics (2 + 2 * h)) := by
  let tame := Count.tameSpecializes_mpcW hq0 hqe (by omega : 1 ≤ alpha)
    r (p epsilon r) d.display h
  refine
    { tameSpecialization := tame
      coreRel := fun G _ _ _ _ _ t =>
        t.eval (pro2 (mpcW alpha r (p epsilon r) d.display h))
      proTwoWord := fun _ _ _ _ _ _ _ => rfl
      pro2 := pro2G
      ker_pro2 := hker
      hpro2 := hpro2
      compat := compat
      tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
      smulZmod2 := scalarActionZmodTwo _
      contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
      htriv := scalarActionZmodTwo_triv _
      exactLifting := ?_
      stokes := ?_
      scalar := mpcCandidate_scalar d halpha hr hqe
      determinant := ?_
      htame := Count.htame_of_tameSpecializes _
      hwild := Count.hwild_of_tameSpecializes _ }
  · have H := RecordBlocks.recBl_mpc_exactLiftingRN
      (alpha := alpha) (r := r) (h := h) (q := q) (epsilon := epsilon)
      d halpha hr hqe nuP
    rw [MProcyclicExact.gamma_sign_eq_display alpha r h q epsilon d] at H
    exact NProcyclic.exactLiftingRN_standard_congr (by omega) H
  · apply RecordBlocks.recBl_stokes_standard_congr
      (n := 2 * h + 2) (m := 2 + 2 * h) (by omega)
    exact mpcCand_stokes_displayed
      (alpha := alpha) (r := r) (pp := p epsilon r) (h := h) (q := q)
      d halpha hr hqe (P := P) (nuP := nuP)
  · apply RecordBlocks.recBl_determinant_standard_congr
      (n := 2 * h + 2) (m := 2 + 2 * h) (by omega)
    apply mpcAffineDeterminantCertificate_handles d halpha hr hqe nuP
      (tameOfSpec (2 + 2 * h) q
        (mpcW alpha r (p epsilon r) d.display h) tame)
      pro2G compat
    · exact TameSpec.tameOfSpec_gammaGen _ .sigma
    · exact TameSpec.tameOfSpec_gammaGen _ .tau
    · exact fun i => TameSpec.tameOfSpec_gammaGen _ (.wild i)

/-- A normalized presentation of any word equivalent to displayed Mpc inherits the full
corrected certificate. -/
noncomputable def mpcWordCertificateRN_of_wordEquiv
    {alpha r h q : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ} (d : MpcDisplayFor eta)
    (halpha : 2 ≤ alpha) (hr : 1 ≤ r) (hq0 : q ≠ 0) (hqe : Even q)
    {R : PWord (Generator (2 + 2 * h))}
    {P : ProfiniteGrp} (hP : IsProP 2 P) {nuP : ContinuousMonoidHom P Ztwo}
    (C : FlexibleCoreLeavesRN (2 + 2 * h) R P nuP)
    (hspec : TameSpecializes (2 + 2 * h) q R)
    (e : ContinuousMulEquiv
      ((GammaR (2 + 2 * h) q R) : Type)
      ((GammaR (2 + 2 * h) q
        (mpcW alpha r (p epsilon r) d.display h)) : Type))
    (htame : tameOfSpec (2 + 2 * h) q R hspec =
      (tameOfSpec (2 + 2 * h) q
        (mpcW alpha r (p epsilon r) d.display h)
        (Count.tameSpecializes_mpcW hq0 hqe (by omega)
          r (p epsilon r) d.display h)).comp
        (e : ContinuousMonoidHom _ _)) :
    WordCertificateRN (2 + 2 * h) q R P hP nuP
      (standardNumerics (2 + 2 * h)) := by
  let p1 := C.pro2 hq0 hqe
  let p0 : ContinuousMonoidHom
      ((GammaR (2 + 2 * h) q
        (mpcW alpha r (p epsilon r) d.display h)) : Type) P :=
    p1.comp (e.symm : ContinuousMonoidHom _ _)
  have hcompat0 : ∀ g, nuTq q
      (tameOfSpec (2 + 2 * h) q
        (mpcW alpha r (p epsilon r) d.display h)
        (Count.tameSpecializes_mpcW hq0 hqe (by omega)
          r (p epsilon r) d.display h) g) = nuP (p0 g) := by
    intro g
    have hg := C.compat hq0 hqe hspec (e.symm g)
    rw [DFunLike.congr_fun htame (e.symm g)] at hg
    simpa [p0, p1] using hg
  let W0 := mpcWordCertificateRN_of_boundary d halpha hr hq0 hqe hP p0
    (ker_comp_continuousMulEquiv e.symm p1 (C.ker_pro2 hq0 hqe))
    ((C.hpro2 hq0 hqe).comp e.symm.surjective) hcompat0
  have hq2 : 2 ≤ q := by
    obtain ⟨k, hk⟩ := hqe
    omega
  exact W0.transportWordEquiv hq2 hqe hspec e htame

#print axioms mCompactWordCertificateRN_of_boundary
#print axioms mCompactWordCertificateRN_of_wordEquiv
#print axioms mpcWordCertificateRN_of_boundary
#print axioms mpcWordCertificateRN_of_wordEquiv

end

end GQ2.Dyadic.Instances.EvenMChangedWordCertificate

