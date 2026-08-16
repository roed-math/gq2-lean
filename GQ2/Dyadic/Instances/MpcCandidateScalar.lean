import GQ2.Dyadic.Instances.RecordBlocks

/-!
# Scalar certificates for procyclic-M candidates

This module packages the scalar-character count and scalar Hilbert certificate for
every valid displayed procyclic-M candidate.  It does not supply the remaining
Stokes-count certificate or the determinant phase needed for a full corrected word
certificate.
-/

namespace GQ2.Dyadic.Instances.MpcCandidateScalar

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.MProcyclicExact
open GQ2.Dyadic.Count.PilotN
open GQ2.CardH2GammaA
open GQ2.Dyadic.Instances.MProcyclicCore
open GQ2.Dyadic.MarkedCore GQ2.Dyadic.TameSpec

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-- The scalar character count for a displayed procyclic-M candidate. -/
theorem mpcCandidate_homCard_of_uniformPushed
    {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : UniformPushedHsimp alpha r pp h q d)
    (hα : 1 ≤ alpha) (hr : 1 ≤ r) (hqe : Even q) :
    Nat.card (ContinuousMonoidHom
      ((displayedGamma alpha r pp h q d : Type)) (Multiplicative (ZMod 2)))
      = (standardNumerics (2 * h + 2)).homScalar := by
  letI : TopologicalSpace Base := ⊥
  letI : DiscreteTopology Base := ⟨rfl⟩
  letI : DiscreteTopology (Base ⧸ datum.M) := discreteTopology_quotient datum
  letI := scalarActionZmodTwo (Base ⧸ datum.M)
  set rho := datumRho alpha r pp h q d hα hr with hrho
  have hb := resolvesAt_and_endpoint_uniformHeis
    (C := Base ⧸ datum.M) (A := ZMod 2)
    (by decide : ∀ a : ZMod 2, a + a = 0)
    (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) hα hqe d
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d (4 * Monoid.exponent (Base ⧸ datum.M)))
      (WordLift (ZMod 2) (Base ⧸ datum.M)) := by
    let incl : ContinuousMonoidHom (WordLift (ZMod 2) (Base ⧸ datum.M))
        (HeisLift (ZMod 2) (Base ⧸ datum.M)) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  exact Count.homCard_field_goal rho (fun _ ↦ rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mpcW alpha r pp d h)) hres
    (isWildTwo_of_gammaGen rho (datumRho_surjective alpha r pp h q d hα hr) (fun _ ↦ rfl))
    (nCompact_degree h)
    (hsimp (Base ⧸ datum.M) rho (ZMod 2) (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2

/-- The complete scalar certificate for a displayed procyclic-M candidate. -/
theorem mpcCandidate_scalar_of_uniformPushed
    {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : UniformPushedHsimp alpha r pp h q d)
    (hα : 1 ≤ alpha) (hr : 1 ≤ r) (hqe : Even q) :
    ScalarHilbertCertificate (displayedGamma alpha r pp h q d) (2 * h + 2)
      (standardNumerics (2 * h + 2)) (scalarActionZmodTwo _) :=
  ⟨mpcCandidate_homCard_of_uniformPushed hsimp hα hr hqe,
   cardH2_of_uniformPushed hsimp hα hr hqe⟩

/-- The scalar certificate, with no analytic premise, for every valid display package. -/
theorem mpcCandidate_scalar {alpha r pp h q : ℕ} {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) (hα : 2 ≤ alpha) (hr : 1 ≤ r) (hqe : Even q) :
    ScalarHilbertCertificate
      (GammaR (2 + 2 * h) q (mpcW alpha r pp d.display h)) (2 + 2 * h)
      (standardNumerics (2 + 2 * h)) (scalarActionZmodTwo _) := by
  apply RowClauses.rowCl_scalar_standard_congr (n := 2 * h + 2) (m := 2 + 2 * h)
    _ (by omega)
  exact mpcCandidate_scalar_of_uniformPushed
    (RecordBlocks.recBl_mpc_uniformPushedHsimp hα hqe d) (by omega) hr hqe

#print axioms mpcCandidate_homCard_of_uniformPushed
#print axioms mpcCandidate_scalar_of_uniformPushed
#print axioms mpcCandidate_scalar

end

end GQ2.Dyadic.Instances.MpcCandidateScalar
