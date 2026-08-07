/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLDeterminantUnramifiedData
import GQ2.Dyadic.Instances.GammaLDeterminantRamifiedData
import GQ2.Dyadic.Instances.GammaLReconstruction

/-!
# The determinant residue for the improved L presentation

Assembly of the two head-factored branch models into `DeterminantWordPhaseSupply`, hence into
`DeterminantResidue`, hence into `LSquareAnalyticLeavesRN` — its first producer.

The unramified branch is unconditional.  The ramified branch consumes exactly one input, the
presentation-independent `LRamifiedSourceArfData` per block and recursion level *under the
ramification hypothesis its consumer already carries*, packaged here as
`LRamifiedSourceArfSupply`.  That is the candidate-side mirror of the field side's
`ramifiedData` binder in `GQ2.Dyadic.affineDeterminant_galK`: on the field side it is supplied by
`DyadicLocalInput.ramifiedData` (local duality), and it is the only arithmetic that the L word
does not itself compute.

The three tame pins `htameSigma`/`htameTau`/`htameWild` hold for any `tameOfSpec`, so the
canonical constructor at the end takes no tame hypotheses at all.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes
open GQ2.Dyadic.Count
open GQ2.Dyadic.TameSpec

/-! ## The residual ramified arithmetic input -/

set_option linter.unusedVariables false in
/-- The per-block, per-level form of `LRamifiedSourceArfData`: the descended continuous source
form is a form of Arf invariant zero.  Nothing about the L presentation appears in the
conclusion; this is the candidate-side twin of the field side's `ramifiedData` binder.

**The binder list matches `wordPhaseResidueK_ramified_lSq`'s tail exactly** — `m`, `hcard`,
`l`, `hl`, `hram` — and that is deliberate.  Without the ramification hypothesis `hram` the
statement is *false*: in an unramified block the descended source form carries the negative
Gauss sign of `prop_6_9_unramified`, i.e. `Arf = 1`, so no route can supply the unconditioned
form (see refutation (3) in `GQ2/Dyadic/Instances/GammaLSourceArfGeneral.lean`'s module
docstring).  The `m`/`hcard` pair is unused by the conclusion but is what every producer needs
(the Arf count runs on a space of order `2 ^ (2 * m)`); the sole consumer,
`determinantWordPhaseSupply_lSq`, has both in scope, so binding them costs nothing there and
lets `lRamifiedSourceArf_blockK` discharge the supply verbatim
(`lRamifiedSourceArfSupply_pow`). -/
def LRamifiedSourceArfSupply {h q : ℕ} {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (gamma h q) (Tq q))
    (pro2 : ContinuousMonoidHom (gamma h q) P)
    (compat : ∀ g : (gamma h q : Type), nuTq q (tame g) = nuP (pro2 g)) : Type 1 :=
  ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (m : ℕ)
    (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod = 2 ^ (2 * m))
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (hl : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
    (hram :
      letI := blockPS_commGroup Blk
      letI := SectionNine.headAct T Blk
      ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau q) • v ≠ v),
      let En := blockEnrichmentDK T Blk hE2 hq0 hqe F
      let DD := En.descData l hl
      letI : TopologicalSpace DD.Vmod := ⊥
      letI : DiscreteTopology DD.Vmod := ⟨rfl⟩
      letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
        scalarActionZmodTwo ((gamma h q : Type))
      ∀ rho : BoundaryLiftsK (sourceBoundaryMapK tame pro2 compat) F
          (SectionNine.blockFrame T Blk hE2).TC,
        let rhoM := rhoPrimeK (SectionNine.blockFrame T Blk hE2)
          (sourceBoundaryMapK tame pro2 compat) F (En.radData l hl) rfl rho
        letI : DistribMulAction ((gamma h q : Type)) DD.Vmod :=
          DistribMulAction.compHom DD.Vmod (rho0 DD rhoM)
        let hcomp : ∀ (g : (gamma h q : Type)) (v : DD.Vmod),
            g • v = rho0 DD rhoM g • v := fun _ _ ↦ rfl
        LRamifiedSourceArfData rhoM (scalarActionZmodTwo_triv _) hcomp

/-! ## The word phase supply and the determinant residue -/

set_option maxHeartbeats 1200000 in
/-- **The complete word-phase supply for the improved L presentation.**  The unramified clause is
unconditional; the ramified clause consumes only the source-Arf supply. -/
def determinantWordPhaseSupply_lSq {h q : ℕ} {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (gamma h q) (Tq q))
    (pro2 : ContinuousMonoidHom (gamma h q) P)
    (compat : ∀ g : (gamma h q : Type), nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame (gammaGen (2 * h + 1) q (lSqW h) .sigma) = tqSigma q)
    (htameTau : tame (gammaGen (2 * h + 1) q (lSqW h) .tau) = tqTau q)
    (htameWild : ∀ i : Fin (2 * h + 1 + 1),
      tame (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = 1)
    (S : LRamifiedSourceArfSupply nuP tame pro2 compat) :
    DeterminantWordPhaseSupply nuP tame pro2 compat where
  unramified := fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl hunram =>
    wordPhaseResidueK_unramified_lSq T Blk hE2 hq0 hqe F tame pro2 compat
      htameSigma htameTau htameWild hsimple hVne hnt m hm hcard l hl hunram
  ramified := fun T Blk _ _ _ hE2 hq0 hqe F _ _ _ m _ hcard l hl hram =>
    wordPhaseResidueK_ramified_lSq T Blk hE2 hq0 hqe F tame pro2 compat
      htameSigma htameTau htameWild m hcard l hl hram
      (S T Blk hE2 hq0 hqe F m hcard l hl hram)

set_option maxHeartbeats 1200000 in
/-- **The determinant residue for the improved L presentation.**  Every analytic leaf of the L
row is now a theorem over the single arithmetic supply `S`. -/
theorem determinantResidue_lSq {h q : ℕ} {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (gamma h q) (Tq q))
    (pro2 : ContinuousMonoidHom (gamma h q) P)
    (compat : ∀ g : (gamma h q : Type), nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame (gammaGen (2 * h + 1) q (lSqW h) .sigma) = tqSigma q)
    (htameTau : tame (gammaGen (2 * h + 1) q (lSqW h) .tau) = tqTau q)
    (htameWild : ∀ i : Fin (2 * h + 1 + 1),
      tame (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = 1)
    (S : LRamifiedSourceArfSupply nuP tame pro2 compat) :
    DeterminantResidue nuP tame pro2 compat :=
  affineDeterminantCertificate_of_wordPhaseSupply nuP tame pro2 compat
    (determinantWordPhaseSupply_lSq nuP tame pro2 compat htameSigma htameTau htameWild S)

/-- All three analytic leaves of the L row, from the single arithmetic supply. -/
theorem analyticLeaves_lSq {h q : ℕ} (hqe : Even q) {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (gamma h q) (Tq q))
    (pro2 : ContinuousMonoidHom (gamma h q) P)
    (compat : ∀ g : (gamma h q : Type), nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame (gammaGen (2 * h + 1) q (lSqW h) .sigma) = tqSigma q)
    (htameTau : tame (gammaGen (2 * h + 1) q (lSqW h) .tau) = tqTau q)
    (htameWild : ∀ i : Fin (2 * h + 1 + 1),
      tame (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = 1)
    (S : LRamifiedSourceArfSupply nuP tame pro2 compat) :
    StokesDualityCertificate (gamma h q) (2 * h + 1) q P nuP
        (standardNumerics (2 * h + 1))
        (scalarActionZmodTwo ((gamma h q : Type))) ∧
      ScalarHilbertCertificate (gamma h q) (2 * h + 1)
        (standardNumerics (2 * h + 1))
        (scalarActionZmodTwo ((gamma h q : Type))) ∧
      AffineDeterminantCertificate (gamma h q) (2 * h + 1) q P nuP
        (standardNumerics (2 * h + 1)) tame pro2 compat
        (scalarActionZmodTwo ((gamma h q : Type))) :=
  analyticLeaves_of_actionImage hqe nuP tame pro2 compat
    (determinantResidue_lSq nuP tame pro2 compat htameSigma htameTau htameWild S)

/-! ## The canonical L row -/

/-- The canonical tame map's three generator values.  `tameOfSpec` is the classifying map of
`tameMarking`, so all three are definitional. -/
theorem tameOfSpec_lSq_sigma {h q : ℕ} (hq2 : 2 ≤ q) (hqe : Even q) :
    tameOfSpec (2 * h + 1) q (lSqW h) (lCanonicalTameSpecialization h q hq2 hqe)
      (gammaGen (2 * h + 1) q (lSqW h) .sigma) = tqSigma q :=
  tameOfSpec_gammaGen _ _

theorem tameOfSpec_lSq_tau {h q : ℕ} (hq2 : 2 ≤ q) (hqe : Even q) :
    tameOfSpec (2 * h + 1) q (lSqW h) (lCanonicalTameSpecialization h q hq2 hqe)
      (gammaGen (2 * h + 1) q (lSqW h) .tau) = tqTau q :=
  tameOfSpec_gammaGen _ _

theorem tameOfSpec_lSq_wild {h q : ℕ} (hq2 : 2 ≤ q) (hqe : Even q)
    (i : Fin (2 * h + 1 + 1)) :
    tameOfSpec (2 * h + 1) q (lSqW h) (lCanonicalTameSpecialization h q hq2 hqe)
      (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = 1 :=
  tameOfSpec_gammaGen _ _

set_option maxHeartbeats 1200000 in
/-- **The first producer of `LSquareAnalyticLeavesRN`.**

The candidate-side analytic residue of the corrected L row is now exactly the ramified
source-Arf supply: no word certificate, no Stokes or scalar input, no per-lift graph datum. -/
def lSquareAnalyticLeavesRN_of_sourceArf {h q : ℕ} (hq2 : 2 ≤ q) (hqe : Even q)
    (S : LRamifiedSourceArfSupply (Instances.LSquareCore.lNu h)
      (tameOfSpec (2 * h + 1) q (lSqW h) (lCanonicalTameSpecialization h q hq2 hqe))
      (lCanonicalPro2 h q hq2 hqe) (lCanonicalCompat h q hq2 hqe)) :
    LSquareAnalyticLeavesRN h q hq2 hqe where
  determinant :=
    determinantResidue_lSq (Instances.LSquareCore.lNu h)
      (tameOfSpec (2 * h + 1) q (lSqW h) (lCanonicalTameSpecialization h q hq2 hqe))
      (lCanonicalPro2 h q hq2 hqe) (lCanonicalCompat h q hq2 hqe)
      (tameOfSpec_lSq_sigma hq2 hqe) (tameOfSpec_lSq_tau hq2 hqe)
      (tameOfSpec_lSq_wild hq2 hqe) S

/-- Regression: the corrected L word certificate is now available from the arithmetic supply
alone. -/
noncomputable def wordCertificateRN_lSq_of_sourceArf {h q : ℕ} (hq2 : 2 ≤ q) (hqe : Even q)
    (S : LRamifiedSourceArfSupply (Instances.LSquareCore.lNu h)
      (tameOfSpec (2 * h + 1) q (lSqW h) (lCanonicalTameSpecialization h q hq2 hqe))
      (lCanonicalPro2 h q hq2 hqe) (lCanonicalCompat h q hq2 hqe)) :
    WordCertificateRN (2 * h + 1) q (lSqW h) (SqCore.DSq h)
      (SqCore.isProP_DSq h) (Instances.LSquareCore.lNu h)
      (standardNumerics (2 * h + 1)) :=
  wordCertificateRN_lSq_of_actionImage hq2 hqe (lSquareAnalyticLeavesRN_of_sourceArf hq2 hqe S)

end

end GQ2.Dyadic.LSquare

#print axioms GQ2.Dyadic.LSquare.determinantWordPhaseSupply_lSq
#print axioms GQ2.Dyadic.LSquare.determinantResidue_lSq
#print axioms GQ2.Dyadic.LSquare.analyticLeaves_lSq
#print axioms GQ2.Dyadic.LSquare.lSquareAnalyticLeavesRN_of_sourceArf
#print axioms GQ2.Dyadic.LSquare.wordCertificateRN_lSq_of_sourceArf
