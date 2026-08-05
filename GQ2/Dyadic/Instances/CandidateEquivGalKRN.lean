/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.ThmFourTwoRN
import GQ2.Dyadic.Instances.GammaLReconstruction

/-!
# The general-word reconstruction wrapper against `G_K`

§7's corrected capstones compare two abstract sources
(`nonempty_continuousMulEquiv_of_sourcesRN`) or two word certificates
(`nonempty_continuousMulEquiv_of_wordCertificatesRN`), but the named statement consumed by the
per-row reconstruction files — *a certified candidate word is `G_K`* — existed only in its L
instantiation (`gammaLFieldRealization_of_wordCertificateRN_reconstruction`,
`GQ2/Dyadic/Instances/GammaLReconstruction.lean`).  This file states that glue once,
row-generically:

* `GalKArithmeticSourceRN` — the row-independent arithmetic supply: a corrected source whose
  carrier is identified with `G_K`, with surjective tame quotient and pro-2 wild kernel.  It is
  `GammaLCorrectedArithmeticInput` minus the L-specific slot pins and the degree equation.
* `candidate_equiv_galK_of_supplyRN` — the wrapper: a `WordCertificateRN` for an arbitrary
  degree-`n` word, compared against such a supply over the same slot, yields
  `Γ_{R,q} ≅ G_K`.

The L regression re-derives the concrete instance's equivalence through the general wrapper,
so the row files' reconstruction glue and this statement can never drift apart.
-/

namespace GQ2.Dyadic

open GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable section

/-- Row-generic arithmetic supply for reconstruction against `G_K`: a corrected degree-`n`
source over the slot `(q, P, hP, νP, SN)` whose carrier is identified with `G_K`, together
with the two structural reconstruction hypotheses.  This is the row-independent core of the L
instance's `LSquare.GammaLCorrectedArithmeticInput`. -/
structure GalKArithmeticSourceRN (n q : ℕ) (P : ProfiniteGrp) (hP : IsProP 2 P)
    (nuP : ContinuousMonoidHom P Ztwo) (SN : SourceNumerics n)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K] where
  /-- The arithmetic corrected source over the shared slot. -/
  source : SourceDataRN n q P hP nuP SN
  /-- The identification of the arithmetic carrier with `G_K` — an input, never an output. -/
  equivGalK : ContinuousMulEquiv source.Γ (GalK K)
  /-- The arithmetic tame quotient is onto. -/
  tame_surjective : Function.Surjective source.tame
  /-- The arithmetic wild kernel is pro-2. -/
  wild_isProP : IsProP 2 source.tame.toMonoidHom.ker

/-- **The general-word RN assembly wrapper.**  A corrected word certificate for an arbitrary
degree-`n` word, compared against an arithmetic corrected source identified with `G_K` over
the same slot with surjective orientation, reconstructs the candidate presentation as `G_K`.
This is the L instance's reconstruction glue
(`gammaLFieldRealization_of_wordCertificateRN_reconstruction`) with `lSqW h` replaced by an
arbitrary word and the slot left generic. -/
theorem candidate_equiv_galK_of_supplyRN {n q : ℕ} {R : PWord (Generator n)}
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    {SN : SourceNumerics n} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    (W : WordCertificateRN n q R P hP nuP SN)
    (A : GalKArithmeticSourceRN n q P hP nuP SN K)
    (hq2 : 2 ≤ q) (hqe : Even q) (hnuP : Function.Surjective nuP) :
    Nonempty (ContinuousMulEquiv (GammaR n q R) (GalK K)) :=
  ⟨((nonempty_continuousMulEquiv_of_sourcesRN (W.toSourceRN hq2 hqe) A.source
      (by omega) hqe hnuP W.htame W.hwild A.tame_surjective A.wild_isProP).some).trans
    A.equivGalK⟩

/-- The L instance's arithmetic record forgets to the row-generic supply. -/
def GalKArithmeticSourceRN.ofGammaLCorrectedArithmeticInput {h q : ℕ}
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    (AK : LSquare.GammaLCorrectedArithmeticInput h q K) :
    GalKArithmeticSourceRN (2 * h + 1) q (SqCore.DSq h) (SqCore.isProP_DSq h)
      (Instances.LSquareCore.lNu h) (standardNumerics (2 * h + 1)) K where
  source := AK.source
  equivGalK := AK.equivGalK
  tame_surjective := AK.tame_surjective
  wild_isProP := AK.wild_isProP

/-- **L regression.**  The concrete L reconstruction is an instance of the general wrapper:
the surjectivity of the canonical L orientation is the only row-specific input consumed. -/
theorem lSq_candidate_equiv_galK_of_supplyRN {h q : ℕ}
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    (W : WordCertificateRN (2 * h + 1) q (Words.LSq.lSqW h) (SqCore.DSq h)
      (SqCore.isProP_DSq h) (Instances.LSquareCore.lNu h) (standardNumerics (2 * h + 1)))
    (AK : LSquare.GammaLCorrectedArithmeticInput h q K) (hq2 : 2 ≤ q) (hqe : Even q) :
    Nonempty (ContinuousMulEquiv (GammaR (2 * h + 1) q (Words.LSq.lSqW h)) (GalK K)) :=
  candidate_equiv_galK_of_supplyRN W (.ofGammaLCorrectedArithmeticInput AK) hq2 hqe
    (LSquare.lNu_surjective h)

end

end GQ2.Dyadic
