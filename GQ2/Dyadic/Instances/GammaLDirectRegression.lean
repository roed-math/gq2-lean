/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLRelatorRealization
import GQ2.Dyadic.Instances.GammaLTateDirect

/-!
# End-to-end regression from the two direct L proof fronts

This file composes the noncircular Tate constructor with finite relator realization.  It is a
regression theorem rather than a new hypothesis: once the two mathematical inputs targeted by
the current campaign are supplied, the corrected exact-lifting conclusion follows with no use
of the foundational Tate-duality axiom.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Dyadic GQ2.Dyadic.LiftingDualityG

/-- The two direct campaign inputs compose all the way to corrected exact lifting.

`D` contains a scalar orientation, source/word comparison cores, and independently proved word
Stokes duality, but no cup-perfectness hypothesis.  `hreal` is the finite relation-level supply
for simple coefficients.  The Tate record and canonical `H²` surjectivity used by the legacy
consumer are constructed from these inputs. -/
theorem exactLiftingRN_of_lNoCupProvider_relatorRealization
    {h q e : ℕ}
    [DistribMulAction ((gamma h q : Type)) (MuN 2)]
    [ContinuousSMul ((gamma h q : Type)) (MuN 2)]
    (hq : Even q) (he : Odd e)
    (D : LNoCupTateProvider h q e hq he)
    (hreal : UniformSimpleRelatorRealizationSingleSupply (h := h) (q := q))
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma h q) (2 * h + 1) q P nuP
      (standardNumerics (2 * h + 1)) :=
  exactLiftingRN_of_uniformRelatorRealization_tateDuality hq
    (tateDualityG_of_lNoCupTateProvider D) hreal nuP

end

end GQ2.Dyadic.LSquare
