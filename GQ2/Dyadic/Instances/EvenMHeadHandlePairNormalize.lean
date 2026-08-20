/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.EvenMHeadHandlePairCore
import GQ2.Dyadic.Instances.GammaRCorePresentationNuNormalize

/-!
# Uniformly normalizing the strict-handle pair source

Apply the rank-generic simultaneous wild shear to the W347 pair-promoted presentation.  The
new word has a complete `FlexibleCoreLeavesRN` as soon as the promoted handle has unramified
value `1`; no separate all-wild normalization premise remains.

This is only a specialization of the generic normalization theorem.  It introduces no class,
degree, field, or finite-stage argument.
-/

namespace GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalize

noncomputable section

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.EvenMHeadHandlePairSource
open GQ2.Dyadic.Instances.EvenMHeadHandlePairCore
open GQ2.Dyadic.Instances.GammaRCorePresentationNuNormalize
open GQ2.Dyadic.Instances.FieldFamilyFlexibleCertificate

/-- The uniform normalized word obtained from the strict-handle pair presentation. -/
def headHandlePairNormalizedW
    (alpha h : ℕ) (halpha : 1 ≤ alpha) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo) :
    PWord (Generator (2 + 2 * h)) :=
  let C := headHandlePairCorePresentation alpha h halpha j
  PWord.subst (wildShearNielsen (wildNuCoefficient nuP C.mark)).backward
    (headHandlePairCompactW alpha j)

/-- The normalized word has complete flexible core leaves from the promoted head row alone. -/
noncomputable def headHandlePairNormalizedFlexibleCore
    {alpha h : ℕ} (halpha : 1 ≤ alpha) (j : Fin h)
    (nuP : ContinuousMonoidHom (DM alpha h : Type) Ztwo)
    (hU : nuP (dmGen alpha h (handleIdxU j)) = ztwoOne) :
    FlexibleCoreLeavesRN (2 + 2 * h)
      (headHandlePairNormalizedW alpha h halpha j nuP) (DM alpha h) nuP := by
  let C := headHandlePairCorePresentation alpha h halpha j
  refine normalizedFlexibleCoreLeaves C nuP ?_
  change nuP ((headHandlePairCorePresentation alpha h halpha j).mark .sigma) =
    ztwoOne
  rw [headHandlePairCorePresentation_mark_sigma]
  exact hU

#print axioms headHandlePairNormalizedW
#print axioms headHandlePairNormalizedFlexibleCore

end

end GQ2.Dyadic.Instances.EvenMHeadHandlePairNormalize
