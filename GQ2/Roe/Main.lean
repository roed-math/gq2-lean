/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.MainCore
import GQ2.Foundations.Axioms

/-!
# Legacy axiom-backed `Γ_R` capstones

The generic implementations live in `GQ2.Roe.MainCore` and take `[LiteratureInputs]`.  This
compatibility module preserves the historical public statements by selecting the instance assembled
from the original nine literature axioms.
-/

namespace GQ2

section Capstones

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- Legacy compatibility wrapper for `eq_154_R_of_inputs`. -/
theorem eq_154_R (hBLab : BLabHypothesis) (G : Type) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] [Finite G] :
    Nat.card (ContSurj GammaR G) = Nat.card (ContSurj AbsGalQ2 G) :=
  eq_154_R_of_inputs hBLab G

/-- Legacy compatibility wrapper for `main_surjection_count_R_of_inputs`. -/
theorem main_surjection_count_R (hBLab : BLabHypothesis) (G : Type) [Group G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] : contSurjCount G = admissibleCountR G :=
  main_surjection_count_R_of_inputs hBLab G

/-- Legacy compatibility wrapper for `admissibleCountR_eq_admissibleCount_of_inputs`. -/
theorem admissibleCountR_eq_admissibleCount (hBLab : BLabHypothesis) (G : Type) [Group G]
    [Finite G] [TopologicalSpace G] [DiscreteTopology G] :
    admissibleCountR G = admissibleCount G :=
  admissibleCountR_eq_admissibleCount_of_inputs hBLab G

end Capstones

/-- Legacy compatibility wrapper for the conditional Replacement theorem. -/
theorem main_presentation_literal_roe (hBLab : BLabHypothesis) :
    Nonempty (ContinuousMulEquiv GammaR AbsGalQ2) :=
  main_presentation_literal_roe_of_inputs hBLab

/-- Legacy compatibility wrapper for the unconditional Replacement theorem. -/
theorem main_presentation_literal_roe_unconditional :
    Nonempty (ContinuousMulEquiv GammaR AbsGalQ2) :=
  main_presentation_literal_roe_unconditional_of_inputs

end GQ2
