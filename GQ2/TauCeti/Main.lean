/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5.5
-/
import GQ2.TauCeti.Instance
import GQ2.PresentationLiteralWithInputs
import GQ2.SectionTenSourcesWithInputs
import GQ2.Roe.MainWithInputs

/-!
# The presentation theorems, unconditionally, via Tau Ceti

The generic capstones take the nine literature inputs as the typeclass `GQ2.LiteratureInputs`.
Instantiating them at `GQ2.TauCetiBridge.tauCetiInputs` (`GQ2/TauCeti/Instance.lean`), where every
input is proved from Tau Ceti, gives the four capstones below with no literature hypothesis and no
literature axiom: each prints exactly `propext`, `Classical.choice`, `Quot.sound`
(`GQ2/TauCetiAxiomAudit.lean`, `scripts/check_axioms.sh` check 5). Their statements are those of
the legacy axiom-backed capstones `GQ2.main_presentation_literal`,
`GQ2.main_presentation_literal_roe_unconditional`, `GQ2.SectionTen.main_surjection_count'` and
`GQ2.main_surjection_count_R` (the last with its Labute hypothesis discharged by
`GQ2.Roe.Labute.bLab`, as in `main_presentation_literal_roe_unconditional`).

This file uses plain imports because the capstone files it instantiates are not `module` files.
It imports neither `GQ2.Foundations.Axioms` nor `GQ2.Foundations.AxiomInstance`.
-/

namespace GQ2

/-- **Theorem 1.2 for `Γ_A`, unconditionally**: `Γ_A ≅ G_ℚ₂` as topological groups, with the
literature inputs proved from Tau Ceti. -/
theorem main_presentation_literal_tauceti :
    Nonempty (ContinuousMulEquiv GammaA AbsGalQ2) :=
  @main_presentation_literal_of_inputs TauCetiBridge.tauCetiInputs

/-- **Theorem 1.2 for `Γ_R`, unconditionally**: `Γ_R ≅ G_ℚ₂` as topological groups, with the
literature inputs proved from Tau Ceti and the Labute instance discharged by `Roe.Labute.bLab`. -/
theorem main_presentation_literal_roe_tauceti :
    Nonempty (ContinuousMulEquiv GammaR AbsGalQ2) :=
  @main_presentation_literal_roe_unconditional_of_inputs TauCetiBridge.tauCetiInputs

/-- **Theorem 1.2, surjection-count form, for `Γ_A`, unconditionally**: the continuous surjections
`G_ℚ₂ ↠ G` onto a finite group are counted by the admissible markings of `G`. -/
theorem main_surjection_count_tauceti
    (G : Type) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G] :
    contSurjCount G = admissibleCount G :=
  letI := TauCetiBridge.tauCetiInputs
  SectionTen.main_surjection_count_of_inputs G

/-- **Theorem 1.2, surjection-count form, for `Γ_R`, unconditionally**: the continuous surjections
`G_ℚ₂ ↠ G` onto a finite group are counted by the admissible Roe markings of `G`. -/
theorem main_surjection_count_R_tauceti
    (G : Type) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G] :
    contSurjCount G = admissibleCountR G :=
  letI := TauCetiBridge.tauCetiInputs
  main_surjection_count_R_of_inputs Roe.Labute.bLab G

end GQ2
