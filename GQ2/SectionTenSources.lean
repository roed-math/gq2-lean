/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.SectionTenSourcesWithInputs
import GQ2.Foundations.AxiomInstance
import Mathlib.FieldTheory.Galois.Profinite

/-! Legacy axiom-backed wrappers for the `Γ_A` §10 capstones. -/

namespace GQ2.SectionTen

noncomputable local instance absGalQ2_compactSpace : CompactSpace AbsGalQ2 := by
  change CompactSpace (AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2])
  infer_instance

noncomputable local instance absGalQ2_totallyDisconnectedSpace :
    TotallyDisconnectedSpace AbsGalQ2 := by
  change TotallyDisconnectedSpace (AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2])
  infer_instance

/-- Legacy compatibility wrapper for `eq_154_of_inputs`. -/
theorem eq_154 (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G] [Finite G] :
    Nat.card (ContSurj GammaA G) = Nat.card (ContSurj AbsGalQ2 G) :=
  eq_154_of_inputs G

/-- Legacy compatibility wrapper for `main_surjection_count_of_inputs`. -/
theorem main_surjection_count'
    (G : Type) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G] :
    contSurjCount G = admissibleCount G :=
  main_surjection_count_of_inputs G

end GQ2.SectionTen
