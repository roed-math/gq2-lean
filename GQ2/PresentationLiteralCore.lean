/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8, Fable-5, and OpenAI Codex
-/
import GQ2.GammaA
import GQ2.SectionTenSourcesCore
import GQ2.Prop23
import GQ2.FinitelyGenerated
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Theorem 1.2 from explicit literature inputs

This is the axiom-free core of the literal `Γ_A` presentation theorem.  Its single bundled
hypothesis exposes the nine cited literature results used by the proof graph.
-/

namespace GQ2

noncomputable local instance absGalQ2_compactSpace_of_inputs : CompactSpace AbsGalQ2 := by
  change CompactSpace (AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2])
  infer_instance

noncomputable local instance absGalQ2_totallyDisconnectedSpace_of_inputs :
    TotallyDisconnectedSpace AbsGalQ2 := by
  change TotallyDisconnectedSpace (AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2])
  infer_instance

/-- The literal `Γ_A` presentation theorem, conditional on the bundled literature inputs. -/
theorem main_presentation_literal_of_inputs [lit : LiteratureInputs] :
    Nonempty (ContinuousMulEquiv GammaA AbsGalQ2) :=
  main_presentation GammaA
    gammaA_topologicallyFinitelyGenerated
    lit.absGalQ2_isTopologicallyFinitelyGenerated
    prop_2_3
    (fun G => SectionTen.main_surjection_count_of_inputs G)

end GQ2
