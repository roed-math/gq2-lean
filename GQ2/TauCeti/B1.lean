/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5.5
-/
module

public import TauCeti.NumberTheory.LocalField.Generation.AbsoluteGaloisGroup
public import TauCeti.Topology.Algebra.Group.Generation
public import GQ2.Statement

@[expose] public section

/-!
# B1 from Tau Ceti: topological finite generation of `G_ℚ₂`

The `absGalQ2_isTopologicallyFinitelyGenerated` field of `GQ2.LiteratureInputs`, proved from
Tau Ceti's `isTopologicallyFinitelyGenerated_absoluteGaloisGroup` at `K = ℚ_[2]`. Every instance
argument (`ValuativeRel`, `IsNonarchimedeanLocalField`, `ValuativeExtension ℚ_[2] ℚ_[2]`, …) is
found automatically; Tau Ceti's predicate is not exposed, so it is unfolded through its `_iff`
lemma rather than by `rfl` (T2 recon memo, section B1).

This module's imports make Galois-instance search at `AlgebraicClosure ℚ_[2]` time out (memo,
cross-cutting finding 2), so it states nothing else.
-/

namespace GQ2.TauCetiBridge

/-- **B1 from Tau Ceti**: `G_ℚ₂` is topologically finitely generated. The statement is the type of
the `absGalQ2_isTopologicallyFinitelyGenerated` field of `GQ2.LiteratureInputs`. -/
theorem absGalQ2_isTopologicallyFinitelyGenerated_tauceti :
    ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤ :=
  TauCeti.isTopologicallyFinitelyGenerated_iff.mp
    (TauCeti.isTopologicallyFinitelyGenerated_absoluteGaloisGroup 2 ℚ_[2])

end GQ2.TauCetiBridge
