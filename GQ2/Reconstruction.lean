import Mathlib

/-!
# Lemma 2.5 — one-sided profinite reconstruction

Paper Lemma 2.5: *Let `P` be a topologically finitely generated profinite group and `Q` any
profinite group. If `|Sur(P, H)| = |Sur(Q, H)|` for every finite group `H`, then `P ≅ Q`.*

The proof (paper): finiteness of `Sur(P, Pₙ)` gives, by compactness, an epimorphism `Q ↠ P`;
symmetrically `P ↠ Q`; the composite `P ↠ Q ↠ P` is a surjective endomorphism of a
topologically finitely generated profinite group, which is **Hopfian**, hence an isomorphism.

This is grade **F′**: reachable from `ProfiniteGrp` once the Hopfian property of topologically
f.g. profinite groups is packaged. Stated here; proof deferred.
-/

namespace GQ2

open scoped Classical

/-- Continuous surjections from a topological group `P` onto a finite (discrete) group `H`. -/
def ContSurj (P : Type*) [Group P] [TopologicalSpace P]
    (H : Type*) [Group H] [TopologicalSpace H] : Type _ :=
  {f : ContinuousMonoidHom P H // Function.Surjective f}

/-- **Lemma 2.5 (one-sided profinite reconstruction).** *(Statement scaffold; proof deferred.)*
`P` is a topologically finitely generated profinite group, `Q` is profinite, and they have the
same (finite) number of continuous surjections onto every finite group; then `P ≅ Q` as
topological groups. -/
theorem reconstruction
    {P Q : Type*}
    [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
      [CompactSpace P] [TotallyDisconnectedSpace P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
      [CompactSpace Q] [TotallyDisconnectedSpace Q]
    (hPfg : ∃ s : Finset P, (Subgroup.closure (s : Set P)).topologicalClosure = ⊤)
    (hcount : ∀ (H : Type) [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H],
        Nat.card (ContSurj P H) = Nat.card (ContSurj Q H)) :
    Nonempty (ContinuousMulEquiv P Q) := by
  sorry

end GQ2
