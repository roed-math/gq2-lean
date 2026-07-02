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

/-- **Finite core of the reconstruction lemma.**  For *finite* groups, having the same number of
surjections onto every finite group forces an isomorphism.  This is the counting heart of
Lemma 2.5 (the profinite case reduces to it, level by level, along the finite quotient system):
`|Sur(P,P)| ≥ 1` gives a surjection `Q ↠ P`, symmetrically `P ↠ Q`, so `|P| = |Q|`, and a
surjection between equinumerous finite groups is an isomorphism. -/
theorem reconstruction_finite {P Q : Type} [Group P] [Group Q] [Finite P] [Finite Q]
    (hcount : ∀ (H : Type) [Group H] [Finite H],
        Nat.card {f : P →* H // Function.Surjective f}
          = Nat.card {f : Q →* H // Function.Surjective f}) :
    Nonempty (P ≃* Q) := by
  classical
  haveI : Finite (P →* P) := Finite.of_injective _ DFunLike.coe_injective
  haveI : Finite (Q →* P) := Finite.of_injective _ DFunLike.coe_injective
  haveI : Finite (P →* Q) := Finite.of_injective _ DFunLike.coe_injective
  haveI : Finite (Q →* Q) := Finite.of_injective _ DFunLike.coe_injective
  -- A surjection `Q ↠ P` exists, since `|Sur(Q,P)| = |Sur(P,P)| ≥ 1` (identity).
  have hposP : 0 < Nat.card {f : P →* P // Function.Surjective f} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨MonoidHom.id P, Function.surjective_id⟩⟩, inferInstance⟩
  obtain ⟨g, hg⟩ : Nonempty {f : Q →* P // Function.Surjective f} :=
    (Nat.card_pos_iff.mp (by rw [← hcount P]; exact hposP)).1
  -- Symmetrically a surjection `P ↠ Q`.
  have hposQ : 0 < Nat.card {f : Q →* Q // Function.Surjective f} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨MonoidHom.id Q, Function.surjective_id⟩⟩, inferInstance⟩
  obtain ⟨f, hf⟩ : Nonempty {f : P →* Q // Function.Surjective f} :=
    (Nat.card_pos_iff.mp (by rw [hcount Q]; exact hposQ)).1
  -- Mutual surjections between finite groups force equal cardinality.
  have hcard : Nat.card Q = Nat.card P :=
    le_antisymm (Nat.card_le_card_of_surjective f hf) (Nat.card_le_card_of_surjective g hg)
  -- A surjection between equinumerous finite groups is bijective.
  haveI : Fintype P := Fintype.ofFinite P
  haveI : Fintype Q := Fintype.ofFinite Q
  have hbij : Function.Bijective g :=
    (Fintype.bijective_iff_surjective_and_card g).mpr
      ⟨hg, by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard]⟩
  exact ⟨(MulEquiv.ofBijective g hbij).symm⟩

end GQ2
