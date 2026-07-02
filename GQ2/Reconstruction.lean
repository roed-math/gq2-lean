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

/-- A bijective continuous group homomorphism from a compact group to a Hausdorff group is a
topological isomorphism.  (Mirrors `ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor`,
but stated for bare types so it can be used on the reconstruction hypotheses.) -/
noncomputable def continuousMulEquivOfBijective
    {P Q : Type*} [Group P] [TopologicalSpace P] [Group Q] [TopologicalSpace Q]
    [CompactSpace P] [T2Space Q]
    (f : ContinuousMonoidHom P Q) (hf : Function.Bijective f) :
    ContinuousMulEquiv P Q :=
  { Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ hf) f.continuous_toFun with
    map_mul' := f.map_mul' }

/-- **Profinite Hopfian property** (paper Lemma 2.5, key input): a continuous surjective
endomorphism of a *topologically finitely generated* profinite group is injective.  Non-standard;
absent from Mathlib.  Proof idea: a topologically f.g. profinite group has only finitely many open
subgroups of each index, so a surjective endomorphism acts as a surjection — hence a bijection — on
each finite quotient level, forcing injectivity in the limit.  Stated here; proof deferred. -/
theorem profinite_hopfian
    {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
      [CompactSpace P] [TotallyDisconnectedSpace P]
    (hPfg : ∃ s : Finset P, (Subgroup.closure (s : Set P)).topologicalClosure = ⊤)
    (φ : ContinuousMonoidHom P P) (hφ : Function.Surjective φ) :
    Function.Injective φ := by
  sorry

/-- **Surjection assembly from surjection counts** (paper Lemma 2.5, compactness input): if a
profinite group `S` continuously surjects onto at least as many finite groups (counted with
multiplicity) as a profinite group `R` does, then `S` continuously surjects onto `R`.  Taking `H`
to range over the finite quotients `R/V` shows every level `S ↠ R/V` is inhabited; the surjection
`S ↠ R` is assembled from these by compactness (König's lemma on the cofiltered system of finite
quotients of `R`).  Stated here; proof deferred. -/
theorem exists_contSurj_of_card_le
    {S R : Type*} [Group S] [TopologicalSpace S] [IsTopologicalGroup S]
      [CompactSpace S] [TotallyDisconnectedSpace S]
    [Group R] [TopologicalSpace R] [IsTopologicalGroup R]
      [CompactSpace R] [TotallyDisconnectedSpace R]
    (h : ∀ (H : Type) [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H],
        Nat.card (ContSurj R H) ≤ Nat.card (ContSurj S H)) :
    Nonempty (ContSurj S R) := by
  sorry

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
  -- A continuous surjection `Q ↠ P` (from `|Sur(P,H)| = |Sur(Q,H)|`, so `≥`).
  obtain ⟨⟨g, hg⟩⟩ : Nonempty (ContSurj Q P) :=
    exists_contSurj_of_card_le (fun H => le_of_eq (hcount H))
  -- A continuous surjection `P ↠ Q` (symmetric count).
  obtain ⟨⟨f, hf⟩⟩ : Nonempty (ContSurj P Q) :=
    exists_contSurj_of_card_le (fun H => ge_of_eq (hcount H))
  -- The composite `P → Q → P` is a continuous surjective endomorphism of the top. f.g. profinite `P`.
  have hcoe : (⇑(g.comp f) : P → P) = ⇑g ∘ ⇑f := rfl
  have hcomp : Function.Surjective (g.comp f : ContinuousMonoidHom P P) := by
    rw [hcoe]; exact hg.comp hf
  -- Hopfian ⇒ the composite is injective ⇒ `f` is injective.
  have hginj : Function.Injective (⇑(g.comp f) : P → P) := profinite_hopfian hPfg _ hcomp
  rw [hcoe] at hginj
  have hfinj : Function.Injective (f : P → Q) := hginj.of_comp
  -- `f` is a continuous bijection `P → Q`, hence a topological isomorphism.
  exact ⟨continuousMulEquivOfBijective f ⟨hfinj, hf⟩⟩

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
