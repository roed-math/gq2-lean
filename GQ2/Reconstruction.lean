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

/-- For a topologically finitely generated profinite group `P` and a finite discrete group `H`,
there are only finitely many continuous homomorphisms `P → H`: such a hom is determined by its
values on a topological generating set (it is continuous, and two continuous homs agreeing on a
dense subgroup agree everywhere), giving an injection into `s → H`. -/
theorem finite_continuousMonoidHom
    {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
      [CompactSpace P] [TotallyDisconnectedSpace P]
    (hPfg : ∃ s : Finset P, (Subgroup.closure (s : Set P)).topologicalClosure = ⊤)
    (H : Type*) [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H] :
    Finite (ContinuousMonoidHom P H) := by
  obtain ⟨s, hs⟩ := hPfg
  have hdense : Dense (↑(Subgroup.closure (s : Set P)) : Set P) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, hs, Subgroup.coe_top]
  refine Finite.of_injective (fun (φ : ContinuousMonoidHom P H) => fun (x : s) => φ (x : P)) ?_
  intro φ ψ hφψ
  have heq : Set.EqOn (⇑φ.toMonoidHom) (⇑ψ.toMonoidHom) (s : Set P) := by
    intro x hx
    exact congrFun hφψ ⟨x, hx⟩
  have hcl : Set.EqOn (⇑φ.toMonoidHom) (⇑ψ.toMonoidHom) (↑(Subgroup.closure (s : Set P))) :=
    MonoidHom.eqOn_closure heq
  have hfun : (⇑φ : P → H) = ⇑ψ :=
    Continuous.ext_on hdense φ.continuous_toFun ψ.continuous_toFun hcl
  exact DFunLike.coe_injective hfun

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
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hx1
  -- Separate `x` from `1` by an open normal subgroup `U`, so `x ∉ U`.
  obtain ⟨U, hUsub⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (U := ({x}ᶜ : Set P)) isOpen_compl_singleton
    (Set.mem_compl_singleton_iff.mpr fun h => hx1 h.symm)
  haveI : DiscreteTopology (P ⧸ U.toSubgroup) := inferInstance
  haveI : Finite (P ⧸ U.toSubgroup) := inferInstance
  -- The (continuous, surjective) projection `π : P ↠ P ⧸ U` onto the finite discrete quotient.
  let π : ContinuousMonoidHom P (P ⧸ U.toSubgroup) :=
    ⟨QuotientGroup.mk' U.toSubgroup, QuotientGroup.continuous_mk⟩
  have hπx : π x ≠ 1 := by
    intro hcontra
    have hxmem : x ∈ U.toSubgroup := (QuotientGroup.eq_one_iff x).mp hcontra
    exact absurd (hUsub hxmem) (by simp)
  -- `Hom(P, P⧸U)` is finite, and precomposition by the surjection `φ` is injective on it,
  -- hence (finite pigeonhole) surjective: some `β` satisfies `β ∘ φ = π`.
  haveI : Finite (ContinuousMonoidHom P (P ⧸ U.toSubgroup)) :=
    finite_continuousMonoidHom hPfg (P ⧸ U.toSubgroup)
  have hprecomp_inj :
      Function.Injective (fun α : ContinuousMonoidHom P (P ⧸ U.toSubgroup) => α.comp φ) := by
    intro a b hab
    have hcoe : (⇑a : P → _) ∘ ⇑φ = (⇑b : P → _) ∘ ⇑φ := by
      have := congrArg (fun γ : ContinuousMonoidHom P (P ⧸ U.toSubgroup) => (⇑γ : P → _)) hab
      simpa only [ContinuousMonoidHom.coe_comp] using this
    exact DFunLike.coe_injective (hφ.injective_comp_right hcoe)
  obtain ⟨β, hβ⟩ := (Finite.injective_iff_surjective.mp hprecomp_inj) π
  -- Then `π x = β (φ x) = β 1 = 1`, contradicting `π x ≠ 1`.
  apply hπx
  have hβ' : β.comp φ = π := hβ
  rw [← hβ']
  simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply, hx, map_one]

/-- **Surjection assembly from surjection counts** (paper Lemma 2.5, compactness input): if a
profinite group `S` continuously surjects onto at least as many finite groups (counted with
multiplicity) as a profinite group `R` does, then `S` continuously surjects onto `R`.

This is *standard* profinite group theory (Ribes–Zalesskiĭ, *Profinite Groups*, Ch. 1–2), deferred
here rather than the novel content of the paper.  Execution recipe:
* For each `V : OpenNormalSubgroup R`, the quotient `R ⧸ V` is finite discrete and
  `ContSurj R (R ⧸ V)` is inhabited (it contains `ProfiniteGrp.proj V`), so `0 < Nat.card` there;
  by `h` (applied at `H := R ⧸ V`) also `0 < Nat.card (ContSurj S (R ⧸ V))`, whence via
  `Nat.card_pos_iff` the level set `{surjections S ↠ R ⧸ V}` is nonempty **and finite**.
* These level sets, with the restriction maps induced by `V' ≤ V`, form a cofiltered inverse system
  of nonempty finite sets over `OpenNormalSubgroup R`; `nonempty_sections_of_finite_inverse_system`
  (`Mathlib/CategoryTheory/CofilteredSystem.lean`) gives a compatible section.
* The section is a cone over `ProfiniteGrp.diagram R` with vertex `S`, hence — through
  `ProfiniteGrp.isoLimittoFiniteQuotientFunctor R` (`R ≅ lim (diagram R)`) — a continuous hom
  `S → R` that is surjective onto every `R ⧸ V`.  Its image is compact (closed) and dense
  (surjective on every finite quotient), so it is all of `R`: the desired `S ↠ R`.

Stated here; proof deferred. -/
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
