import Mathlib
import GQ2.Words
import GQ2.Reconstruction

/-!
# The main theorem (Theorem 1.2)

We give the **surjection-count form** of the theorem, which is:
* complete and faithful to the paper (it is exactly paper eq. (154) combined with Prop. 2.3),
* statable with *current* Mathlib (no free profinite groups or `ℤ̂` needed), and
* equivalent to the literal presentation statement via Lemma 2.5 (`GQ2.reconstruction`).

Let `G_{ℚ₂}` be the absolute Galois group of `ℚ₂` (Mathlib's `Field.absoluteGaloisGroup ℚ_[2]`,
which for the char-0 field `ℚ₂` is the genuine `Gal(ℚ₂^sep/ℚ₂)`).

> **Theorem 1.2 (surjection-count form).** For every finite group `G`, the number of
> continuous surjections `G_{ℚ₂} ↠ G` equals the number of *admissible marked generating
> quadruples* in `G` (`GQ2.admissibleCount G`).

Combined with `GQ2.reconstruction` (Lemma 2.5) and `GQ2.admissibleCount = |Sur(Γ_A, ·)|`
(Prop. 2.3), this yields the literal statement `G_{ℚ₂} ≅ Γ_A`, i.e. Theorem 1.2 as printed.
-/

namespace GQ2

open scoped Classical

/-- `G_{ℚ₂}`, the absolute Galois group of the 2-adic numbers, as a topological group. -/
noncomputable abbrev AbsGalQ2 : Type := Field.absoluteGaloisGroup ℚ_[2]

/-- The number of continuous surjections `G_{ℚ₂} ↠ G` onto a finite discrete group `G`. -/
noncomputable def contSurjCount (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G] : ℕ :=
  Nat.card (ContSurj AbsGalQ2 G)

/-- **Theorem 1.2 (surjection-count form).** For every finite group `G`, the number of continuous
surjections `G_{ℚ₂} ↠ G` equals `admissibleCount G`, the number of admissible marked generating
quadruples `(σ,τ,x₀,x₁) ∈ G⁴` (paper eq. (154) + Prop. 2.3).

*Status:* the honest computational content of the paper; proof deferred (needs the §§3–9 tower).
The paper proves this via eq. (154) `|Sur(Γ_A,G)| = |Sur(G_ℚ₂,G)|` (Lemma 10.1 + Theorem 4.2 +
Prop 2.3). That tower reduces to a **minimal list of nine classical literature results** (Demushkin
classification, `G_ℚ₂(2)` Demushkin, local reciprocity, local Tate duality, local Euler
characteristic, dyadic Hilbert symbol, 2-adic cyclotomic surjectivity, `G_ℚ₂` top. f.g., Evens/
Stiefel–Whitney) — enumerated with precise statements and citations in `docs/literature-axioms.md`,
and (where Mathlib has the types) stated in `GQ2/Foundations.lean`. -/
theorem main_surjection_count
    (G : Type) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G] :
    contSurjCount G = admissibleCount G := by
  sorry

/-!
## The literal presentation form (Theorem 1.2 as printed)

The honest candidate `Γ_A` is now constructed in `GQ2/GammaA.lean` (the paper's marked quotient
construction, eq. (7), on `GQ2.FreeProfiniteGroup (Fin 4)`, with the relations readable both
profinitely via `ℤ̂`/`ω₂`/`^ᶻ` from `GQ2/Zhat.lean` and finitely via `GQ2/Words.lean` — the two
readings provably agree).  The literal Theorem 1.2 is stated there as
`GQ2.main_presentation_literal : Nonempty (ContinuousMulEquiv GammaA AbsGalQ2)`.

The schematic form below keeps the top-level logic explicit and checked: given Prop. 2.3 for a
candidate (`hΓA`: its continuous surjection counts are the admissible-marking counts) and
topological finite generation, `reconstruction` (Lemma 2.5) + `main_surjection_count` deliver
the isomorphism.  Instantiating it at `Γ_A` (i.e. discharging `hΓA` — paper §2, Prop. 2.3 — and
`hfgΓ`) is step 2 of the program; see `docs/formalization-plan.md`.
-/

/-- **Theorem 1.2 (literal presentation form), schematic.** Any candidate profinite group `Γ_A`
with the surjection-count property of Prop. 2.3 (the honest one is `GQ2.GammaA`)
is continuously isomorphic to `G_{ℚ₂}`.

`ΓA` stands in for the presented profinite group; `hΓA` is Prop. 2.3 (its finite quotients are the
admissible markings); `hfgΓ`/`hfgG` are topological finite generation of `Γ_A` and of `G_{ℚ₂}`
(both true — `G_{ℚ₂}` is topologically finitely generated, being the absolute Galois group of a
local field; assumed here as it is not yet formalized). The conclusion is Theorem 1.2. -/
theorem main_presentation
    (ΓA : Type)
    [Group ΓA] [TopologicalSpace ΓA] [IsTopologicalGroup ΓA]
      [CompactSpace ΓA] [TotallyDisconnectedSpace ΓA]
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (hfgΓ : ∃ s : Finset ΓA, (Subgroup.closure (s : Set ΓA)).topologicalClosure = ⊤)
    (hfgG : ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤)
    (hΓA : ∀ (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G] [Finite G],
        Nat.card (ContSurj ΓA G) = admissibleCount G) :
    Nonempty (ContinuousMulEquiv ΓA AbsGalQ2) := by
  apply reconstruction hfgΓ hfgG
  intro G _ _ _ _
  rw [hΓA G]
  -- `admissibleCount G = |Sur(G_{ℚ₂}, G)|` is `main_surjection_count` (reversed).
  exact (main_surjection_count G).symm

end GQ2
