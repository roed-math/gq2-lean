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

*Status:* the honest computational content of the paper; proof deferred (needs the §§3–9 tower —
see `docs/proof-architecture.md`). -/
theorem main_surjection_count
    (G : Type) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G] :
    contSurjCount G = admissibleCount G := by
  sorry

/-!
## The literal presentation form (Theorem 1.2 as printed)

To state `G_{ℚ₂} ≅ ⟨σ,τ,x₀,x₁ | τ^σ=τ², h₀u₁⁻¹x₁^σc₀=1, ⟨⟨x₀,x₁⟩⟩ pro-2⟩` literally, one needs
two foundations **absent from Mathlib and its open PR queue** (see `docs/foundations-audit.md`):

1. `FreeProfiniteGroup (Fin 4)` and profinite presentations (quotient by the closed normal
   closure of the two relators), to build the candidate profinite group `Γ_A`.
2. `ℤ̂` and its idempotent `ω₂`, to interpret `x ^ ω₂` in the profinite group directly
   (on finite quotients this is `GQ2.powOmega2`, which we already have).

Given those, the candidate `Γ_A` satisfies (paper Prop. 2.3)
`Nat.card (ContSurj Γ_A G) = admissibleCount G` for every finite `G`, so
`main_surjection_count` becomes `∀ G, |Sur(Γ_A, G)| = |Sur(G_{ℚ₂}, G)|`, and `reconstruction`
(Lemma 2.5) delivers `Nonempty (ContinuousMulEquiv Γ_A G_{ℚ₂})` — Theorem 1.2.

This wiring is recorded as a `sorry`-backed target so the top-level logic is explicit:
-/

/-- **Theorem 1.2 (literal presentation form), schematic.** The candidate profinite group `Γ_A`
(hypothesised here with the property proved in Prop. 2.3, since `FreeProfiniteGroup`/`ℤ̂` are not
yet in Mathlib) is continuously isomorphic to `G_{ℚ₂}`.

`ΓA` stands in for the presented profinite group; `hΓA` is Prop. 2.3 (its finite quotients are the
admissible markings); `hfg` is topological finite generation. The conclusion is Theorem 1.2. -/
theorem main_presentation
    (ΓA : Type)
    [Group ΓA] [TopologicalSpace ΓA] [IsTopologicalGroup ΓA]
      [CompactSpace ΓA] [TotallyDisconnectedSpace ΓA]
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (hfgΓ : ∃ s : Finset ΓA, (Subgroup.closure (s : Set ΓA)).topologicalClosure = ⊤)
    (hΓA : ∀ (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G] [Finite G],
        Nat.card (ContSurj ΓA G) = admissibleCount G) :
    Nonempty (ContinuousMulEquiv ΓA AbsGalQ2) := by
  apply reconstruction hfgΓ
  intro G _ _ _ _
  rw [hΓA G]
  -- `admissibleCount G = |Sur(G_{ℚ₂}, G)|` is `main_surjection_count` (reversed).
  exact (main_surjection_count G).symm

end GQ2
