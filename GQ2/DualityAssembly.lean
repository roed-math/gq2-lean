import GQ2.Devissage
import GQ2.TrivialSelfDual

/-!
# P-13f: assembling `prop_5_15` (deformation duality) from the simple-module case + dévissage

`prop_5_15 : IsSelfDual t A` for every finite elementary `𝔽₂[C]`-module.  Route: the simple modules
are self-dual (trivial module via `trivialSelfDual`; nontrivial simples via `lemma_5_13` + the
degree-one pairing), then `lemma_5_11` (dévissage, `GQ2/Devissage.lean`) two-out-of-three along a
composition series.

This file lives outside `FoxHeisenberg.lean` because it needs `lemma_5_11` (in `Devissage`, which
imports `FoxHeisenberg`) — the import runs the other way, the `TrivialSelfDual.lean` pattern.

## Card bookkeeping for the simple case

For a nontrivial simple module the invariants `H⁰w(A) = A^C` vanish, so the normal form
`H¹w ≅ A` (`lemma_5_13`) forces `#Z¹w = #A²` and `#H²w = 1` — clauses 1 and 2 of `IsSelfDual`.
-/

namespace GQ2.FoxH

open scoped Classical

variable {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [Finite A]
  [DistribMulAction C A]

/-- **`H¹w ≅ A` from the normal form**: when every `x₀`-supported tuple is a cocycle and every
cocycle is uniquely `x₀`-supported modulo coboundaries (`lemma_5_13`), the class map `A → H¹w`,
`c ↦ [x₀Supported c]`, is a bijection, so `#H¹w = #A`. -/
theorem card_H1w_of_normalForm (t : Marking C)
    (hx0mem : ∀ c : A, x0Supported c ∈ Z1w (A := A) t)
    (hnf : ∀ x ∈ Z1w (A := A) t, ∃! c : A, x - x0Supported c ∈ B1w (A := A) t) :
    Nat.card (H1w (A := A) t) = Nat.card A := by
  have key : ∀ (a b : Z1w (A := A) t),
      h1wMk t a = h1wMk t b ↔ b.val - a.val ∈ B1w (A := A) t := by
    intro a b
    show QuotientAddGroup.mk a = QuotientAddGroup.mk b ↔ _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    show -a.val + b.val ∈ B1w (A := A) t ↔ b.val - a.val ∈ B1w (A := A) t
    rw [show -a.val + b.val = b.val - a.val from by abel]
  refine (Nat.card_eq_of_bijective (fun c => h1wMk t ⟨x0Supported c, hx0mem c⟩) ⟨?_, ?_⟩).symm
  · -- injective
    intro c c' hcc
    rw [key] at hcc
    -- `hcc : x₀Supported c' − x₀Supported c ∈ B¹w`
    obtain ⟨cu, -, huniq⟩ := hnf (x0Supported c) (hx0mem c)
    have e1 : c = cu := huniq c (show x0Supported c - x0Supported c ∈ B1w (A := A) t by
      rw [sub_self]; exact (B1w (A := A) t).zero_mem)
    have e2 : c' = cu := huniq c' (show x0Supported c - x0Supported c' ∈ B1w (A := A) t by
      have h := (B1w (A := A) t).neg_mem hcc; rwa [neg_sub] at h)
    exact e1.trans e2.symm
  · -- surjective
    intro h
    induction h using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨c, hc, -⟩ := hnf x.val x.2
      exact ⟨c, (key ⟨x0Supported c, hx0mem c⟩ x).mpr hc⟩

end GQ2.FoxH
