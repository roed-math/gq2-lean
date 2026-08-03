/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoFoxCounterexample
import GQ2.Dyadic.Count.HTwoRelationModuleCokernel
import GQ2.Dyadic.Count.Variation

/-!
# The trivial-target obstruction persists modulo the word differential

For a two-relator Stokes endpoint at the trivial target, both relation-character value vectors
and the image of `heisD1` lie in the diagonal of `(ZMod 2) × (ZMod 2)`.  Passing from exact
relator coordinates to values modulo `heisD1.range` therefore does **not** repair fixed-target
surjectivity: every relation character still represents the zero cokernel class, while the
class of `(0,1)` is nonzero.

Thus continuous relator realization cannot in general be obtained by transgressing relation
characters at the action target itself.  A deeper finite quotient, as allowed by
`ModuleRelatorRealization` and `VectorwiseRefinedRelationCharacterRealization`, is essential.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.FoxH

section TrivialTarget

variable {I : Type} [Fintype I] [DecidableEq I]
  {w : Fin 2 → FreeGroup I}

/-- At the trivial target, a Stokes endpoint has no fixed-target relation-character supply even
after displayed values are taken modulo the word differential. -/
theorem not_relationModuleRelatorCokernelSurjective_punit
    (hend : IsStokesEndpoint w)
    (hrel : ∀ k, FreeGroup.lift (fun _ : I ↦ (1 : PUnit)) (w k) = 1) :
    ¬ RelationModuleRelatorCokernelSurjective (A := ZMod 2) w hrel := by
  intro hsurj
  let r : Fin 2 → ZMod 2 := ![0, 1]
  obtain ⟨chi, hchi⟩ := hsurj r
  obtain ⟨x, hx⟩ := hchi
  have hsum := sum_heisD1_zmod2 hrel hend x
  rw [hx, Fin.sum_univ_two] at hsum
  have heq :=
    FreeRelationCharacter.val_zero_eq_val_one_of_stokesEndpoint_punit hend chi
  change
    (chi.val ⟨w 0, Subsingleton.elim _ _⟩ - 0) +
      (chi.val ⟨w 1, Subsingleton.elim _ _⟩ - 1) = 0 at hsum
  rw [heq] at hsum
  have htwo : chi.val ⟨w 1, Subsingleton.elim _ _⟩ +
      chi.val ⟨w 1, Subsingleton.elim _ _⟩ = 0 :=
    CharTwo.add_self_eq_zero _
  rw [sub_zero, sub_eq_add_neg, ← add_assoc, htwo, zero_add] at hsum
  exact one_ne_zero (neg_eq_zero.mp hsum)

end TrivialTarget

end

end GQ2.Dyadic.Count
