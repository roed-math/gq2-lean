/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Word.Stokes

/-!
# Stokes comparison from Heisenberg coordinates

Equality of both first jets and of the central coordinate is exactly the datum needed to
identify Stokes ladders. No equality of the base values, relator-death premise, or endpoint
premise is needed for this comparison of the ladders themselves.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2 GQ2.FoxH

variable {X I C A : Type*} [Fintype I]
  [Group C] [AddCommGroup A] [DistribMulAction C A]

theorem stokesDuality_iff_of_heisWord_coordinates
    (c : X → C) (w v : I → FreeGroup X)
    (h : ∀ (x : X → A) (y : X → ElemDual A) (k : I),
      let p := FreeGroup.lift (heisGen c x y) (w k)
      let q := FreeGroup.lift (heisGen c x y) (v k)
      p.a = q.a ∧ p.l = q.l ∧ p.z = q.z) :
    StokesDuality c w A ↔ StokesDuality c v A := by
  have hA : heisD1 (A := A) c w = heisD1 c v := by
    apply AddMonoidHom.ext
    intro x
    funext k
    exact (h x 0 k).1
  have hD : heisD1 (A := ElemDual A) c w = heisD1 c v := by
    apply AddMonoidHom.ext
    intro y
    funext k
    simp only [heisD1_apply, ← heisWord_l_eq_dual_a c (0 : X → A) y]
    exact (h 0 y k).2.1
  have hη : heisEta1 (A := A) c w = heisEta1 c v := by
    apply AddMonoidHom.ext
    intro x
    apply ElemDual.ext
    intro y
    exact Finset.sum_congr rfl fun k _ ↦ (h x y k).2.2
  unfold StokesDuality
  rw [hA, hD, hη]

#print axioms stokesDuality_iff_of_heisWord_coordinates

end
end GQ2.Dyadic
