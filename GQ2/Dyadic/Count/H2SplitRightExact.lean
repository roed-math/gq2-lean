/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.CohomologyDevissage

/-!
# The split part of degree-two coefficient right exactness

An equivariantly split coefficient surjection is automatically surjective on continuous `H²`:
apply the coefficient map induced by the section and then the original coefficient map.  This
elementary observation isolates the genuinely missing CD-2 input to nonsplit finite module
quotients.  No presentation, Tate duality, Euler characteristic, or field realization is used.
-/

namespace GQ2.ContCoh

noncomputable section

variable {G A B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DistribMulAction G B] [ContinuousSMul G B]

/-- A continuous equivariant additive right inverse to a coefficient map. -/
structure EquivariantAddSection (g : A →+ B) where
  sect : B →+ A
  continuous_sect : Continuous sect
  sect_equivariant : ∀ (c : G) (b : B), sect (c • b) = c • sect b
  right_inv : ∀ b : B, g (sect b) = b

/-- A continuously and equivariantly split coefficient map is surjective on continuous `H²`.

The proof is on normalized cocycle representatives and therefore does not need a general
functorial-composition theorem for `mapCoeff2`. -/
theorem H2RightExactAt.of_equivariantAddSection
    (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a)
    (S : EquivariantAddSection (G := G) g) : H2RightExactAt g hgC hg := by
  intro y
  obtain ⟨z, rfl⟩ := H2mk_surjective (G := G) (M := B) y
  let x : H2 G A := mapCoeff2 S.sect S.continuous_sect S.sect_equivariant
    (H2mk G B z)
  refine ⟨x, ?_⟩
  rw [show x = mapCoeff2 S.sect S.continuous_sect S.sect_equivariant
      (H2mk G B z) from rfl]
  rw [mapCoeff2_H2mk_coeff, mapCoeff2_H2mk_coeff]
  apply congrArg (H2mk G B)
  apply Subtype.ext
  funext p
  exact S.right_inv (z.1 p)

/-- The unresolved part of a finite coefficient CD-2 theorem consists only of maps without an
equivariant additive section: split maps are discharged by
`H2RightExactAt.of_equivariantAddSection`. -/
theorem H2RightExactAt.of_nonsplit_or_section
    (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a)
    (hnonsplit : (¬ Nonempty (EquivariantAddSection (G := G) g)) →
      H2RightExactAt g hgC hg) :
    H2RightExactAt g hgC hg := by
  by_cases hS : Nonempty (EquivariantAddSection (G := G) g)
  · exact H2RightExactAt.of_equivariantAddSection g hgC hg hS.some
  · exact hnonsplit hS

end

end GQ2.ContCoh
