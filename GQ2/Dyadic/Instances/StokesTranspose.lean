/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Word.Stokes

/-!
# Transposing the Heisenberg pairing

Exchanging the primal and dual coordinates adds the diagonal evaluation to the central
coordinate. This defines a group homomorphism into the Heisenberg lift of the dual module.
For generator offsets with zero pointwise pairing, it identifies word evaluations; on
primal cocycles the diagonal correction vanishes, giving symmetry without a field or
finite-stage hypothesis. The raw hyperbolic source uses this for its two cross terms.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2.FoxH

variable {C A ι : Type*} [Group C] [AddCommGroup A] [DistribMulAction C A]

/-- Exchange the two first jets, correcting the central coordinate by evaluation. -/
def heisTranspose : HeisLift A C →* HeisLift (ElemDual A) C where
  toFun p := ⟨p.l, dualEval A p.a, p.z + p.l p.a, p.g⟩
  map_one' := by
    apply HeisLift.ext
    · rfl
    · change dualEval A 0 = 0
      exact map_zero _
    · simp
    · rfl
  map_mul' p q := by
    apply HeisLift.ext
    · rfl
    · apply ElemDual.ext
      intro lam
      change lam (p.a + p.g • q.a) = lam p.a + (p.g⁻¹ • lam) q.a
      simp
    · change p.z + q.z + p.l (p.g • q.a) +
          (p.l + p.g • q.l) (p.a + p.g • q.a) =
        p.z + p.l p.a + (q.z + q.l q.a) + (p.g • q.l) p.a
      simp only [ElemDual.add_apply, ElemDual.smul_apply, map_add,
        inv_smul_smul]
      linear_combination CharTwo.add_self_eq_zero (p.l (p.g • q.a))
    · rfl

/-- No generator-level central correction is needed for pointwise orthogonal offsets. -/
theorem heisWord_transpose_of_pointwise_zero
    (c : ι → C) (x : ι → A) (y : ι → ElemDual A)
    (hxy : ∀ i, y i (x i) = 0) (w : FreeGroup ι) :
    (FreeGroup.lift (heisGen c x y) w).z +
        (FreeGroup.lift (heisGen c x y) w).l
          ((FreeGroup.lift (heisGen c x y) w).a) =
      (FreeGroup.lift (heisGen c y (fun i ↦ dualEval A (x i))) w).z := by
  have H : heisTranspose.comp (FreeGroup.lift (heisGen c x y)) =
      FreeGroup.lift (heisGen c y (fun i ↦ dualEval A (x i))) := by
    apply FreeGroup.ext_hom
    intro i
    apply HeisLift.ext <;> simp [heisTranspose, heisGen, hxy]
    rfl
  exact congrArg HeisLift.z (DFunLike.congr_fun H w)

/-- A vanishing primal word jet removes the remaining transpose correction. -/
theorem heisWord_swap_of_pointwise_zero_of_a_zero
    (c : ι → C) (x : ι → A) (y : ι → ElemDual A)
    (hxy : ∀ i, y i (x i) = 0) (w : FreeGroup ι)
    (hx : (FreeGroup.lift (heisGen c x y) w).a = 0) :
    (FreeGroup.lift (heisGen c x y) w).z =
      (FreeGroup.lift (heisGen c y (fun i ↦ dualEval A (x i))) w).z := by
  simpa [hx] using heisWord_transpose_of_pointwise_zero c x y hxy w

/-- Symmetry of the traced pairing on pointwise orthogonal offsets and primal cocycles. -/
theorem heisEta1_swap_of_pointwise_zero_of_cocycle
    {ρ : Type*} [Fintype ρ] (c : ι → C) (w : ρ → FreeGroup ι)
    (x : ι → A) (y : ι → ElemDual A)
    (hxy : ∀ i, y i (x i) = 0) (hx : heisD1 c w x = 0) :
    heisEta1 c w x y = heisEta1 c w y (fun i ↦ dualEval A (x i)) := by
  simp only [heisEta1_apply]
  apply Finset.sum_congr rfl
  intro k _
  apply heisWord_swap_of_pointwise_zero_of_a_zero c x y hxy
  rw [heisWord_a_indep c x y 0]
  exact congrFun hx k

#print axioms heisTranspose
#print axioms heisWord_transpose_of_pointwise_zero
#print axioms heisWord_swap_of_pointwise_zero_of_a_zero
#print axioms heisEta1_swap_of_pointwise_zero_of_cocycle
end
end GQ2.Dyadic
