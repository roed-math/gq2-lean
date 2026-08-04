/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Demushkin
import GQ2.Dyadic.Count.H2SylowPreimageDevissage

/-!
# Scalar Demushkin data does not imply coefficient CD-2

The repository's `IsDemushkin` structure intentionally records scalar mod-two cohomology and
the scalar cup pairing.  It does not contain cohomological dimension two.  This file gives a
formal counterexample to any attempted implication from that record alone.

The cyclic group `C₂` is `IsDemushkin 2` in the repository.  Let it act on the regular
two-dimensional `F₂`-module by swapping the coordinates, and map that module to the trivial
module by augmentation.  The augmentation is onto and has a two-element kernel, but its map on
`H²` is not onto: every image class has zero value under the explicit cyclic-two `H²`
functional, while the scalar cup-square generator has value one.

Thus a genuine torsion-free/asphericity/PD-2 hypothesis is required in the general campaign;
the scalar fields of `IsDemushkin` cannot discharge the residual scalar-kernel tail.
-/

namespace GQ2.ContCoh

noncomputable section

private abbrev CTwo := DihedralGroup 1
private structure CTwoRegular where
  left : ZMod 2
  right : ZMod 2
deriving DecidableEq, Fintype

@[reducible] private def cTwoRegularEquiv : CTwoRegular ≃ ZMod 2 × ZMod 2 where
  toFun v := (v.left, v.right)
  invFun v := ⟨v.1, v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private abbrev sigma : CTwo := DihedralGroup.sr 0

local instance : TopologicalSpace CTwo := ⊥
local instance : DiscreteTopology CTwo := ⟨rfl⟩

local instance : AddCommGroup CTwoRegular :=
  Equiv.addCommGroup cTwoRegularEquiv
local instance : Finite CTwoRegular := by infer_instance

@[simp] private theorem cTwoRegular_zero_left : (0 : CTwoRegular).left = 0 := rfl
@[simp] private theorem cTwoRegular_zero_right : (0 : CTwoRegular).right = 0 := rfl
@[simp] private theorem cTwoRegular_add_left (v w : CTwoRegular) :
    (v + w).left = v.left + w.left := rfl
@[simp] private theorem cTwoRegular_add_right (v w : CTwoRegular) :
    (v + w).right = v.right + w.right := rfl

local instance : TopologicalSpace CTwoRegular := ⊥
local instance : DiscreteTopology CTwoRegular := ⟨rfl⟩
local instance : IsTopologicalAddGroup CTwoRegular := by infer_instance

/-- The regular two-dimensional mod-two representation of `C₂`. -/
@[reducible] private def cTwoRegularSmul : SMul CTwo CTwoRegular :=
  ⟨fun g v ↦ if g = 1 then v else ⟨v.right, v.left⟩⟩

local instance instCTwoRegularAction : DistribMulAction CTwo CTwoRegular where
  toSMul := cTwoRegularSmul
  one_smul v := by
    change (if (1 : CTwo) = 1 then v else ⟨v.right, v.left⟩) = v
    rw [if_pos rfl]
  mul_smul g h v := by
    revert g h v
    decide
  smul_zero g := by
    by_cases hg : g = 1
    · subst g
      rfl
    · change (if g = 1 then (0 : CTwoRegular) else
          CTwoRegular.mk (0 : CTwoRegular).right (0 : CTwoRegular).left) = 0
      rw [if_neg hg]
      apply cTwoRegularEquiv.injective
      simp
  smul_add g v w := by
    by_cases hg : g = 1
    · subst g
      rfl
    · change (if g = 1 then v + w else CTwoRegular.mk (v + w).right (v + w).left) =
        (if g = 1 then v else CTwoRegular.mk v.right v.left) +
          (if g = 1 then w else CTwoRegular.mk w.right w.left)
      rw [if_neg hg, if_neg hg, if_neg hg]
      apply cTwoRegularEquiv.injective
      simp

local instance : ContinuousSMul CTwo CTwoRegular :=
  ⟨continuous_of_discreteTopology⟩

local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩
local instance : ContinuousSMul CTwo (ZMod 2) :=
  ⟨continuous_of_discreteTopology⟩

/-- Augmentation of the regular mod-two representation. -/
def cyclicTwoRegularAugmentation : CTwoRegular →+ ZMod 2 where
  toFun v := v.left + v.right
  map_zero' := by simp
  map_add' _ _ := by simp; abel

theorem cyclicTwoRegularAugmentation_surjective :
    Function.Surjective cyclicTwoRegularAugmentation := by
  intro x
  exact ⟨⟨x, 0⟩, by simp [cyclicTwoRegularAugmentation]⟩

theorem cyclicTwoRegularAugmentation_equivariant
    (g : CTwo) (v : CTwoRegular) :
    cyclicTwoRegularAugmentation (g • v) = g • cyclicTwoRegularAugmentation v := by
  rw [isDemushkin_cyclicTwo.smul_trivial]
  by_cases hg : g = 1
  · subst g
    rfl
  · change (if g = 1 then v else ⟨v.right, v.left⟩).left +
        (if g = 1 then v else ⟨v.right, v.left⟩).right = v.left + v.right
    rw [if_neg hg]
    exact add_comm _ _

theorem cyclicTwoRegularAugmentation_ker_card :
    Nat.card ↑cyclicTwoRegularAugmentation.ker = 2 := by
  let e : ZMod 2 ≃ ↑cyclicTwoRegularAugmentation.ker :=
    { toFun := fun x ↦ ⟨⟨x, x⟩, by
        rw [AddMonoidHom.mem_ker]
        exact CharTwo.add_self_eq_zero x⟩
      invFun := fun x ↦ x.1.left
      left_inv := fun _ ↦ rfl
      right_inv := fun x ↦ by
        apply Subtype.ext
        apply cTwoRegularEquiv.injective
        apply Prod.ext
        · rfl
        · have hx := AddMonoidHom.mem_ker.mp x.2
          change x.1.left + x.1.right = 0 at hx
          exact (eq_neg_of_add_eq_zero_left hx).trans (CharTwo.neg_eq x.1.right) }
  calc
    Nat.card ↑cyclicTwoRegularAugmentation.ker = Nat.card (ZMod 2) :=
      Nat.card_congr e.symm
    _ = 2 := Nat.card_zmod 2

private theorem regularAugmentation_eq_zero_of_sigma_fixed
    (v : CTwoRegular) (hv : sigma • v = v) :
    cyclicTwoRegularAugmentation v = 0 := by
  have hsigma : sigma ≠ (1 : CTwo) := by decide
  change (if sigma = 1 then v else ⟨v.right, v.left⟩) = v at hv
  rw [if_neg hsigma] at hv
  have hcoord : v.right = v.left := congrArg CTwoRegular.left hv
  change v.left + v.right = 0
  rw [hcoord, CharTwo.add_self_eq_zero]

/-- Every augmented regular-module two-cocycle has zero cyclic-two `H²` evaluation. -/
private theorem cyclicTwoRegularAugmentation_z2_eval_zero
    (z : Z2 CTwo CTwoRegular) :
    cyclicTwoRegularAugmentation (z.1 (1, 1)) +
        cyclicTwoRegularAugmentation (z.1 (sigma, sigma)) = 0 := by
  have hcoc := (mem_Z2_iff.mp z.2).2
  have hb : z.1 (1, sigma) = z.1 (1, 1) := by
    have h := hcoc 1 1 sigma
    simp only [one_smul, one_mul] at h
    exact add_left_cancel h
  have hc : z.1 (sigma, 1) = sigma • z.1 (1, 1) := by
    have h := hcoc sigma 1 sigma
    rw [one_mul, mul_one, hb] at h
    rw [add_comm (z.1 (sigma, sigma))] at h
    exact (add_right_cancel h).symm
  have hfixed : sigma • (z.1 (1, 1) + z.1 (sigma, sigma)) =
      z.1 (1, 1) + z.1 (sigma, sigma) := by
    have h := hcoc sigma sigma sigma
    rw [(by decide : sigma * sigma = (1 : CTwo)), hb, hc] at h
    rw [smul_add, add_comm]
    exact h
  rw [← map_add]
  exact regularAugmentation_eq_zero_of_sigma_fixed _ hfixed

/-- The image of regular-module `H²` lies in the zero fiber of the explicit scalar
cyclic-two evaluation functional. -/
theorem h2CyclicTwoEval_mapCoeff2_regularAugmentation
    (x : H2 CTwo CTwoRegular) :
    h2CyclicTwoEval
      (mapCoeff2 cyclicTwoRegularAugmentation continuous_of_discreteTopology
        cyclicTwoRegularAugmentation_equivariant x) = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
      exact cyclicTwoRegularAugmentation_z2_eval_zero z

/-- The augmentation map on `H²` is not surjective. -/
theorem not_surjective_mapCoeff2_cyclicTwoRegularAugmentation :
    ¬ Function.Surjective
      (mapCoeff2 cyclicTwoRegularAugmentation continuous_of_discreteTopology
        cyclicTwoRegularAugmentation_equivariant) := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj (H2mk CTwo (ZMod 2) wCyclicTwo)
  have heval := congrArg h2CyclicTwoEval hx
  rw [h2CyclicTwoEval_mapCoeff2_regularAugmentation] at heval
  have hgen : h2CyclicTwoEval (H2mk CTwo (ZMod 2) wCyclicTwo) = 1 := by decide
  rw [hgen] at heval
  exact zero_ne_one heval

/-- Formal no-go regression: `C₂` satisfies the repository's scalar Demushkin record, but
fails the two-element-kernel `H²` right-exactness conclusion. -/
theorem isDemushkin_not_h2RightExactAt_cyclicTwoRegular :
    IsDemushkin 2 CTwo ∧
      ¬ H2RightExactAt cyclicTwoRegularAugmentation continuous_of_discreteTopology
        cyclicTwoRegularAugmentation_equivariant :=
  ⟨isDemushkin_cyclicTwo,
    not_surjective_mapCoeff2_cyclicTwoRegularAugmentation⟩

end

end GQ2.ContCoh
