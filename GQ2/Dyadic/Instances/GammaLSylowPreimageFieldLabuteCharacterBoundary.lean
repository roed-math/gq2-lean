/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteBracketSpan
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The character boundary for the variable-rank Labute stage

The literal bracket-span obligation is equivalent to one character-vanishing statement:
every mod-two character of the elementary graded layer which kills the five families of
allowed bracket atoms must kill the residual.  This file proves that equivalence by elementary
linear duality.  No finiteness hypothesis on the graded layer is needed.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- An element of an elementary abelian multiplicative group lies in a subgroup exactly when
every mod-two additive character annihilating the subgroup annihilates the element. -/
private theorem mem_subgroup_iff_forall_addHom_eq_zero
    {A : Type*} [CommGroup A] (hA2 : ∀ a : A, a ^ 2 = 1)
    (S : Subgroup A) (x : A) :
    x ∈ S ↔
      ∀ φ : Additive A →+ ZMod 2,
        (∀ s : A, s ∈ S → φ (Additive.ofMul s) = 0) →
          φ (Additive.ofMul x) = 0 := by
  have htwo : ∀ a : Additive A, a + a = 0 := by
    intro a
    apply Additive.toMul.injective
    change a.toMul * a.toMul = 1
    simpa [pow_two] using hA2 a.toMul
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Module (ZMod 2) (Additive A) :=
    AddCommGroup.zmodModule (fun a ↦ by rw [two_nsmul]; exact htwo a)
  let W : Submodule (ZMod 2) (Additive A) :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup S)
  constructor
  · intro hx φ hφ
    exact hφ x hx
  · intro h
    change Additive.ofMul x ∈ W
    refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mp ?_
    intro φ hφ
    exact h φ.toAddMonoidHom (fun s hs ↦ by
      exact (Submodule.mem_dualAnnihilator φ).mp hφ (Additive.ofMul s) hs)

namespace SqCyclotomicStageTuple

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- Coordinate form of the remaining arithmetic boundary. -/
def SharpNeutralResidualCoordinateCharacterCondition {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (W : SharpAdmissibleCorrection T (by omega)) : Prop :=
  ∀ φ : Additive (zLayer (maxProPQuotient 2 (GalK K)) k) →+ ZMod 2,
    (∀ (i : Fin (SqCore.sqRank h))
      (p : sharpNeutralCoordinateSubgroup (K := K)
        (le_trans (by decide : 1 ≤ 3) hk)),
      φ (Additive.ofMul (sharpNeutralCoordinateShiftHom T hk i p)) = 0) →
    φ (Additive.ofMul (sharpNeutralResidualElement T hk W)) = 0

/-- Literal-bracket-set form of the remaining arithmetic boundary. -/
def SharpNeutralResidualBracketCharacterCondition {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (W : SharpAdmissibleCorrection T (by omega)) : Prop :=
  ∀ φ : Additive (zLayer (maxProPQuotient 2 (GalK K)) k) →+ ZMod 2,
    (∀ z : zLayer (maxProPQuotient 2 (GalK K)) k,
      z ∈ sharpNeutralBracketAtomSet T hk → φ (Additive.ofMul z) = 0) →
    φ (Additive.ofMul (sharpNeutralResidualElement T hk W)) = 0

/-- Fully expanded five-family form of the remaining arithmetic boundary. -/
def SharpNeutralResidualFiveAtomCharacterCondition {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (W : SharpAdmissibleCorrection T (by omega)) : Prop :=
  ∀ φ : Additive (zLayer (maxProPQuotient 2 (GalK K)) k) →+ ZMod 2,
    (∀ (z : zLayer (maxProPQuotient 2 (GalK K)) k)
      (p : sharpNeutralCoordinateSubgroup (K := K)
        (le_trans (by decide : 1 ≤ 3) hk)),
      z.1 = commP p.1
        (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 1)) →
      φ (Additive.ofMul z) = 0) →
    (∀ (z : zLayer (maxProPQuotient 2 (GalK K)) k)
      (p : sharpNeutralCoordinateSubgroup (K := K)
        (le_trans (by decide : 1 ≤ 3) hk)),
      z.1 = commP p.1
        (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) →
      φ (Additive.ofMul z) = 0) →
    (∀ (z : zLayer (maxProPQuotient 2 (GalK K)) k)
      (p : sharpNeutralCoordinateSubgroup (K := K)
        (le_trans (by decide : 1 ≤ 3) hk)),
      z.1 = p.1 ^ 2 * commP p.1
        (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 2)) →
      φ (Additive.ofMul z) = 0) →
    (∀ (z : zLayer (maxProPQuotient 2 (GalK K)) k) (j : Fin h)
      (p : sharpNeutralCoordinateSubgroup (K := K)
        (le_trans (by decide : 1 ≤ 3) hk)),
      z.1 = commP p.1 (canonLift (maxProPQuotient 2 (GalK K)) k
        (T.generators (SqCore.sqHandleIdxV j))) →
      φ (Additive.ofMul z) = 0) →
    (∀ (z : zLayer (maxProPQuotient 2 (GalK K)) k) (j : Fin h)
      (p : sharpNeutralCoordinateSubgroup (K := K)
        (le_trans (by decide : 1 ≤ 3) hk)),
      z.1 = commP p.1 (canonLift (maxProPQuotient 2 (GalK K)) k
        (T.generators (SqCore.sqHandleIdxU j))) →
      φ (Additive.ofMul z) = 0) →
    φ (Additive.ofMul (sharpNeutralResidualElement T hk W)) = 0

/-- Character separation identifies bracket-span membership with the bracket-character
condition. -/
theorem sharpNeutralResidual_mem_bracketSpan_iff_bracketCharacterCondition
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega)) :
    sharpNeutralResidualElement T hk W ∈ sharpNeutralBracketSpan T hk ↔
      SharpNeutralResidualBracketCharacterCondition T hk W := by
  let G := maxProPQuotient 2 (GalK K)
  letI : CommGroup (zLayer G k) :=
    { (inferInstance : Group (zLayer G k)) with
      mul_comm := fun a b ↦
        Subtype.ext (Subgroup.mem_center_iff.mp (zLayer_le_center G k a.2) b.1).symm }
  have hsq : ∀ z : zLayer G k, z ^ 2 = 1 := by
    intro z
    apply Subtype.ext
    exact zLayer_sq G z.2
  rw [mem_subgroup_iff_forall_addHom_eq_zero hsq]
  unfold SharpNeutralResidualBracketCharacterCondition
  constructor
  · intro H φ hatom
    apply H φ
    intro z hz
    rw [sharpNeutralBracketSpan] at hz
    refine Subgroup.closure_induction (p := fun z _ ↦
      φ (Additive.ofMul z) = 0) hatom ?_ ?_ ?_ hz
    · exact φ.map_zero
    · intro x y _ _ hx hy
      simpa [hx, hy] using φ.map_add (Additive.ofMul x) (Additive.ofMul y)
    · intro x _ hx
      simpa [hx] using φ.map_neg (Additive.ofMul x)
  · intro H φ hspan
    apply H φ
    intro z hz
    exact hspan z (Subgroup.subset_closure hz)

/-- The coordinate and literal-bracket formulations of the character boundary coincide. -/
theorem sharpNeutralResidualCoordinateCharacterCondition_iff_bracketCharacterCondition
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega)) :
    SharpNeutralResidualCoordinateCharacterCondition T hk W ↔
      SharpNeutralResidualBracketCharacterCondition T hk W := by
  unfold SharpNeutralResidualCoordinateCharacterCondition
    SharpNeutralResidualBracketCharacterCondition
  constructor
  · intro H φ hatom
    apply H φ
    intro i p
    apply hatom
    rw [← sharpNeutralCoordinateHomImageSet_eq_bracketAtomSet T hk]
    exact ⟨i, p, rfl⟩
  · intro H φ hcoordinate
    apply H φ
    intro z hz
    rw [← sharpNeutralCoordinateHomImageSet_eq_bracketAtomSet T hk] at hz
    obtain ⟨i, p, rfl⟩ := hz
    exact hcoordinate i p

/-- The bracket-set and fully expanded five-family character conditions coincide. -/
theorem sharpNeutralResidualBracketCharacterCondition_iff_fiveAtomCharacterCondition
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega)) :
    SharpNeutralResidualBracketCharacterCondition T hk W ↔
      SharpNeutralResidualFiveAtomCharacterCondition T hk W := by
  unfold SharpNeutralResidualBracketCharacterCondition
    SharpNeutralResidualFiveAtomCharacterCondition
  constructor
  · intro H φ hzero hone htwo hU hV
    apply H φ
    intro z hz
    rcases hz with ⟨p, hp⟩ | ⟨p, hp⟩ | ⟨p, hp⟩ | ⟨j, p, hp⟩ | ⟨j, p, hp⟩
    · exact hzero z p hp
    · exact hone z p hp
    · exact htwo z p hp
    · exact hU z j p hp
    · exact hV z j p hp
  · intro H φ hatom
    apply H φ
    · intro z p hz
      exact hatom z (Or.inl ⟨p, hz⟩)
    · intro z p hz
      exact hatom z (Or.inr (Or.inl ⟨p, hz⟩))
    · intro z p hz
      exact hatom z (Or.inr (Or.inr (Or.inl ⟨p, hz⟩)))
    · intro z j p hz
      exact hatom z (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, p, hz⟩))))
    · intro z j p hz
      exact hatom z (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, p, hz⟩))))

/-- The stage residual is reachable exactly when the coordinate-character boundary holds. -/
theorem sharpNeutralResidualReachable_iff_coordinateCharacterCondition
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega)) :
    SharpNeutralResidualReachable T hk W ↔
      SharpNeutralResidualCoordinateCharacterCondition T hk W :=
  (sharpNeutralResidualReachable_iff_mem_bracketSpan W).trans
    ((sharpNeutralResidual_mem_bracketSpan_iff_bracketCharacterCondition W).trans
      (sharpNeutralResidualCoordinateCharacterCondition_iff_bracketCharacterCondition W).symm)

end SqCyclotomicStageTuple

#print axioms SqCyclotomicStageTuple.sharpNeutralResidual_mem_bracketSpan_iff_bracketCharacterCondition
#print axioms SqCyclotomicStageTuple.sharpNeutralResidualCoordinateCharacterCondition_iff_bracketCharacterCondition
#print axioms SqCyclotomicStageTuple.sharpNeutralResidualBracketCharacterCondition_iff_fiveAtomCharacterCondition
#print axioms SqCyclotomicStageTuple.sharpNeutralResidualReachable_iff_coordinateCharacterCondition

end

end GQ2.Dyadic.LSquare
