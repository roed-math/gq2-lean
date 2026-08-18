/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcBalancedTargetCharacterObstruction

/-!
# Mod-four coordinates for the balanced target-character obstruction

W231 expresses constrained target coverage using every complex character of a finite
neutrality cokernel, and W232 records the exact detecting-character obstruction. This file
makes that obstruction finite and explicit.

Every complex character of the two-digit plane `(ZMod 4) × (ZMod 4)` is determined by a
coefficient pair `(a,b)`. Pulling a quotient character back to the plane therefore gives such
a pair.
Conversely, a coefficient character which kills every CABD interaction row descends through
the quotient. Hence abstract character detection is exactly equivalent to a target digit pair
and two mod-four coefficients which annihilate all interaction rows but not that target.

The resulting coefficient obstruction is equivalent both to failure of constrained coordinate
coverage and to emptiness of the next balanced stage, point by point. No coefficient detector
is asserted to exist uniformly.
-/

namespace GQ2.Dyadic.Instances.MpcBalancedTargetCharacterCoordinates

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcOneHandleBalancedLimit
open GQ2.Dyadic.Instances.MpcBalancedRelativeSpan
open GQ2.Dyadic.Instances.MpcBalancedCoordinateSpan
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCokernel
open GQ2.Dyadic.Instances.MpcBalancedNeutralityInteraction
open GQ2.Dyadic.Instances.MpcBalancedNeutralityCoordinateCokernel
open GQ2.Dyadic.Instances.MpcBalancedTargetCharacters
open GQ2.Dyadic.Instances.MpcBalancedTargetCharacterObstruction

open scoped IsMulCommutative

abbrev OneHandleZModFourPlane :=
  Additive (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))

private def oneHandleZModFourPlaneFst : OneHandleZModFourPlane →+ ZMod 4 where
  toFun z := z.toMul.1.toAdd
  map_zero' := rfl
  map_add' _ _ := rfl

private def oneHandleZModFourPlaneSnd : OneHandleZModFourPlane →+ ZMod 4 where
  toFun z := z.toMul.2.toAdd
  map_zero' := rfl
  map_add' _ _ := rfl

def oneHandleZModFourPlaneCharacter (a b : ZMod 4) :
    AddChar OneHandleZModFourPlane ℂ :=
  (AddChar.zmodAddEquiv a).compAddMonoidHom oneHandleZModFourPlaneFst +
    (AddChar.zmodAddEquiv b).compAddMonoidHom oneHandleZModFourPlaneSnd

@[simp] theorem oneHandleZModFourPlaneCharacter_apply
    (a b : ZMod 4) (z : OneHandleZModFourPlane) :
    oneHandleZModFourPlaneCharacter a b z =
      AddChar.zmodAddEquiv a z.toMul.1.toAdd *
        AddChar.zmodAddEquiv b z.toMul.2.toAdd :=
  rfl

private def oneHandleZModFourPlaneInl : ZMod 4 →+ OneHandleZModFourPlane where
  toFun z := Additive.ofMul (Multiplicative.ofAdd z, 1)
  map_zero' := rfl
  map_add' _ _ := rfl

private def oneHandleZModFourPlaneInr : ZMod 4 →+ OneHandleZModFourPlane where
  toFun z := Additive.ofMul (1, Multiplicative.ofAdd z)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem exists_eq_oneHandleZModFourPlaneCharacter
    (chi : AddChar OneHandleZModFourPlane ℂ) :
    ∃ a b : ZMod 4, chi = oneHandleZModFourPlaneCharacter a b := by
  let a := AddChar.zmodAddEquiv.symm
    (chi.compAddMonoidHom oneHandleZModFourPlaneInl)
  let b := AddChar.zmodAddEquiv.symm
    (chi.compAddMonoidHom oneHandleZModFourPlaneInr)
  refine ⟨a, b, ?_⟩
  ext z
  have hz : z = oneHandleZModFourPlaneInl z.toMul.1.toAdd +
      oneHandleZModFourPlaneInr z.toMul.2.toAdd := by
    apply Additive.toMul.injective
    apply Prod.ext
    · simp [oneHandleZModFourPlaneInl, oneHandleZModFourPlaneInr]
    · simp [oneHandleZModFourPlaneInl, oneHandleZModFourPlaneInr]
  calc
    chi z = chi (oneHandleZModFourPlaneInl z.toMul.1.toAdd +
        oneHandleZModFourPlaneInr z.toMul.2.toAdd) := congrArg chi hz
    _ = chi (oneHandleZModFourPlaneInl z.toMul.1.toAdd) *
        chi (oneHandleZModFourPlaneInr z.toMul.2.toAdd) :=
      AddChar.map_add_eq_mul _ _ _
    _ = AddChar.zmodAddEquiv a z.toMul.1.toAdd *
        AddChar.zmodAddEquiv b z.toMul.2.toAdd := by
      simp only [a, b, AddEquiv.apply_symm_apply,
        AddChar.compAddMonoidHom_apply]
    _ = oneHandleZModFourPlaneCharacter a b z := rfl

private def oneHandleBalancedCoreNeutralityCoordinatePullback
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (chi : AddChar
      (Additive (OneHandleBalancedCoreNeutralityCokernel p k hk)) ℂ) :
    AddChar OneHandleZModFourPlane ℂ :=
  chi.compAddMonoidHom
    (oneHandleBalancedCoreNeutralityCoordinateFactor p k hk).toAdditive

@[simp] private theorem oneHandleBalancedCoreNeutralityCoordinatePullback_apply
    (p : OneHandleBalancedPoint) (k : ℕ) (hk : 3 ≤ k)
    (chi : AddChar
      (Additive (OneHandleBalancedCoreNeutralityCokernel p k hk)) ℂ)
    (z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    oneHandleBalancedCoreNeutralityCoordinatePullback p k hk chi
        (Additive.ofMul z) =
      chi (Additive.ofMul
        (oneHandleBalancedCoreNeutralityCoordinateFactor p k hk z)) :=
  rfl

def OneHandleBalancedCoreTargetCoefficientDetected
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) : Prop :=
  ∃ z : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
    oneHandleBalancedCoreNeutralityCoordinateFactor p k hk z =
        oneHandleBalancedCoreNeutralityObstruction p hk hp hrel ∧
      ∃ a b : ZMod 4,
        oneHandleZModFourPlaneCharacter a b (Additive.ofMul z) ≠ 1 ∧
          ∀ x : oneHandleBalancedCoreNeutralityInteractionSource p k hk,
            oneHandleZModFourPlaneCharacter a b
              (Additive.ofMul
                (oneHandleBalancedCoreNeutralityCoordinateRow p k hk x)) = 1

private noncomputable def descendMonoidHomOfSurjective
    {G Q C : Type*} [Group G] [Group Q] [CommGroup C]
    (f : G →* Q) (hf : Function.Surjective f)
    (psi : G →* C) (hker : f.ker ≤ psi.ker) : Q →* C :=
  f.liftOfSurjective hf ⟨psi, hker⟩

@[simp] private theorem descendMonoidHomOfSurjective_apply
    {G Q C : Type*} [Group G] [Group Q] [CommGroup C]
  (f : G →* Q) (hf : Function.Surjective f)
    (psi : G →* C) (hker : f.ker ≤ psi.ker) (x : G) :
    descendMonoidHomOfSurjective f hf psi hker (f x) = psi x := by
  exact MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hf)
    (Function.rightInverse_surjInv hf) ⟨psi, hker⟩ x

private def monoidHomOfAdditiveAddChar
    {G C : Type*} [Group G] [CommGroup C]
    (psi : AddChar (Additive G) C) : G →* C where
  toFun x := psi (Additive.ofMul x)
  map_one' := AddChar.map_zero_eq_one psi
  map_mul' x y := AddChar.map_add_eq_mul psi
    (Additive.ofMul x) (Additive.ofMul y)

@[simp] private theorem monoidHomOfAdditiveAddChar_apply
    {G C : Type*} [Group G] [CommGroup C]
    (psi : AddChar (Additive G) C) (x : G) :
    monoidHomOfAdditiveAddChar psi x = psi (Additive.ofMul x) :=
  rfl

private def additiveAddCharOfMonoidHom
    {Q C : Type*} [Group Q] [CommGroup C] (f : Q →* C) :
    AddChar (Additive Q) C where
  toFun x := f x.toMul
  map_zero_eq_one' := f.map_one
  map_add_eq_mul' x y := f.map_mul x.toMul y.toMul

@[simp] private theorem additiveAddCharOfMonoidHom_apply
    {Q C : Type*} [Group Q] [CommGroup C]
    (f : Q →* C) (x : Q) :
    additiveAddCharOfMonoidHom f (Additive.ofMul x) = f x :=
  rfl

private theorem exists_quotient_addChar_of_detecting
    {G Q : Type*} [CommGroup G] [CommGroup Q] [Finite G] [Finite Q]
    (f : G →* Q) (hf : Function.Surjective f)
    (psi : AddChar (Additive G) ℂ)
    (hker : ∀ x ∈ f.ker, psi (Additive.ofMul x) = 1)
    (z : G) (hz : psi (Additive.ofMul z) ≠ 1) :
    ∃ chi : AddChar (Additive Q) ℂ,
      chi (Additive.ofMul (f z)) ≠ 1 := by
  let psiCircle := AddChar.circleEquivComplex.symm psi
  have hpsi : AddChar.circleEquivComplex psiCircle = psi :=
    AddEquiv.apply_symm_apply AddChar.circleEquivComplex psi
  have hkerCircle : ∀ x ∈ f.ker,
      psiCircle (Additive.ofMul x) = 1 := by
    intro x hx
    apply Subtype.ext
    exact (DFunLike.congr_fun hpsi (Additive.ofMul x)).trans (hker x hx)
  have hzCircle : psiCircle (Additive.ofMul z) ≠ 1 := by
    intro h
    apply hz
    exact (DFunLike.congr_fun hpsi (Additive.ofMul z)).symm.trans
      (congrArg Subtype.val h)
  have hker' : f.ker ≤ (monoidHomOfAdditiveAddChar psiCircle).ker := by
    intro x hx
    exact MonoidHom.mem_ker.mpr (hkerCircle x hx)
  let desc : Q →* Circle := descendMonoidHomOfSurjective f hf
    (monoidHomOfAdditiveAddChar psiCircle) hker'
  let chiCircle : AddChar (Additive Q) Circle := additiveAddCharOfMonoidHom desc
  have hchiCircle : chiCircle (Additive.ofMul (f z)) ≠ 1 := by
    simpa [chiCircle, desc] using hzCircle
  refine ⟨AddChar.circleEquivComplex chiCircle, ?_⟩
  intro h
  apply hchiCircle
  apply Subtype.ext
  exact h

theorem targetCharacterDetected_of_coefficientDetected
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk)
    (H : OneHandleBalancedCoreTargetCoefficientDetected p hk hp hrel) :
    OneHandleBalancedCoreTargetCharacterDetected p hk hp hrel := by
  rcases H with ⟨z, hz, a, b, htarget, hrow⟩
  let psi := oneHandleZModFourPlaneCharacter a b
  let f := oneHandleBalancedCoreNeutralityCoordinateFactor p k hk
  have hf : Function.Surjective f :=
    oneHandleBalancedCoreNeutralityCoordinateFactor_surjective p k hk
  have hker : ∀ y ∈ f.ker, psi (Additive.ofMul y) = 1 := by
    intro y hy
    have hyrange : y ∈
        (oneHandleBalancedCoreNeutralityCoordinateRow p k hk).range := by
      rw [oneHandleBalancedCoreNeutralityCoordinateRow_range_eq_ker]
      exact hy
    obtain ⟨x, rfl⟩ := hyrange
    exact hrow x
  obtain ⟨chi, hchi⟩ := exists_quotient_addChar_of_detecting
    f hf psi hker z htarget
  refine ⟨chi, ?_⟩
  rwa [hz] at hchi

theorem targetCoefficientDetected_of_characterDetected
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk)
    (H : OneHandleBalancedCoreTargetCharacterDetected p hk hp hrel) :
    OneHandleBalancedCoreTargetCoefficientDetected p hk hp hrel := by
  rcases H with ⟨chi, hchi⟩
  obtain ⟨z, hz⟩ :=
    oneHandleBalancedCoreNeutralityCoordinateFactor_surjective p k hk
      (oneHandleBalancedCoreNeutralityObstruction p hk hp hrel)
  obtain ⟨a, b, hab⟩ := exists_eq_oneHandleZModFourPlaneCharacter
    (oneHandleBalancedCoreNeutralityCoordinatePullback p k hk chi)
  refine ⟨z, hz, a, b, ?_, ?_⟩
  · rw [← hab]
    change chi (Additive.ofMul
      (oneHandleBalancedCoreNeutralityCoordinateFactor p k hk z)) ≠ 1
    rwa [hz]
  · intro x
    rw [← hab]
    change chi (Additive.ofMul
      (oneHandleBalancedCoreNeutralityCoordinateFactor p k hk
        (oneHandleBalancedCoreNeutralityCoordinateRow p k hk x))) = 1
    have hx : oneHandleBalancedCoreNeutralityCoordinateFactor p k hk
        (oneHandleBalancedCoreNeutralityCoordinateRow p k hk x) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [← oneHandleBalancedCoreNeutralityCoordinateRow_range_eq_ker]
      exact ⟨x, rfl⟩
    rw [hx]
    exact AddChar.map_zero_eq_one chi

theorem targetCoefficientDetected_iff_characterDetected
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreTargetCoefficientDetected p hk hp hrel ↔
      OneHandleBalancedCoreTargetCharacterDetected p hk hp hrel :=
  ⟨targetCharacterDetected_of_coefficientDetected p hk hp hrel,
    targetCoefficientDetected_of_characterDetected p hk hp hrel⟩

theorem targetCoefficientDetected_iff_not_coordinateSpan
    {Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0)}
    (p : OneHandleBalancedPoint) {k : ℕ} (hk : 3 ≤ k)
    (hp : p ∈ oneHandleBalancedSet Psi0 k)
    (hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
      oneHandleBalancedCoreRelativeCoordinateSpan p k hk) :
    OneHandleBalancedCoreTargetCoefficientDetected p hk hp hrel ↔
      oneHandleBalancedCoreRelativeTarget p hp ∉
        oneHandleBalancedCoreCoordinateSpan p k hk := by
  rw [targetCoefficientDetected_iff_characterDetected,
    targetCharacterDetected_iff_not_coordinateSpan]

theorem oneHandleBalancedSet_succ_empty_iff_pointwise_coefficientObstruction
    (Psi0 : ContinuousMulEquiv (DM 2 0) (DM 2 0))
    (k : ℕ) (hk : 3 ≤ k) :
    ¬(oneHandleBalancedSet Psi0 (k + 1)).Nonempty ↔
      ∀ p : OneHandleBalancedPoint,
        ∀ hp : p ∈ oneHandleBalancedSet Psi0 k,
          oneHandleBalancedCoreRelativeTarget p hp ∉
              oneHandleBalancedCoreRelativeCoordinateSpan p k hk ∨
            ∃ hrel : oneHandleBalancedCoreRelativeTarget p hp ∈
              oneHandleBalancedCoreRelativeCoordinateSpan p k hk,
                OneHandleBalancedCoreTargetCoefficientDetected p hk hp hrel := by
  simpa only [targetCoefficientDetected_iff_characterDetected] using
    oneHandleBalancedSet_succ_empty_iff_pointwise_characterObstruction
      Psi0 k hk

#print axioms OneHandleZModFourPlane
#print axioms oneHandleZModFourPlaneCharacter
#print axioms oneHandleZModFourPlaneCharacter_apply
#print axioms exists_eq_oneHandleZModFourPlaneCharacter
#print axioms OneHandleBalancedCoreTargetCoefficientDetected
#print axioms targetCharacterDetected_of_coefficientDetected
#print axioms targetCoefficientDetected_of_characterDetected
#print axioms targetCoefficientDetected_iff_characterDetected
#print axioms targetCoefficientDetected_iff_not_coordinateSpan
#print axioms oneHandleBalancedSet_succ_empty_iff_pointwise_coefficientObstruction

end
end GQ2.Dyadic.Instances.MpcBalancedTargetCharacterCoordinates
