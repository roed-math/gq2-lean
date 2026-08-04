/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3CompletedFoxReduction
import GQ2.Dyadic.Certificates.L

/-!
# The augmentation initial row of the improved square relator

The degree-two Magnus initial form of the actual discrete relator
`sqDiscreteRelator h` is

`Y Y + S X + X S + ∑ j, (U_j V_j + V_j U_j)`.

This file records that calculation without assuming completed Fox injectivity or hiding
associated-graded regularity in a renamed premise.  The existing central-extension calculation
`Certificates.LSqStokes.sqRelWord_centLift_fib` computes the displayed degree-two form for an
arbitrary bilinear two-cocycle.  Taking its right Fox derivative gives the degree-one row

`d_S = X, d_X = S, d_Y = Y, d_{U_j} = V_j, d_{V_j} = U_j`.

Thus the *quadratic form's formal Fox row* is the permutation matrix of an explicit involution
on the alphabet.  In particular it contains every Magnus letter exactly once.  Two compatibility
steps are kept explicit: one must identify this formal derivative with the augmentation-linear
jet of `modTwoFoxDerivative`, and then identify the full associated graded of `F₂[[D_sq(h)]]`
with the quadratic one-relator algebra.  The latter PBW/Magnus identification must transfer the
permutation-row cancellation to every augmentation layer.  Neither statement is assumed here.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2.Dyadic GQ2.Dyadic.SqCore

/-! ## Core/handle coordinates and the partner involution -/

/-- Split the improved square alphabet into its three core letters and `h` ordered handle
pairs. -/
def sqInitialAlphabetEquiv (h : ℕ) :
    Fin (sqRank h) ≃ Fin 3 ⊕ (Fin h × Fin 2) :=
  (finCongr (by simp only [sqRank]; omega)).trans <|
    finSumFinEquiv.symm.trans <|
      (Equiv.refl (Fin 3)).sumCongr finProdFinEquiv.symm

@[simp] theorem sqInitialAlphabetEquiv_zero (h : ℕ) :
    sqInitialAlphabetEquiv h 0 = Sum.inl 0 := by
  rw [sqInitialAlphabetEquiv]
  rfl

@[simp] theorem sqInitialAlphabetEquiv_one (h : ℕ) :
    sqInitialAlphabetEquiv h 1 = Sum.inl 1 := by
  rw [sqInitialAlphabetEquiv]
  simp only [Equiv.trans_apply]
  have hc : (finCongr (show sqRank h = 3 + h * 2 by simp only [sqRank]; omega))
      (1 : Fin (sqRank h)) = Fin.castAdd (h * 2) (1 : Fin 3) := by
    apply Fin.ext
    change 1 % sqRank h = 1
    exact Nat.mod_eq_of_lt (by simp only [sqRank]; omega)
  rw [hc]
  rfl

@[simp] theorem sqInitialAlphabetEquiv_two (h : ℕ) :
    sqInitialAlphabetEquiv h 2 = Sum.inl 2 := by
  rw [sqInitialAlphabetEquiv]
  simp only [Equiv.trans_apply]
  have hc : (finCongr (show sqRank h = 3 + h * 2 by simp only [sqRank]; omega))
      (2 : Fin (sqRank h)) = Fin.castAdd (h * 2) (2 : Fin 3) := by
    apply Fin.ext
    change 2 % sqRank h = 2
    exact Nat.mod_eq_of_lt (by simp only [sqRank]; omega)
  rw [hc]
  rfl

@[simp] theorem sqInitialAlphabetEquiv_handleU {h : ℕ} (j : Fin h) :
    sqInitialAlphabetEquiv h (sqHandleIdxU j) = Sum.inr (j, 0) := by
  rw [sqInitialAlphabetEquiv]
  simp only [Equiv.trans_apply]
  have hc : (finCongr (show sqRank h = 3 + h * 2 by simp only [sqRank]; omega))
        (sqHandleIdxU j) = Fin.natAdd 3 (finProdFinEquiv (j, 0)) := by
    apply Fin.ext
    simp [finProdFinEquiv, sqHandleIdxU]
  rw [hc]
  simp

@[simp] theorem sqInitialAlphabetEquiv_handleV {h : ℕ} (j : Fin h) :
    sqInitialAlphabetEquiv h (sqHandleIdxV j) = Sum.inr (j, 1) := by
  rw [sqInitialAlphabetEquiv]
  simp only [Equiv.trans_apply]
  have hc : (finCongr (show sqRank h = 3 + h * 2 by simp only [sqRank]; omega))
        (sqHandleIdxV j) = Fin.natAdd 3 (finProdFinEquiv (j, 1)) := by
    apply Fin.ext
    simp [finProdFinEquiv, sqHandleIdxV]
    omega
  rw [hc]
  simp

/-- On core/handle coordinates, swap `S` with `X`, fix `Y`, and swap the two letters in
each handle pair. -/
def sqInitialCoordinatePartner (h : ℕ) :
    (Fin 3 ⊕ (Fin h × Fin 2)) ≃ (Fin 3 ⊕ (Fin h × Fin 2)) :=
  (Equiv.swap (0 : Fin 3) 1).sumCongr
    ((Equiv.refl (Fin h)).prodCongr (Equiv.swap (0 : Fin 2) 1))

/-- The partner permutation encoded by the quadratic initial relation. -/
def sqInitialPartner (h : ℕ) : Equiv.Perm (Fin (sqRank h)) :=
  (sqInitialAlphabetEquiv h).trans <|
    (sqInitialCoordinatePartner h).trans (sqInitialAlphabetEquiv h).symm

@[simp] theorem sqInitialPartner_zero (h : ℕ) : sqInitialPartner h 0 = 1 := by
  apply (sqInitialAlphabetEquiv h).injective
  simp [sqInitialPartner, sqInitialCoordinatePartner]

@[simp] theorem sqInitialPartner_one (h : ℕ) : sqInitialPartner h 1 = 0 := by
  apply (sqInitialAlphabetEquiv h).injective
  simp [sqInitialPartner, sqInitialCoordinatePartner]

@[simp] theorem sqInitialPartner_two (h : ℕ) : sqInitialPartner h 2 = 2 := by
  apply (sqInitialAlphabetEquiv h).injective
  simp only [sqInitialPartner, Equiv.trans_apply, sqInitialAlphabetEquiv_two,
    sqInitialCoordinatePartner, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.apply_symm_apply, Sum.inl.injEq]
  exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)

@[simp] theorem sqInitialPartner_handleU {h : ℕ} (j : Fin h) :
    sqInitialPartner h (sqHandleIdxU j) = sqHandleIdxV j := by
  apply (sqInitialAlphabetEquiv h).injective
  simp [sqInitialPartner, sqInitialCoordinatePartner]

@[simp] theorem sqInitialPartner_handleV {h : ℕ} (j : Fin h) :
    sqInitialPartner h (sqHandleIdxV j) = sqHandleIdxU j := by
  apply (sqInitialAlphabetEquiv h).injective
  simp [sqInitialPartner, sqInitialCoordinatePartner]

@[simp] theorem sqInitialPartner_involutive (h : ℕ) (i : Fin (sqRank h)) :
    sqInitialPartner h (sqInitialPartner h i) = i := by
  apply (sqInitialAlphabetEquiv h).injective
  rcases hi : sqInitialAlphabetEquiv h i with a | p
  · fin_cases a <;> simp [sqInitialPartner, sqInitialCoordinatePartner, hi]
  · rcases p with ⟨j, b⟩
    fin_cases b <;> simp [sqInitialPartner, sqInitialCoordinatePartner, hi]

/-! ## The actual degree-two relator form -/

/-- The degree-two Magnus coefficient of the improved relator.  A pair `(a,b)` has coefficient
one exactly when `b` is the partner of `a`; hence this is
`YY + SX + XS + Σ(UV+VU)`. -/
def sqRelatorQuadraticInitialCoefficient (h : ℕ)
    (a b : Fin (sqRank h)) : ZMod 2 :=
  if b = sqInitialPartner h a then 1 else 0

/-- Contraction of the degree-two initial form against an arbitrary matrix `κ`, displayed
in core/handle constructor coordinates. -/
def sqRelatorQuadraticInitialGram (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2) : ZMod 2 :=
  κ 2 2 + (κ 0 1 + κ 1 0) +
    ∑ j, (κ (sqHandleIdxU j) (sqHandleIdxV j) +
      κ (sqHandleIdxV j) (sqHandleIdxU j))

/-- Constructor table for the quadratic initial form. -/
theorem sqRelatorQuadraticInitialGram_eq (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2) :
    sqRelatorQuadraticInitialGram h κ =
      κ 2 2 + (κ 0 1 + κ 1 0) +
        ∑ j, (κ (sqHandleIdxU j) (sqHandleIdxV j) +
          κ (sqHandleIdxV j) (sqHandleIdxU j)) := by
  rfl

/-- The existing arbitrary-cocycle central-extension calculation is literally the displayed
quadratic Magnus initial form.  This is the link to the actual improved word, rather than an
independent declaration of a matrix with the desired shape. -/
theorem sqRelWord_centLift_fib_eq_quadraticInitialGram
    {L : Type*} [Group L] {c : GQ2.DRCoh.TwoCocycle L}
    (hc : GQ2.Dyadic.MarkedCore.IsCupCocycle c) (h : ℕ)
    (m : Fin (sqRank h) → L) :
    (sqRelWord (fun i => GQ2.Dyadic.MarkedCore.centLift c (m i))).fib =
      sqRelatorQuadraticInitialGram h (fun i j => c.κ (m i) (m j)) := by
  rw [sqRelatorQuadraticInitialGram]
  exact GQ2.Dyadic.Certificates.LSqStokes.sqRelWord_centLift_fib hc m

/-! ## The right Fox row of the quadratic initial form -/

/-- The coefficient of the Magnus letter `a` in the *formal right Fox derivative* of the
certified quadratic relation form with respect to generator `i`.  Fox differentiation on
augmentation monomials is the right skew derivative: `∂(AB)/∂i = A · ∂B/∂i`.

This definition is deliberately not named as a completed-row initial coefficient: the
Fox--Magnus compatibility identifying it with the first augmentation jet of
`modTwoFoxDerivative` has not yet been formalized. -/
def sqQuadraticFoxLinearInitialCoefficient (h : ℕ)
    (i a : Fin (sqRank h)) : ZMod 2 :=
  sqRelatorQuadraticInitialCoefficient h a i

theorem sqQuadraticFoxLinearInitialCoefficient_eq (h : ℕ)
    (i a : Fin (sqRank h)) :
    sqQuadraticFoxLinearInitialCoefficient h i a =
      if a = sqInitialPartner h i then 1 else 0 := by
  rw [sqQuadraticFoxLinearInitialCoefficient,
    sqRelatorQuadraticInitialCoefficient]
  simp only [show i = sqInitialPartner h a ↔ a = sqInitialPartner h i by
    constructor <;> intro e
    · have e' := congrArg (sqInitialPartner h) e
      simpa only [sqInitialPartner_involutive] using e'.symm
    · have e' := congrArg (sqInitialPartner h) e
      simpa only [sqInitialPartner_involutive] using e'.symm]

@[simp] theorem sqQuadraticFoxLinearInitial_zero (h : ℕ)
    (a : Fin (sqRank h)) :
    sqQuadraticFoxLinearInitialCoefficient h 0 a =
      if a = 1 then 1 else 0 := by
  rw [sqQuadraticFoxLinearInitialCoefficient_eq, sqInitialPartner_zero]

@[simp] theorem sqQuadraticFoxLinearInitial_one (h : ℕ)
    (a : Fin (sqRank h)) :
    sqQuadraticFoxLinearInitialCoefficient h 1 a =
      if a = 0 then 1 else 0 := by
  rw [sqQuadraticFoxLinearInitialCoefficient_eq, sqInitialPartner_one]

@[simp] theorem sqQuadraticFoxLinearInitial_two (h : ℕ)
    (a : Fin (sqRank h)) :
    sqQuadraticFoxLinearInitialCoefficient h 2 a =
      if a = 2 then 1 else 0 := by
  rw [sqQuadraticFoxLinearInitialCoefficient_eq, sqInitialPartner_two]

@[simp] theorem sqQuadraticFoxLinearInitial_handleU {h : ℕ}
    (j : Fin h) (a : Fin (sqRank h)) :
    sqQuadraticFoxLinearInitialCoefficient h (sqHandleIdxU j) a =
      if a = sqHandleIdxV j then 1 else 0 := by
  rw [sqQuadraticFoxLinearInitialCoefficient_eq, sqInitialPartner_handleU]

@[simp] theorem sqQuadraticFoxLinearInitial_handleV {h : ℕ}
    (j : Fin h) (a : Fin (sqRank h)) :
    sqQuadraticFoxLinearInitialCoefficient h (sqHandleIdxV j) a =
      if a = sqHandleIdxU j then 1 else 0 := by
  rw [sqQuadraticFoxLinearInitialCoefficient_eq, sqInitialPartner_handleV]

/-- Every formal degree-one Fox initial form is a single Magnus letter. -/
theorem sqQuadraticFoxLinearInitial_support (h : ℕ)
    (i a : Fin (sqRank h)) :
    sqQuadraticFoxLinearInitialCoefficient h i a = 1 ↔
      a = sqInitialPartner h i := by
  rw [sqQuadraticFoxLinearInitialCoefficient_eq]
  split <;> simp_all

/-- The linear initial row is a nonsingular permutation matrix. -/
theorem sqQuadraticFoxLinearInitial_nondegenerate (h : ℕ)
    (c : Fin (sqRank h) → ZMod 2)
    (hc : ∀ i, ∑ a, c a *
      sqQuadraticFoxLinearInitialCoefficient h i a = 0) :
    c = 0 := by
  funext a
  have ha := hc (sqInitialPartner h a)
  simp only [sqQuadraticFoxLinearInitialCoefficient_eq,
    sqInitialPartner_involutive] at ha
  simpa using ha

/-! ## The honest free-Magnus cancellation lemma -/

/-- The degree-one initial Fox row inside the free associative Magnus algebra. -/
def sqFreeMagnusLinearInitial (h : ℕ) (i : Fin (sqRank h)) :
    MonoidAlgebra (ZMod 2) (FreeMonoid (Fin (sqRank h))) :=
  MonoidAlgebra.single (FreeMonoid.of (sqInitialPartner h i)) 1

/-- The free-Magnus row represents exactly the formal coefficient table above. -/
theorem sqFreeMagnusLinearInitial_coefficient (h : ℕ)
    (i a : Fin (sqRank h)) :
    sqFreeMagnusLinearInitial h i (FreeMonoid.of a) =
      sqQuadraticFoxLinearInitialCoefficient h i a := by
  rw [sqFreeMagnusLinearInitial, sqQuadraticFoxLinearInitialCoefficient_eq]
  by_cases e : a = sqInitialPartner h i
  · subst a
    simp
  · rw [if_neg e]
    apply Finsupp.single_eq_of_ne
    intro heq
    apply e
    have hl := congrArg FreeMonoid.toList heq.symm
    simpa using hl.symm

/-- A Magnus letter is right-regular in the free associative algebra. -/
theorem freeMagnusLetter_rightRegular {I : Type} [DecidableEq I] (i : I) :
    Function.Injective (fun a : MonoidAlgebra (ZMod 2) (FreeMonoid I) =>
      a * MonoidAlgebra.single (FreeMonoid.of i) 1) := by
  intro a b hab
  exact mul_right_cancel₀ (by simp) hab

/-- **Free graded cancellation for the formal row of the actual quadratic relation.**  Before
imposing the quadratic relator, the formal row has zero common left annihilator: its `Y` entry
alone is right-regular.

The remaining PBW theorem must show that this cancellation survives in the quadratic quotient
which is the associated graded of the completed presented group algebra.  This theorem does not
assume that quotient identification. -/
theorem sqFreeMagnusLinearInitial_commonLeftAnnihilator (h : ℕ) :
    RowCommonLeftAnnihilatorFree (sqFreeMagnusLinearInitial h) := by
  intro a ha
  apply freeMagnusLetter_rightRegular (2 : Fin (sqRank h))
  change a * MonoidAlgebra.single (FreeMonoid.of (2 : Fin (sqRank h))) 1 =
    0 * MonoidAlgebra.single (FreeMonoid.of (2 : Fin (sqRank h))) 1
  rw [zero_mul]
  simpa [sqFreeMagnusLinearInitial] using ha (2 : Fin (sqRank h))

/-!
The exact next compatibility lemma is now unambiguous.  Let `I` be the augmentation ideal in
the free completed mod-two group algebra and identify `I/I²` with the span of the marked
letters.  For every `i`, the image of the actual
`sqCompletedModTwoFoxDerivativeRow h i` in `I/I²` must have coefficient function
`sqQuadraticFoxLinearInitialCoefficient h i`.  The arbitrary-cocycle theorem above proves the
corresponding degree-two statement for `sqDiscreteRelator`; a formal Fox--Magnus chain rule is
still needed to pass from that statement to the derivative row.  After that, a PBW/Diamond
theorem for the quadratic quotient must propagate this first-layer table through all layers.
-/

end

end GQ2.ContCoh
