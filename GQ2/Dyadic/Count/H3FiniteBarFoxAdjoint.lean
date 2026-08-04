/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3FiniteBarFoxChainHomotopy
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Finite coefficient adjoints of the low-degree bar--Fox homotopy

At a finite quotient, the full `F₂`-linear dual of a regular module
`F₂[Q]^(A) = (Q × A →₀ F₂)` is the function space `Q × A → F₂`.  This file
constructs that coefficient pairing and the full adjoint of a linear map between regular
modules.  It then transposes the already-proved degree-two forward--reverse homotopy identity.

The calculation also exposes a genuine degree issue.  The full adjoints of the bar boundaries
are the three- and four-term reduced coboundaries.  The inhomogeneous `d²` and `d³` used by the
continuous-cohomology interface have one additional leading term.  Thus the existing chain
identity through `B₂` supplies explicit fixed-level adjoints, but by itself it is not the desired
degree-three cochain reconstruction identity.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh GQ2.FoxH

variable {Q I rel : Type} [Group Q]

/-! ## The full coefficient pairing and adjoint -/

/-- Evaluate a coefficient function against a finitely supported vector. -/
def finiteFinsuppCoefficientEval {A : Type}
    (c : A → ZMod 2) : (A →₀ ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  Finsupp.linearCombination (ZMod 2) c

@[simp] theorem finiteFinsuppCoefficientEval_single {A : Type}
    (c : A → ZMod 2) (a : A) (x : ZMod 2) :
    finiteFinsuppCoefficientEval c (Finsupp.single a x) = x * c a := by
  simp [finiteFinsuppCoefficientEval, smul_eq_mul]

theorem finiteFinsuppCoefficientEval_add_function {A : Type}
    (c d : A → ZMod 2) (x : A →₀ ZMod 2) :
    finiteFinsuppCoefficientEval (c + d) x =
      finiteFinsuppCoefficientEval c x + finiteFinsuppCoefficientEval d x := by
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | single_add a z x ha hz ih =>
      simp only [map_add, finiteFinsuppCoefficientEval_single, Pi.add_apply, ih]
      rw [mul_add]
      abel

theorem finiteFinsuppCoefficientEval_smul_function {A : Type}
    (z : ZMod 2) (c : A → ZMod 2) (x : A →₀ ZMod 2) :
    finiteFinsuppCoefficientEval (z • c) x =
      z • finiteFinsuppCoefficientEval c x := by
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | single_add a b x ha hb ih =>
      simp only [map_add, finiteFinsuppCoefficientEval_single, Pi.smul_apply,
        ih, smul_eq_mul]
      ring

/-- The full coefficient adjoint of a linear map between finitely supported modules. -/
def finiteFinsuppFullAdjoint {A B : Type}
    (T : (A →₀ ZMod 2) →ₗ[ZMod 2] (B →₀ ZMod 2)) :
    (B → ZMod 2) →ₗ[ZMod 2] (A → ZMod 2) where
  toFun c a := finiteFinsuppCoefficientEval c (T (Finsupp.single a 1))
  map_add' c d := by
    funext a
    exact finiteFinsuppCoefficientEval_add_function c d _
  map_smul' x c := by
    funext a
    exact finiteFinsuppCoefficientEval_smul_function x c _

@[simp] theorem finiteFinsuppFullAdjoint_apply {A B : Type}
    (T : (A →₀ ZMod 2) →ₗ[ZMod 2] (B →₀ ZMod 2))
    (c : B → ZMod 2) (a : A) :
    finiteFinsuppFullAdjoint T c a =
      finiteFinsuppCoefficientEval c (T (Finsupp.single a 1)) :=
  rfl

/-- Evaluation against the adjoint equals evaluation after applying the original map. -/
theorem finiteFinsuppCoefficientEval_fullAdjoint {A B : Type}
    (T : (A →₀ ZMod 2) →ₗ[ZMod 2] (B →₀ ZMod 2))
    (c : B → ZMod 2) (x : A →₀ ZMod 2) :
    finiteFinsuppCoefficientEval (finiteFinsuppFullAdjoint T c) x =
      finiteFinsuppCoefficientEval c (T x) := by
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | single_add a z x ha hz ih =>
      simp only [map_add, ih, finiteFinsuppCoefficientEval_single,
        finiteFinsuppFullAdjoint_apply]
      have hsingle : Finsupp.single a z = z • Finsupp.single a (1 : ZMod 2) := by
        simp
      rw [hsingle, map_smul, map_smul, smul_eq_mul]

/-- Full adjoints reverse composition. -/
theorem finiteFinsuppFullAdjoint_comp {A B C : Type}
    (S : (B →₀ ZMod 2) →ₗ[ZMod 2] (C →₀ ZMod 2))
    (T : (A →₀ ZMod 2) →ₗ[ZMod 2] (B →₀ ZMod 2)) :
    finiteFinsuppFullAdjoint (S.comp T) =
      (finiteFinsuppFullAdjoint T).comp (finiteFinsuppFullAdjoint S) := by
  ext c a
  change finiteFinsuppCoefficientEval c (S (T (Finsupp.single a 1))) =
    finiteFinsuppCoefficientEval (finiteFinsuppFullAdjoint S c)
      (T (Finsupp.single a 1))
  exact (finiteFinsuppCoefficientEval_fullAdjoint S c _).symm

/-- Full adjoints preserve sums. -/
theorem finiteFinsuppFullAdjoint_add {A B : Type}
    (S T : (A →₀ ZMod 2) →ₗ[ZMod 2] (B →₀ ZMod 2)) :
    finiteFinsuppFullAdjoint (S + T) =
      finiteFinsuppFullAdjoint S + finiteFinsuppFullAdjoint T := by
  ext c a
  simp [finiteFinsuppFullAdjoint_apply]

/-- The full adjoint of the identity is the identity. -/
theorem finiteFinsuppFullAdjoint_id (A : Type) :
    finiteFinsuppFullAdjoint (LinearMap.id (R := ZMod 2) (M := A →₀ ZMod 2)) =
      LinearMap.id := by
  ext c a
  simp [finiteFinsuppFullAdjoint_apply]

/-! ## Full adjoints of the finite bar boundaries -/

/-- The full coefficient adjoint of `B₂ → B₁`. -/
def finiteModTwoBarFullCoboundaryTwo :
    FiniteModTwoBarCochainTwo Q →ₗ[ZMod 2] FiniteModTwoBarCochainThree Q :=
  finiteFinsuppFullAdjoint (finiteModTwoBarBoundaryTwo (Q := Q))

/-- The full coefficient adjoint of `B₃ → B₂`. -/
def finiteModTwoBarFullCoboundaryThree :
    FiniteModTwoBarCochainThree Q →ₗ[ZMod 2] FiniteModTwoBarCochainFour Q :=
  finiteFinsuppFullAdjoint (finiteModTwoBarBoundaryThree (Q := Q))

@[simp] theorem finiteModTwoBarFullCoboundaryTwo_apply
    (c : FiniteModTwoBarCochainTwo Q) (g q r : Q) :
    finiteModTwoBarFullCoboundaryTwo c (g, q, r) =
      c (g * q, r) + c (g, q * r) + c (g, q) := by
  classical
  simp [finiteModTwoBarFullCoboundaryTwo,
    finiteFinsuppFullAdjoint_apply, finiteModTwoBarBoundaryTwo_single]

@[simp] theorem finiteModTwoBarFullCoboundaryThree_apply
    (c : FiniteModTwoBarCochainThree Q) (g q r s : Q) :
    finiteModTwoBarFullCoboundaryThree c (g, q, r, s) =
      c (g * q, r, s) + c (g, q * r, s) +
        c (g, q, r * s) + c (g, q, r) := by
  classical
  simp [finiteModTwoBarFullCoboundaryThree,
    finiteFinsuppFullAdjoint_apply, finiteModTwoBarBoundaryThree_single]

/-- The usual inhomogeneous `d²` is the full boundary adjoint plus its leading term. -/
theorem finiteModTwoBarDTwo_eq_leading_add_full
    (c : FiniteModTwoBarCochainTwo Q) (g q r : Q) :
    finiteModTwoBarDTwo Q c (g, q, r) =
      c (q, r) + finiteModTwoBarFullCoboundaryTwo c (g, q, r) := by
  letI := trivialZModTwoAction Q
  simp [finiteModTwoBarDTwo, dTwo, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  rw [show g • c (q, r) = c (q, r) by rfl]
  abel

/-- The usual inhomogeneous `d³` is the full boundary adjoint plus its leading term. -/
theorem finiteModTwoBarDThree_eq_leading_add_full
    (c : FiniteModTwoBarCochainThree Q) (g q r s : Q) :
    finiteModTwoBarDThree Q c (g, q, r, s) =
      c (q, r, s) + finiteModTwoBarFullCoboundaryThree c (g, q, r, s) := by
  letI := trivialZModTwoAction Q
  simp [finiteModTwoBarDThree, dThree, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  rw [show g • c (q, r, s) = c (q, r, s) by rfl]
  abel

/-! ## Adjoints of the concrete forward--reverse homotopy -/

/-- Fixed-level cochain adjoint of the concrete degree-one chain homotopy. -/
def finiteBarForwardReverseHomotopyOneFullAdjoint
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarCochainThree Q →ₗ[ZMod 2] FiniteModTwoBarCochainTwo Q :=
  finiteFinsuppFullAdjoint (finiteBarForwardReverseHomotopyOne m heval)

/-- Fixed-level cochain adjoint of the concrete degree-two chain homotopy. -/
def finiteBarForwardReverseHomotopyTwoFullAdjoint
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarCochainFour Q →ₗ[ZMod 2] FiniteModTwoBarCochainThree Q :=
  finiteFinsuppFullAdjoint (finiteBarForwardReverseHomotopyTwo m heval)

/-- The full adjoint of the universal forward--reverse relation term. -/
def finiteUniversalForwardReverseFullAdjoint
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarCochainThree Q →ₗ[ZMod 2] FiniteModTwoBarCochainThree Q :=
  finiteFinsuppFullAdjoint
    ((finiteUniversalRelationToBarTwo m).comp
      (finiteBarToUniversalRelationTwo m heval))

/-- The explicit universal relation-error adjoint.  A finitely supported universal relation
coefficient is viewed as a coefficient functional before transposing the reverse map. -/
def finiteUniversalRelationErrorFullAdjoint
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    RegularModTwoRelationModule Q (FreeRelationKernel m) →ₗ[ZMod 2]
      FiniteModTwoBarCochainThree Q :=
  (finiteFinsuppFullAdjoint
    (finiteBarToUniversalRelationTwo m heval)).comp Finsupp.lcoeFun

/-- **Transposed fixed-level identity.** This is the exact full-coefficient adjoint of
`finiteBarForwardReverseHomotopyTwo_identity`. -/
theorem finiteBarForwardReverseHomotopyTwo_fullAdjoint_identity
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (c : FiniteModTwoBarCochainThree Q) :
    finiteModTwoBarFullCoboundaryTwo
        (finiteBarForwardReverseHomotopyOneFullAdjoint m heval c) +
      finiteUniversalForwardReverseFullAdjoint m heval c +
      finiteBarForwardReverseHomotopyTwoFullAdjoint m heval
        (finiteModTwoBarFullCoboundaryThree c) = c := by
  let H₁ := finiteBarForwardReverseHomotopyOne m heval
  let H₂ := finiteBarForwardReverseHomotopyTwo m heval
  let F₂ := finiteUniversalRelationToBarTwo m
  let R₂ := finiteBarToUniversalRelationTwo m heval
  have hchain :
      (finiteModTwoBarBoundaryThree (Q := Q)).comp H₂ +
          H₁.comp finiteModTwoBarBoundaryTwo + F₂.comp R₂ =
        LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact finiteBarForwardReverseHomotopyTwo_identity m heval x
  have hadjoint := congrArg finiteFinsuppFullAdjoint hchain
  rw [finiteFinsuppFullAdjoint_add, finiteFinsuppFullAdjoint_add,
    finiteFinsuppFullAdjoint_comp, finiteFinsuppFullAdjoint_comp,
    finiteFinsuppFullAdjoint_comp, finiteFinsuppFullAdjoint_id] at hadjoint
  simpa [finiteModTwoBarFullCoboundaryTwo,
    finiteBarForwardReverseHomotopyOneFullAdjoint,
    finiteUniversalForwardReverseFullAdjoint,
    finiteBarForwardReverseHomotopyTwoFullAdjoint,
    finiteModTwoBarFullCoboundaryThree, finiteFinsuppFullAdjoint_comp,
    add_assoc, add_comm, add_left_comm, H₁, H₂, F₂, R₂] using
      LinearMap.congr_fun hadjoint c

end

end GQ2.Dyadic.Count
