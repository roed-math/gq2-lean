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

/-- Coefficient evaluation only depends on values on the finite support of the vector. -/
theorem finiteFinsuppCoefficientEval_congr_on_support {A : Type}
    (c d : A → ZMod 2) (x : A →₀ ZMod 2)
    (h : ∀ a ∈ x.support, c a = d a) :
    finiteFinsuppCoefficientEval c x = finiteFinsuppCoefficientEval d x := by
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | single_add a z x ha hz ih =>
      simp only [map_add, finiteFinsuppCoefficientEval_single]
      have haSupport : a ∈ (Finsupp.single a z + x).support := by
        rw [Finsupp.mem_support_iff, Finsupp.add_apply,
          Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp ha, add_zero]
        exact hz
      rw [h a haSupport]
      congr 1
      apply ih
      intro b hb
      have hba : b ≠ a := by
        intro hba
        subst b
        exact ha hb
      apply h b
      rw [Finsupp.mem_support_iff, Finsupp.add_apply,
        Finsupp.single_eq_of_ne hba]
      simpa using Finsupp.mem_support_iff.mp hb

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

/-! ## Equivariant cochains inside full coefficient functions -/

/-- A trivial-coefficient cochain is the full coefficient function independent of the regular
group coordinate. -/
def finiteRegularInvariantCoe (A : Type) :
    (A → ZMod 2) →ₗ[ZMod 2] (Q × A → ZMod 2) where
  toFun c p := c p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Read a full coefficient function on the regular basis at group coordinate `1`. -/
def finiteRegularAtOne (A : Type) :
    (Q × A → ZMod 2) →ₗ[ZMod 2] (A → ZMod 2) where
  toFun C a := C (1, a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem finiteRegularAtOne_invariantCoe (A : Type) :
    (finiteRegularAtOne (Q := Q) A).comp (finiteRegularInvariantCoe (Q := Q) A) =
      LinearMap.id := by
  rfl

/-- The full adjoint of `B₃ → B₂` preserves invariant coefficient functions and restricts
to the actual inhomogeneous `d²`. -/
theorem finiteModTwoBarFullCoboundaryThree_invariant
    (c : FiniteModTwoBarCochainTwo Q) :
    finiteModTwoBarFullCoboundaryThree
        (finiteRegularInvariantCoe (Q := Q) (Q × Q) c) =
      finiteRegularInvariantCoe (Q := Q) (Q × Q × Q)
        (finiteModTwoBarDTwo Q c) := by
  letI := trivialZModTwoAction Q
  funext p
  rcases p with ⟨g, q, r, s⟩
  simp [finiteRegularInvariantCoe, finiteModTwoBarDTwo, dTwo,
    sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  rw [show q • c (r, s) = c (r, s) by rfl]

/-! ## Bar degree four and recovery of `d³` -/

/-- Degree four of the finite mod-two inhomogeneous bar resolution. -/
abbrev FiniteModTwoBarChainFour (Q : Type) :=
  RegularModTwoRelationModule Q (Q × Q × Q × Q)

/-- The bar boundary `B₄ → B₃` in characteristic two. -/
def finiteModTwoBarBoundaryFour :
    FiniteModTwoBarChainFour Q →ₗ[ZMod 2] FiniteModTwoBarChainThree Q :=
  (Finsupp.lsum (ZMod 2)) fun p : Q × (Q × Q × Q × Q) ↦
    LinearMap.toSpanSingleton (ZMod 2) _
      (Finsupp.single (p.1 * p.2.1, (p.2.2.1, p.2.2.2.1, p.2.2.2.2)) 1 +
        Finsupp.single (p.1, (p.2.1 * p.2.2.1, p.2.2.2.1, p.2.2.2.2)) 1 +
        Finsupp.single (p.1, (p.2.1, p.2.2.1 * p.2.2.2.1, p.2.2.2.2)) 1 +
        Finsupp.single (p.1, (p.2.1, p.2.2.1, p.2.2.2.1 * p.2.2.2.2)) 1 +
        Finsupp.single (p.1, (p.2.1, p.2.2.1, p.2.2.2.1)) 1)

@[simp] theorem finiteModTwoBarBoundaryFour_single
    (g q r s t : Q) (a : ZMod 2) :
    finiteModTwoBarBoundaryFour (Finsupp.single (g, (q, r, s, t)) a) =
      Finsupp.single (g * q, (r, s, t)) a +
        Finsupp.single (g, (q * r, s, t)) a +
        Finsupp.single (g, (q, r * s, t)) a +
        Finsupp.single (g, (q, r, s * t)) a +
        Finsupp.single (g, (q, r, s)) a := by
  classical
  rw [finiteModTwoBarBoundaryFour, Finsupp.lsum_single]
  simp [LinearMap.toSpanSingleton_apply, smul_add, smul_eq_mul]

/-- The full coefficient adjoint of `B₄ → B₃`. -/
def finiteModTwoBarFullCoboundaryFour :
    FiniteModTwoBarCochainFour Q →ₗ[ZMod 2]
      (Q × Q × Q × Q × Q → ZMod 2) :=
  finiteFinsuppFullAdjoint (finiteModTwoBarBoundaryFour (Q := Q))

/-- Restricting the full `B₄` adjoint to invariant coefficients is exactly inhomogeneous
`d³`, including its leading term. -/
theorem finiteModTwoBarFullCoboundaryFour_invariant
    (c : FiniteModTwoBarCochainThree Q) :
    finiteModTwoBarFullCoboundaryFour
        (finiteRegularInvariantCoe (Q := Q) (Q × Q × Q) c) =
      finiteRegularInvariantCoe (Q := Q) (Q × Q × Q × Q)
        (finiteModTwoBarDThree Q c) := by
  letI := trivialZModTwoAction Q
  funext p
  rcases p with ⟨g, q, r, s, t⟩
  classical
  simp [finiteModTwoBarFullCoboundaryFour,
    finiteFinsuppFullAdjoint_apply, finiteRegularInvariantCoe,
    finiteModTwoBarBoundaryFour_single, finiteModTwoBarDThree, dThree,
    sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  rw [show q • c (r, s, t) = c (r, s, t) by rfl]

/-! ## The canonical contraction in bar degree three -/

/-- Insert a bar three-cell `g[q|r|s]` as the bar four-cell `[g|q|r|s]`. -/
def finiteModTwoBarContractThree :
    FiniteModTwoBarChainThree Q →ₗ[ZMod 2] FiniteModTwoBarChainFour Q :=
  (Finsupp.lsum (ZMod 2)) fun p : Q × (Q × Q × Q) =>
    LinearMap.toSpanSingleton (ZMod 2) _
      (Finsupp.single (1, (p.1, p.2.1, p.2.2.1, p.2.2.2)) 1)

@[simp] theorem finiteModTwoBarContractThree_single
    (g q r s : Q) (a : ZMod 2) :
    finiteModTwoBarContractThree (Finsupp.single (g, (q, r, s)) a) =
      Finsupp.single (1, (g, q, r, s)) a := by
  classical
  rw [finiteModTwoBarContractThree, Finsupp.lsum_single]
  simp [LinearMap.toSpanSingleton_apply, smul_eq_mul]

/-- The all-chain contraction identity `∂₄s₃ + s₂∂₃ = id` on bar degree three. -/
theorem finiteModTwoBar_contracting_identity_three
    (c : FiniteModTwoBarChainThree Q) :
    finiteModTwoBarBoundaryFour (finiteModTwoBarContractThree c) +
        finiteModTwoBarContractTwo (finiteModTwoBarBoundaryThree c) = c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, q, r, s⟩
      simp only [map_add, finiteModTwoBarContractThree_single,
        finiteModTwoBarBoundaryFour_single,
        finiteModTwoBarBoundaryThree_single,
        finiteModTwoBarContractTwo_single, one_mul]
      let A : FiniteModTwoBarChainThree Q := Finsupp.single (1, (g * q, r, s)) a
      let B : FiniteModTwoBarChainThree Q := Finsupp.single (1, (g, q * r, s)) a
      let C : FiniteModTwoBarChainThree Q := Finsupp.single (1, (g, q, r * s)) a
      let D : FiniteModTwoBarChainThree Q := Finsupp.single (1, (g, q, r)) a
      let S : FiniteModTwoBarChainThree Q := Finsupp.single (g, (q, r, s)) a
      let T : FiniteModTwoBarChainThree Q :=
        finiteModTwoBarBoundaryFour (finiteModTwoBarContractThree c)
      let U : FiniteModTwoBarChainThree Q :=
        finiteModTwoBarContractTwo (finiteModTwoBarBoundaryThree c)
      change S + A + B + C + D + T + (A + B + C + D + U) = S + c
      calc
        S + A + B + C + D + T + (A + B + C + D + U) =
            S + (T + U) + (A + A) + (B + B) + (C + C) + (D + D) := by
              abel
        _ = S + (T + U) := by
          rw [regularModTwoRelationModule_add_self,
            regularModTwoRelationModule_add_self,
            regularModTwoRelationModule_add_self,
            regularModTwoRelationModule_add_self]
          simp
        _ = S + c := by rw [ih]

/-! ## What the proved `B₂` identity gives on actual cochains -/

/-- The actual cochain adjoint `C³ → C²` of the proved chain homotopy `H₂ : B₂ → B₃`. -/
def finiteBarForwardReverseHomotopyTwoCochainAdjoint
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarCochainThree Q →ₗ[ZMod 2] FiniteModTwoBarCochainTwo Q :=
  (finiteRegularAtOne (Q := Q) (Q × Q)).comp
    ((finiteFinsuppFullAdjoint
      (finiteBarForwardReverseHomotopyTwo m heval)).comp
        (finiteRegularInvariantCoe (Q := Q) (Q × Q × Q)))

/-- The remaining `H₁ ∂₂` term in the restricted `C²` identity. -/
def finiteBarHomotopyOneBoundaryCochainCorrection
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarCochainTwo Q →ₗ[ZMod 2] FiniteModTwoBarCochainTwo Q :=
  (finiteRegularAtOne (Q := Q) (Q × Q)).comp
    ((finiteFinsuppFullAdjoint finiteModTwoBarBoundaryTwo).comp
      ((finiteFinsuppFullAdjoint
        (finiteBarForwardReverseHomotopyOne m heval)).comp
          (finiteRegularInvariantCoe (Q := Q) (Q × Q))))

/-- The universal forward--reverse term restricted to actual two-cochains. -/
def finiteUniversalForwardReverseCochainCorrection
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarCochainTwo Q →ₗ[ZMod 2] FiniteModTwoBarCochainTwo Q :=
  (finiteRegularAtOne (Q := Q) (Q × Q)).comp
    ((finiteUniversalForwardReverseFullAdjoint m heval).comp
      (finiteRegularInvariantCoe (Q := Q) (Q × Q)))

/-- **Exact restricted consequence of the existing chain homotopy.**  The identity on `B₂`
gives a reconstruction of actual degree-two cochains.  Its first term uses the concrete
`C³ → C²` adjoint on `d² c`; it does not give a reconstruction of degree-three cochains. -/
theorem finiteBarForwardReverseHomotopyTwo_cochainTwo_identity
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (c : FiniteModTwoBarCochainTwo Q) :
    finiteBarHomotopyOneBoundaryCochainCorrection m heval c +
      finiteUniversalForwardReverseCochainCorrection m heval c +
      finiteBarForwardReverseHomotopyTwoCochainAdjoint m heval
        (finiteModTwoBarDTwo Q c) = c := by
  have hfull := finiteBarForwardReverseHomotopyTwo_fullAdjoint_identity
    m heval (finiteRegularInvariantCoe (Q := Q) (Q × Q) c)
  have hatOne := congrArg
    (finiteRegularAtOne (Q := Q) (Q × Q)) hfull
  rw [finiteModTwoBarFullCoboundaryThree_invariant] at hatOne
  funext a
  have ha := congrFun hatOne a
  simpa [finiteBarHomotopyOneBoundaryCochainCorrection,
    finiteUniversalForwardReverseCochainCorrection,
    finiteBarForwardReverseHomotopyTwoCochainAdjoint,
    finiteBarForwardReverseHomotopyOneFullAdjoint,
    finiteBarForwardReverseHomotopyTwoFullAdjoint,
    finiteModTwoBarFullCoboundaryTwo,
    finiteFinsuppFullAdjoint_apply,
    finiteRegularAtOne, finiteRegularInvariantCoe] using ha

/-! ## The explicit chain comparison in degree three -/

/-- The degree-three reverse comparison is the already constructed reverse degree-two map
applied to the bar boundary. -/
def finiteBarToUniversalRelationThree
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarChainThree Q →ₗ[ZMod 2]
      RegularModTwoRelationModule Q (FreeRelationKernel m) :=
  (finiteBarToUniversalRelationTwo m heval).comp finiteModTwoBarBoundaryThree

/-- The degree-three forward comparison contracts the existing universal relation-to-bar
two-chain. -/
def finiteUniversalRelationToBarThree (m : I → Q) :
    RegularModTwoRelationModule Q (FreeRelationKernel m) →ₗ[ZMod 2]
      FiniteModTwoBarChainThree Q :=
  (finiteModTwoBarContractTwo (Q := Q)).comp
    (finiteUniversalRelationToBarTwo m)

/-- On the image of the degree-three reverse map, the contracted universal comparison has
boundary equal to the original universal bar two-chain. -/
theorem finiteUniversalRelationToBarThree_boundary
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (x : FiniteModTwoBarChainThree Q) :
    finiteModTwoBarBoundaryThree
        (finiteUniversalRelationToBarThree m
          (finiteBarToUniversalRelationThree m heval x)) =
      finiteUniversalRelationToBarTwo m
        (finiteBarToUniversalRelationThree m heval x) := by
  have hboundary :
      finiteModTwoBarBoundaryTwo (finiteModTwoBarBoundaryThree x) = 0 := by
    have h := LinearMap.congr_fun
      (finiteModTwoBarBoundaryTwo_comp_boundaryThree (Q := Q)) x
    simpa using h
  have hfox :
      (finiteUniversalRelationFoxBoundary m).map
          (finiteBarToUniversalRelationThree m heval x) = 0 := by
    rw [finiteBarToUniversalRelationThree, LinearMap.comp_apply,
      ← finiteBarToMarkedOne_boundaryTwo, hboundary, map_zero]
  have huniversalBoundary :
      finiteModTwoBarBoundaryTwo
          (finiteUniversalRelationToBarTwo m
            (finiteBarToUniversalRelationThree m heval x)) = 0 := by
    rw [finiteUniversalRelationToBarTwo_boundary, hfox, map_zero]
  have hcontract := finiteModTwoBar_contracting_identity_two
    (Q := Q)
    (finiteUniversalRelationToBarTwo m
      (finiteBarToUniversalRelationThree m heval x))
  rw [huniversalBoundary, map_zero, add_zero] at hcontract
  simpa [finiteUniversalRelationToBarThree] using hcontract

/-- The degree-three error before applying the canonical bar contraction. -/
def finiteBarForwardReverseDifferenceThree
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarChainThree Q →ₗ[ZMod 2] FiniteModTwoBarChainThree Q :=
  (finiteBarForwardReverseHomotopyTwo m heval).comp finiteModTwoBarBoundaryThree +
    (finiteUniversalRelationToBarThree m).comp
      (finiteBarToUniversalRelationThree m heval) +
    LinearMap.id

/-- The degree-three forward--reverse error is a bar cycle. -/
theorem finiteBarForwardReverseDifferenceThree_boundary
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (x : FiniteModTwoBarChainThree Q) :
    finiteModTwoBarBoundaryThree
        (finiteBarForwardReverseDifferenceThree m heval x) = 0 := by
  have hboundary :
      finiteModTwoBarBoundaryTwo (finiteModTwoBarBoundaryThree x) = 0 := by
    have h := LinearMap.congr_fun
      (finiteModTwoBarBoundaryTwo_comp_boundaryThree (Q := Q)) x
    simpa using h
  have htwo := finiteBarForwardReverseHomotopyTwo_identity
    m heval (finiteModTwoBarBoundaryThree x)
  rw [hboundary, map_zero, add_zero] at htwo
  simp only [finiteBarForwardReverseDifferenceThree, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.id_apply, map_add,
    finiteUniversalRelationToBarThree_boundary]
  let A : FiniteModTwoBarChainTwo Q :=
    finiteModTwoBarBoundaryThree
      (finiteBarForwardReverseHomotopyTwo m heval
        (finiteModTwoBarBoundaryThree x))
  let B : FiniteModTwoBarChainTwo Q :=
    finiteUniversalRelationToBarTwo m
      (finiteBarToUniversalRelationThree m heval x)
  let C : FiniteModTwoBarChainTwo Q := finiteModTwoBarBoundaryThree x
  change A + B + C = 0
  have hAB : A + B = C := by simpa [A, B, C, finiteBarToUniversalRelationThree] using htwo
  rw [hAB]
  exact regularModTwoRelationModule_add_self Q (Q × Q) C

/-- Fill the degree-three error by the canonical bar contraction. -/
def finiteBarForwardReverseHomotopyThree
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarChainThree Q →ₗ[ZMod 2] FiniteModTwoBarChainFour Q :=
  (finiteModTwoBarContractThree (Q := Q)).comp
    (finiteBarForwardReverseDifferenceThree m heval)

/-- **Concrete degree-three chain-homotopy identity.** The universal-Fox comparison is
chain-homotopic to the identity on every bar three-chain. -/
theorem finiteBarForwardReverseHomotopyThree_identity
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (x : FiniteModTwoBarChainThree Q) :
    finiteModTwoBarBoundaryFour
        (finiteBarForwardReverseHomotopyThree m heval x) +
      finiteBarForwardReverseHomotopyTwo m heval
        (finiteModTwoBarBoundaryThree x) +
      finiteUniversalRelationToBarThree m
        (finiteBarToUniversalRelationThree m heval x) = x := by
  have hcontract := finiteModTwoBar_contracting_identity_three
    (Q := Q) (finiteBarForwardReverseDifferenceThree m heval x)
  rw [finiteBarForwardReverseDifferenceThree_boundary m heval x,
    map_zero, add_zero] at hcontract
  change finiteModTwoBarBoundaryFour
      (finiteModTwoBarContractThree
        (finiteBarForwardReverseDifferenceThree m heval x)) + _ + _ = x
  rw [hcontract]
  simp only [finiteBarForwardReverseDifferenceThree, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.id_apply]
  let A : FiniteModTwoBarChainThree Q :=
    finiteBarForwardReverseHomotopyTwo m heval
      (finiteModTwoBarBoundaryThree x)
  let B : FiniteModTwoBarChainThree Q :=
    finiteUniversalRelationToBarThree m
      (finiteBarToUniversalRelationThree m heval x)
  change A + B + x + A + B = x
  calc
    A + B + x + A + B = x + (A + A) + (B + B) := by abel
    _ = x := by
      rw [regularModTwoRelationModule_add_self,
        regularModTwoRelationModule_add_self]
      simp

/-- A one-degree-higher chain comparison is the fixed-quotient datum whose invariant full
adjoint yields a degree-three full-coefficient reconstruction. -/
structure FiniteUniversalBarFoxChainHomotopyThree
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) where
  /-- The new bar homotopy `B₃ → B₄`. -/
  homotopyThree :
    FiniteModTwoBarChainThree Q →ₗ[ZMod 2] FiniteModTwoBarChainFour Q
  /-- The degree-three comparison term may factor through a finite-support universal relation
  module; this is its bar-to-relation half. -/
  barToUniversalThree :
    FiniteModTwoBarChainThree Q →ₗ[ZMod 2]
      RegularModTwoRelationModule Q (FreeRelationKernel m)
  /-- The relation-to-bar half of the degree-three comparison term. -/
  universalToBarThree :
    RegularModTwoRelationModule Q (FreeRelationKernel m) →ₗ[ZMod 2]
      FiniteModTwoBarChainThree Q
  /-- The chain homotopy identity one degree above the theorem already proved. -/
  homotopyThree_identity : ∀ x,
    finiteModTwoBarBoundaryFour (homotopyThree x) +
        finiteBarForwardReverseHomotopyTwo m heval
          (finiteModTwoBarBoundaryThree x) +
        universalToBarThree (barToUniversalThree x) = x

/-- The explicit degree-three chain comparison assembled from the degree-two comparison and
the canonical bar contractions. -/
def finiteUniversalBarFoxChainHomotopyThree
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteUniversalBarFoxChainHomotopyThree m heval where
  homotopyThree := finiteBarForwardReverseHomotopyThree m heval
  barToUniversalThree := finiteBarToUniversalRelationThree m heval
  universalToBarThree := finiteUniversalRelationToBarThree m
  homotopyThree_identity := finiteBarForwardReverseHomotopyThree_identity m heval

/-! ## Full adjoint and fixed-level degree-three identities -/

/-- The full coefficient adjoint of the explicit degree-three bar homotopy. -/
def finiteBarForwardReverseHomotopyThreeFullAdjoint
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    (Q × Q × Q × Q × Q → ZMod 2) →ₗ[ZMod 2]
      FiniteModTwoBarCochainFour Q :=
  finiteFinsuppFullAdjoint (finiteBarForwardReverseHomotopyThree m heval)

/-- The full coefficient adjoint of the degree-three universal comparison term. -/
def finiteUniversalForwardReverseThreeFullAdjoint
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarCochainFour Q →ₗ[ZMod 2]
      FiniteModTwoBarCochainFour Q :=
  finiteFinsuppFullAdjoint
    ((finiteUniversalRelationToBarThree m).comp
      (finiteBarToUniversalRelationThree m heval))

/-- **Raw transposed degree-three identity.** This is the exact full-coefficient adjoint of
`finiteBarForwardReverseHomotopyThree_identity`, before imposing invariance or finite support. -/
theorem finiteBarForwardReverseHomotopyThree_fullAdjoint_identity
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (c : FiniteModTwoBarCochainFour Q) :
    finiteBarForwardReverseHomotopyThreeFullAdjoint m heval
        (finiteModTwoBarFullCoboundaryFour c) +
      finiteModTwoBarFullCoboundaryThree
        (finiteBarForwardReverseHomotopyTwoFullAdjoint m heval c) +
      finiteUniversalForwardReverseThreeFullAdjoint m heval c = c := by
  let H₂ := finiteBarForwardReverseHomotopyTwo m heval
  let H₃ := finiteBarForwardReverseHomotopyThree m heval
  let U₃ := finiteUniversalRelationToBarThree m
  let R₃ := finiteBarToUniversalRelationThree m heval
  have hchain :
      (finiteModTwoBarBoundaryFour (Q := Q)).comp H₃ +
          H₂.comp finiteModTwoBarBoundaryThree + U₃.comp R₃ =
        LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact finiteBarForwardReverseHomotopyThree_identity m heval x
  have hadjoint := congrArg finiteFinsuppFullAdjoint hchain
  rw [finiteFinsuppFullAdjoint_add, finiteFinsuppFullAdjoint_add,
    finiteFinsuppFullAdjoint_comp, finiteFinsuppFullAdjoint_comp,
    finiteFinsuppFullAdjoint_comp, finiteFinsuppFullAdjoint_id] at hadjoint
  simpa [finiteBarForwardReverseHomotopyThreeFullAdjoint,
    finiteUniversalForwardReverseThreeFullAdjoint,
    finiteBarForwardReverseHomotopyTwoFullAdjoint,
    finiteModTwoBarFullCoboundaryThree,
    finiteModTwoBarFullCoboundaryFour, finiteFinsuppFullAdjoint_comp,
    H₂, H₃, U₃, R₃] using LinearMap.congr_fun hadjoint c

/-- The actual-cochain adjoint of `H₃ : B₃ → B₄`. -/
def finiteBarForwardReverseHomotopyThreeCochainAdjoint
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarCochainFour Q →ₗ[ZMod 2]
      FiniteModTwoBarCochainThree Q :=
  (finiteRegularAtOne (Q := Q) (Q × Q × Q)).comp
    ((finiteBarForwardReverseHomotopyThreeFullAdjoint m heval).comp
      (finiteRegularInvariantCoe (Q := Q) (Q × Q × Q × Q)))

/-- The raw restricted adjoint of the `H₂∂₃` term.  This is kept distinct from
`d²(H₂†c)`, because the canonical contraction defining `H₂` is not equivariant. -/
def finiteBarHomotopyTwoBoundaryRawCochainCorrection
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarCochainThree Q →ₗ[ZMod 2]
      FiniteModTwoBarCochainThree Q :=
  (finiteRegularAtOne (Q := Q) (Q × Q × Q)).comp
    ((finiteModTwoBarFullCoboundaryThree (Q := Q)).comp
      ((finiteBarForwardReverseHomotopyTwoFullAdjoint m heval).comp
        (finiteRegularInvariantCoe (Q := Q) (Q × Q × Q))))

/-- The explicit failure of the full adjoint of `H₂` to turn the boundary adjoint into the
ordinary inhomogeneous `d²` after restriction to invariant coefficients. -/
def finiteBarHomotopyTwoAdjointBarDefect
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarCochainThree Q →+
      FiniteModTwoBarCochainThree Q :=
  (finiteBarHomotopyTwoBoundaryRawCochainCorrection m heval).toAddMonoidHom +
    (finiteModTwoBarDTwo Q).comp
      (finiteBarForwardReverseHomotopyTwoCochainAdjoint m heval).toAddMonoidHom

/-- The unrestricted universal degree-three correction on actual three-cochains. -/
def finiteUniversalForwardReverseThreeCochainCorrection
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    FiniteModTwoBarCochainThree Q →ₗ[ZMod 2]
      FiniteModTwoBarCochainThree Q :=
  (finiteRegularAtOne (Q := Q) (Q × Q × Q)).comp
    ((finiteUniversalForwardReverseThreeFullAdjoint m heval).comp
      (finiteRegularInvariantCoe (Q := Q) (Q × Q × Q)))

/-- A finitely supported universal relation coefficient can be transposed through the
bar-to-universal degree-three map and then restricted to an actual three-cochain. -/
def finiteUniversalRelationThreeFiniteSupportCorrection
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m)) :
    RegularModTwoRelationModule Q (FreeRelationKernel m) →ₗ[ZMod 2]
      FiniteModTwoBarCochainThree Q :=
  (finiteRegularAtOne (Q := Q) (Q × Q × Q)).comp
    ((finiteFinsuppFullAdjoint
      (finiteBarToUniversalRelationThree m heval)).comp Finsupp.lcoeFun)

/-- A witness that the adjoint of the universal-to-bar map has finite support. -/
def FiniteUniversalToBarThreeAdjointSupportWitness
    (m : I → Q) (c : FiniteModTwoBarCochainThree Q)
    (u : RegularModTwoRelationModule Q (FreeRelationKernel m)) : Prop :=
  finiteFinsuppFullAdjoint (finiteUniversalRelationToBarThree m)
      (finiteRegularInvariantCoe (Q := Q) (Q × Q × Q) c) =
    (Finsupp.lcoeFun :
      RegularModTwoRelationModule Q (FreeRelationKernel m) →ₗ[ZMod 2]
        (Q × FreeRelationKernel m → ZMod 2)) u

/-- Existence of a finitely supported universal adjoint coefficient is exactly finite support
of the unrestricted coefficient function.  Finiteness of `Q` alone does not discharge the
right-hand side, since the universal relation alphabet `FreeRelationKernel m` need not be
finite. -/
theorem exists_finiteUniversalToBarThreeAdjointSupportWitness_iff
    (m : I → Q) (c : FiniteModTwoBarCochainThree Q) :
    (∃ u : RegularModTwoRelationModule Q (FreeRelationKernel m),
        FiniteUniversalToBarThreeAdjointSupportWitness m c u) ↔
      (finiteFinsuppFullAdjoint (finiteUniversalRelationToBarThree m)
        (finiteRegularInvariantCoe (Q := Q) (Q × Q × Q) c)).HasFiniteSupport := by
  let f := finiteFinsuppFullAdjoint (finiteUniversalRelationToBarThree m)
    (finiteRegularInvariantCoe (Q := Q) (Q × Q × Q) c)
  constructor
  · rintro ⟨u, hu⟩
    unfold FiniteUniversalToBarThreeAdjointSupportWitness at hu
    rw [hu]
    exact u.hasFiniteSupport
  · intro hf
    let u : RegularModTwoRelationModule Q (FreeRelationKernel m) :=
      Finsupp.mk hf.toFinset f fun _a => Set.Finite.mem_toFinset _
    refine ⟨u, ?_⟩
    unfold FiniteUniversalToBarThreeAdjointSupportWitness
    rfl

/-- When the full universal relation index is finite, the unrestricted adjoint has a canonical
finitely supported representative.  At the intended finite quotients the extra finiteness of
`FreeRelationKernel m`, not finiteness of `Q`, is the substantive hypothesis. -/
def finiteUniversalToBarThreeAdjointFiniteSupportCoefficient
    (m : I → Q) [Finite Q] [Finite (FreeRelationKernel m)]
    (c : FiniteModTwoBarCochainThree Q) :
    RegularModTwoRelationModule Q (FreeRelationKernel m) :=
  Finsupp.equivFunOnFinite.symm
    (finiteFinsuppFullAdjoint (finiteUniversalRelationToBarThree m)
      (finiteRegularInvariantCoe (Q := Q) (Q × Q × Q) c))

/-- The canonical coefficient on a finite universal relation index is a support witness. -/
theorem finiteUniversalToBarThreeAdjointSupportWitness_of_finite
    (m : I → Q) [Finite Q] [Finite (FreeRelationKernel m)]
    (c : FiniteModTwoBarCochainThree Q) :
    FiniteUniversalToBarThreeAdjointSupportWitness m c
      (finiteUniversalToBarThreeAdjointFiniteSupportCoefficient m c) := by
  unfold FiniteUniversalToBarThreeAdjointSupportWitness
  rw [finiteUniversalToBarThreeAdjointFiniteSupportCoefficient]
  exact (Finsupp.coe_equivFunOnFinite_symm _).symm

/-- The separate finite-support defect of the universal adjoint, relative to a proposed
finitely supported universal relation coefficient. -/
def finiteUniversalThreeAdjointFiniteSupportDefect
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (c : FiniteModTwoBarCochainThree Q)
    (u : RegularModTwoRelationModule Q (FreeRelationKernel m)) :
    FiniteModTwoBarCochainThree Q :=
  finiteUniversalForwardReverseThreeCochainCorrection m heval c +
    finiteUniversalRelationThreeFiniteSupportCorrection m heval u

/-- A genuine support witness makes the universal finite-support defect vanish. -/
theorem finiteUniversalThreeAdjointFiniteSupportDefect_eq_zero
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (c : FiniteModTwoBarCochainThree Q)
    (u : RegularModTwoRelationModule Q (FreeRelationKernel m))
    (hu : FiniteUniversalToBarThreeAdjointSupportWitness m c u) :
    finiteUniversalThreeAdjointFiniteSupportDefect m heval c u = 0 := by
  funext a
  have hcombined := finiteFinsuppFullAdjoint_comp
    (finiteUniversalRelationToBarThree m)
    (finiteBarToUniversalRelationThree m heval)
  simp only [finiteUniversalThreeAdjointFiniteSupportDefect,
    finiteUniversalForwardReverseThreeCochainCorrection,
    finiteUniversalForwardReverseThreeFullAdjoint,
    finiteUniversalRelationThreeFiniteSupportCorrection,
    LinearMap.comp_apply, finiteRegularAtOne]
  rw [hcombined]
  change
    finiteFinsuppFullAdjoint (finiteBarToUniversalRelationThree m heval)
          (finiteFinsuppFullAdjoint (finiteUniversalRelationToBarThree m)
            (finiteRegularInvariantCoe (Q := Q) (Q × Q × Q) c)) (1, a) +
        finiteFinsuppFullAdjoint (finiteBarToUniversalRelationThree m heval)
          (Finsupp.lcoeFun u) (1, a) = 0
  unfold FiniteUniversalToBarThreeAdjointSupportWitness at hu
  rw [hu]
  exact ZModModule.add_self _

/-- At a finite quotient, the universal adjoint can always be truncated to a finitely supported
coefficient without changing its image under `R₃†`.  This is weaker than the generally false
claim that the unrestricted coefficient function itself has finite support: one takes the union
of the supports of `R₃` on the finitely many bar-three basis vectors read at group coordinate
`1`. -/
theorem exists_finiteUniversalThreeAdjointFiniteSupportDefect_eq_zero
    [Fintype Q]
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (c : FiniteModTwoBarCochainThree Q) :
    ∃ u : RegularModTwoRelationModule Q (FreeRelationKernel m),
      finiteUniversalThreeAdjointFiniteSupportDefect m heval c u = 0 := by
  classical
  let R₃ := finiteBarToUniversalRelationThree m heval
  let f := finiteFinsuppFullAdjoint (finiteUniversalRelationToBarThree m)
    (finiteRegularInvariantCoe (Q := Q) (Q × Q × Q) c)
  let S : Finset (Q × FreeRelationKernel m) :=
    Finset.univ.biUnion fun a : Q × Q × Q =>
      (R₃ (Finsupp.single (1, a) 1)).support
  let u : RegularModTwoRelationModule Q (FreeRelationKernel m) :=
    Finsupp.onFinset S (fun z => if z ∈ S then f z else 0) (by
      intro z hz
      by_contra hzS
      simp [hzS] at hz)
  refine ⟨u, ?_⟩
  have hR₃ (a : Q × Q × Q) :
      finiteFinsuppFullAdjoint R₃ f (1, a) =
        finiteFinsuppFullAdjoint R₃
          (u : Q × FreeRelationKernel m → ZMod 2) (1, a) := by
    apply finiteFinsuppCoefficientEval_congr_on_support
    intro z hz
    have hzS : z ∈ S := by
      apply Finset.mem_biUnion.mpr
      exact ⟨a, Finset.mem_univ a, hz⟩
    simp [u, hzS]
  funext a
  have hcombined := finiteFinsuppFullAdjoint_comp
    (finiteUniversalRelationToBarThree m) R₃
  simp only [finiteUniversalThreeAdjointFiniteSupportDefect,
    finiteUniversalForwardReverseThreeCochainCorrection,
    finiteUniversalForwardReverseThreeFullAdjoint,
    finiteUniversalRelationThreeFiniteSupportCorrection,
    LinearMap.comp_apply, finiteRegularAtOne]
  rw [hcombined]
  change finiteFinsuppFullAdjoint R₃ f (1, a) +
      finiteFinsuppFullAdjoint R₃
        (u : Q × FreeRelationKernel m → ZMod 2) (1, a) = 0
  rw [hR₃]
  exact ZModModule.add_self _

/-- The raw degree-three identity restricted to actual cochains.  No invariance claim for
`H₂†`, and no finite-support claim for the universal adjoint, is used here. -/
theorem finiteBarForwardReverseHomotopyThree_cochain_raw_identity
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (c : FiniteModTwoBarCochainThree Q) :
    finiteBarForwardReverseHomotopyThreeCochainAdjoint m heval
        (finiteModTwoBarDThree Q c) +
      finiteBarHomotopyTwoBoundaryRawCochainCorrection m heval c +
      finiteUniversalForwardReverseThreeCochainCorrection m heval c = c := by
  have hfull := finiteBarForwardReverseHomotopyThree_fullAdjoint_identity
    m heval (finiteRegularInvariantCoe (Q := Q) (Q × Q × Q) c)
  rw [finiteModTwoBarFullCoboundaryFour_invariant] at hfull
  have hatOne := congrArg
    (finiteRegularAtOne (Q := Q) (Q × Q × Q)) hfull
  funext a
  exact congrFun hatOne a

/-- On a three-cocycle, the non-invariant bar defect is coupled exactly to the unrestricted
universal adjoint: together they give the residual `c + d²(H₂†c)`.  Thus the bar defect is not
an independent term that may simply be required to vanish. -/
theorem finiteBarHomotopyTwoAdjointBarDefect_add_universal_of_cocycle
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (c : FiniteModTwoBarCochainThree Q)
    (hc : finiteModTwoBarDThree Q c = 0) :
    finiteBarHomotopyTwoAdjointBarDefect m heval c +
      finiteUniversalForwardReverseThreeCochainCorrection m heval c =
        c + finiteModTwoBarDTwo Q
          (finiteBarForwardReverseHomotopyTwoCochainAdjoint m heval c) := by
  have hraw := finiteBarForwardReverseHomotopyThree_cochain_raw_identity m heval c
  rw [hc, map_zero, zero_add] at hraw
  funext a
  have ha := congrFun hraw a
  simp only [finiteBarHomotopyTwoAdjointBarDefect, AddMonoidHom.add_apply]
  let B : ZMod 2 := finiteBarHomotopyTwoBoundaryRawCochainCorrection m heval c a
  let D : ZMod 2 := finiteModTwoBarDTwo Q
    (finiteBarForwardReverseHomotopyTwoCochainAdjoint m heval c) a
  let U : ZMod 2 := finiteUniversalForwardReverseThreeCochainCorrection m heval c a
  let C : ZMod 2 := c a
  change B + D + U = C + D
  change B + U = C at ha
  calc
    B + D + U = (B + U) + D := by abel
    _ = C + D := by rw [ha]

/-- If a finitely supported universal coefficient has zero truncation defect, it satisfies the
same cocycle coupling formula.  The finite-quotient truncation theorem above supplies such a
coefficient pointwise without any global support assumption. -/
theorem finiteBarHomotopyTwoAdjointBarDefect_add_finiteSupport_of_cocycle
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (c : FiniteModTwoBarCochainThree Q)
    (u : RegularModTwoRelationModule Q (FreeRelationKernel m))
    (hc : finiteModTwoBarDThree Q c = 0)
    (hu : finiteUniversalThreeAdjointFiniteSupportDefect m heval c u = 0) :
    finiteBarHomotopyTwoAdjointBarDefect m heval c +
      finiteUniversalRelationThreeFiniteSupportCorrection m heval u =
        c + finiteModTwoBarDTwo Q
          (finiteBarForwardReverseHomotopyTwoCochainAdjoint m heval c) := by
  have hcoupled :=
    finiteBarHomotopyTwoAdjointBarDefect_add_universal_of_cocycle m heval c hc
  funext a
  have hcoupA := congrFun hcoupled a
  have huA := congrFun hu a
  simp only [finiteUniversalThreeAdjointFiniteSupportDefect] at huA
  let B : ZMod 2 := finiteBarHomotopyTwoAdjointBarDefect m heval c a
  let U : ZMod 2 := finiteUniversalForwardReverseThreeCochainCorrection m heval c a
  let F : ZMod 2 := finiteUniversalRelationThreeFiniteSupportCorrection m heval u a
  let R : ZMod 2 :=
    (c + finiteModTwoBarDTwo Q
      (finiteBarForwardReverseHomotopyTwoCochainAdjoint m heval c)) a
  change B + F = R
  change B + U = R at hcoupA
  change U + F = 0 at huA
  have hUF : U = F := by
    calc
      U = U + (F + F) := by rw [ZModModule.add_self, add_zero]
      _ = (U + F) + F := by abel
      _ = F := by rw [huA, zero_add]
  rw [← hUF, hcoupA]

/-- **Fixed-level degree-three reconstruction with explicit defects.**  The bar defect records
non-invariance of `H₂†`; the universal defect independently records the failure of the
universal adjoint coefficient to equal the proposed finite-support coefficient `u`. -/
theorem finiteBarForwardReverseHomotopyThree_cochain_identity_with_defects
    (m : I → Q) (heval : Function.Surjective (FreeGroup.lift m))
    (c : FiniteModTwoBarCochainThree Q)
    (u : RegularModTwoRelationModule Q (FreeRelationKernel m)) :
    finiteBarForwardReverseHomotopyThreeCochainAdjoint m heval
        (finiteModTwoBarDThree Q c) +
      finiteModTwoBarDTwo Q
        (finiteBarForwardReverseHomotopyTwoCochainAdjoint m heval c) +
      finiteUniversalRelationThreeFiniteSupportCorrection m heval u +
      finiteBarHomotopyTwoAdjointBarDefect m heval c +
      finiteUniversalThreeAdjointFiniteSupportDefect m heval c u = c := by
  funext a
  have hraw := congrFun
    (finiteBarForwardReverseHomotopyThree_cochain_raw_identity m heval c) a
  rw [← hraw]
  simp only [finiteBarHomotopyTwoAdjointBarDefect,
    finiteUniversalThreeAdjointFiniteSupportDefect]
  let A : ZMod 2 :=
    finiteBarForwardReverseHomotopyThreeCochainAdjoint m heval
      (finiteModTwoBarDThree Q c) a
  let B : ZMod 2 := finiteBarHomotopyTwoBoundaryRawCochainCorrection m heval c a
  let D : ZMod 2 := finiteModTwoBarDTwo Q
    (finiteBarForwardReverseHomotopyTwoCochainAdjoint m heval c) a
  let U : ZMod 2 := finiteUniversalRelationThreeFiniteSupportCorrection m heval u a
  let V : ZMod 2 := finiteUniversalForwardReverseThreeCochainCorrection m heval c a
  change A + D + U + (B + D) + (V + U) = A + B + V
  calc
    A + D + U + (B + D) + (V + U) =
        A + B + V + (D + D) + (U + U) := by abel
    _ = A + B + V := by
      rw [ZModModule.add_self, ZModModule.add_self]
      simp

end

end GQ2.Dyadic.Count
