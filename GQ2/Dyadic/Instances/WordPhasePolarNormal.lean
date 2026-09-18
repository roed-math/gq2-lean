/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhase
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Explicit polar block certificate for the common even phase

For `Q(c0,c1,(u,v)) = q(c0) + B(c0,c1) + sum B(u,v)`, the polar matrix has head
`[[B,B],[B,0]]` and one handle block `[[0,B],[B,0]]` per handle. Relative to the
coordinatewise B-pairing it is represented by the explicit additive equivalence
`J(c0,c1,(u,v)) = (c0+c1,c0,(v,u))`. Its inverse is `(d0,d1,(v,u)) ↦ (d1,d0-d1,(u,v))`.

This is a basis-independent, rank-uniform certificate for the actual reduced phase. It is
an additive compositional acceptance artifact, not an assertion that a ledger owner has
approved replacing the old appendices. No source certificate hypothesis is changed.
-/

namespace GQ2.Dyadic.Instances.WordPhasePolarNormal
noncomputable section
open GQ2 GQ2.QuadraticFp2 GQ2.Dyadic
open Instances.WordPhase

variable {V : Type} [AddCommGroup V]

/-- Coordinates for the common even endpoint form. -/
abbrev CompactCoordinates (V : Type) (h : ℕ) := (V × V) × (Fin h → V × V)

/-- The diagonal coordinatewise pairing, with one copy of B for every scalar coordinate. -/
def coordinatePairing (q : V → ZMod 2) (h : ℕ)
    (x y : CompactCoordinates V h) : ZMod 2 :=
  polar q x.1.1 y.1.1 + polar q x.1.2 y.1.2 +
    ∑ j, (polar q (x.2 j).1 (y.2 j).1 + polar q (x.2 j).2 (y.2 j).2)

/-- The actual polar block operator, including an explicit inverse. No basis is chosen. -/
def polarBlockEquiv (V : Type) [AddCommGroup V] (h : ℕ) :
    CompactCoordinates V h ≃+ CompactCoordinates V h where
  toFun x := ((x.1.1 + x.1.2, x.1.1), fun j => ((x.2 j).2, (x.2 j).1))
  invFun y := ((y.1.2, y.1.1 - y.1.2), fun j => ((y.2 j).2, (y.2 j).1))
  left_inv x := by ext <;> simp
  right_inv y := by ext <;> simp
  map_add' x y := by ext <;> simp; abel

@[simp] theorem polarBlockEquiv_apply (h : ℕ) (x : CompactCoordinates V h) :
    polarBlockEquiv V h x =
      ((x.1.1 + x.1.2, x.1.1), fun j => ((x.2 j).2, (x.2 j).1)) := rfl

@[simp] theorem polarBlockEquiv_symm_apply (h : ℕ) (y : CompactCoordinates V h) :
    (polarBlockEquiv V h).symm y =
      ((y.1.2, y.1.1 - y.1.2), fun j => ((y.2 j).2, (y.2 j).1)) := rfl

private theorem polar_handle (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (x y : V × V) :
    polar (fun p : V × V => polar q p.1 p.2) x y =
      polar q x.1 y.2 + polar q x.2 y.1 := by
  change polar q (x.1 + y.1) (x.2 + y.2) + polar q x.1 x.2 + polar q y.1 y.2 = _
  rw [hq.polar_add_left, hq.polar_add_right, hq.polar_add_right, polar_comm q y.1 x.2]
  have key : ∀ a b c d : ZMod 2, (a + b + (c + d)) + a + d = b + c := by decide
  exact key _ _ _ _

/-- The full reduced polar form, displaying the head block and every handle block. -/
theorem polar_compactPhase_blocks (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (h : ℕ) (x y : CompactCoordinates V h) :
    polar (wPhCompactWallHandlePhase q h) x y =
      (polar q x.1.1 y.1.1 + polar q x.1.1 y.1.2 + polar q x.1.2 y.1.1) +
        ∑ j, (polar q (x.2 j).1 (y.2 j).2 + polar q (x.2 j).2 (y.2 j).1) := by
  have hsplit : polar (wPhCompactWallHandlePhase q h) x y =
      polar (plusFormD q q) x.1 y.1 +
        ∑ j, polar (fun p : V × V => polar q p.1 p.2) (x.2 j) (y.2 j) := by
    simp only [polar, wPhCompactWallHandlePhase, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    simp only [Finset.sum_add_distrib]
    abel
  rw [hsplit, polar_plusFormD q q hq, polar_comm q y.1.1 x.1.2]
  congr 1
  exact Finset.sum_congr rfl fun j _ => polar_handle q hq (x.2 j) (y.2 j)

/-- Exact factorization of the reduced polar matrix through the invertible block operator J. -/
theorem polar_compactPhase_eq_coordinatePairing (q : V → ZMod 2)
    (hq : IsQuadraticFp2 q) (h : ℕ) (x y : CompactCoordinates V h) :
    polar (wPhCompactWallHandlePhase q h) x y =
      coordinatePairing q h (polarBlockEquiv V h x) y := by
  rw [polar_compactPhase_blocks q hq]
  simp only [coordinatePairing, polarBlockEquiv_apply, hq.polar_add_left]
  have hs : (∑ j, (polar q (x.2 j).1 (y.2 j).2 + polar q (x.2 j).2 (y.2 j).1)) =
      ∑ j, (polar q (x.2 j).2 (y.2 j).1 + polar q (x.2 j).1 (y.2 j).2) := by
    apply Finset.sum_congr rfl
    intro j _
    exact add_comm _ _
  rw [hs]
  abel

/-- Solving the polar equation requires only the displayed inverse J⁻¹. -/
theorem coordinatePairing_eq_polar_inverse (q : V → ZMod 2)
    (hq : IsQuadraticFp2 q) (h : ℕ) (x y : CompactCoordinates V h) :
    coordinatePairing q h x y =
      polar (wPhCompactWallHandlePhase q h) ((polarBlockEquiv V h).symm x) y := by
  rw [polar_compactPhase_eq_coordinatePairing q hq, AddEquiv.apply_symm_apply]

theorem coordinatePairing_add_left (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (h : ℕ) (x y z : CompactCoordinates V h) :
    coordinatePairing q h (x + y) z = coordinatePairing q h x z + coordinatePairing q h y z := by
  simp only [coordinatePairing, Prod.fst_add, Prod.snd_add, Pi.add_apply, hq.polar_add_left]
  simp_rw [show ∀ a b c d : ZMod 2, (a + b) + (c + d) = (a + c) + (b + d) by intros; abel]
  rw [Finset.sum_add_distrib]

theorem coordinatePairing_add_right (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (h : ℕ) (x y z : CompactCoordinates V h) :
    coordinatePairing q h x (y + z) = coordinatePairing q h x y + coordinatePairing q h x z := by
  simp only [coordinatePairing, Prod.fst_add, Prod.snd_add, Pi.add_apply, hq.polar_add_right]
  simp_rw [show ∀ a b c d : ZMod 2, (a + b) + (c + d) = (a + c) + (b + d) by intros; abel]
  rw [Finset.sum_add_distrib]

/-- Quadraticity of the complete phase follows from the explicit bilinear block expression. -/
theorem isQuadratic_compactPhase (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (h : ℕ) :
    IsQuadraticFp2 (wPhCompactWallHandlePhase q h) where
  map_zero := by simp [wPhCompactWallHandlePhase, plusFormD, hq.map_zero, polar_zero_left q hq]
  polar_add_left x y z := by
    simp only [polar_compactPhase_eq_coordinatePairing q hq, map_add,
      coordinatePairing_add_left q hq]
  polar_add_right x y z := by
    simp only [polar_compactPhase_eq_coordinatePairing q hq, coordinatePairing_add_right q hq]

/-- Vanishing against all coordinate tests forces every coordinate to vanish. -/
theorem coordinatePairing_left_eq_zero (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (h : ℕ) (x : CompactCoordinates V h)
    (hx : ∀ y, coordinatePairing q h x y = 0) : x = 0 := by
  classical
  have hz : ∀ v : V, (∀ w, polar q v w = 0) → v = 0 := by
    intro v hv
    by_contra hn
    obtain ⟨w, hw⟩ := hns v hn
    exact hw (hv w)
  have h0 : x.1.1 = 0 := hz _ fun w => by
    simpa [coordinatePairing, polar_zero_right q hq] using hx ((w, 0), 0)
  have h1 : x.1.2 = 0 := hz _ fun w => by
    simpa [coordinatePairing, polar_zero_right q hq] using hx ((0, w), 0)
  have hu : ∀ j, (x.2 j).1 = 0 := fun j => hz _ fun w => by
    simpa [coordinatePairing, apply_ite, polar_zero_right q hq] using
      hx ((0, 0), fun k => if k = j then (w, 0) else (0, 0))
  have hv : ∀ j, (x.2 j).2 = 0 := fun j => hz _ fun w => by
    simpa [coordinatePairing, apply_ite, polar_zero_right q hq] using
      hx ((0, 0), fun k => if k = j then (0, w) else (0, 0))
  apply Prod.ext
  · exact Prod.ext h0 h1
  · funext j
    exact Prod.ext (hu j) (hv j)

/-- The explicit invertible polar block operator proves nonsingularity at every handle count. -/
theorem nonsingular_compactPhase (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (h : ℕ) : Nonsingular (wPhCompactWallHandlePhase q h) := by
  classical
  intro x hx
  by_contra hn
  have hz : polarBlockEquiv V h x = 0 :=
    coordinatePairing_left_eq_zero q hq hns h _ fun y => by
      rw [← polar_compactPhase_eq_coordinatePairing q hq]
      by_contra hne
      exact hn ⟨y, hne⟩
  exact hx ((polarBlockEquiv V h).injective (hz.trans (map_zero (polarBlockEquiv V h)).symm))

/-! ## Literal two-by-two coefficient matrices

Each scalar entry multiplies the same bilinear form B. Thus the displayed scalar matrices
stand for the basis-independent B-blocks, rather than assuming a basis in which B is identity.
-/

/-- The head coefficient block `[[1,1],[1,0]]`, meaning `[[B,B],[B,0]]`. -/
def headMatrix : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 1; 1, 0]

/-- The inverse head coefficient block in characteristic two. -/
def headInverseMatrix : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 1]

/-- A handle coefficient block `[[0,1],[1,0]]`, meaning `[[0,B],[B,0]]`. -/
def handleMatrix : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 0]

theorem headMatrix_mul_inverse : headMatrix * headInverseMatrix = 1 := by decide
theorem headInverseMatrix_mul_head : headInverseMatrix * headMatrix = 1 := by decide
theorem handleMatrix_mul_self : handleMatrix * handleMatrix = 1 := by decide

/-- Evaluation of a coefficient block against B, without choosing any basis of V. -/
def blockPairing (q : V → ZMod 2) (A : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (x y : V × V) : ZMod 2 :=
  ∑ i, ∑ j, A i j * polar q (![x.1, x.2] i) (![y.1, y.2] j)

theorem blockPairing_headMatrix (q : V → ZMod 2) (x y : V × V) :
    blockPairing q headMatrix x y =
      polar q x.1 y.1 + polar q x.1 y.2 + polar q x.2 y.1 := by
  simp [blockPairing, headMatrix, Fin.sum_univ_two]

theorem blockPairing_handleMatrix (q : V → ZMod 2) (x y : V × V) :
    blockPairing q handleMatrix x y = polar q x.1 y.2 + polar q x.2 y.1 := by
  simp [blockPairing, handleMatrix, Fin.sum_univ_two]

/-- The actual reduced polar matrix is a head block plus h hyperbolic blocks. -/
theorem polar_compactPhase_blockMatrices (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (h : ℕ) (x y : CompactCoordinates V h) :
    polar (wPhCompactWallHandlePhase q h) x y =
      blockPairing q headMatrix x.1 y.1 +
        ∑ j, blockPairing q handleMatrix (x.2 j) (y.2 j) := by
  simp only [blockPairing_headMatrix, blockPairing_handleMatrix]
  exact polar_compactPhase_blocks q hq h x y

/-- Head coordinates followed by the two coordinates of each handle. -/
abbrev BlockIndex (h : ℕ) := Fin 2 ⊕ (Fin h × Fin 2)

/-- The complete block-diagonal coefficient matrix, with all off-block entries zero. -/
def reducedCoefficientMatrix (h : ℕ) : Matrix (BlockIndex h) (BlockIndex h) (ZMod 2)
  | .inl i, .inl j => headMatrix i j
  | .inr i, .inr j => if i.1 = j.1 then handleMatrix i.2 j.2 else 0
  | _, _ => 0

/-- The complete inverse coefficient matrix: inverse head and unchanged handle blocks. -/
def reducedInverseMatrix (h : ℕ) : Matrix (BlockIndex h) (BlockIndex h) (ZMod 2)
  | .inl i, .inl j => headInverseMatrix i j
  | .inr i, .inr j => if i.1 = j.1 then handleMatrix i.2 j.2 else 0
  | _, _ => 0

/-- A literal inverse for the whole matrix, uniformly in the number of handles. -/
theorem reducedCoefficientMatrix_mul_inverse (h : ℕ) :
    reducedCoefficientMatrix h * reducedInverseMatrix h = 1 := by
  ext i j
  rcases i with i | ⟨i, k⟩ <;> rcases j with j | ⟨j, l⟩
  · fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type,
        reducedCoefficientMatrix, reducedInverseMatrix, headMatrix, headInverseMatrix,
        handleMatrix, CharTwo.add_self_eq_zero]
  · fin_cases i <;> fin_cases l <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type,
        reducedCoefficientMatrix, reducedInverseMatrix, headMatrix, headInverseMatrix,
        handleMatrix]
  · fin_cases k <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type,
        reducedCoefficientMatrix, reducedInverseMatrix, headMatrix, headInverseMatrix,
        handleMatrix]
  · fin_cases k <;> fin_cases l <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
        reducedCoefficientMatrix, reducedInverseMatrix, headMatrix, headInverseMatrix,
        handleMatrix, Matrix.one_apply, ite_mul, mul_ite]

/-- The opposite product is also the identity. -/
theorem reducedInverseMatrix_mul_coefficient (h : ℕ) :
    reducedInverseMatrix h * reducedCoefficientMatrix h = 1 := by
  ext i j
  rcases i with i | ⟨i, k⟩ <;> rcases j with j | ⟨j, l⟩
  · fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type,
        reducedCoefficientMatrix, reducedInverseMatrix, headMatrix, headInverseMatrix,
        handleMatrix, CharTwo.add_self_eq_zero]
  · fin_cases i <;> fin_cases l <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type,
        reducedCoefficientMatrix, reducedInverseMatrix, headMatrix, headInverseMatrix,
        handleMatrix]
  · fin_cases k <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type,
        reducedCoefficientMatrix, reducedInverseMatrix, headMatrix, headInverseMatrix,
        handleMatrix]
  · fin_cases k <;> fin_cases l <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
        reducedCoefficientMatrix, reducedInverseMatrix, headMatrix, headInverseMatrix,
        handleMatrix, Matrix.one_apply, ite_mul, mul_ite]

/-- Flatten the pair coordinates to the exact row/column index of the displayed matrix. -/
def blockCoordinates (h : ℕ) (x : CompactCoordinates V h) : BlockIndex h → V
  | .inl i => ![x.1.1, x.1.2] i
  | .inr i => ![(x.2 i.1).1, (x.2 i.1).2] i.2

/-- Literal finite-matrix certificate for the whole rank-uniform reduced polar form. -/
theorem polar_compactPhase_reducedMatrix (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (h : ℕ) (x y : CompactCoordinates V h) :
    polar (wPhCompactWallHandlePhase q h) x y =
      ∑ i, ∑ j, reducedCoefficientMatrix h i j *
        polar q (blockCoordinates h x i) (blockCoordinates h y j) := by
  rw [polar_compactPhase_blockMatrices q hq]
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, reducedCoefficientMatrix,
    blockCoordinates, blockPairing, ite_mul, Finset.sum_add_distrib]

#print axioms polarBlockEquiv
#print axioms polar_compactPhase_blocks
#print axioms polar_compactPhase_eq_coordinatePairing
#print axioms coordinatePairing_eq_polar_inverse
#print axioms isQuadratic_compactPhase
#print axioms coordinatePairing_left_eq_zero
#print axioms nonsingular_compactPhase
#print axioms headMatrix_mul_inverse
#print axioms headInverseMatrix_mul_head
#print axioms handleMatrix_mul_self
#print axioms polar_compactPhase_blockMatrices
#print axioms polar_compactPhase_reducedMatrix
#print axioms reducedCoefficientMatrix_mul_inverse
#print axioms reducedInverseMatrix_mul_coefficient

end
end GQ2.Dyadic.Instances.WordPhasePolarNormal
