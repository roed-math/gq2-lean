/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.WordPhaseWallHandleCertificates

/-!
# The arbitrary-diagonal wall polar operator and its inverse

For the phase `d₀(x₀) + Bq(x₀,x₁) + ∑ Bq(u,v)`, suppose the polar of `d₀`
is represented relative to `Bq` by an additive operator `L`. Its polar operator is
`J_L(x₀,x₁,(u,v)) = (L x₀+x₁,x₀,(v,u))`, with inverse
`J_L⁻¹(y₀,y₁,(u,v)) = (y₁,y₀-L y₁,(v,u))`.

The first part works for a supplied adjoint, without finiteness or nonsingularity.
The second constructs the unique adjoint on any finite additive group with nonsingular
quadratic `q`, using the existing finite polar-representative theorem. Thus there is no
additional adjoint hypothesis in the final factorization and inverse theorems.

These are identities for the polar form. They do not identify two quadratic phases
having the same polar form or discard the actual diagonal `d₀` from a phase certificate.
-/

namespace GQ2.Dyadic.Instances.WordPhaseWallHandlePolarInverse
noncomputable section
open GQ2 GQ2.Dyadic GQ2.QuadraticFp2
open Instances.WordPhasePolarNormal Instances.WordPhaseWallHandleCertificates

variable {V : Type} [AddCommGroup V]

/-- The invertible operator with head block `[[L,1],[1,0]]` and swapped handles. -/
def wallPolarBlockEquiv (L : V →+ V) (h : ℕ) :
    CompactCoordinates V h ≃+ CompactCoordinates V h where
  toFun x := ((L x.1.1 + x.1.2, x.1.1), fun j => ((x.2 j).2, (x.2 j).1))
  invFun y := ((y.1.2, y.1.1 - L y.1.2), fun j => ((y.2 j).2, (y.2 j).1))
  left_inv x := by ext <;> simp
  right_inv y := by ext <;> simp
  map_add' x y := by ext <;> simp; abel

@[simp] theorem wallPolarBlockEquiv_apply (L : V →+ V) (h : ℕ)
    (x : CompactCoordinates V h) :
    wallPolarBlockEquiv L h x =
      ((L x.1.1 + x.1.2, x.1.1), fun j => ((x.2 j).2, (x.2 j).1)) := rfl

@[simp] theorem wallPolarBlockEquiv_symm_apply (L : V →+ V) (h : ℕ)
    (y : CompactCoordinates V h) :
    (wallPolarBlockEquiv L h).symm y =
      ((y.1.2, y.1.1 - L y.1.2), fun j => ((y.2 j).2, (y.2 j).1)) := rfl

/-- Exact factorization of the arbitrary-diagonal polar form through the displayed operator. -/
theorem polar_wallHandlePhase_eq_coordinatePairing_of_adjoint
    (d₀ q : V → ZMod 2) (hq : IsQuadraticFp2 q) (L : V →+ V)
    (hL : ∀ v w, polar d₀ v w = polar q (L v) w)
    (h : ℕ) (x y : CompactCoordinates V h) :
    polar (wallHandlePhase d₀ q h) x y =
      coordinatePairing q h (wallPolarBlockEquiv L h x) y := by
  rw [polar_wallHandlePhase d₀ q hq]
  simp only [coordinatePairing, wallPolarBlockEquiv_apply, hq.polar_add_left, hL]
  have hs : (∑ j, (polar q (x.2 j).1 (y.2 j).2 + polar q (x.2 j).2 (y.2 j).1)) =
      ∑ j, (polar q (x.2 j).2 (y.2 j).1 + polar q (x.2 j).1 (y.2 j).2) := by
    apply Finset.sum_congr rfl
    intro j _
    exact add_comm _ _
  rw [hs]
  abel

/-- Solving the polar equation with a supplied adjoint uses the explicit inverse. -/
theorem coordinatePairing_eq_wallPolar_inverse_of_adjoint
    (d₀ q : V → ZMod 2) (hq : IsQuadraticFp2 q) (L : V →+ V)
    (hL : ∀ v w, polar d₀ v w = polar q (L v) w)
    (h : ℕ) (x y : CompactCoordinates V h) :
    coordinatePairing q h x y =
      polar (wallHandlePhase d₀ q h) ((wallPolarBlockEquiv L h).symm x) y := by
  rw [polar_wallHandlePhase_eq_coordinatePairing_of_adjoint d₀ q hq L hL,
    AddEquiv.apply_symm_apply]

/-- The additive map to the additive dual defined by a quadratic polar form. -/
def polarDualHom (q : V → ZMod 2) (hq : IsQuadraticFp2 q) :
    V →+ (V →+ ZMod 2) :=
  AddMonoidHom.mk'
    (fun v => AddMonoidHom.mk' (fun w => polar q v w) (hq.polar_add_right v))
    (fun v v' => by ext w; exact hq.polar_add_left v v' w)

@[simp] theorem polarDualHom_apply (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (v w : V) : polarDualHom q hq v w = polar q v w := rfl

/-- Nonsingularity gives injectivity without a finiteness or exponent-two assumption. -/
theorem polarDualHom_injective (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) : Function.Injective (polarDualHom q hq) := by
  intro v v' hvv
  by_contra hne
  obtain ⟨w, hw⟩ := hns (v - v') (sub_ne_zero.mpr hne)
  apply hw
  have heq : polar q v w = polar q v' w := DFunLike.congr_fun hvv w
  have hadd := hq.polar_add_left (v - v') v' w
  rw [sub_add_cancel, heq] at hadd
  exact (add_right_cancel (show (0 : ZMod 2) + polar q v' w =
    polar q (v - v') w + polar q v' w by simpa only [zero_add] using hadd)).symm

/-- Finite nonsingular polar duality, proved from the existing Fourier representative theorem. -/
def polarDualEquiv [Finite V] (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) : V ≃+ (V →+ ZMod 2) := by
  letI : Fintype V := Fintype.ofFinite V
  refine AddEquiv.ofBijective (polarDualHom q hq) ⟨polarDualHom_injective q hq hns, ?_⟩
  intro ell
  obtain ⟨v, hv⟩ := polar_rep_exists q hq hns ell
  refine ⟨v, ?_⟩
  ext w
  exact (polar_comm q v w).trans (hv w).symm

@[simp] theorem polarDualEquiv_apply [Finite V] (q : V → ZMod 2)
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (v w : V) :
    polarDualEquiv q hq hns v w = polar q v w := rfl

/-- The unique adjoint of the diagonal polar form relative to the nonsingular `q` pairing. -/
def diagonalPolarAdjoint [Finite V] (d₀ q : V → ZMod 2)
    (hd : IsQuadraticFp2 d₀) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) : V →+ V :=
  (polarDualEquiv q hq hns).symm.toAddMonoidHom.comp (polarDualHom d₀ hd)

/-- The constructed adjoint represents the actual diagonal polar form. -/
theorem diagonalPolarAdjoint_spec [Finite V] (d₀ q : V → ZMod 2)
    (hd : IsQuadraticFp2 d₀) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (v w : V) :
    polar d₀ v w = polar q (diagonalPolarAdjoint d₀ q hd hq hns v) w := by
  have heq := DFunLike.congr_fun
    ((polarDualEquiv q hq hns).apply_symm_apply (polarDualHom d₀ hd v)) w
  exact heq.symm

/-- Any supplied adjoint agrees with the canonical finite construction. -/
theorem diagonalPolarAdjoint_unique [Finite V] (d₀ q : V → ZMod 2)
    (hd : IsQuadraticFp2 d₀) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (L : V →+ V) (hL : ∀ v w, polar d₀ v w = polar q (L v) w) :
    L = diagonalPolarAdjoint d₀ q hd hq hns := by
  ext v
  apply polarDualHom_injective q hq hns
  ext w
  exact (hL v w).symm.trans (diagonalPolarAdjoint_spec d₀ q hd hq hns v w)

/-- The canonical polar operator and its explicit inverse, with no additional adjoint input. -/
def canonicalWallPolarEquiv [Finite V] (d₀ q : V → ZMod 2)
    (hd : IsQuadraticFp2 d₀) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (h : ℕ) :
    CompactCoordinates V h ≃+ CompactCoordinates V h :=
  wallPolarBlockEquiv (diagonalPolarAdjoint d₀ q hd hq hns) h

theorem polar_wallHandlePhase_eq_coordinatePairing [Finite V] (d₀ q : V → ZMod 2)
    (hd : IsQuadraticFp2 d₀) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (h : ℕ) (x y : CompactCoordinates V h) :
    polar (wallHandlePhase d₀ q h) x y =
      coordinatePairing q h (canonicalWallPolarEquiv d₀ q hd hq hns h x) y :=
  polar_wallHandlePhase_eq_coordinatePairing_of_adjoint d₀ q hq _
    (diagonalPolarAdjoint_spec d₀ q hd hq hns) h x y

/-- Literal inverse formula for the arbitrary-diagonal wall polar operator. -/
@[simp] theorem canonicalWallPolarEquiv_symm_apply [Finite V] (d₀ q : V → ZMod 2)
    (hd : IsQuadraticFp2 d₀) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (h : ℕ) (y : CompactCoordinates V h) :
    (canonicalWallPolarEquiv d₀ q hd hq hns h).symm y =
      ((y.1.2, y.1.1 - diagonalPolarAdjoint d₀ q hd hq hns y.1.2),
        fun j => ((y.2 j).2, (y.2 j).1)) := rfl

theorem coordinatePairing_eq_wallPolar_inverse [Finite V] (d₀ q : V → ZMod 2)
    (hd : IsQuadraticFp2 d₀) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (h : ℕ) (x y : CompactCoordinates V h) :
    coordinatePairing q h x y = polar (wallHandlePhase d₀ q h)
      ((canonicalWallPolarEquiv d₀ q hd hq hns h).symm x) y := by
  rw [polar_wallHandlePhase_eq_coordinatePairing d₀ q hd hq hns,
    AddEquiv.apply_symm_apply]

/-- The arbitrary-diagonal head block as a literal matrix of additive endomorphisms. -/
def wallHeadMatrix (L : V →+ V) : Matrix (Fin 2) (Fin 2) (AddMonoid.End V) :=
  !![L, 1; 1, 0]

/-- Its inverse is `[[0,1],[1,-L]]`; no commutativity of endomorphism composition is needed. -/
def wallHeadInverseMatrix (L : V →+ V) : Matrix (Fin 2) (Fin 2) (AddMonoid.End V) :=
  !![0, 1; 1, -L]

theorem wallHeadMatrix_mul_inverse (L : V →+ V) :
    wallHeadMatrix L * wallHeadInverseMatrix L = 1 := by
  have key : ∀ M : AddMonoid.End V,
      (!![M, 1; 1, 0] * !![0, 1; 1, -M] : Matrix (Fin 2) (Fin 2) (AddMonoid.End V)) = 1 := by
    intro M
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  exact key L

theorem wallHeadInverseMatrix_mul_head (L : V →+ V) :
    wallHeadInverseMatrix L * wallHeadMatrix L = 1 := by
  have key : ∀ M : AddMonoid.End V,
      (!![0, 1; 1, -M] * !![M, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (AddMonoid.End V)) = 1 := by
    intro M
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  exact key L

/-- The old compact head is the special case in which the diagonal is `q` itself. -/
theorem diagonalPolarAdjoint_self [Finite V] (q : V → ZMod 2)
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q) :
    diagonalPolarAdjoint q q hq hq hns = AddMonoidHom.id V :=
  (diagonalPolarAdjoint_unique q q hq hq hns (AddMonoidHom.id V) (fun _ _ => rfl)).symm

theorem canonicalWallPolarEquiv_self [Finite V] (q : V → ZMod 2)
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (h : ℕ) :
    canonicalWallPolarEquiv q q hq hq hns h = polarBlockEquiv V h := by
  unfold canonicalWallPolarEquiv
  rw [diagonalPolarAdjoint_self q hq hns]
  ext x <;> rfl

#print axioms wallPolarBlockEquiv
#print axioms wallPolarBlockEquiv_apply
#print axioms wallPolarBlockEquiv_symm_apply
#print axioms polar_wallHandlePhase_eq_coordinatePairing_of_adjoint
#print axioms coordinatePairing_eq_wallPolar_inverse_of_adjoint
#print axioms polarDualHom
#print axioms polarDualHom_apply
#print axioms polarDualHom_injective
#print axioms polarDualEquiv
#print axioms polarDualEquiv_apply
#print axioms diagonalPolarAdjoint
#print axioms diagonalPolarAdjoint_spec
#print axioms diagonalPolarAdjoint_unique
#print axioms canonicalWallPolarEquiv
#print axioms polar_wallHandlePhase_eq_coordinatePairing
#print axioms canonicalWallPolarEquiv_symm_apply
#print axioms coordinatePairing_eq_wallPolar_inverse
#print axioms wallHeadMatrix
#print axioms wallHeadInverseMatrix
#print axioms wallHeadMatrix_mul_inverse
#print axioms wallHeadInverseMatrix_mul_head
#print axioms diagonalPolarAdjoint_self
#print axioms canonicalWallPolarEquiv_self

end
end GQ2.Dyadic.Instances.WordPhaseWallHandlePolarInverse
