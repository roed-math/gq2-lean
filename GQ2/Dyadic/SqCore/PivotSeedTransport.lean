/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.PivotUnitizer

/-!
# The pivot family from a transported affine family: the linear interface

`SqCore/PivotCoreMoves.lean` reduced the `h = 0` model-side residual to two one-parameter
families of automorphisms of `D_sq(0) = D_R`.  This file supplies the **linear algebra** that
turns *any* two-parameter affine family of automorphisms into those two families, so that the
remaining obligation is a single, purely structural package of data.

## The observation

`SqPivotCoreMove 0 m k` asks only for a χ-preserving automorphism `Ψ` whose effect on the two
core **rows** is `(m, k)` against the pivot row.  Rows are `ν'`-linear, so the whole statement
lives on the abelianization: if some frame `D_sq(0)^{ab} ≅ ℤ/2 ⊕ ℤ₂·e_S ⊕ ℤ₂·e_Y` is available
in which

* `σ` has coordinates `(·, pS, qS)` and `x₀` has coordinates `(·, pX, qX)`,
* a family `Ψ_{u,b}` acts by `e_S ↦ u·e_S`, `e_Y ↦ b·e_S + e_Y` (the affine group of the
  `e_S`-line), and
* the χ-trivial pivot `w = σ·x₀^{−c₀}` lies **on** that line, i.e. `qS = c₀·qX`,

then the family already realizes every pivot core move on the determinant locus, with the
dictionary `u = sqPivotDet m k` and one linear solve for `b`.  Two units fall out for free from
two evaluations at explicit markings, so nothing about the frame has to be assumed beyond the
displayed rows.

## Contents

* **§1** `nuSqOf a b`, the marking with prescribed core rows `(a, b)` (the `x₁`-row `2b` is
  forced), with its five value lemmas and its pivot row `a − c₀·b`.  This is the two-element
  test family that makes §3 work.
* **§2** `SqPivotAffine`, the package: four coordinates, two marking-valued coefficient
  functions, the family `psi`, its χ-clause, the two row formulas, the two transported row
  formulas, and the **one** geometric hypothesis `qS = c₀·qX` ("the pivot is on the scaled
  line").
* **§3** the two unit lemmas `SqPivotAffine.isUnit_pW` and `SqPivotAffine.isUnit_qX`, extracted
  from the markings `ν(σ,x₀) = (1,0)` and `(0,1)` alone.
* **§4** `sqPivotCoreMove_zero_of_affine`: every move on the determinant locus, and hence
  `sqPivotTranslation_zero_of_affine`, `sqPivotScaling_zero_of_affine`, and the milestone shape
  `sqNuOrientedClear_zero_of_affine`.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`.  Every declaration prints **std-3** (`propext`,
`Classical.choice`, `Quot.sound`).  Census unchanged at **11**.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 Markings with prescribed core rows -/

section Markings

/-- **The marking with prescribed core rows** `ν(σ) = a`, `ν(x₀) = b`.  The `x₁`-row is the
forced `2b` and the handle rows vanish; the relator dies by the abelian collapse
`−4b + 2·(2b) = 0`.  `nuSq h` is the case `(1, 0)`. -/
noncomputable def nuSqOf (h : ℕ) (a b : ℤ_[2]) :
    ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
  sqLiftHom h PropOneOne.isProP_two_multPadicInt
    (sqMark (ofAdd a) (ofAdd b) (ofAdd (2 * b))) (by
      rw [sqRelWord_sqMark]
      show sqWord (ofAdd a) (ofAdd b) (ofAdd (2 * b)) = 1
      rw [sqWord_comm, ← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add, ← ofAdd_zero]
      congr 1
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      ring)

variable (h : ℕ) (a b : ℤ_[2])

@[simp] theorem nuSqOf_sigma : nuSqOf h a b (dsqSigma h) = ofAdd a :=
  (sqLiftHom_gen _ _ _ _ 0).trans (sqMark_zero _ _ _)

@[simp] theorem nuSqOf_x0 : nuSqOf h a b (dsqX0 h) = ofAdd b :=
  (sqLiftHom_gen _ _ _ _ 1).trans (sqMark_one _ _ _)

@[simp] theorem nuSqOf_x1 : nuSqOf h a b (dsqX1 h) = ofAdd (2 * b) :=
  (sqLiftHom_gen _ _ _ _ 2).trans (sqMark_two _ _ _)

@[simp] theorem nuSqOf_handleU (j : Fin h) : nuSqOf h a b (sqGen h (sqHandleIdxU j)) = 1 :=
  (sqLiftHom_gen _ _ _ _ _).trans (sqMark_handleU _ _ _ j)

@[simp] theorem nuSqOf_handleV (j : Fin h) : nuSqOf h a b (sqGen h (sqHandleIdxV j)) = 1 :=
  (sqLiftHom_gen _ _ _ _ _).trans (sqMark_handleV _ _ _ j)

/-- The pivot row of `nuSqOf a b` is `a − c₀·b`. -/
theorem toAdd_nuSqOf_sqPivot : toAdd (nuSqOf h a b (sqPivot h)) = a - sqPivotExp * b := by
  rw [toAdd_nu_sqPivot, nuSqOf_sigma, nuSqOf_x0, toAdd_ofAdd, toAdd_ofAdd]

end Markings

/-! ## §2 The transported affine package -/

section Affine

/-- Abbreviation for the markings of the rank-three core. -/
abbrev SqMarking : Type := ContinuousMonoidHom (DSq 0 : Type) (Multiplicative ℤ_[2])

/-- **A transported affine family for the pivot core.**  The data of a rank-two coordinate
system on the rows of `D_sq(0)`, together with a two-parameter family of χ-preserving
automorphisms acting on it by the affine group of the first coordinate line, and the one
geometric hypothesis `qS = c₀·qX` that puts the χ-trivial pivot **on** that line.

Nothing here mentions the frame itself: `cS` and `cY` are the two coordinate functionals read
off *at each marking*, which is all the row clauses of `SqPivotCoreMove` ever see. -/
structure SqPivotAffine where
  /-- The `e_S`-coordinate of `σ`. -/
  pS : ℤ_[2]
  /-- The `e_S`-coordinate of `x₀`. -/
  pX : ℤ_[2]
  /-- The `e_Y`-coordinate of `σ`. -/
  qS : ℤ_[2]
  /-- The `e_Y`-coordinate of `x₀`. -/
  qX : ℤ_[2]
  /-- The value of a marking on the `e_S`-coordinate vector. -/
  cS : SqMarking → ℤ_[2]
  /-- The value of a marking on the `e_Y`-coordinate vector. -/
  cY : SqMarking → ℤ_[2]
  /-- The two-parameter family: the **unit** `u` scales the `e_S`-line, `b` shears `e_Y` into
  it.  The unit constraint is not cosmetic: `sqPivotDet` of the resulting move is `u`, and
  `isUnit_sqPivotDet_of_sqPivotCoreMove` shows no move exists off the unit locus, so a family
  indexed by all of `ℤ₂` would be uninhabited. -/
  psi : ℤ_[2]ˣ → ℤ_[2] → ContinuousMulEquiv (DSq 0 : Type) (DSq 0 : Type)
  /-- Every member of the family preserves the orientation. -/
  chi_psi : ∀ (u : ℤ_[2]ˣ) (b : ℤ_[2]) (x : (DSq 0 : Type)), chiSq 0 (psi u b x) = chiSq 0 x
  /-- The `σ`-row in coordinates. -/
  sigma_row : ∀ nu' : SqMarking, toAdd (nu' (dsqSigma 0)) = pS * cS nu' + qS * cY nu'
  /-- The `x₀`-row in coordinates. -/
  x0_row : ∀ nu' : SqMarking, toAdd (nu' (dsqX0 0)) = pX * cS nu' + qX * cY nu'
  /-- The transported `σ`-row: the `e_S`-coordinate is scaled by `u` and receives `b·qS`. -/
  psi_sigma : ∀ (u : ℤ_[2]ˣ) (b : ℤ_[2]) (nu' : SqMarking),
    toAdd (nu' (psi u b (dsqSigma 0)))
      = ((u : ℤ_[2]) * pS + b * qS) * cS nu' + qS * cY nu'
  /-- The transported `x₀`-row. -/
  psi_x0 : ∀ (u : ℤ_[2]ˣ) (b : ℤ_[2]) (nu' : SqMarking),
    toAdd (nu' (psi u b (dsqX0 0)))
      = ((u : ℤ_[2]) * pX + b * qX) * cS nu' + qX * cY nu'
  /-- **The pivot lies on the scaled line**: `w = σ·x₀^{−c₀}` has vanishing `e_Y`-coordinate.
  This is the χ-clause of the transport: `w` is χ-trivial, and on a frame in which the family
  scales the `e_S`-line by an arbitrary unit the χ-trivial line *is* that line. -/
  pivot_on_line : qS = sqPivotExp * qX

namespace SqPivotAffine

variable (F : SqPivotAffine)

/-- The `e_S`-coordinate of the pivot. -/
noncomputable def pW : ℤ_[2] := F.pS - sqPivotExp * F.pX

/-- **The pivot row in coordinates**: only the `e_S`-coordinate survives. -/
theorem pivot_row (nu' : SqMarking) : toAdd (nu' (sqPivot 0)) = F.pW * F.cS nu' := by
  rw [toAdd_nu_sqPivot, F.sigma_row, F.x0_row, F.pivot_on_line, pW]
  ring

/-! ## §3 The two units, from two markings -/

/-- The pivot row of `nuSqOf 1 0` is `1`, so the pivot's coordinate is a unit. -/
theorem isUnit_pW : IsUnit F.pW := by
  have h := F.pivot_row (nuSqOf 0 1 0)
  rw [toAdd_nuSqOf_sqPivot] at h
  exact ⟨⟨F.pW, F.cS (nuSqOf 0 1 0), by linear_combination -h, by linear_combination -h⟩, rfl⟩

/-- The `x₀`-row is not a multiple of the pivot row: the markings `(1, 0)` and `(0, 1)` give it
independent values, so `qX` is a unit. -/
theorem isUnit_qX : IsUnit F.qX := by
  have hp1 : F.pW * F.cS (nuSqOf 0 1 0) = 1 := by
    have h := F.pivot_row (nuSqOf 0 1 0)
    rw [toAdd_nuSqOf_sqPivot] at h
    linear_combination -h
  have hp2 : F.pW * F.cS (nuSqOf 0 0 1) = -sqPivotExp := by
    have h := F.pivot_row (nuSqOf 0 0 1)
    rw [toAdd_nuSqOf_sqPivot] at h
    linear_combination -h
  have hx1 : F.pX * F.cS (nuSqOf 0 1 0) + F.qX * F.cY (nuSqOf 0 1 0) = 0 := by
    have h := F.x0_row (nuSqOf 0 1 0)
    rw [nuSqOf_x0, toAdd_ofAdd] at h
    linear_combination -h
  have hx2 : F.pX * F.cS (nuSqOf 0 0 1) + F.qX * F.cY (nuSqOf 0 0 1) = 1 := by
    have h := F.x0_row (nuSqOf 0 0 1)
    rw [nuSqOf_x0, toAdd_ofAdd] at h
    linear_combination -h
  obtain ⟨e, he⟩ := F.isUnit_pW
  have hpe : F.pW * ((e⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [← he, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hcomb : F.pW * (F.cS (nuSqOf 0 0 1) + sqPivotExp * F.cS (nuSqOf 0 1 0)) = 0 := by
    linear_combination hp2 + sqPivotExp * hp1
  have hzero : F.cS (nuSqOf 0 0 1) + sqPivotExp * F.cS (nuSqOf 0 1 0) = 0 := by
    linear_combination ((e⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * hcomb
      - (F.cS (nuSqOf 0 0 1) + sqPivotExp * F.cS (nuSqOf 0 1 0)) * hpe
  refine ⟨⟨F.qX, F.cY (nuSqOf 0 0 1) + sqPivotExp * F.cY (nuSqOf 0 1 0), ?_, ?_⟩, rfl⟩
  · linear_combination hx2 + sqPivotExp * hx1 - F.pX * hzero
  · linear_combination hx2 + sqPivotExp * hx1 - F.pX * hzero

/-! ## §4 The pivot core moves -/

include F in
/-- **The transported family realizes every pivot core move on the determinant locus.**  The
scaling parameter is the determinant itself, `u = 1 + m − k·c₀`, and the shear parameter solves
the single linear equation `(u − 1)·pX + b·qX = k·pW`, which is solvable because `qX` is a unit
(§3).  The `σ`-clause is then automatic: it is the `x₀`-clause plus the pivot clause. -/
theorem sqPivotCoreMove_zero_of_affine {m k : ℤ_[2]} (h : IsUnit (sqPivotDet m k)) :
    SqPivotCoreMove 0 m k := by
  intro nu'
  obtain ⟨e, he⟩ := F.isUnit_qX
  obtain ⟨uu, huu⟩ := h
  set qinv : ℤ_[2] := ((e⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) with hqinv
  have hqq : F.qX * qinv = 1 := by
    rw [hqinv, ← he, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdet : (uu : ℤ_[2]) - 1 = m - k * sqPivotExp := by
    rw [huu, sqPivotDet]; ring
  set b : ℤ_[2] := (k * F.pW - ((uu : ℤ_[2]) - 1) * F.pX) * qinv with hb
  have hkey : ((uu : ℤ_[2]) - 1) * F.pX + b * F.qX = k * F.pW := by
    rw [hb]
    linear_combination (k * F.pW - ((uu : ℤ_[2]) - 1) * F.pX) * hqq
  have hkeyS : ((uu : ℤ_[2]) - 1) * F.pS + b * F.qS = m * F.pW := by
    have hpS : F.pS = F.pW + sqPivotExp * F.pX := by rw [pW]; ring
    rw [hpS, F.pivot_on_line]
    linear_combination sqPivotExp * hkey + F.pW * hdet
  refine ⟨F.psi uu b, F.chi_psi uu b, ?_, ?_, fun j => j.elim0, fun j => j.elim0⟩
  · rw [F.psi_sigma, F.sigma_row, F.pivot_row]
    linear_combination (F.cS nu') * hkeyS
  · rw [F.psi_x0, F.x0_row, F.pivot_row]
    linear_combination (F.cS nu') * hkey

include F in
/-- The translation subgroup, from the transported family. -/
theorem sqPivotTranslation_zero_of_affine (c : ℤ_[2]) : SqPivotTranslation 0 c :=
  F.sqPivotCoreMove_zero_of_affine (by rw [sqPivotDet_translation]; exact isUnit_one)

include F in
/-- The scaling subgroup, from the transported family. -/
theorem sqPivotScaling_zero_of_affine {a : ℤ_[2]} (ha : IsUnit a) : SqPivotScaling 0 a :=
  F.sqPivotCoreMove_zero_of_affine (by rw [sqPivotDet_scaling]; exact ha)

include F in
/-- **The `h = 0` model-side residual, from the transported family alone.** -/
theorem sqNuOrientedClear_zero_of_affine : SqNuOrientedClear 0 :=
  sqNuOrientedClear_zero_of_two_subgroups F.sqPivotTranslation_zero_of_affine
    (fun _ ha => F.sqPivotScaling_zero_of_affine ha)

end SqPivotAffine

end Affine

/-! ## §5 Stress pins -/

section StressTests

/-- The prescribed-row marking really has the prescribed rows. -/
example (a b : ℤ_[2]) : nuSqOf 0 a b (dsqSigma 0) = ofAdd a ∧ nuSqOf 0 a b (dsqX0 0) = ofAdd b :=
  ⟨nuSqOf_sigma 0 a b, nuSqOf_x0 0 a b⟩

/-- …and the forced `x₁`-row. -/
example (a b : ℤ_[2]) : nuSqOf 0 a b (dsqX1 0) = ofAdd (2 * b) := nuSqOf_x1 0 a b

/-- The pivot row of a prescribed-row marking. -/
example (a b : ℤ_[2]) : toAdd (nuSqOf 0 a b (sqPivot 0)) = a - sqPivotExp * b :=
  toAdd_nuSqOf_sqPivot 0 a b

/-- A transported affine family gives the whole determinant locus. -/
example (F : SqPivotAffine) (m k : ℤ_[2]) (h : IsUnit (sqPivotDet m k)) :
    SqPivotCoreMove 0 m k := F.sqPivotCoreMove_zero_of_affine h

/-- …hence both one-parameter subgroups, hence the residual. -/
example (F : SqPivotAffine) : SqNuOrientedClear 0 := F.sqNuOrientedClear_zero_of_affine

end StressTests

/-! ## §6 Axiom pins -/

section AxiomPins

#print axioms nuSqOf
#print axioms nuSqOf_sigma
#print axioms toAdd_nuSqOf_sqPivot
#print axioms SqPivotAffine.pivot_row
#print axioms SqPivotAffine.isUnit_pW
#print axioms SqPivotAffine.isUnit_qX
#print axioms SqPivotAffine.sqPivotCoreMove_zero_of_affine
#print axioms SqPivotAffine.sqPivotTranslation_zero_of_affine
#print axioms SqPivotAffine.sqPivotScaling_zero_of_affine
#print axioms SqPivotAffine.sqNuOrientedClear_zero_of_affine

end AxiomPins

end SqCore

end Dyadic

end GQ2
