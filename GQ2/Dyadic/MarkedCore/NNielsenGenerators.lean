/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.MarkedCore.NFullStabilizerLift

/-!
# The N-side bridge to the full stabilizer lifting theorem

Wave 363, lane MC-N, at the rank-four core (`h = 0`, `alpha >= 2`).

## Why this is not the N twin of `MNielsenGenerators`

The packet's **MC-N** row asks for the same finite Nielsen-generator artifact that
`MNielsenGenerators.lean` produces at M. **It cannot be produced yet**, and the obstruction is
not on the lifting side: there is no N-side factorization to compose. `N.lean` has the
classification `nStabilizer_classification`, but there is no `nNielsen_factorization` and there
are no `nFamN1` through `nFamN6` values anywhere in `GQ2/`. The six N families live only in the
design memo `docs/dyadic/mc-design.md` section 3.4, as a table, and the completeness argument
sketched there ("N2/N3 generate `SL_2(Z_2)` on the `(sigma, x2)` block, N4 supplies the
determinant") is unformalized. It is strictly more than the M side needed, because the M
rank-four frame has no such block.

## What is here instead

The **bridge**, which is the half that is available and is what the missing factorization would
consume. `nFullStabilizer_lift` wants the semantic predicate `NFrameCupIsometry`, which
quantifies over every continuous mod-two character of the frame, and until now the only producer
of that predicate was `mCupFrameCupIsometry_of_aut`'s N analogue, i.e. "it comes from an actual
core automorphism", precisely what one does not have for a family one is trying to lift. Here
the predicate is produced from **finite mod-two matrix data** in `N.lean`'s own column
convention:

* `nNielsenGen_coord_zero` through `nNielsenGen_coord_three`: the four mod-two frame coordinates
  of an arbitrary frame element. Unlike M, the N frame has no forced `A`-row, so these are the
  bare reductions with no `2^(alpha-1)` correction.
* `nNielsenGen_character_apply`: every continuous mod-two character of the full N frame is the
  coordinate expansion of its own values on the canonical marks.
* `nNielsenGenMat`: the reduced mod-two matrix of a frame automorphism, entry `(i, j)` being the
  `i`-th coordinate of the image of the `j`-th mark. This is exactly the shape of `NRows.mat`.
* `nNielsenGen_cup_of_mat`: `A G A^T = G` in that convention gives the semantic predicate.
* `nNielsenGen_lift_of_mat` and `nNielsenGen_lift_of_rows`: the resulting lifting criterion,
  the second stated in `NRows.IsCupIsometry` vocabulary so that a consumer holding
  `nStabilizer_classification`'s clause can feed it directly.

The orientation hypothesis is `nFrameOrientation_preserved_iff`'s concrete form: the integral
`x1` coordinate is fixed on the nose. That is stronger than M's, where only the `B` parity is
pinned; the asymmetry is the one recorded in `MFrameMatrixLift`.

Every declaration in this file is std-3 (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section

open GQ2 GQ2.SectionThree Multiplicative
open GQ2.Dyadic.EvenModel
open scoped GQ2.SectionThree.TopAbInstances

/-! ## The mod-two coordinates of the full N frame -/

private theorem nNielsenGen_nRed_val (a : ZMod 2) : nRed ((a.val : ℤ_[2])) = a := by
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) a with rfl | rfl
  · rw [show (((0 : ZMod 2).val : ℕ) : ℤ_[2]) = 0 by
      rw [show ((0 : ZMod 2).val) = 0 from rfl, Nat.cast_zero], map_zero]
  · rw [show (((1 : ZMod 2).val : ℕ) : ℤ_[2]) = 1 by
      rw [show ((1 : ZMod 2).val) = 1 from rfl, Nat.cast_one], map_one]

/-- **Every mod-two N frame coordinate, evaluated on an arbitrary frame element.** -/
theorem nNielsenGen_coord {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ) (j : Fin (coreRank h))
    (z : NFrameModel h) :
    toAdd (nFrameModTwoCoordinate ha h j z) = nRed (nFrameCoordinateSection z j) := by
  have hp : freeNFrameProjection ha h
      (freeTwoCoordinateWord (coreRank h) (nFrameCoordinateSection z)) = z := by
    change nPhiHom ha h (freeNAbProjection alpha h
      (freeTwoCoordinateWord (coreRank h) (nFrameCoordinateSection z))) = z
    rw [freeNAbProjection_coordinateWord]
    exact nPhiHom_coordinateSection ha h z
  conv_lhs => rw [← hp]
  rw [nFrameModTwoCoordinate_freeNFrameProjection, freeTwoCoordinateWord_coordinate]

theorem nNielsenGen_coord_zero {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ) (z : NFrameModel h) :
    toAdd (nFrameModTwoCoordinate ha h 0 z) = z.toAdd.1 := by
  rw [nNielsenGen_coord ha h 0 z]
  show nRed (nSurjVec _ _ _ _ _ 0) = _
  rw [nSurjVec_zero, nNielsenGen_nRed_val]

theorem nNielsenGen_coord_one {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ) (z : NFrameModel h) :
    toAdd (nFrameModTwoCoordinate ha h 1 z) = nRed z.toAdd.2.1 := by
  rw [nNielsenGen_coord ha h 1 z]
  show nRed (nSurjVec _ _ _ _ _ 1) = _
  rw [nSurjVec_one]

theorem nNielsenGen_coord_two {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ) (z : NFrameModel h) :
    toAdd (nFrameModTwoCoordinate ha h 2 z) = nRed z.toAdd.2.2.1 := by
  rw [nNielsenGen_coord ha h 2 z]
  show nRed (nSurjVec _ _ _ _ _ 2) = _
  rw [nSurjVec_two]

theorem nNielsenGen_coord_three {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ) (z : NFrameModel h) :
    toAdd (nFrameModTwoCoordinate ha h 3 z) = nRed z.toAdd.2.2.2.1 := by
  rw [nNielsenGen_coord ha h 3 z]
  show nRed (nSurjVec _ _ _ _ _ 3) = _
  rw [nSurjVec_three]

/-! ## Every continuous mod-two character is its own coordinate expansion -/

private theorem nNielsenGen_nRed_two : nRed (2 : ℤ_[2]) = 0 := by
  rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num, map_natCast]
  decide

private theorem nNielsenGen_nRed_eq (a : ℤ_[2]) :
    (((PadicInt.toZModPow (p := 2) 1 a).val : ℕ) : ZMod 2) = nRed a := by
  rcases (by decide : ∀ z : ZMod (2 ^ 1), z = 0 ∨ z = 1)
    (PadicInt.toZModPow (p := 2) 1 a) with h | h
  · have hk : (2 : ℤ_[2]) ∣ a := by
      have h0 : PadicInt.toZModPow (p := 2) 1 a = 0 := h
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton, pow_one] at h0
      exact h0
    obtain ⟨y, hy⟩ := hk
    rw [h, hy, map_mul, nNielsenGen_nRed_two, zero_mul]
    decide
  · have hk : (2 : ℤ_[2]) ∣ (a - 1) := by
      have h0 : PadicInt.toZModPow (p := 2) 1 (a - 1) = 0 := by
        rw [map_sub, map_one, h, sub_self]
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton, pow_one] at h0
      exact h0
    obtain ⟨y, hy⟩ := hk
    have ha' : a = 1 + 2 * y := by linear_combination hy
    rw [h, ha', map_add, map_one, map_mul, nNielsenGen_nRed_two, zero_mul, add_zero]
    decide

private theorem nNielsenGen_toAdd_zpowZtwo (q : Multiplicative (ZMod 2)) (a : ℤ_[2]) :
    toAdd (zpowZtwo isProP_two_multZMod2 q a) = nRed a * toAdd q := by
  have hq : ∀ z : Multiplicative (ZMod 2), z ^ 2 = 1 := by decide
  rw [zpowZtwo_of_sq_eq_one isProP_two_multZMod2 q (hq q) a]
  show (PadicInt.toZModPow 1 a).val • toAdd q = _
  rw [nsmul_eq_mul, nNielsenGen_nRed_eq]

/-- **The character expansion at N.** A continuous mod-two character of the full N frame is
determined by its values on the canonical marks, linearly in the mod-two frame coordinates. -/
theorem nNielsenGen_character_apply {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ)
    (c : ContinuousMonoidHom (NFrameModel h) (Multiplicative (ZMod 2)))
    (z : NFrameModel h) :
    toAdd (c z) = ∑ j, toAdd (nFrameModTwoCoordinate ha h j z) *
      toAdd (c (nFrameCanonicalMark ha h j)) := by
  obtain ⟨x, rfl⟩ := freeNFrameProjection_surjective ha h z
  have hx : (c.comp (freeNFrameProjection ha h)) x =
      ∏ j, zpowZtwo isProP_two_multZMod2
        ((c.comp (freeNFrameProjection ha h)) (freeTwoRankGen (coreRank h) j))
        (toAdd (freeTwoCoordinate (coreRank h) j x)) :=
    freeTwo_commutative_hom_coordinates isProP_two_multZMod2 (coreRank h) _ x
  have hgen : ∀ j, (c.comp (freeNFrameProjection ha h)) (freeTwoRankGen (coreRank h) j) =
      c (nFrameCanonicalMark ha h j) := fun j =>
    congrArg c (freeNFrameProjection_gen ha h j)
  simp only [hgen] at hx
  have hz : c (freeNFrameProjection ha h x) =
      ∏ j, zpowZtwo isProP_two_multZMod2 (c (nFrameCanonicalMark ha h j))
        (toAdd (freeTwoCoordinate (coreRank h) j x)) := hx
  rw [hz, toAdd_prod]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [nNielsenGen_toAdd_zpowZtwo, nFrameModTwoCoordinate_freeNFrameProjection ha h j x]

/-! ## The semantic cup condition from N's own reduced mod-two matrix -/

theorem nNielsenGen_evenCup_eq (v w : Fin (coreRank 0) → ZMod 2) :
    evenCupForm v w = nCupForm v w := by
  rw [evenCupForm, nCupForm]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, ← add_assoc]
  rfl

/-- **The reduced mod-two matrix of a frame automorphism, in N's own column convention**:
entry `(i, j)` is the `i`-th mod-two frame coordinate of the image of the `j`-th canonical
mark. This is exactly the shape of `N.lean`'s `NRows.mat`. -/
noncomputable def nNielsenGenMat {alpha : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0))
    (i j : Fin (coreRank 0)) : ZMod 2 :=
  toAdd (nFrameModTwoCoordinate ha 0 i (phi (nFrameCanonicalMark ha 0 j)))

private theorem nNielsenGen_cup_core (A : Fin 4 → Fin 4 → ZMod 2) (u v : Fin 4 → ZMod 2)
    (hA : ∀ i j, nCupForm (A i) (A j) = nGram i j) :
    nCupForm (fun i => ∑ j, A j i * u j) (fun i => ∑ j, A j i * v j) = nCupForm u v := by
  have h00 : nCupForm (A 0) (A 0) = 1 := hA 0 0
  have h01 : nCupForm (A 0) (A 1) = 1 := hA 0 1
  have h02 : nCupForm (A 0) (A 2) = 0 := hA 0 2
  have h03 : nCupForm (A 0) (A 3) = 0 := hA 0 3
  have h10 : nCupForm (A 1) (A 0) = 1 := hA 1 0
  have h11 : nCupForm (A 1) (A 1) = 0 := hA 1 1
  have h12 : nCupForm (A 1) (A 2) = 0 := hA 1 2
  have h13 : nCupForm (A 1) (A 3) = 0 := hA 1 3
  have h20 : nCupForm (A 2) (A 0) = 0 := hA 2 0
  have h21 : nCupForm (A 2) (A 1) = 0 := hA 2 1
  have h22 : nCupForm (A 2) (A 2) = 0 := hA 2 2
  have h23 : nCupForm (A 2) (A 3) = 1 := hA 2 3
  have h30 : nCupForm (A 3) (A 0) = 0 := hA 3 0
  have h31 : nCupForm (A 3) (A 1) = 0 := hA 3 1
  have h32 : nCupForm (A 3) (A 2) = 1 := hA 3 2
  have h33 : nCupForm (A 3) (A 3) = 0 := hA 3 3
  simp only [nCupForm, Fin.sum_univ_four] at *
  linear_combination (u 0 * v 0) * h00 + (u 0 * v 1) * h01 + (u 0 * v 2) * h02 + (u 0 *
    v 3) * h03 + (u 1 * v 0) * h10 + (u 1 * v 1) * h11 + (u 1 * v 2) * h12 + (u 1 * v 3)
    * h13 + (u 2 * v 0) * h20 + (u 2 * v 1) * h21 + (u 2 * v 2) * h22 + (u 2 * v 3) *
    h23 + (u 3 * v 0) * h30 + (u 3 * v 1) * h31 + (u 3 * v 2) * h32 + (u 3 * v 3) * h33

/-- **T1 at N.** If the reduced mod-two matrix of a continuous frame automorphism satisfies
`N.lean`'s own cup clause `A G A^T = G` (the clause of `NRows.IsCupIsometry`, in the
column-image variance), then the automorphism is a full semantic cup isometry of the actual
N frame. -/
theorem nNielsenGen_cup_of_mat {alpha : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0))
    (hmat : ∀ i j, nCupForm (nNielsenGenMat ha phi i) (nNielsenGenMat ha phi j)
      = nGram i j) :
    NFrameCupIsometry ha phi := by
  intro c d
  rw [nNielsenGen_evenCup_eq, nNielsenGen_evenCup_eq]
  have key : ∀ (e : ContinuousMonoidHom (NFrameModel 0) (Multiplicative (ZMod 2)))
      (i : Fin (coreRank 0)),
      toAdd (e (phi (nFrameCanonicalMark ha 0 i))) =
        ∑ j, nNielsenGenMat ha phi j i * toAdd (e (nFrameCanonicalMark ha 0 j)) :=
    fun e i => nNielsenGen_character_apply ha 0 e (phi (nFrameCanonicalMark ha 0 i))
  simp only [key]
  exact nNielsenGen_cup_core _ _ _ hmat

/-- **The N-side lifting criterion in matrix form.** A continuous automorphism of the actual
full rank-four N frame that fixes the integral `x1` coordinate (equivalently, by
`nFrameOrientation_preserved_iff`, preserves the canonical orientation) and whose reduced
mod-two matrix is a cup isometry in N's own variance lifts to an actual `chiN`-preserving
continuous automorphism of `D_N` with the exact all-element commuting frame square. -/
theorem nNielsenGen_lift_of_mat {alpha : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0))
    (hx1 : ∀ z : NFrameModel 0, (phi z).toAdd.2.1 = z.toAdd.2.1)
    (hmat : ∀ i j, nCupForm (nNielsenGenMat ha phi i) (nNielsenGenMat ha phi j)
      = nGram i j) :
    ∃ Psi : ContinuousMulEquiv (DN alpha 0 : Type) (DN alpha 0 : Type),
      (∀ x, chiN alpha 0 (Psi x) = chiN alpha 0 x) ∧
      (∀ x, nPhiHom ha 0 (abMk (Psi x)) = phi (nPhiHom ha 0 (abMk x))) :=
  nFullStabilizer_lift ha phi ((nFrameOrientation_preserved_iff ha 0 phi).mpr hx1)
    (nNielsenGen_cup_of_mat ha phi hmat)

/-- The same with the cup clause stated in `N.lean`'s `NRows` vocabulary, so that a consumer
holding `nStabilizer_classification`'s `IsNStab` clause can feed it directly. -/
theorem nNielsenGen_lift_of_rows {alpha : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0)) (R : NRows)
    (hx1 : ∀ z : NFrameModel 0, (phi z).toAdd.2.1 = z.toAdd.2.1)
    (hR : ∀ i j, nNielsenGenMat ha phi i j = R.mat i j)
    (hcup : R.IsCupIsometry) :
    ∃ Psi : ContinuousMulEquiv (DN alpha 0 : Type) (DN alpha 0 : Type),
      (∀ x, chiN alpha 0 (Psi x) = chiN alpha 0 x) ∧
      (∀ x, nPhiHom ha 0 (abMk (Psi x)) = phi (nPhiHom ha 0 (abMk x))) := by
  refine nNielsenGen_lift_of_mat ha phi hx1 (fun i j => ?_)
  rw [funext (hR i), funext (hR j)]
  exact hcup i j

#print axioms nNielsenGen_nRed_val
#print axioms nNielsenGen_coord
#print axioms nNielsenGen_coord_zero
#print axioms nNielsenGen_coord_one
#print axioms nNielsenGen_coord_two
#print axioms nNielsenGen_coord_three
#print axioms nNielsenGen_nRed_two
#print axioms nNielsenGen_nRed_eq
#print axioms nNielsenGen_toAdd_zpowZtwo
#print axioms nNielsenGen_character_apply
#print axioms nNielsenGen_evenCup_eq
#print axioms nNielsenGenMat
#print axioms nNielsenGen_cup_core
#print axioms nNielsenGen_cup_of_mat
#print axioms nNielsenGen_lift_of_mat
#print axioms nNielsenGen_lift_of_rows

end
end GQ2.Dyadic.MarkedCore
