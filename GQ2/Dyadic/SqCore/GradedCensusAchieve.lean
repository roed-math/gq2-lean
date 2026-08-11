/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedCensusHorn
import GQ2.Dyadic.SqCore.GradedForceSharp

/-!
# W66-ACHIEVE: the census endgame - achievability DISCHARGED

(placeholder header, rewritten at the end of the lane)
-/

open scoped commutatorElement

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The engine: one achievable killing dressing, at each of the five slots -/

section Engine

variable {R : Type} [CommRing R] {h : ℕ} {j : Fin h}

variable (h) in
/-- **The dressing carrying `w` on the `x0` slot and nothing anywhere else.**
`GradedGammaTwoCensus.censSlotU` at the second core slot instead of at a handle.  The two core
slots have no dressing family in the tree: the census reached them only through its nested
sweep, and section 2 needs one at `x0`. -/
def censAchSlotX (w : SqU6 R) : Fin (sqRank h) → SqU6 R :=
  fun i => if (i : ℕ) = 1 then w else 1

theorem censAchSlotX_isGaTwo {w : SqU6 R} (hw : w.IsGaTwo) (i : Fin (sqRank h)) :
    (censAchSlotX h w i).IsGaTwo := by
  by_cases hi : (i : ℕ) = 1
  · rw [censAchSlotX, if_pos hi]; exact hw
  · rw [censAchSlotX, if_neg hi]; exact SqU6.isGaTwo_one

theorem censAchSlotX_mem_forceLcs {H : Subgroup (SqU6 gr3R)} {w : SqU6 gr3R}
    (hw : w ∈ forceLcs H 1) (i : Fin (sqRank h)) : censAchSlotX h w i ∈ forceLcs H 1 := by
  by_cases hi : (i : ℕ) = 1
  · rw [censAchSlotX, if_pos hi]; exact hw
  · rw [censAchSlotX, if_neg hi]; exact one_mem _

/-- Dressing the `x0` slot reparametrises the marking, exactly as at the sigma slot. -/
theorem conFiveDress_fiveTuple_censAchSlotX (S X Y U V w : SqU6 R) :
    conFiveDress (fiveTuple R h j S X Y U V) (censAchSlotX h w)
      = fiveTuple R h j S (X * w) Y U V := by
  funext i
  rw [conFiveDress_apply]
  by_cases hi : (i : ℕ) = 1
  · rw [censAchSlotX, if_pos hi]
    simp only [fiveTuple, if_neg (show ¬ (i : ℕ) = 0 by omega), if_pos hi]
  · rw [censAchSlotX, if_neg hi, mul_one]
    simp only [fiveTuple, if_neg hi]

/-- The `gamma_2`-shape of a single-slot dressing at the sigma slot. -/
theorem censAch_sigDress_isGaTwo {w : SqU6 R} (hw : w.IsGaTwo) (i : Fin (sqRank h)) :
    (cenSigDress h w i).IsGaTwo := by
  by_cases hi : (i : ℕ) = 0
  · rw [cenSigDress, if_pos hi]; exact hw
  · rw [cenSigDress, if_neg hi]; exact SqU6.isGaTwo_one

end Engine

section Kill

variable {h : ℕ} {j : Fin h} {S X Y U V w : SqU6 gr3R} {c : gr3R}

/-- `liftO c * liftO (-c) = 1`: the bookkeeping of every kill in this file, once. -/
theorem censAch_liftO_neg (c : gr3R) : SqU6.liftO c * SqU6.liftO (-c) = 1 := by
  rw [SqU6.liftO_mul_liftO, add_neg_cancel]
  ext <;> simp [SqU6.liftO]

/-- ⭐⭐⭐ **THE KILL AT THE SIGMA SLOT, from an ARBITRARY achievable element.**  At a marking of
the one-handle-live family whose relator is an ODD CENTRAL translation, any achievable element
`w` whose sigma-slot dressing kills the relator outright refutes the `gamma_2` forcing, the
centrality line and the parity line at once.

⭐ This is `GradedGammaTwoCensus.cens_lines_false_of_sigKnob` with the KNOB replaced by an
arbitrary lattice element: the shift is central because the dressed relator is `1` and the
undressed one is central, so no closed form for the shift is needed.  ⚠ It is exactly the
mechanism the census measured at the `6` points where no knob is achievable and a general
lattice element kills. -/
theorem censAch_lines_false_sig
    (hres : sqWord S X Y * commP U V = SqU6.liftO c) (hodd : selPar c = 1)
    (hkill : sqWord (S * w) X Y * commP U V = 1)
    (hach : w ∈ forceLcs (Subgroup.closure (Set.range (fiveTuple gr3R h j S X Y U V))) 1) :
    ¬ GaTwoForces (fiveTuple gr3R h j S X Y U V)
      ∧ ¬ GaTwoCentral (fiveTuple gr3R h j S X Y U V)
      ∧ ¬ GaTwoOrth (fiveTuple gr3R h j S X Y U V) := by
  have hr : sqRelWord (fiveTuple gr3R h j S X Y U V) = SqU6.liftO c := by
    rw [sqRelWord_fiveTuple]; exact hres
  refine cens_lines_false_of_central_kill (g := -c) (z := cenSigDress h w) hr hodd ?_
    (by ring) (censAch_sigDress_isGaTwo (isGaTwo_of_mem_forceLcs hach))
    (fun i => cens_sigDress_mem_forceLcs hach i)
  rw [conFiveDress_fiveTuple_cenSigDress, sqRelWord_fiveTuple, hkill, hr,
    censAch_liftO_neg]

/-- ⭐⭐ **…and at the `x0` slot.**  The census's two CORE slots carry no knob - the same
dressing there disturbs the class-three and class-four rows - so this is the only route to them,
and section 2 uses it at six binder points. -/
theorem censAch_lines_false_x0
    (hres : sqWord S X Y * commP U V = SqU6.liftO c) (hodd : selPar c = 1)
    (hkill : sqWord S (X * w) Y * commP U V = 1)
    (hach : w ∈ forceLcs (Subgroup.closure (Set.range (fiveTuple gr3R h j S X Y U V))) 1) :
    ¬ GaTwoForces (fiveTuple gr3R h j S X Y U V)
      ∧ ¬ GaTwoCentral (fiveTuple gr3R h j S X Y U V)
      ∧ ¬ GaTwoOrth (fiveTuple gr3R h j S X Y U V) := by
  have hr : sqRelWord (fiveTuple gr3R h j S X Y U V) = SqU6.liftO c := by
    rw [sqRelWord_fiveTuple]; exact hres
  refine cens_lines_false_of_central_kill (g := -c) (z := censAchSlotX h w) hr hodd ?_
    (by ring) (censAchSlotX_isGaTwo (isGaTwo_of_mem_forceLcs hach))
    (fun i => censAchSlotX_mem_forceLcs hach i)
  rw [conFiveDress_fiveTuple_censAchSlotX, sqRelWord_fiveTuple, hkill, hr,
    censAch_liftO_neg]

/-- ⭐⭐ **…and at the live handle's `u` slot.** -/
theorem censAch_lines_false_u
    (hres : sqWord S X Y * commP U V = SqU6.liftO c) (hodd : selPar c = 1)
    (hkill : sqWord S X Y * commP (U * w) V = 1)
    (hach : w ∈ forceLcs (Subgroup.closure (Set.range (fiveTuple gr3R h j S X Y U V))) 1) :
    ¬ GaTwoForces (fiveTuple gr3R h j S X Y U V)
      ∧ ¬ GaTwoCentral (fiveTuple gr3R h j S X Y U V)
      ∧ ¬ GaTwoOrth (fiveTuple gr3R h j S X Y U V) := by
  have hr : sqRelWord (fiveTuple gr3R h j S X Y U V) = SqU6.liftO c := by
    rw [sqRelWord_fiveTuple]; exact hres
  refine cens_lines_false_of_central_kill (g := -c) (z := censSlotU h j w) hr hodd ?_
    (by ring) (censSlotU_isGaTwo (isGaTwo_of_mem_forceLcs hach))
    (fun i => censSlotU_mem_forceLcs hach i)
  rw [conFiveDress_fiveTuple_censSlotU, sqRelWord_fiveTuple, hkill, hr, censAch_liftO_neg]

/-- ⭐⭐ **…and at the live handle's `v` slot.** -/
theorem censAch_lines_false_v
    (hres : sqWord S X Y * commP U V = SqU6.liftO c) (hodd : selPar c = 1)
    (hkill : sqWord S X Y * commP U (V * w) = 1)
    (hach : w ∈ forceLcs (Subgroup.closure (Set.range (fiveTuple gr3R h j S X Y U V))) 1) :
    ¬ GaTwoForces (fiveTuple gr3R h j S X Y U V)
      ∧ ¬ GaTwoCentral (fiveTuple gr3R h j S X Y U V)
      ∧ ¬ GaTwoOrth (fiveTuple gr3R h j S X Y U V) := by
  have hr : sqRelWord (fiveTuple gr3R h j S X Y U V) = SqU6.liftO c := by
    rw [sqRelWord_fiveTuple]; exact hres
  refine cens_lines_false_of_central_kill (g := -c) (z := censSlotV h j w) hr hodd ?_
    (by ring) (censSlotV_isGaTwo (isGaTwo_of_mem_forceLcs hach))
    (fun i => censSlotV_mem_forceLcs hach i)
  rw [conFiveDress_fiveTuple_censSlotV, sqRelWord_fiveTuple, hkill, hr, censAch_liftO_neg]

end Kill

/-! ## 2 The census points -/

section Points

variable {h : ℕ} {j : Fin h}

variable (h j) in
/-- **A census binder point**: the DIAGONALLY dressed frame of a bare point whose sigma letter
is the committed `fiveSigMark`.  All `67` points of `scripts/w64_census5/results/census.txt`
have this shape, and at every one of them the BARE frame kills the relator outright while this
one carries an ODD CENTRAL residue. -/
def censAchPt (X Y U V : SqU6 gr3R) : Fin (sqRank h) → SqU6 gr3R :=
  fiveTuple gr3R h j (fiveSigMark gr3R * X) X Y U V

/-- The five letters of a census point lie in its own image. -/
theorem censAch_letters_mem (h : ℕ) (j : Fin h) (X Y U V : SqU6 gr3R) :
    fiveSigMark gr3R * X ∈ Subgroup.closure (Set.range (censAchPt h j X Y U V))
      ∧ X ∈ Subgroup.closure (Set.range (censAchPt h j X Y U V))
      ∧ Y ∈ Subgroup.closure (Set.range (censAchPt h j X Y U V))
      ∧ U ∈ Subgroup.closure (Set.range (censAchPt h j X Y U V))
      ∧ V ∈ Subgroup.closure (Set.range (censAchPt h j X Y U V)) :=
  ⟨Subgroup.subset_closure ⟨0, by rw [censAchPt, fiveTuple_zero]⟩,
    Subgroup.subset_closure ⟨1, by rw [censAchPt, fiveTuple_one]⟩,
    Subgroup.subset_closure ⟨2, by rw [censAchPt, fiveTuple_two]⟩,
    Subgroup.subset_closure ⟨sqHandleIdxU j, by rw [censAchPt, fiveTuple_handleU]⟩,
    Subgroup.subset_closure ⟨sqHandleIdxV j, by rw [censAchPt, fiveTuple_handleV]⟩⟩

/- ⚠ **The one budget setting in this file**, and it is NOT a heartbeat bump: the `decide`
calls below evaluate the core word at a concrete marking with a commutator word substituted
into one slot, and the default recursion depth of `512` does not reach the bottom of that
unfolding.  Nothing here raises `maxHeartbeats`, which the census file family carries at
`400000`. -/
set_option maxRecDepth 8000

/-! ### The letters -/

/-- The `x0` letter `<a = 2, e = 1>`, one of the census's live `x0` letters. -/
def censAchX21 : SqU6 gr3R := ⟨2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `x0` letter `<a = 2, e = 3>`, one of the census's live `x0` letters. -/
def censAchX23 : SqU6 gr3R := ⟨2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `x0` letter `<a = 2, e = 5>`, one of the census's live `x0` letters. -/
def censAchX25 : SqU6 gr3R := ⟨2, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `x0` letter `<a = 2, e = 7>`, one of the census's live `x0` letters. -/
def censAchX27 : SqU6 gr3R := ⟨2, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `x0` letter `<a = 6, e = 1>`, one of the census's live `x0` letters. -/
def censAchX61 : SqU6 gr3R := ⟨6, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `x0` letter `<a = 6, e = 3>`, one of the census's live `x0` letters. -/
def censAchX63 : SqU6 gr3R := ⟨6, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `x0` letter `<a = 6, e = 5>`, one of the census's live `x0` letters. -/
def censAchX65 : SqU6 gr3R := ⟨6, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `x0` letter `<a = 6, e = 7>`, one of the census's live `x0` letters. -/
def censAchX67 : SqU6 gr3R := ⟨6, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `x0` letter `<a = 4, e = 5>`, one of the census's live `x0` letters. -/
def censAchX45 : SqU6 gr3R := ⟨4, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The `u` letter of FRESH handle triple 1 (`scripts/w64_census5/results/triples.txt`). -/
def censAchU1 : SqU6 gr3R := ⟨2, 6, 4, 5, 1, 5, 3, 5, 0, 3, 6, 7, 5, 0, 4⟩

/-- The `v` letter of FRESH handle triple 1. -/
def censAchV1 : SqU6 gr3R := ⟨0, 0, 6, 7, 1, 1, 5, 1, 4, 6, 2, 6, 3, 4, 3⟩

/-- The `u` letter of FRESH handle triple 2 (`scripts/w64_census5/results/triples.txt`). -/
def censAchU2 : SqU6 gr3R := ⟨0, 3, 2, 1, 4, 2, 1, 3, 2, 7, 3, 6, 4, 2, 7⟩

/-- The `v` letter of FRESH handle triple 2. -/
def censAchV2 : SqU6 gr3R := ⟨6, 4, 4, 1, 6, 1, 0, 5, 5, 3, 3, 5, 3, 5, 3⟩

/-- The `u` letter of FRESH handle triple 3 (`scripts/w64_census5/results/triples.txt`). -/
def censAchU3 : SqU6 gr3R := ⟨6, 4, 6, 7, 7, 6, 0, 4, 5, 7, 1, 7, 4, 7, 2⟩

/-- The `v` letter of FRESH handle triple 3. -/
def censAchV3 : SqU6 gr3R := ⟨2, 4, 0, 5, 1, 3, 6, 2, 7, 0, 1, 0, 7, 1, 3⟩

/-! ### The `67` points, one theorem each -/

/-- ⭐ **Census point 1 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `1`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_01 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j stageX stageY stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j stageX stageY stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j stageX stageY stageU stageV) := by
  have L := censAch_letters_mem h j stageX stageY stageU stageV
  exact censAch_lines_false_sig (c := 1)
    (w := commP stageU stageY⁻¹ * commP stageV stageY)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.2.1 (Subgroup.inv_mem _ L.2.2.1))
      (commP_mem_commSub L.2.2.2.2 L.2.2.1))

/-- The `x1` letter of census point 2. -/
def censAchY02 : SqU6 gr3R := ⟨4, 4, 4, 4, 6, 1, 1, 5, 0, 0, 0, 2, 1, 1, 5⟩

/-- ⭐ **Census point 2 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `5`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_02 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX21 censAchY02 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX21 censAchY02 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX21 censAchY02 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX21 censAchY02 stageU stageV
  exact censAch_lines_false_sig (c := 5)
    (w := commP censAchY02 stageU * commP censAchY02⁻¹ stageV)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.1)
      (commP_mem_commSub (Subgroup.inv_mem _ L.2.2.1) L.2.2.2.2))

/-- The `x1` letter of census point 3. -/
def censAchY03 : SqU6 gr3R := ⟨4, 4, 4, 4, 6, 1, 1, 5, 0, 0, 0, 2, 1, 1, 1⟩

/-- ⭐ **Census point 3 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `5`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_03 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX21 censAchY03 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX21 censAchY03 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX21 censAchY03 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX21 censAchY03 stageU stageV
  exact censAch_lines_false_sig (c := 5)
    (w := commP censAchY03 stageU * commP censAchY03⁻¹ stageV)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.1)
      (commP_mem_commSub (Subgroup.inv_mem _ L.2.2.1) L.2.2.2.2))

/-- The `x1` letter of census point 4. -/
def censAchY04 : SqU6 gr3R := ⟨4, 4, 4, 4, 6, 1, 1, 5, 0, 0, 0, 2, 1, 5, 1⟩

/-- ⭐ **Census point 4 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `5`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_04 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX21 censAchY04 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX21 censAchY04 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX21 censAchY04 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX21 censAchY04 stageU stageV
  exact censAch_lines_false_sig (c := 5)
    (w := commP censAchY04 stageU * commP censAchY04⁻¹ stageV)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.1)
      (commP_mem_commSub (Subgroup.inv_mem _ L.2.2.1) L.2.2.2.2))

/-- The `x1` letter of census point 5. -/
def censAchY05 : SqU6 gr3R := ⟨4, 4, 4, 4, 6, 1, 1, 5, 0, 0, 0, 2, 1, 5, 5⟩

/-- ⭐ **Census point 5 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `5`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_05 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX21 censAchY05 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX21 censAchY05 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX21 censAchY05 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX21 censAchY05 stageU stageV
  exact censAch_lines_false_sig (c := 5)
    (w := commP censAchY05 stageU * commP censAchY05⁻¹ stageV)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.1)
      (commP_mem_commSub (Subgroup.inv_mem _ L.2.2.1) L.2.2.2.2))

/-- The `x1` letter of census point 6. -/
def censAchY06 : SqU6 gr3R := ⟨4, 4, 4, 4, 6, 5, 1, 5, 0, 0, 4, 2, 7, 1, 7⟩

/-- ⭐ **Census point 6 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `1`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_06 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX21 censAchY06 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX21 censAchY06 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX21 censAchY06 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX21 censAchY06 stageU stageV
  exact censAch_lines_false_sig (c := 1)
    (w := commP censAchY06 stageU * commP stageV censAchY06)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.1) (commP_mem_commSub L.2.2.2.2 L.2.2.1))

/-- The `x1` letter of census point 7. -/
def censAchY07 : SqU6 gr3R := ⟨4, 4, 4, 4, 6, 5, 1, 5, 0, 0, 4, 2, 7, 1, 3⟩

/-- ⭐ **Census point 7 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `1`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_07 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX21 censAchY07 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX21 censAchY07 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX21 censAchY07 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX21 censAchY07 stageU stageV
  exact censAch_lines_false_sig (c := 1)
    (w := commP censAchY07 stageU * commP stageV censAchY07)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.1) (commP_mem_commSub L.2.2.2.2 L.2.2.1))

/-- The `x1` letter of census point 8. -/
def censAchY08 : SqU6 gr3R := ⟨4, 4, 4, 4, 6, 5, 5, 5, 0, 4, 0, 2, 3, 5, 7⟩

/-- ⭐ **Census point 8 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_08 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX23 censAchY08 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX23 censAchY08 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX23 censAchY08 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX23 censAchY08 stageU stageV
  exact censAch_lines_false_sig (c := 3)
    (w := commP censAchY08 stageU * commP stageV censAchY08)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.1) (commP_mem_commSub L.2.2.2.2 L.2.2.1))

/-- The `x1` letter of census point 9. -/
def censAchY09 : SqU6 gr3R := ⟨4, 4, 4, 4, 6, 5, 5, 5, 0, 4, 0, 2, 3, 5, 3⟩

/-- ⭐ **Census point 9 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_09 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX23 censAchY09 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX23 censAchY09 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX23 censAchY09 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX23 censAchY09 stageU stageV
  exact censAch_lines_false_sig (c := 3)
    (w := commP censAchY09 stageU * commP stageV censAchY09)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.1) (commP_mem_commSub L.2.2.2.2 L.2.2.1))

/-- The `x1` letter of census point 10. -/
def censAchY10 : SqU6 gr3R := ⟨4, 4, 4, 4, 6, 5, 5, 5, 0, 0, 4, 6, 3, 1, 1⟩

/-- ⭐ **Census point 10 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_10 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX23 censAchY10 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX23 censAchY10 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX23 censAchY10 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX23 censAchY10 stageU stageV
  exact censAch_lines_false_sig (c := 3)
    (w := commP stageV censAchY10 * commP censAchY10 stageU)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.2.2 L.2.2.1) (commP_mem_commSub L.2.2.1 L.2.2.2.1))

/-- The `x1` letter of census point 11. -/
def censAchY11 : SqU6 gr3R := ⟨4, 4, 4, 4, 6, 5, 5, 5, 0, 0, 4, 6, 3, 1, 5⟩

/-- ⭐ **Census point 11 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_11 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX23 censAchY11 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX23 censAchY11 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX23 censAchY11 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX23 censAchY11 stageU stageV
  exact censAch_lines_false_sig (c := 3)
    (w := commP stageV censAchY11 * commP censAchY11 stageU)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.2.2 L.2.2.1) (commP_mem_commSub L.2.2.1 L.2.2.2.1))

/-- The `x1` letter of census point 12. -/
def censAchY12 : SqU6 gr3R := ⟨4, 4, 4, 4, 6, 5, 5, 5, 0, 0, 4, 6, 7, 5, 5⟩

/-- ⭐ **Census point 12 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_12 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX23 censAchY12 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX23 censAchY12 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX23 censAchY12 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX23 censAchY12 stageU stageV
  exact censAch_lines_false_sig (c := 3)
    (w := commP stageV censAchY12 * commP censAchY12 stageU)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.2.2 L.2.2.1) (commP_mem_commSub L.2.2.1 L.2.2.2.1))

/-- The `x1` letter of census point 13. -/
def censAchY13 : SqU6 gr3R := ⟨4, 4, 4, 4, 6, 5, 5, 5, 0, 0, 4, 6, 7, 5, 1⟩

/-- ⭐ **Census point 13 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_13 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX23 censAchY13 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX23 censAchY13 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX23 censAchY13 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX23 censAchY13 stageU stageV
  exact censAch_lines_false_sig (c := 3)
    (w := commP stageV censAchY13 * commP censAchY13 stageU)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.2.2 L.2.2.1) (commP_mem_commSub L.2.2.1 L.2.2.2.1))

/-- The `x1` letter of census point 14. -/
def censAchY14 : SqU6 gr3R := ⟨4, 4, 4, 4, 6, 5, 5, 1, 0, 4, 0, 6, 1, 1, 3⟩

/-- ⭐ **Census point 14 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `1`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_14 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX25 censAchY14 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX25 censAchY14 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX25 censAchY14 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX25 censAchY14 stageU stageV
  exact censAch_lines_false_sig (c := 1)
    (w := commP censAchY14 stageU * commP stageV censAchY14)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.1) (commP_mem_commSub L.2.2.2.2 L.2.2.1))

/-- The `x1` letter of census point 15. -/
def censAchY15 : SqU6 gr3R := ⟨4, 4, 4, 4, 6, 5, 5, 1, 0, 4, 0, 6, 1, 1, 7⟩

/-- ⭐ **Census point 15 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `1`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_15 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX25 censAchY15 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX25 censAchY15 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX25 censAchY15 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX25 censAchY15 stageU stageV
  exact censAch_lines_false_sig (c := 1)
    (w := commP censAchY15 stageU * commP stageV censAchY15)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.1) (commP_mem_commSub L.2.2.2.2 L.2.2.1))

/-- The `x1` letter of census point 16. -/
def censAchY16 : SqU6 gr3R := ⟨4, 4, 4, 4, 6, 5, 5, 1, 0, 4, 0, 6, 5, 1, 3⟩

/-- ⭐ **Census point 16 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `1`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_16 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX25 censAchY16 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX25 censAchY16 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX25 censAchY16 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX25 censAchY16 stageU stageV
  exact censAch_lines_false_sig (c := 1)
    (w := commP censAchY16 stageU * commP stageV censAchY16)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.1) (commP_mem_commSub L.2.2.2.2 L.2.2.1))

/-- The `x1` letter of census point 17. -/
def censAchY17 : SqU6 gr3R := ⟨4, 4, 4, 4, 6, 5, 5, 1, 0, 4, 0, 6, 5, 1, 7⟩

/-- ⭐ **Census point 17 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `1`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_17 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX25 censAchY17 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX25 censAchY17 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX25 censAchY17 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX25 censAchY17 stageU stageV
  exact censAch_lines_false_sig (c := 1)
    (w := commP censAchY17 stageU * commP stageV censAchY17)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.1) (commP_mem_commSub L.2.2.2.2 L.2.2.1))

/-- The `x1` letter of census point 18. -/
def censAchY18 : SqU6 gr3R := ⟨4, 4, 4, 4, 2, 1, 1, 1, 4, 0, 4, 0, 3, 1, 2⟩

/-- ⭐ **Census point 18 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `5`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_18 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX25 censAchY18 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX25 censAchY18 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX25 censAchY18 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX25 censAchY18 stageU stageV
  exact censAch_lines_false_sig (c := 5)
    (w := commP stageV censAchY18 * commP stageU censAchY18⁻¹)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.2.2 L.2.2.1)
      (commP_mem_commSub L.2.2.2.1 (Subgroup.inv_mem _ L.2.2.1)))

/-- The `x1` letter of census point 19. -/
def censAchY19 : SqU6 gr3R := ⟨4, 4, 4, 4, 2, 1, 1, 1, 4, 0, 4, 0, 3, 1, 6⟩

/-- ⭐ **Census point 19 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `5`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_19 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX25 censAchY19 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX25 censAchY19 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX25 censAchY19 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX25 censAchY19 stageU stageV
  exact censAch_lines_false_sig (c := 5)
    (w := commP stageV censAchY19 * commP stageU censAchY19⁻¹)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.2.2 L.2.2.1)
      (commP_mem_commSub L.2.2.2.1 (Subgroup.inv_mem _ L.2.2.1)))

/-- The `x1` letter of census point 20. -/
def censAchY20 : SqU6 gr3R := ⟨0, 4, 4, 4, 2, 5, 1, 5, 0, 2, 4, 0, 3, 3, 0⟩

/-- ⭐ **Census point 20 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_20 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX27 censAchY20 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX27 censAchY20 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX27 censAchY20 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX27 censAchY20 stageU stageV
  exact censAch_lines_false_sig (c := 3)
    (w := commP stageU⁻¹ censAchY20 * commP stageV censAchY20)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub (Subgroup.inv_mem _ L.2.2.2.1) L.2.2.1)
      (commP_mem_commSub L.2.2.2.2 L.2.2.1))

/-- The `x1` letter of census point 21. -/
def censAchY21 : SqU6 gr3R := ⟨0, 4, 4, 4, 2, 5, 1, 5, 0, 2, 4, 0, 3, 3, 4⟩

/-- ⭐ **Census point 21 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_21 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX27 censAchY21 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX27 censAchY21 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX27 censAchY21 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX27 censAchY21 stageU stageV
  exact censAch_lines_false_sig (c := 3)
    (w := commP stageU⁻¹ censAchY21 * commP stageV censAchY21)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub (Subgroup.inv_mem _ L.2.2.2.1) L.2.2.1)
      (commP_mem_commSub L.2.2.2.2 L.2.2.1))

/-- The `x1` letter of census point 22. -/
def censAchY22 : SqU6 gr3R := ⟨0, 4, 4, 4, 2, 5, 1, 5, 0, 2, 4, 0, 3, 7, 4⟩

/-- ⭐ **Census point 22 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_22 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX27 censAchY22 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX27 censAchY22 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX27 censAchY22 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX27 censAchY22 stageU stageV
  exact censAch_lines_false_sig (c := 3)
    (w := commP stageU⁻¹ censAchY22 * commP stageV censAchY22)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub (Subgroup.inv_mem _ L.2.2.2.1) L.2.2.1)
      (commP_mem_commSub L.2.2.2.2 L.2.2.1))

/-- The `x1` letter of census point 23. -/
def censAchY23 : SqU6 gr3R := ⟨0, 4, 4, 4, 2, 5, 1, 5, 0, 2, 4, 0, 3, 7, 0⟩

/-- ⭐ **Census point 23 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_23 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX27 censAchY23 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX27 censAchY23 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX27 censAchY23 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX27 censAchY23 stageU stageV
  exact censAch_lines_false_sig (c := 3)
    (w := commP stageU⁻¹ censAchY23 * commP stageV censAchY23)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub (Subgroup.inv_mem _ L.2.2.2.1) L.2.2.1)
      (commP_mem_commSub L.2.2.2.2 L.2.2.1))

/-- The `x1` letter of census point 24. -/
def censAchY24 : SqU6 gr3R := ⟨0, 4, 4, 4, 2, 5, 1, 5, 0, 2, 0, 4, 7, 7, 2⟩

/-- ⭐ **Census point 24 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_24 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX27 censAchY24 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX27 censAchY24 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX27 censAchY24 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX27 censAchY24 stageU stageV
  exact censAch_lines_false_sig (c := 3)
    (w := commP stageV censAchY24 * commP stageU⁻¹ censAchY24)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.2.2 L.2.2.1)
      (commP_mem_commSub (Subgroup.inv_mem _ L.2.2.2.1) L.2.2.1))

/-- The `x1` letter of census point 25. -/
def censAchY25 : SqU6 gr3R := ⟨0, 4, 4, 4, 2, 5, 1, 5, 0, 2, 0, 4, 7, 7, 6⟩

/-- ⭐ **Census point 25 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_25 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX27 censAchY25 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX27 censAchY25 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX27 censAchY25 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX27 censAchY25 stageU stageV
  exact censAch_lines_false_sig (c := 3)
    (w := commP stageV censAchY25 * commP stageU⁻¹ censAchY25)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.2.2 L.2.2.1)
      (commP_mem_commSub (Subgroup.inv_mem _ L.2.2.2.1) L.2.2.1))

/-- The `x1` letter of census point 26. -/
def censAchY26 : SqU6 gr3R := ⟨4, 0, 0, 0, 2, 7, 1, 1, 4, 2, 4, 0, 4, 5, 1⟩

/-- ⭐ **Census point 26 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `7`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_26 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX61 censAchY26 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX61 censAchY26 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX61 censAchY26 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX61 censAchY26 stageU stageV
  exact censAch_lines_false_sig (c := 7)
    (w := commP censAchY26 stageU⁻¹ * commP censAchY26 stageV)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 (Subgroup.inv_mem _ L.2.2.2.1))
      (commP_mem_commSub L.2.2.1 L.2.2.2.2))

/-- The `x1` letter of census point 27. -/
def censAchY27 : SqU6 gr3R := ⟨4, 0, 0, 0, 2, 7, 1, 1, 4, 2, 4, 0, 4, 5, 5⟩

/-- ⭐ **Census point 27 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `7`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_27 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX61 censAchY27 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX61 censAchY27 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX61 censAchY27 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX61 censAchY27 stageU stageV
  exact censAch_lines_false_sig (c := 7)
    (w := commP censAchY27 stageU⁻¹ * commP censAchY27 stageV)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 (Subgroup.inv_mem _ L.2.2.2.1))
      (commP_mem_commSub L.2.2.1 L.2.2.2.2))

/-- The `x1` letter of census point 28. -/
def censAchY28 : SqU6 gr3R := ⟨4, 0, 0, 0, 2, 7, 1, 1, 4, 6, 4, 4, 0, 5, 7⟩

/-- ⭐ **Census point 28 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `7`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_28 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX61 censAchY28 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX61 censAchY28 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX61 censAchY28 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX61 censAchY28 stageU stageV
  exact censAch_lines_false_sig (c := 7)
    (w := commP censAchY28 stageU⁻¹ * commP censAchY28 stageV)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 (Subgroup.inv_mem _ L.2.2.2.1))
      (commP_mem_commSub L.2.2.1 L.2.2.2.2))

/-- The `x1` letter of census point 29. -/
def censAchY29 : SqU6 gr3R := ⟨4, 0, 0, 0, 2, 7, 1, 1, 4, 6, 4, 4, 0, 5, 3⟩

/-- ⭐ **Census point 29 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `7`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_29 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX61 censAchY29 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX61 censAchY29 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX61 censAchY29 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX61 censAchY29 stageU stageV
  exact censAch_lines_false_sig (c := 7)
    (w := commP censAchY29 stageU⁻¹ * commP censAchY29 stageV)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 (Subgroup.inv_mem _ L.2.2.2.1))
      (commP_mem_commSub L.2.2.1 L.2.2.2.2))

/-- The `x1` letter of census point 30. -/
def censAchY30 : SqU6 gr3R := ⟨4, 0, 0, 0, 2, 7, 1, 1, 4, 2, 4, 0, 4, 1, 5⟩

/-- ⭐ **Census point 30 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `7`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_30 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX61 censAchY30 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX61 censAchY30 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX61 censAchY30 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX61 censAchY30 stageU stageV
  exact censAch_lines_false_sig (c := 7)
    (w := commP censAchY30 stageU⁻¹ * commP censAchY30 stageV)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 (Subgroup.inv_mem _ L.2.2.2.1))
      (commP_mem_commSub L.2.2.1 L.2.2.2.2))

/-- The `x1` letter of census point 31. -/
def censAchY31 : SqU6 gr3R := ⟨4, 0, 0, 0, 2, 7, 1, 1, 4, 2, 4, 0, 4, 1, 1⟩

/-- ⭐ **Census point 31 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `7`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_31 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX61 censAchY31 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX61 censAchY31 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX61 censAchY31 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX61 censAchY31 stageU stageV
  exact censAch_lines_false_sig (c := 7)
    (w := commP censAchY31 stageU⁻¹ * commP censAchY31 stageV)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 (Subgroup.inv_mem _ L.2.2.2.1))
      (commP_mem_commSub L.2.2.1 L.2.2.2.2))

/-- The `x1` letter of census point 32. -/
def censAchY32 : SqU6 gr3R := ⟨0, 0, 0, 0, 6, 7, 5, 5, 0, 4, 0, 6, 2, 1, 0⟩

/-- ⭐ **Census point 32 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `5`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_32 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX63 censAchY32 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX63 censAchY32 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX63 censAchY32 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX63 censAchY32 stageU stageV
  exact censAch_lines_false_sig (c := 5)
    (w := commP censAchY32 stageV * commP stageU censAchY32)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.2) (commP_mem_commSub L.2.2.2.1 L.2.2.1))

/-- The `x1` letter of census point 33. -/
def censAchY33 : SqU6 gr3R := ⟨0, 0, 0, 0, 6, 7, 5, 5, 0, 4, 0, 6, 2, 1, 4⟩

/-- ⭐ **Census point 33 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `5`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_33 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX63 censAchY33 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX63 censAchY33 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX63 censAchY33 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX63 censAchY33 stageU stageV
  exact censAch_lines_false_sig (c := 5)
    (w := commP censAchY33 stageV * commP stageU censAchY33)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.2) (commP_mem_commSub L.2.2.2.1 L.2.2.1))

/-- The `x1` letter of census point 34. -/
def censAchY34 : SqU6 gr3R := ⟨0, 0, 0, 0, 6, 3, 5, 1, 4, 0, 4, 6, 6, 3, 4⟩

/-- ⭐ **Census point 34 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `5`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_34 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX63 censAchY34 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX63 censAchY34 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX63 censAchY34 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX63 censAchY34 stageU stageV
  exact censAch_lines_false_sig (c := 5)
    (w := commP censAchY34 stageU * commP censAchY34 stageV⁻¹)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.1)
      (commP_mem_commSub L.2.2.1 (Subgroup.inv_mem _ L.2.2.2.2)))

/-- The `x1` letter of census point 35. -/
def censAchY35 : SqU6 gr3R := ⟨0, 0, 0, 0, 6, 3, 5, 1, 4, 0, 4, 6, 6, 3, 0⟩

/-- ⭐ **Census point 35 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `5`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_35 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX63 censAchY35 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX63 censAchY35 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX63 censAchY35 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX63 censAchY35 stageU stageV
  exact censAch_lines_false_sig (c := 5)
    (w := commP censAchY35 stageU * commP censAchY35 stageV⁻¹)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.1)
      (commP_mem_commSub L.2.2.1 (Subgroup.inv_mem _ L.2.2.2.2)))

/-- The `x1` letter of census point 36. -/
def censAchY36 : SqU6 gr3R := ⟨0, 0, 0, 0, 6, 3, 5, 1, 4, 4, 0, 6, 6, 3, 0⟩

/-- ⭐ **Census point 36 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `5`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_36 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX63 censAchY36 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX63 censAchY36 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX63 censAchY36 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX63 censAchY36 stageU stageV
  exact censAch_lines_false_sig (c := 5)
    (w := commP censAchY36 stageV⁻¹ * commP censAchY36 stageU)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 (Subgroup.inv_mem _ L.2.2.2.2))
      (commP_mem_commSub L.2.2.1 L.2.2.2.1))

/-- The `x1` letter of census point 37. -/
def censAchY37 : SqU6 gr3R := ⟨0, 0, 0, 0, 6, 3, 5, 1, 4, 4, 0, 6, 6, 3, 4⟩

/-- ⭐ **Census point 37 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `5`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_37 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX63 censAchY37 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX63 censAchY37 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX63 censAchY37 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX63 censAchY37 stageU stageV
  exact censAch_lines_false_sig (c := 5)
    (w := commP censAchY37 stageV⁻¹ * commP censAchY37 stageU)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 (Subgroup.inv_mem _ L.2.2.2.2))
      (commP_mem_commSub L.2.2.1 L.2.2.2.1))

/-- The `x1` letter of census point 38. -/
def censAchY38 : SqU6 gr3R := ⟨4, 4, 4, 4, 2, 7, 1, 1, 0, 4, 0, 4, 0, 3, 3⟩

/-- ⭐ **Census point 38 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_38 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX65 censAchY38 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX65 censAchY38 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX65 censAchY38 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX65 censAchY38 stageU stageV
  exact censAch_lines_false_sig (c := 3)
    (w := commP censAchY38 stageV * commP stageU censAchY38)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.2) (commP_mem_commSub L.2.2.2.1 L.2.2.1))

/-- The `x1` letter of census point 39. -/
def censAchY39 : SqU6 gr3R := ⟨4, 4, 4, 4, 2, 7, 1, 1, 0, 4, 0, 4, 0, 3, 7⟩

/-- ⭐ **Census point 39 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_39 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX65 censAchY39 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX65 censAchY39 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX65 censAchY39 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX65 censAchY39 stageU stageV
  exact censAch_lines_false_sig (c := 3)
    (w := commP censAchY39 stageV * commP stageU censAchY39)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.2) (commP_mem_commSub L.2.2.2.1 L.2.2.1))

/-- The `x1` letter of census point 40. -/
def censAchY40 : SqU6 gr3R := ⟨4, 4, 4, 4, 2, 7, 5, 5, 0, 0, 4, 0, 6, 7, 3⟩

/-- ⭐ **Census point 40 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `7`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_40 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX65 censAchY40 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX65 censAchY40 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX65 censAchY40 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX65 censAchY40 stageU stageV
  exact censAch_lines_false_sig (c := 7)
    (w := commP censAchY40 stageV * commP stageU censAchY40)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.2) (commP_mem_commSub L.2.2.2.1 L.2.2.1))

/-- The `x1` letter of census point 41. -/
def censAchY41 : SqU6 gr3R := ⟨4, 4, 4, 4, 2, 7, 5, 5, 0, 0, 4, 0, 6, 7, 7⟩

/-- ⭐ **Census point 41 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `7`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_41 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX65 censAchY41 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX65 censAchY41 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX65 censAchY41 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX65 censAchY41 stageU stageV
  exact censAch_lines_false_sig (c := 7)
    (w := commP censAchY41 stageV * commP stageU censAchY41)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.2) (commP_mem_commSub L.2.2.2.1 L.2.2.1))

/-- The `x1` letter of census point 42. -/
def censAchY42 : SqU6 gr3R := ⟨4, 4, 4, 4, 2, 7, 1, 1, 0, 4, 0, 4, 4, 3, 3⟩

/-- ⭐ **Census point 42 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_42 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX65 censAchY42 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX65 censAchY42 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX65 censAchY42 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX65 censAchY42 stageU stageV
  exact censAch_lines_false_sig (c := 3)
    (w := commP censAchY42 stageV * commP stageU censAchY42)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.2) (commP_mem_commSub L.2.2.2.1 L.2.2.1))

/-- The `x1` letter of census point 43. -/
def censAchY43 : SqU6 gr3R := ⟨4, 4, 4, 4, 2, 7, 1, 1, 0, 4, 0, 4, 4, 3, 7⟩

/-- ⭐ **Census point 43 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_43 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX65 censAchY43 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX65 censAchY43 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX65 censAchY43 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX65 censAchY43 stageU stageV
  exact censAch_lines_false_sig (c := 3)
    (w := commP censAchY43 stageV * commP stageU censAchY43)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.2) (commP_mem_commSub L.2.2.2.1 L.2.2.1))

/-- The `x1` letter of census point 44. -/
def censAchY44 : SqU6 gr3R := ⟨0, 0, 4, 0, 2, 3, 5, 1, 0, 6, 0, 4, 6, 7, 3⟩

/-- ⭐ **Census point 44 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `1`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_44 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX67 censAchY44 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX67 censAchY44 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX67 censAchY44 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX67 censAchY44 stageU stageV
  exact censAch_lines_false_sig (c := 1)
    (w := commP censAchY44 stageV * commP stageU censAchY44)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.2) (commP_mem_commSub L.2.2.2.1 L.2.2.1))

/-- The `x1` letter of census point 45. -/
def censAchY45 : SqU6 gr3R := ⟨0, 0, 4, 0, 2, 3, 5, 1, 0, 6, 0, 4, 6, 7, 7⟩

/-- ⭐ **Census point 45 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `1`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_45 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX67 censAchY45 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX67 censAchY45 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX67 censAchY45 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX67 censAchY45 stageU stageV
  exact censAch_lines_false_sig (c := 1)
    (w := commP censAchY45 stageV * commP stageU censAchY45)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.2) (commP_mem_commSub L.2.2.2.1 L.2.2.1))

/-- The `x1` letter of census point 46. -/
def censAchY46 : SqU6 gr3R := ⟨0, 4, 0, 4, 2, 3, 5, 1, 4, 4, 0, 4, 6, 5, 3⟩

/-- ⭐ **Census point 46 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `1`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_46 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX67 censAchY46 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX67 censAchY46 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX67 censAchY46 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX67 censAchY46 stageU stageV
  exact censAch_lines_false_sig (c := 1)
    (w := commP censAchY46 stageV⁻¹ * commP censAchY46 stageU)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 (Subgroup.inv_mem _ L.2.2.2.2))
      (commP_mem_commSub L.2.2.1 L.2.2.2.1))

/-- The `x1` letter of census point 47. -/
def censAchY47 : SqU6 gr3R := ⟨0, 4, 0, 4, 2, 3, 5, 1, 4, 4, 0, 4, 6, 5, 7⟩

/-- ⭐ **Census point 47 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `1`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_47 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX67 censAchY47 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX67 censAchY47 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX67 censAchY47 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX67 censAchY47 stageU stageV
  exact censAch_lines_false_sig (c := 1)
    (w := commP censAchY47 stageV⁻¹ * commP censAchY47 stageU)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 (Subgroup.inv_mem _ L.2.2.2.2))
      (commP_mem_commSub L.2.2.1 L.2.2.2.1))

/-- The `x1` letter of census point 48. -/
def censAchY48 : SqU6 gr3R := ⟨0, 4, 0, 4, 6, 3, 5, 5, 4, 4, 0, 2, 0, 7, 4⟩

/-- ⭐ **Census point 48 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `5`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_48 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX67 censAchY48 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX67 censAchY48 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX67 censAchY48 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX67 censAchY48 stageU stageV
  exact censAch_lines_false_sig (c := 5)
    (w := commP censAchY48 stageV⁻¹ * commP censAchY48 stageU)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 (Subgroup.inv_mem _ L.2.2.2.2))
      (commP_mem_commSub L.2.2.1 L.2.2.2.1))

/-- The `x1` letter of census point 49. -/
def censAchY49 : SqU6 gr3R := ⟨0, 4, 0, 4, 6, 3, 5, 5, 4, 4, 0, 2, 0, 7, 0⟩

/-- ⭐ **Census point 49 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `5`, lattice `2^26`, sigma knob achievable. -/
theorem censAch_kill_49 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX67 censAchY49 stageU stageV)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX67 censAchY49 stageU stageV)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX67 censAchY49 stageU stageV) := by
  have L := censAch_letters_mem h j censAchX67 censAchY49 stageU stageV
  exact censAch_lines_false_sig (c := 5)
    (w := commP censAchY49 stageV⁻¹ * commP censAchY49 stageU)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 (Subgroup.inv_mem _ L.2.2.2.2))
      (commP_mem_commSub L.2.2.1 L.2.2.2.1))

/-- The `x1` letter of census point 56. -/
def censAchY56 : SqU6 gr3R := ⟨0, 0, 4, 4, 6, 7, 6, 1, 7, 2, 3, 5, 7, 3, 6⟩

/-- ⭐ **Census point 56 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the `x0` slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^25`, sigma knob NOT achievable. -/
theorem censAch_kill_56 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX45 censAchY56 censAchU2 censAchV2)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX45 censAchY56 censAchU2 censAchV2)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX45 censAchY56 censAchU2 censAchV2) := by
  have L := censAch_letters_mem h j censAchX45 censAchY56 censAchU2 censAchV2
  exact censAch_lines_false_x0 (c := 3)
    (w := commP censAchX45 censAchY56 * commP censAchY56 censAchU2⁻¹)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.1 L.2.2.1)
      (commP_mem_commSub L.2.2.1 (Subgroup.inv_mem _ L.2.2.2.1)))

/-- The `x1` letter of census point 57. -/
def censAchY57 : SqU6 gr3R := ⟨0, 0, 4, 4, 6, 7, 6, 1, 7, 2, 3, 5, 7, 3, 2⟩

/-- ⭐ **Census point 57 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the `x0` slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^25`, sigma knob NOT achievable. -/
theorem censAch_kill_57 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX45 censAchY57 censAchU2 censAchV2)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX45 censAchY57 censAchU2 censAchV2)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX45 censAchY57 censAchU2 censAchV2) := by
  have L := censAch_letters_mem h j censAchX45 censAchY57 censAchU2 censAchV2
  exact censAch_lines_false_x0 (c := 3)
    (w := commP censAchX45 censAchY57 * commP censAchY57 censAchU2⁻¹)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.1 L.2.2.1)
      (commP_mem_commSub L.2.2.1 (Subgroup.inv_mem _ L.2.2.2.1)))

/-- The `x1` letter of census point 58. -/
def censAchY58 : SqU6 gr3R := ⟨0, 0, 4, 0, 2, 3, 2, 5, 7, 2, 7, 3, 3, 5, 1⟩

/-- ⭐ **Census point 58 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the `x0` slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^25`, sigma knob NOT achievable. -/
theorem censAch_kill_58 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX45 censAchY58 censAchU2 censAchV2)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX45 censAchY58 censAchU2 censAchV2)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX45 censAchY58 censAchU2 censAchV2) := by
  have L := censAch_letters_mem h j censAchX45 censAchY58 censAchU2 censAchV2
  exact censAch_lines_false_x0 (c := 3)
    (w := commP censAchX45 censAchY58⁻¹ * commP censAchY58 censAchU2)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.1 (Subgroup.inv_mem _ L.2.2.1))
      (commP_mem_commSub L.2.2.1 L.2.2.2.1))

/-- The `x1` letter of census point 59. -/
def censAchY59 : SqU6 gr3R := ⟨0, 0, 4, 0, 2, 3, 2, 5, 7, 2, 7, 3, 3, 5, 5⟩

/-- ⭐ **Census point 59 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the `x0` slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^25`, sigma knob NOT achievable. -/
theorem censAch_kill_59 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX45 censAchY59 censAchU2 censAchV2)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX45 censAchY59 censAchU2 censAchV2)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX45 censAchY59 censAchU2 censAchV2) := by
  have L := censAch_letters_mem h j censAchX45 censAchY59 censAchU2 censAchV2
  exact censAch_lines_false_x0 (c := 3)
    (w := commP censAchX45 censAchY59⁻¹ * commP censAchY59 censAchU2)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.1 (Subgroup.inv_mem _ L.2.2.1))
      (commP_mem_commSub L.2.2.1 L.2.2.2.1))

/-- The `x1` letter of census point 60. -/
def censAchY60 : SqU6 gr3R := ⟨0, 0, 4, 4, 6, 7, 6, 1, 7, 2, 7, 1, 7, 7, 0⟩

/-- ⭐ **Census point 60 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the `x0` slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^25`, sigma knob NOT achievable. -/
theorem censAch_kill_60 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX45 censAchY60 censAchU2 censAchV2)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX45 censAchY60 censAchU2 censAchV2)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX45 censAchY60 censAchU2 censAchV2) := by
  have L := censAch_letters_mem h j censAchX45 censAchY60 censAchU2 censAchV2
  exact censAch_lines_false_x0 (c := 3)
    (w := commP censAchX45 censAchY60 * commP censAchY60 censAchU2⁻¹)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.1 L.2.2.1)
      (commP_mem_commSub L.2.2.1 (Subgroup.inv_mem _ L.2.2.2.1)))

/-- The `x1` letter of census point 61. -/
def censAchY61 : SqU6 gr3R := ⟨0, 0, 4, 4, 6, 7, 6, 1, 7, 2, 7, 1, 7, 7, 4⟩

/-- ⭐ **Census point 61 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the `x0` slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^25`, sigma knob NOT achievable. -/
theorem censAch_kill_61 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX45 censAchY61 censAchU2 censAchV2)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX45 censAchY61 censAchU2 censAchV2)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX45 censAchY61 censAchU2 censAchV2) := by
  have L := censAch_letters_mem h j censAchX45 censAchY61 censAchU2 censAchV2
  exact censAch_lines_false_x0 (c := 3)
    (w := commP censAchX45 censAchY61 * commP censAchY61 censAchU2⁻¹)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.1 L.2.2.1)
      (commP_mem_commSub L.2.2.1 (Subgroup.inv_mem _ L.2.2.2.1)))

/-- The `x1` letter of census point 62. -/
def censAchY62 : SqU6 gr3R := ⟨4, 0, 4, 0, 6, 7, 4, 5, 2, 1, 1, 1, 6, 2, 0⟩

/-- ⭐ **Census point 62 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `7`, lattice `2^25`, sigma knob NOT achievable. -/
theorem censAch_kill_62 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX65 censAchY62 censAchU3 censAchV3)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX65 censAchY62 censAchU3 censAchV3)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX65 censAchY62 censAchU3 censAchV3) := by
  have L := censAch_letters_mem h j censAchX65 censAchY62 censAchU3 censAchV3
  exact censAch_lines_false_sig (c := 7)
    (w := commP censAchY62 censAchV3 * commP censAchY62 censAchU3)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.2) (commP_mem_commSub L.2.2.1 L.2.2.2.1))

/-- The `x1` letter of census point 63. -/
def censAchY63 : SqU6 gr3R := ⟨4, 0, 4, 0, 6, 7, 4, 5, 2, 1, 1, 1, 6, 2, 4⟩

/-- ⭐ **Census point 63 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `7`, lattice `2^25`, sigma knob NOT achievable. -/
theorem censAch_kill_63 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX65 censAchY63 censAchU3 censAchV3)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX65 censAchY63 censAchU3 censAchV3)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX65 censAchY63 censAchU3 censAchV3) := by
  have L := censAch_letters_mem h j censAchX65 censAchY63 censAchU3 censAchV3
  exact censAch_lines_false_sig (c := 7)
    (w := commP censAchY63 censAchV3 * commP censAchY63 censAchU3)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.2) (commP_mem_commSub L.2.2.1 L.2.2.2.1))

/-- The `x1` letter of census point 64. -/
def censAchY64 : SqU6 gr3R := ⟨4, 0, 4, 0, 6, 3, 0, 5, 6, 5, 1, 1, 4, 6, 2⟩

/-- ⭐ **Census point 64 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^25`, sigma knob NOT achievable. -/
theorem censAch_kill_64 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX65 censAchY64 censAchU3 censAchV3)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX65 censAchY64 censAchU3 censAchV3)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX65 censAchY64 censAchU3 censAchV3) := by
  have L := censAch_letters_mem h j censAchX65 censAchY64 censAchU3 censAchV3
  exact censAch_lines_false_sig (c := 3)
    (w := commP censAchY64 censAchU3 * commP censAchV3 censAchY64)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.1) (commP_mem_commSub L.2.2.2.2 L.2.2.1))

/-- The `x1` letter of census point 65. -/
def censAchY65 : SqU6 gr3R := ⟨4, 0, 4, 0, 6, 3, 0, 5, 6, 5, 1, 1, 4, 6, 6⟩

/-- ⭐ **Census point 65 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^25`, sigma knob NOT achievable. -/
theorem censAch_kill_65 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX65 censAchY65 censAchU3 censAchV3)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX65 censAchY65 censAchU3 censAchV3)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX65 censAchY65 censAchU3 censAchV3) := by
  have L := censAch_letters_mem h j censAchX65 censAchY65 censAchU3 censAchV3
  exact censAch_lines_false_sig (c := 3)
    (w := commP censAchY65 censAchU3 * commP censAchV3 censAchY65)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.1) (commP_mem_commSub L.2.2.2.2 L.2.2.1))

/-- The `x1` letter of census point 66. -/
def censAchY66 : SqU6 gr3R := ⟨4, 0, 4, 0, 6, 3, 0, 5, 6, 1, 5, 1, 4, 6, 6⟩

/-- ⭐ **Census point 66 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^25`, sigma knob NOT achievable. -/
theorem censAch_kill_66 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX65 censAchY66 censAchU3 censAchV3)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX65 censAchY66 censAchU3 censAchV3)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX65 censAchY66 censAchU3 censAchV3) := by
  have L := censAch_letters_mem h j censAchX65 censAchY66 censAchU3 censAchV3
  exact censAch_lines_false_sig (c := 3)
    (w := commP censAchY66 censAchU3 * commP censAchV3 censAchY66)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.1) (commP_mem_commSub L.2.2.2.2 L.2.2.1))

/-- The `x1` letter of census point 67. -/
def censAchY67 : SqU6 gr3R := ⟨4, 0, 4, 0, 6, 3, 0, 5, 6, 1, 5, 1, 4, 6, 2⟩

/-- ⭐ **Census point 67 is DEAD**, at every handle count and every handle: the
displayed product of two commutators of the point's own letters is achievable, and
dressing the sigma slot with it kills the relator outright, so all three `gamma_2`
lines fail.  Residue `3`, lattice `2^25`, sigma knob NOT achievable. -/
theorem censAch_kill_67 (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (censAchPt h j censAchX65 censAchY67 censAchU3 censAchV3)
      ∧ ¬ GaTwoCentral (censAchPt h j censAchX65 censAchY67 censAchU3 censAchV3)
      ∧ ¬ GaTwoOrth (censAchPt h j censAchX65 censAchY67 censAchU3 censAchV3) := by
  have L := censAch_letters_mem h j censAchX65 censAchY67 censAchU3 censAchV3
  exact censAch_lines_false_sig (c := 3)
    (w := commP censAchY67 censAchU3 * commP censAchV3 censAchY67)
    (by decide) (by decide) (by decide)
    (mul_mem (commP_mem_commSub L.2.2.1 L.2.2.2.1) (commP_mem_commSub L.2.2.2.2 L.2.2.1))


end Points

end SqCore

end Dyadic

end GQ2
