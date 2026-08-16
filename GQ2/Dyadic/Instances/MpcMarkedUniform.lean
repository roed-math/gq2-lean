/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcInitialRelatorAbsorption
import GQ2.Dyadic.Instances.MpcSqrtNegTenDeterminant

/-!
# Uniform full-marked supply for the procyclic-M ladder

Initial-relator absorption completes the head-marked cost range. Together with head
reflection, this proves the corrected source exactness theorem. The recursive secondary is
in the five carrier kernel, so source exactness places it in the next full marked cost range.

`MpcMkGood` intentionally forgets the marked-head invariant, so it is not the right induction
state: an arbitrary witness need not have zero D-coordinate. `MpcMkMarkedGood` retains exactly
that invariant. The class-five point `mpcLadW4` supplies the base, `mpcMkAdvance` preserves its
marked head, and `mpcMk_markedGood_succ` gives the uniform successor. Projecting the resulting
all-r family yields full marked supply at every rung and hence `MpcPivShift 2`.

The final wrapper feeds this unconditional shift to the existing tied `sqrt(-10)` branch
producer. The marked-group part of this module uses only the standard three axioms. The field
wrapper inherits the established field-side axioms of that producer and introduces none.
-/

namespace GQ2.Dyadic.Instances.MpcMk

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcPiv GQ2.Dyadic.Instances.MpcOrb
open GQ2.Dyadic.Instances.MpcWord GQ2.Dyadic.Instances.MpcBld
open GQ2.Dyadic.Instances.MpcLad GQ2.Dyadic.Instances.MpcFv
open GQ2.Dyadic.Instances.MpcSx GQ2.Roe.Labute GQ2.Dyadic.SqCore

noncomputable section

/-- Corrected full marked-source exactness at every rung and permitted base pair. -/
theorem mpcMk_sourceExact
    (r : ℕ) (hr : 2 ≤ r) {t n : (DM 2 0 : Type)}
    (ht : t ∈ twoCentralSeries (DM 2 0 : Type) 2)
    (hn : n ∈ twoCentralSeries (DM 2 0 : Type) 2) :
    MpcMkSourceExact r hr t n :=
  mpcMk_sourceExact_of_headReflection_of_headCompletion r hr t n
    (mpcMk_headReflection r hr t n)
    (mpcMk_headCompletion_of_initialRelatorAbsorption r hr ht hn
      (mpcMk_initialRelatorAbsorption r hr))

/-- The recursively arising secondary lies in the successor full marked cost range. -/
theorem mpcMk_secondary_mem_costRange {j : ℕ} (hj : 3 ≤ j)
    {p : MpcMkPoint} (hp : p ∈ mpcWordSet (j + 1))
    (hmarked : MpcMkMarkedHead p) (u : MpcMkCostDomain j)
    (hu : mpcMkCost j (by omega) p.2.1 p.2.2.2 u =
      mpcMkDefectTop j p hp) :
    mpcMkDefectTop (j + 1) (mpcMkAdvance j p u)
        (mpcMk_advance_mem (by omega) hp u hu) ∈
      MonoidHom.range
        (mpcMkCost (j + 1) (by omega) p.2.1 p.2.2.2) := by
  apply mpcMk_mem_markedCostRange_of_sourceExact
    (r := j + 1) (by omega) hp.2.1.1 hp.2.2.2.1.1
    (mpcMk_sourceExact (j + 1) (by omega) hp.2.1.1 hp.2.2.2.1.1)
  rw [mpcMkDefectTop_advance_eq_liftResidual_mul_hall hj hp u hu]
  exact mpcMkSecondary_mem_fiveCarrierKernel hj hp hmarked u hu

/-- A good rung retaining the marked-head invariant needed by the corrected D-coordinate. -/
def MpcMkMarkedGood (j : ℕ) : Prop :=
  ∃ hj : 2 ≤ j, ∃ p, ∃ hp : p ∈ mpcWordSet (j + 1),
    MpcMkMarkedHead p ∧
      mpcMkDefectTop j p hp ∈
        MonoidHom.range (mpcMkCost j hj p.2.1 p.2.2.2)

/-- Forgetting marked-head state recovers the existing good-rung predicate. -/
theorem MpcMkMarkedGood.good {j : ℕ} (h : MpcMkMarkedGood j) : MpcMkGood j := by
  obtain ⟨hj, p, hp, _, hrange⟩ := h
  exact ⟨hj, p, hp, hrange⟩

/-- The existing class-five point and move form the marked induction base. -/
theorem mpcMk_markedGood_three : MpcMkMarkedGood 3 := by
  refine ⟨by omega, mpcLadW4, mpcLad_w4_mem, mpcMk_markedHead_w4, ?_⟩
  exact (mpcMk_fullSupply_iff_mem_costRange (by omega) mpcLad_w4_mem).mp
    mpcMk_fullSupply_three

/-- Source exactness advances a marked good rung while preserving its marked head. -/
theorem mpcMk_markedGood_succ {j : ℕ} (hj : 3 ≤ j)
    (h : MpcMkMarkedGood j) : MpcMkMarkedGood (j + 1) := by
  obtain ⟨_, p, hp, hmarked, u, hu⟩ := h
  let hq : mpcMkAdvance j p u ∈ mpcWordSet (j + 2) :=
    mpcMk_advance_mem (by omega) hp u hu
  refine ⟨by omega, mpcMkAdvance j p u, hq,
    mpcMk_markedHead_advance hmarked u, ?_⟩
  have hnext := mpcMk_secondary_mem_costRange hj hp hmarked u hu
  have hcost := mpcMk_cost_succ_base_indep (by omega)
    p.2.1 p.2.2.2 u.2.1.2.2 u.2.2.2.2.2
  change mpcMkDefectTop (j + 1) (mpcMkAdvance j p u) hq ∈
    MonoidHom.range (mpcMkCost (j + 1) (by omega)
      (p.2.1 * u.2.1) (p.2.2.2 * u.2.2.2))
  rw [hcost]
  exact hnext

/-- Marked good rungs indexed from the class-five base. -/
theorem mpcMk_markedGood_all (k : ℕ) : MpcMkMarkedGood (3 + k) := by
  induction k with
  | zero => simpa using mpcMk_markedGood_three
  | succ k ih =>
      simpa only [Nat.add_assoc] using mpcMk_markedGood_succ (by omega) ih

/-- Every required rung has a marked good witness. -/
theorem mpcMk_markedGood_of_three_le {j : ℕ} (hj : 3 ≤ j) :
    MpcMkMarkedGood j := by
  have h := mpcMk_markedGood_all (j - 3)
  have heq : 3 + (j - 3) = j := by omega
  rwa [heq] at h

/-- Every required rung satisfies the original good-rung predicate. -/
theorem mpcMk_good_of_three_le {j : ℕ} (hj : 3 ≤ j) : MpcMkGood j :=
  (mpcMk_markedGood_of_three_le hj).good

/-- Every required rung has a concrete full marked supply witness. -/
theorem mpcMk_exists_fullSupply {j : ℕ} (hj : 3 ≤ j) :
    ∃ p ∈ mpcWordSet (j + 1), MpcMkFullSupply j p :=
  (mpcMk_good_iff_exists_fullSupply (by omega)).mp
    (mpcMk_good_of_three_le hj)

/-- The uniform full-marked ladder proves the procyclic-M pivot shift. -/
theorem mpcMk_pivShift : MpcPivShift 2 := by
  apply mpcMk_shift_of_fullSupply
  exact fun _ hj ↦ mpcMk_exists_fullSupply hj

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

open GQ2.Dyadic.Fields

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    {R : LocalReciprocity}

/-- The tied `sqrt(-10)` branch at its canonical marking, now without a shift premise. -/
theorem mpcMk_genAsmBranch_sqrtNegTen (B : MarkedRecip R KSqrtNegTen) :
    ∃ G : GenAsmBranch KSqrtNegTen B,
      G.pres = .Mpc 2 1 true .one 0 ∧
        HEq G.nuP
          (MProcyclicCore.mpcNu 2 1 (p true 1) (by omega)) :=
  mpcPiv_genAsmBranch_sqrtNegTen_of_shift mpcMk_pivShift B

/-- The corrected `sqrt(-10)` candidate is the absolute Galois group, with no residual shift
premise. -/
theorem mpcMk_candidate_equiv_galKRN_sqrtNegTen
    [T2Space (GalK KSqrtNegTen)] (B : MarkedRecip R KSqrtNegTen)
    {FF : DyadicUnitFiltration KSqrtNegTen}
    (F : GenAsmFieldInputs KSqrtNegTen B FF
      (SelectedPresentation.Mpc 2 1 true .one 0).degree) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.Mpc 2 1 true .one 0).degree
        (qOf KSqrtNegTen FF) (SelectedPresentation.Mpc 2 1 true .one 0).word :
        ProfiniteGrp) : Type) (GalK KSqrtNegTen)) :=
  MpcSqrtNegTenDeterminant.mpcSqrtNegTen_candidate_equiv_galKRN
    mpcMk_pivShift B F

/-! ## Axiom pins -/

#print axioms mpcMk_sourceExact
#print axioms mpcMk_secondary_mem_costRange
#print axioms MpcMkMarkedGood
#print axioms MpcMkMarkedGood.good
#print axioms mpcMk_markedGood_three
#print axioms mpcMk_markedGood_succ
#print axioms mpcMk_markedGood_all
#print axioms mpcMk_markedGood_of_three_le
#print axioms mpcMk_good_of_three_le
#print axioms mpcMk_exists_fullSupply
#print axioms mpcMk_pivShift
#print axioms mpcMk_genAsmBranch_sqrtNegTen
#print axioms mpcMk_candidate_equiv_galKRN_sqrtNegTen

end

end GQ2.Dyadic.Instances.MpcMk
