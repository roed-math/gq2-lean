/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.MpcGeneralStageTowerBoundary

/-!
# Frattini base independence for the general Mpc tower boundary

A depth-`k-1` correction bracket in `Q_(k+1)` depends on its partner only modulo the
Frattini subgroup.  The controlled general ladder preserves the Frattini classes of the
universal marking, so both the marked shift homomorphism and the remaining tower brackets
may be computed at the canonical `dmGen` marking.

This removes the current stage tuple from the last theorem.  What remains is one standard-base
graded statement, still uniform in `alpha`, the handle count, the rung, and the tower atom.
-/

namespace GQ2.Dyadic.Instances.MpcGeneralFrattiniBaseReduction

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.Instances.MpcGeneralFiniteSpan
open GQ2.Dyadic.Instances.MpcGeneralMarkedSpan
open GQ2.Dyadic.Instances.MpcGeneralStageTowerBoundary
open GQ2.Dyadic.Instances.MpcGeneralTowerAtoms
open GQ2.Roe.Labute

/-- A top correction bracket depends on its partner only modulo the Frattini layer. -/
theorem commP_congr_frattini_slot
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {k : ℕ} (hk : 3 ≤ k) {v g g' : levelQuot G (k + 1)}
    (hv : v ∈ lambdaImage G (k - 1) (k + 1))
    (hg : g⁻¹ * g' ∈ lambdaImage G 2 (k + 1)) :
    commP v g = commP v g' := by
  have hg' : g' = g * (g⁻¹ * g') := by group
  have herror : commP v (g⁻¹ * g') = 1 := by
    have hmem := commP_mem_lambdaImage_add hv hg
    rw [show k - 1 + 2 = k + 1 by omega, lambdaImage_self] at hmem
    simpa using hmem
  have hcentral : commP v g ∈ zLayer G k := by
    have hg1 : g ∈ lambdaImage G 1 (k + 1) := by
      rw [lambdaImage_one_eq_top]
      trivial
    have hmem := commP_mem_lambdaImage_add hv hg1
    rwa [show k - 1 + 1 = k by omega] at hmem
  have hformula : commP v (g * (g⁻¹ * g')) =
      commP v (g⁻¹ * g') *
        ((g⁻¹ * g')⁻¹ * commP v g * (g⁻¹ * g')) := by
    simp only [commP]
    group
  have hcomm := Subgroup.mem_center_iff.mp
    (zLayer_le_center G k hcentral) (g⁻¹ * g')
  rw [hg', hformula, herror, one_mul, mul_assoc, ← hcomm, ← mul_assoc,
    inv_mul_cancel, one_mul]

/-- The complete even first-variation word depends on its base only modulo the Frattini
layer, uniformly in the number of handles and the filtration rung. -/
theorem evenRawDbarWord_congr_frattini_base
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ} (hk : 3 ≤ k)
    {base base' c : Fin (coreRank h) → levelQuot G (k + 1)}
    (hb : ∀ i, (base i)⁻¹ * base' i ∈ lambdaImage G 2 (k + 1))
    (hc : ∀ i, c i ∈ lambdaImage G (k - 1) (k + 1)) :
    evenRawDbarWord base c = evenRawDbarWord base' c := by
  have key : ∀ j i : Fin (coreRank h),
      commP (c j) (base i) = commP (c j) (base' i) :=
    fun j i => commP_congr_frattini_slot hk (hc j) (hb i)
  simp only [evenRawDbarWord, evenRawCoreDbarWord,
    evenRawHandleDbarWord, key]

/-- A controlled stage marking and the canonical marking have the same finite Frattini
classes. -/
theorem mpcGeneralFrattiniStage_level_congr_standard
    {alpha h k : ℕ} {m : Fin (coreRank h) → (DM alpha h : Type)}
    (hm : m ∈ mpcGeneralFrattiniStage alpha h k) (i : Fin (coreRank h)) :
    (levelMk (DM alpha h) (k + 1) (dmGen alpha h i))⁻¹ *
        levelMk (DM alpha h) (k + 1) (m i) ∈
      lambdaImage (DM alpha h) 2 (k + 1) := by
  refine ⟨(dmGen alpha h i)⁻¹ * m i, hm.2 i, ?_⟩
  simp only [map_mul, map_inv]

/-- At a controlled stage, the fully marked finite shift homomorphism is literally the
standard-base homomorphism. -/
theorem mpcGeneralMarkedLevelShiftHom_eq_standard
    {alpha h k : ℕ} {m : Fin (coreRank h) → (DM alpha h : Type)}
    (hm : m ∈ mpcGeneralFrattiniStage alpha h k) (hk : 3 ≤ k) :
    mpcGeneralMarkedLevelShiftHom m k hk =
      mpcGeneralMarkedLevelShiftHom (dmGen alpha h) k hk := by
  ext E
  change evenRawDbarWord
      (fun i => levelMk (DM alpha h) (k + 1) (m i))
      (mpcGeneralMarkedLevelToRaw E).correction =
    evenRawDbarWord
      (fun i => levelMk (DM alpha h) (k + 1) (dmGen alpha h i))
      (mpcGeneralMarkedLevelToRaw E).correction
  symm
  exact evenRawDbarWord_congr_frattini_base hk
    (mpcGeneralFrattiniStage_level_congr_standard hm)
    (mpcGeneralMarkedLevelToRaw E).depth

/-- The final standard-base graded statement. -/
def MpcGeneralStandardTowerAtomBracketSupply (alpha h : ℕ) : Prop :=
  ∀ (halpha : 2 ≤ alpha) k (hk : 3 ≤ k)
    (x : DM alpha h) (hx : x ∈ twoCentralSeries (DM alpha h : Type) (k - 1))
    (hchi : chiM alpha h x = 1) (i : Fin (coreRank h)),
    let a := mpcGeneralTowerAtom (by omega : 1 ≤ alpha) x i
    let ha := (mpcGeneralTowerAtom_mem halpha hk hx hchi i).1
    (⟨commP (levelMk (DM alpha h) (k + 1) a)
        (levelMk (DM alpha h) (k + 1) (dmGen alpha h 3)),
      commP_mem_zLayer k hk ⟨a, ha, rfl⟩ _⟩ : zLayer (DM alpha h) k) ∈
        (mpcGeneralMarkedLevelShiftHom (dmGen alpha h) k hk).range

/-- Standard-base atom brackets imply the reachable-stage bracket theorem. -/
theorem mpcGeneralStageTowerAtomBracketSupply_of_standard
    {alpha h : ℕ} (H : MpcGeneralStandardTowerAtomBracketSupply alpha h) :
    MpcGeneralStageTowerAtomBracketSupply alpha h := by
  intro halpha k hk m hm x hx hchi i
  dsimp only
  obtain ⟨E, hE⟩ := H halpha k hk x hx hchi i
  refine ⟨E, ?_⟩
  rw [mpcGeneralMarkedLevelShiftHom_eq_standard hm hk]
  rw [hE]
  apply Subtype.ext
  exact commP_congr_frattini_slot hk
    ⟨mpcGeneralTowerAtom (by omega) x i,
      (mpcGeneralTowerAtom_mem halpha hk hx hchi i).1, rfl⟩
    (mpcGeneralFrattiniStage_level_congr_standard hm 3)

/-- The single standard-base atom theorem proves the pivot shift for arbitrary degree and
handle count. -/
theorem mpcPivShiftH_of_generalStandardTowerBrackets
    {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (H : MpcGeneralStandardTowerAtomBracketSupply alpha h) :
    GQ2.Dyadic.Instances.MpcGeneralHandlePivotBoundary.MpcPivShiftH alpha h :=
  mpcPivShiftH_of_generalStageTowerBrackets halpha
    (mpcGeneralStageTowerAtomBracketSupply_of_standard H)

end

end GQ2.Dyadic.Instances.MpcGeneralFrattiniBaseReduction

section AxiomPins

open GQ2.Dyadic.Instances.MpcGeneralFrattiniBaseReduction

#print axioms commP_congr_frattini_slot
#print axioms evenRawDbarWord_congr_frattini_base
#print axioms mpcGeneralFrattiniStage_level_congr_standard
#print axioms mpcGeneralMarkedLevelShiftHom_eq_standard
#print axioms MpcGeneralStandardTowerAtomBracketSupply
#print axioms mpcGeneralStageTowerAtomBracketSupply_of_standard
#print axioms mpcPivShiftH_of_generalStandardTowerBrackets

end AxiomPins
