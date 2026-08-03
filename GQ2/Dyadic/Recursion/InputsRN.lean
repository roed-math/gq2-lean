/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Recursion.Recursion

/-!
# Degree-indexed input bundle for the R-stage

This file leaves `RecursionInputsK` and `ClosedRecursionK` frozen.  It adds the corrected input
companion: only the coefficient in (136) changes, from `RF.zR` to `zRN RF SN`.  At degree one
the input bundles convert definitionally.  The parallel general-degree closed path consuming
this record is in `GQ2.Dyadic.Recursion.ClosedRN`; no coefficient equality is imposed there.
-/

namespace GQ2.Dyadic

open GQ2.SectionEight

open scoped Classical in
/-- The corrected source-side input bundle.  Its last two fields are literally the frozen
`RecursionInputsK` fields; only `stageR136` uses the degree-indexed coefficient. -/
structure RecursionInputsRN {H E Y : Type} [Group H] [TopologicalSpace H]
    [DiscreteTopology H] [Finite H] [CommGroup E] [TopologicalSpace E]
    [DiscreteTopology E] [Finite E] [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {q n : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (SN : SourceNumerics n)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (μ : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT]
    (phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC)
    (mM vH : ℕ) : Prop where
  stageR136 : (Nat.card RF.DR : ℤ) * exactImageCountK b F T
    = zRN RF SN * ∑ᶠ l : RF.DR,
        (2 * (mBK RF b F l : ℤ) - exactImageCountK b F RF.TB)
  half139 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (¬∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
        N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) →
      2 * zBCK RF b F l h = mM * exactImageCountK b F RF.TC
  phase140 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
        N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) →
      2 * (Nat.card DT : ℤ) * zBCK RF b F l h
        = μ * ((vH : ℕ) * exactImageCountK b F RF.TC
            + G0 * ∑ᶠ ζ : DT,
                (2 * (nPhaseK RF b F (phase l h ζ) : ℤ)
                  - exactImageCountK b F RF.TC))

namespace RecursionInputsRN

/-- The precise bridge to the frozen recursion input.  The coefficient equality is the only
extra hypothesis: all other fields are unchanged. -/
def toRecursionInputsK {H E Y : Type} [Group H] [TopologicalSpace H]
    [DiscreteTopology H] [Finite H] [CommGroup E] [TopologicalSpace E]
    [DiscreteTopology E] [Finite E] [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    {RF : RecursionFrame T Blk} {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {q n : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {SN : SourceNumerics n}
    {b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)} {F : BoundaryFrameK q P H E}
    {μ : ℕ} {G0 : ℤ} {DT : Type} [Fintype DT]
    {phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC}
    {mM vH : ℕ} (I : RecursionInputsRN RF SN b F μ G0 DT phase mM vH)
    (hz : zRN RF SN = RF.zR) : RecursionInputsK RF b F μ G0 DT phase mM vH where
  stageR136 := by simpa only [← hz] using I.stageR136
  half139 := I.half139
  phase140 := I.phase140

/-- Conversely, a frozen input supplies the corrected bundle whenever its two coefficients
agree. -/
def ofRecursionInputsK {H E Y : Type} [Group H] [TopologicalSpace H]
    [DiscreteTopology H] [Finite H] [CommGroup E] [TopologicalSpace E]
    [DiscreteTopology E] [Finite E] [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    {RF : RecursionFrame T Blk} {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {q n : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {SN : SourceNumerics n}
    {b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)} {F : BoundaryFrameK q P H E}
    {μ : ℕ} {G0 : ℤ} {DT : Type} [Fintype DT]
    {phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC}
    {mM vH : ℕ} (I : RecursionInputsK RF b F μ G0 DT phase mM vH)
    (hz : zRN RF SN = RF.zR) : RecursionInputsRN RF SN b F μ G0 DT phase mM vH where
  stageR136 := by simpa only [hz] using I.stageR136
  half139 := I.half139
  phase140 := I.phase140

/-- Degree one is the exact regression: no propositional coefficient hypothesis is needed. -/
def toRecursionInputsK_standard_one {H E Y : Type} [Group H] [TopologicalSpace H]
    [DiscreteTopology H] [Finite H] [CommGroup E] [TopologicalSpace E]
    [DiscreteTopology E] [Finite E] [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    {RF : RecursionFrame T Blk} {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)} {F : BoundaryFrameK q P H E}
    {μ : ℕ} {G0 : ℤ} {DT : Type} [Fintype DT]
    {phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC}
    {mM vH : ℕ}
    (I : RecursionInputsRN RF (standardNumerics 1) b F μ G0 DT phase mM vH) :
    RecursionInputsK RF b F μ G0 DT phase mM vH :=
  I.toRecursionInputsK (zRN_standard_one RF)

/-- The exact bridge back to the frozen (136) proposition type under coefficient equality.
The general corrected path does not use this theorem; it lives in `ClosedRN.lean`. -/
theorem stageR136_iff_frozen_of_coeff_eq {H E Y : Type} [Group H] [TopologicalSpace H]
    [DiscreteTopology H] [Finite H] [CommGroup E] [TopologicalSpace E]
    [DiscreteTopology E] [Finite E] [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {q n : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (SN : SourceNumerics n)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (hz : zRN RF SN = RF.zR) :
    ((Nat.card RF.DR : ℤ) * exactImageCountK b F T
        = zRN RF SN * ∑ᶠ l : RF.DR,
            (2 * (mBK RF b F l : ℤ) - exactImageCountK b F RF.TB))
      ↔
      ((Nat.card RF.DR : ℤ) * exactImageCountK b F T
        = RF.zR * ∑ᶠ l : RF.DR,
            (2 * (mBK RF b F l : ℤ) - exactImageCountK b F RF.TB)) := by
  rw [hz]

end RecursionInputsRN
end GQ2.Dyadic
