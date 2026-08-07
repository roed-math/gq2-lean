/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.StageAbstraction
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteLevelThreeBase

/-!
# The L instance of the abstract stage machinery, with definitional pins  (EV-4b)

This file instantiates `GQ2/Dyadic/Instances/StageAbstraction.lean` at the odd-degree
parameters — the word `SqCore.sqRelWord`, the rank `SqCore.sqRank h`, and the row table
`frattiniFrameTarget h` — and demonstrates that the committed L route is recovered
**definitionally**:

* the word datum's fields *are* the committed lemmas, so the generic level sets, defect,
  and shift specialise to the committed `sqStageZero`, `sqStageDefect`, `stageModified`,
  `stageShift`, and `sqRawDefectReachable` by `rfl` (§2);
* converters translate between the committed five-fibre-field structures and the generic
  uniform-row structures without touching generators, relation, or generation (§3); and
* the committed endpoint theorems — the level-`k` induction, the finite-level cofinality
  endpoint, the seed reduction, and the unconditional odd-degree level-three base — are
  re-derived through the abstraction with byte-identical statements (§4, the `pin_*`
  theorems, each followed by an axiom print to compare against the committed original).

Nothing here is consumed by the committed route; the file is the EV-4b regression contract
that the even-degree clones (EV-3) build against.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.Dyadic.LSquare.FrattiniFrameSupply (frattiniFrameTarget frattiniFrameTarget_zero
  frattiniFrameTarget_one frattiniFrameTarget_two frattiniFrameTarget_handleU
  frattiniFrameTarget_handleV)

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The L word datum and the index eliminator -/

/-- The odd-degree (L-row) word datum: the literal improved square word `SqCore.sqRelWord`
with its committed naturality and central-shift lemmas as the two field values.  Because the
fields are the committed constants themselves, every generic definition specialises to its
committed counterpart definitionally. -/
def lSqWord (h : ℕ) : StageWord (SqCore.sqRank h) where
  word m := SqCore.sqRelWord m
  map_word φ m := SqCore.map_sqRelWord φ m
  zshift z m hz := LSquare.sqRelWord_zLayer_shift z m hz

/-- Exhaustive case analysis on the improved square alphabet: every index is one of the
three core letters or a handle letter. -/
theorem sqIndex_cases {h : ℕ} {P : Fin (SqCore.sqRank h) → Prop}
    (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (hU : ∀ j : Fin h, P (SqCore.sqHandleIdxU j))
    (hV : ∀ j : Fin h, P (SqCore.sqHandleIdxV j))
    (i : Fin (SqCore.sqRank h)) : P i := by
  rcases hi : GQ2.ContCoh.sqInitialAlphabetEquiv h i with a | ⟨j, b⟩
  · fin_cases a
    · have h0' : i = 0 := (GQ2.ContCoh.sqInitialAlphabetEquiv h).injective
        (hi.trans (GQ2.ContCoh.sqInitialAlphabetEquiv_zero h).symm)
      rw [h0']
      exact h0
    · have h1' : i = 1 := (GQ2.ContCoh.sqInitialAlphabetEquiv h).injective
        (hi.trans (GQ2.ContCoh.sqInitialAlphabetEquiv_one h).symm)
      rw [h1']
      exact h1
    · have h2' : i = 2 := (GQ2.ContCoh.sqInitialAlphabetEquiv h).injective
        (hi.trans (GQ2.ContCoh.sqInitialAlphabetEquiv_two h).symm)
      rw [h2']
      exact h2
  · fin_cases b
    · have hU' : i = SqCore.sqHandleIdxU j := (GQ2.ContCoh.sqInitialAlphabetEquiv h).injective
        (hi.trans (GQ2.ContCoh.sqInitialAlphabetEquiv_handleU j).symm)
      rw [hU']
      exact hU j
    · have hV' : i = SqCore.sqHandleIdxV j := (GQ2.ContCoh.sqInitialAlphabetEquiv h).injective
        (hi.trans (GQ2.ContCoh.sqInitialAlphabetEquiv_handleV j).symm)
      rw [hV']
      exact hV j

/-- Regression for the shape helper: the committed L zshift is also derivable through
`zshift_of_core_handles`, confirming that the even tickets' route through the four-letter
core case is the same mechanism the L word uses. -/
example {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {h k : ℕ}
    (z m : Fin (SqCore.sqRank h) → levelQuot G (k + 1)) (hz : ∀ i, z i ∈ zLayer G k) :
    SqCore.sqRelWord (fun i ↦ z i * m i) = SqCore.sqRelWord m :=
  zshift_of_core_handles
    (fun mm ↦ SqCore.sqWord (mm 0) (mm 1) (mm 2))
    ![0, 1, 2] SqCore.sqHandleIdxU SqCore.sqHandleIdxV
    (fun mm ↦ SqCore.sqRelWord mm)
    (fun _ ↦ rfl)
    (fun _z' _m' hz' ↦ drWord_zLayer_shift (hz' 0) (hz' 1) (hz' 2) _ _ _)
    z m hz

/-! ## §2 Definitional pins of the defect calculus

The generic definitions at `lSqWord h` are the committed definitions, on the nose. -/

section DefeqPins

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {h k : ℕ}

example : LSquare.sqStageZero G h k = stageZero (lSqWord h) G k := rfl

example (T : Fin (SqCore.sqRank h) → levelQuot G k) :
    LSquare.sqStageDefect G h k T = stageDefect (lSqWord h) G k T := rfl

example (base correction : Fin (SqCore.sqRank h) → levelQuot G (k + 1)) :
    LSquare.SqCyclotomicStageTuple.stageModified base correction =
      stageModified (n := SqCore.sqRank h) base correction := rfl

example (base correction : Fin (SqCore.sqRank h) → levelQuot G (k + 1)) :
    LSquare.SqCyclotomicStageTuple.stageShift base correction =
      stageShift (lSqWord h) base correction := rfl

example (T : Fin (SqCore.sqRank h) → levelQuot G k) :
    LSquare.SqCyclotomicStageTuple.sqRawDefectReachable G h k T =
      rawDefectReachable (lSqWord h) G k T := rfl

/-- Pin: the committed level-set restriction, re-derived generically. -/
example {T : Fin (SqCore.sqRank h) → levelQuot G (k + 1)}
    (hT : T ∈ LSquare.sqStageZero G h (k + 1)) :
    (fun i ↦ levelProj G k (T i)) ∈ LSquare.sqStageZero G h k :=
  stageZero_levelProj (lSqWord h) hT

/-- Pin: the committed lift-independence of the defect, re-derived generically. -/
example (T : Fin (SqCore.sqRank h) → levelQuot G k)
    (T' : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hT' : ∀ i, levelProj G k (T' i) = T i) :
    SqCore.sqRelWord T' = LSquare.sqStageDefect G h k T :=
  stageDefect_eq_of_lift (lSqWord h) k T T' hT'

/-- Pin: the committed graded-layer membership of the defect, re-derived generically. -/
example {T : Fin (SqCore.sqRank h) → levelQuot G k}
    (hrel : SqCore.sqRelWord T = 1) :
    LSquare.sqStageDefect G h k T ∈ zLayer G k :=
  stageDefect_mem_zLayer (lSqWord h) k hrel

/-- Pin: the committed shift identity, re-derived generically. -/
example (base correction : Fin (SqCore.sqRank h) → levelQuot G (k + 1)) :
    SqCore.sqRelWord (LSquare.SqCyclotomicStageTuple.stageModified base correction) =
      SqCore.sqRelWord base *
        LSquare.SqCyclotomicStageTuple.stageShift base correction :=
  word_stageModified (lSqWord h) base correction

end DefeqPins

/-! ## §3 Converters between the committed and generic structures -/

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- Repackage a committed L stage tuple as a generic tuple.  Generators, relation, and
generation transfer unchanged; the five fibre fields become the uniform row table. -/
def ofSq {h k : ℕ} (T : LSquare.SqCyclotomicStageTuple K h k) :
    Tuple (lSqWord h) (frattiniFrameTarget h)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k where
  generators := T.generators
  rows := by
    refine sqIndex_cases ?_ ?_ ?_ ?_ ?_
    · obtain ⟨x, hx, hg⟩ := T.sigma
      exact ⟨x, by rw [frattiniFrameTarget_zero]; exact hx, hg⟩
    · obtain ⟨x, hx, hg⟩ := T.x0
      exact ⟨x, by rw [frattiniFrameTarget_one]; exact hx, hg⟩
    · obtain ⟨x, hx, hg⟩ := T.x1
      exact ⟨x, by rw [frattiniFrameTarget_two]; exact hx, hg⟩
    · intro j
      obtain ⟨x, hx, hg⟩ := T.handleU j
      exact ⟨x, by rw [frattiniFrameTarget_handleU]; exact hx, hg⟩
    · intro j
      obtain ⟨x, hx, hg⟩ := T.handleV j
      exact ⟨x, by rw [frattiniFrameTarget_handleV]; exact hx, hg⟩
  relation := T.relation
  topGen := T.topGen

/-- Repackage a generic tuple at the L parameters as a committed L stage tuple. -/
def toSq {h k : ℕ}
    (T : Tuple (lSqWord h) (frattiniFrameTarget h)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k) :
    LSquare.SqCyclotomicStageTuple K h k where
  generators := T.generators
  sigma := by
    obtain ⟨x, hx, hg⟩ := T.rows 0
    rw [frattiniFrameTarget_zero] at hx
    exact ⟨x, hx, hg⟩
  x0 := by
    obtain ⟨x, hx, hg⟩ := T.rows 1
    rw [frattiniFrameTarget_one] at hx
    exact ⟨x, hx, hg⟩
  x1 := by
    obtain ⟨x, hx, hg⟩ := T.rows 2
    rw [frattiniFrameTarget_two] at hx
    exact ⟨x, hx, hg⟩
  handleU := by
    intro j
    obtain ⟨x, hx, hg⟩ := T.rows (SqCore.sqHandleIdxU j)
    rw [frattiniFrameTarget_handleU] at hx
    exact ⟨x, hx, hg⟩
  handleV := by
    intro j
    obtain ⟨x, hx, hg⟩ := T.rows (SqCore.sqHandleIdxV j)
    rw [frattiniFrameTarget_handleV] at hx
    exact ⟨x, hx, hg⟩
  relation := T.relation
  topGen := T.topGen

@[simp] theorem ofSq_generators {h k : ℕ} (T : LSquare.SqCyclotomicStageTuple K h k) :
    (ofSq T).generators = T.generators := rfl

@[simp] theorem toSq_generators {h k : ℕ}
    (T : Tuple (lSqWord h) (frattiniFrameTarget h)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k) :
    (toSq T).generators = T.generators := rfl

/-- Translate a committed admissible correction of `toSq T` into a generic admissible
correction of `T`.  The correction itself and its depth transfer unchanged: the modified
tuples agree definitionally because `toSq` preserves generators. -/
def admissibleOfSq {h k : ℕ}
    {T : Tuple (lSqWord h) (frattiniFrameTarget h)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k}
    (Wc : LSquare.SqCyclotomicStageTuple.AdmissibleCorrection (toSq T)) :
    Tuple.AdmissibleCorrection T where
  correction := Wc.correction
  depth := Wc.depth
  rows := by
    refine sqIndex_cases ?_ ?_ ?_ ?_ ?_
    · obtain ⟨x, hx, hg⟩ := Wc.sigma
      exact ⟨x, by rw [frattiniFrameTarget_zero]; exact hx, hg⟩
    · obtain ⟨x, hx, hg⟩ := Wc.x0
      exact ⟨x, by rw [frattiniFrameTarget_one]; exact hx, hg⟩
    · obtain ⟨x, hx, hg⟩ := Wc.x1
      exact ⟨x, by rw [frattiniFrameTarget_two]; exact hx, hg⟩
    · intro j
      obtain ⟨x, hx, hg⟩ := Wc.handleU j
      exact ⟨x, by rw [frattiniFrameTarget_handleU]; exact hx, hg⟩
    · intro j
      obtain ⟨x, hx, hg⟩ := Wc.handleV j
      exact ⟨x, by rw [frattiniFrameTarget_handleV]; exact hx, hg⟩

/-- Committed defect reachability of `toSq T` yields generic defect reachability of `T`. -/
theorem defectReachable_ofSq {h k : ℕ}
    {T : Tuple (lSqWord h) (frattiniFrameTarget h)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k}
    (H : LSquare.SqCyclotomicStageTuple.DefectReachable (toSq T)) :
    Tuple.DefectReachable T := by
  obtain ⟨Wc, hW⟩ := H
  exact ⟨admissibleOfSq Wc, hW⟩

/-- Repackage a generic open-quotient tuple at the L parameters as the committed
model-marked finite-level datum, through the committed `finiteLevelEpiDataOfTuple`. -/
def openTupleToEpiData {h : ℕ}
    {U : OpenNormalSubgroup (ProfiniteGrp.of (maxProPQuotient 2 (GalK K)))}
    (O : OpenTuple (lSqWord h) (frattiniFrameTarget h)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) U) :
    LSquare.SqCyclotomicFiniteLevelEpiData (K := K) h U :=
  LSquare.finiteLevelEpiDataOfTuple h U O.generators
    (by obtain ⟨x, hx, hg⟩ := O.rows 0
        rw [frattiniFrameTarget_zero] at hx
        exact ⟨x, hx, hg⟩)
    (by obtain ⟨x, hx, hg⟩ := O.rows 1
        rw [frattiniFrameTarget_one] at hx
        exact ⟨x, hx, hg⟩)
    (by obtain ⟨x, hx, hg⟩ := O.rows 2
        rw [frattiniFrameTarget_two] at hx
        exact ⟨x, hx, hg⟩)
    (fun j ↦ by
        obtain ⟨x, hx, hg⟩ := O.rows (SqCore.sqHandleIdxU j)
        rw [frattiniFrameTarget_handleU] at hx
        exact ⟨x, hx, hg⟩)
    (fun j ↦ by
        obtain ⟨x, hx, hg⟩ := O.rows (SqCore.sqHandleIdxV j)
        rw [frattiniFrameTarget_handleV] at hx
        exact ⟨x, hx, hg⟩)
    O.relation
    O.topGen

/-- Repackage a committed Frattini frame as a generic frame.  As with the tuples, only the
fibre fields are re-indexed. -/
def frameOfSq {h : ℕ} (F : LSquare.SqCyclotomicFrattiniFrame K h) :
    Frame (frattiniFrameTarget h) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) where
  generators := F.generators
  rows := by
    refine sqIndex_cases ?_ ?_ ?_ ?_ ?_
    · rw [frattiniFrameTarget_zero]
      exact F.sigma
    · rw [frattiniFrameTarget_one]
      exact F.x0
    · rw [frattiniFrameTarget_two]
      exact F.x1
    · intro j
      rw [frattiniFrameTarget_handleU]
      exact F.handleU j
    · intro j
      rw [frattiniFrameTarget_handleV]
      exact F.handleV j
  levelTwoGen := F.levelTwoGen

/-- The committed level-three relation of a frame is the generic one, definitionally. -/
example {h : ℕ} (F : LSquare.SqCyclotomicFrattiniFrame K h) :
    F.LevelThreeRelation ↔ (frameOfSq F).LevelThreeRelation (lSqWord h) :=
  Iff.rfl

section CupAdapted

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- The committed cup-adaptedness of a frame is the generic one at the L Gram and the field
cup pairing, definitionally.  This is the pin that fixes the `gram` parameter of the
abstraction as genuine word data. -/
example {h : ℕ} (F : LSquare.SqCyclotomicFrattiniFrame K h) :
    F.IsCupAdapted ↔
      (frameOfSq F).IsCupAdapted (GQ2.ContCoh.sqRelatorQuadraticInitialGram h)
        (fun c d ↦ FieldData.cupFormK K
          (h1MaxProTwoEquivGalK (K := K)
            (LSquare.SqCyclotomicFrattiniFrame.characterClass (K := K) c))
          (h1MaxProTwoEquivGalK (K := K)
            (LSquare.SqCyclotomicFrattiniFrame.characterClass (K := K) d))) :=
  Iff.rfl

end CupAdapted

/-! ## §4 Endpoint pins

Each `pin_*` theorem restates a committed endpoint byte for byte and proves it through the
abstraction; the axiom print of each pin is compared against the committed original below. -/

/-- Pin of `SqCyclotomicStageTuple.stage_nonempty_all_levels`: the committed level-`k`
induction, re-derived through the generic stage induction. -/
theorem pin_stage_nonempty_all_levels
    (h : ℕ) (base : LSquare.SqCyclotomicStageTuple K h 3)
    (hfg : ∃ s : Finset (maxProPQuotient 2 (GalK K)),
      (Subgroup.closure (s : Set (maxProPQuotient 2 (GalK K)))).topologicalClosure = ⊤)
    (Hcorr : ∀ (k : ℕ), 3 ≤ k → ∀ T : LSquare.SqCyclotomicStageTuple K h k,
      LSquare.SqCyclotomicStageTuple.DefectReachable T)
    (k : ℕ) : Nonempty (LSquare.SqCyclotomicStageTuple K h k) :=
  (Tuple.stage_nonempty_all_levels (ofSq base) hfg isProP_maxProPQuotient
    (fun k hk T ↦ defectReachable_ofSq (Hcorr k hk (toSq T))) k).map toSq

/-- Pin of `SqCyclotomicStageTuple.finiteLevelEpiData_nonempty_of_base_and_corrections`:
the committed cofinality endpoint, re-derived through the generic open-quotient descent and
the committed model adapter. -/
theorem pin_finiteLevelEpiData_nonempty_of_base_and_corrections
    (h : ℕ) (base : LSquare.SqCyclotomicStageTuple K h 3)
    (hfg : ∃ s : Finset (maxProPQuotient 2 (GalK K)),
      (Subgroup.closure (s : Set (maxProPQuotient 2 (GalK K)))).topologicalClosure = ⊤)
    (Hcorr : ∀ (k : ℕ), 3 ≤ k → ∀ T : LSquare.SqCyclotomicStageTuple K h k,
      LSquare.SqCyclotomicStageTuple.DefectReachable T)
    (U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K)))) :
    Nonempty (GQ2.Dyadic.LSquare.SqCyclotomicFiniteLevelEpiData (K := K) h U) :=
  (Tuple.openTuple_nonempty_of_base_and_corrections (ofSq base) hfg isProP_maxProPQuotient
    (fun k hk T ↦ defectReachable_ofSq (Hcorr k hk (toSq T))) U).map openTupleToEpiData

/-- Pin of `oddDegree_sqCyclotomicStageTuple_levelThree_of_finiteRealization`: the committed
seed reduction, re-derived through the generic frame adapter. -/
theorem pin_oddDegree_sqCyclotomicStageTuple_levelThree_of_finiteRealization
    (hframe : LSquare.OddDegreeSqCyclotomicFrattiniFrameSupply)
    (hrelation : LSquare.OddDegreeSqLevelThreeRelationRealization)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    {R : LocalReciprocity} (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    Nonempty (LSquare.SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) 3) := by
  obtain ⟨F, hcup⟩ := hframe K B hodd
  exact ⟨toSq ((frameOfSq F).toLevelThree (hrelation K hodd F hcup)
    (LSquare.maxProTwoGalK_isTopologicallyFinGen K) isProP_maxProPQuotient)⟩

/-- Pin of `oddDegree_sqCyclotomicStageTuple_levelThree`: the unconditional arbitrary
odd-degree level-three base, re-derived through the abstraction from the committed frame
supply and transgression realization.  Its axiom print must equal the committed one. -/
theorem pin_oddDegree_sqCyclotomicStageTuple_levelThree
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    {R : LocalReciprocity} (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    Nonempty (LSquare.SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) 3) :=
  pin_oddDegree_sqCyclotomicStageTuple_levelThree_of_finiteRealization
    LSquare.oddDegreeSqCyclotomicFrattiniFrameSupply_holds
    LSquare.oddDegreeSqLevelThreeRelationRealization K B hodd

end

end GQ2.Dyadic.StageGeneric

#print axioms GQ2.Dyadic.StageGeneric.lSqWord
#print axioms GQ2.Dyadic.StageGeneric.sqIndex_cases
#print axioms GQ2.Dyadic.StageGeneric.ofSq
#print axioms GQ2.Dyadic.StageGeneric.toSq
#print axioms GQ2.Dyadic.StageGeneric.admissibleOfSq
#print axioms GQ2.Dyadic.StageGeneric.defectReachable_ofSq
#print axioms GQ2.Dyadic.StageGeneric.openTupleToEpiData
#print axioms GQ2.Dyadic.StageGeneric.frameOfSq

/-! Pins next to their committed originals, for the no-growth axiom comparison. -/

#print axioms GQ2.Dyadic.StageGeneric.pin_stage_nonempty_all_levels
#print axioms GQ2.Dyadic.LSquare.SqCyclotomicStageTuple.stage_nonempty_all_levels

#print axioms GQ2.Dyadic.StageGeneric.pin_finiteLevelEpiData_nonempty_of_base_and_corrections
#print axioms GQ2.Dyadic.LSquare.SqCyclotomicStageTuple.finiteLevelEpiData_nonempty_of_base_and_corrections

#print axioms GQ2.Dyadic.StageGeneric.pin_oddDegree_sqCyclotomicStageTuple_levelThree_of_finiteRealization
#print axioms GQ2.Dyadic.LSquare.oddDegree_sqCyclotomicStageTuple_levelThree_of_finiteRealization

#print axioms GQ2.Dyadic.StageGeneric.pin_oddDegree_sqCyclotomicStageTuple_levelThree
#print axioms GQ2.Dyadic.LSquare.oddDegree_sqCyclotomicStageTuple_levelThree
