/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStageRankOne

/-!
# Primitive-residual regression for the variable-rank stage boundary

Until now only the *defect* form of the all-stage supply had a verified instance (`h = 0`,
`K = ℚ₂`).  The primitive-residual formulation used by the forward capstone
`nonempty_orientedEquiv_oddDegree_of_stageBase_and_primitiveResidualVanishing` had none, and the
in-tree implication chain ran in one direction only:

`PrimitiveResidualVanishing ⟹ KernelResidualCompatibility ⟺ span membership ⟺ defect supply`.

This file closes the loop and instantiates it:

* `stageResidual_primitiveVanishing_of_kernelResidualCompatibility` — the missing converse of
  `sharpCyclotomicInflationKernelResidualCompatibility_of_primitiveVanishing`, so all four
  formulations of the remaining arithmetic obligation are now equivalent, not merely ordered;
* `stageResidual_nonempty_actualDefectSupply_of_defectReachable` — the defect form of the stage
  premise supplies the explicit core-plus-handle sharp correction (previously only the reverse
  adapter `CoreHandleSharpActualDefectSupply.toDefectReachable` existed);
* `sqCyclotomicStageTuple_bot_primitiveResidualVanishing` — the `h = 0`, `K = ⊥` regression:
  the primitive-residual capstone premise is a theorem at the bottom field, derived from the
  unconditional rank-one defect theorem `sqCyclotomicStageTuple_bot_all_defectReachable`;
* `nonempty_orientedEquiv_bot_of_primitiveResidualVanishing` — the full-circle regression: the
  forward capstone consumes the new premise at `⊥` and reproduces the oriented classification.

No statement here weakens the general obligation: for `h > 0` the residual of an arbitrary
sharp-admissible base point remains open; this file certifies that the Prop family measuring it
is consistent and correctly wired.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Roe.Labute ContCoh

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

namespace SqCyclotomicStageTuple

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-! ## From exact fibres to sharp rows, correction by correction -/

/-- Any exact-fibre admissible correction is in particular sharp-admissible: exact character
representatives determine the extra mod-`2^(k+2)` digit.  Unlike
`sharpAdmissibleCorrection_nonempty`, this keeps the *given* correction, so equations about its
literal improved-word shift transfer unchanged. -/
noncomputable def stageResidualSharpOfAdmissible {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} (hk : 1 ≤ k)
    (W : AdmissibleCorrection T) : SharpAdmissibleCorrection T hk where
  correction := W.correction
  depth := W.depth
  sigma := exactFibre_implies_sharpChiLevel (by omega) W.sigma
  x0 := exactFibre_implies_sharpChiLevel (by omega) W.x0
  x1 := exactFibre_implies_sharpChiLevel (by omega) W.x1
  handleU := by
    intro j
    obtain ⟨x, hxchi, hx⟩ := W.handleU j
    have H : ∃ x : maxProPQuotient 2 (GalK K),
        chiCycKTwo (K := K) x = 1 ∧
          stageModified
            (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
            W.correction (SqCore.sqHandleIdxU j) =
              levelMk (maxProPQuotient 2 (GalK K)) (k + 1) x :=
      ⟨x, MonoidHom.mem_ker.mp hxchi, hx⟩
    simpa using exactFibre_implies_sharpChiLevel (by omega) H
  handleV := by
    intro j
    obtain ⟨x, hxchi, hx⟩ := W.handleV j
    have H : ∃ x : maxProPQuotient 2 (GalK K),
        chiCycKTwo (K := K) x = 1 ∧
          stageModified
            (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
            W.correction (SqCore.sqHandleIdxV j) =
              levelMk (maxProPQuotient 2 (GalK K)) (k + 1) x :=
      ⟨x, MonoidHom.mem_ker.mp hxchi, hx⟩
    simpa using exactFibre_implies_sharpChiLevel (by omega) H

@[simp] theorem stageResidualSharpOfAdmissible_correction {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} (hk : 1 ≤ k)
    (W : AdmissibleCorrection T) :
    (stageResidualSharpOfAdmissible hk W).correction = W.correction := rfl

/-! ## The defect form supplies the explicit core-plus-handle statement -/

/-- A defect-reachable stage has a sharp-admissible correction whose *literal* core-plus-handle
word kills the current actual defect.  This is the previously missing forward adapter into
`CoreHandleSharpActualDefectSupply`; the in-tree `toDefectReachable` is its converse (up to the
proven sharp exact-fibre lifting). -/
theorem stageResidual_nonempty_actualDefectSupply_of_defectReachable {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} (hk : 3 ≤ k)
    (H : DefectReachable T) :
    Nonempty (CoreHandleSharpActualDefectSupply T hk) := by
  obtain ⟨W, hW⟩ := H
  refine ⟨{ correction := stageResidualSharpOfAdmissible (by omega) W
            hitsDefect := ?_ }⟩
  let base := fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)
  change sqCoreHandleDbarWord base W.correction =
    (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹
  rw [sqCoreHandleDbarWord,
    ← stageShift_eq_dbarWordR2_mul_sqHandleDbarWord h k hk base W.correction W.depth]
  exact hW

/-! ## The converse transgression bridge -/

/-- **Converse of the primitive handoff.**  The residual functional identity on the higher
inflation kernel already forces the chain-level primitive statement: any primitive of any
inflated representative has vanishing normalized value on any lift of the residual.  Together
with `sharpCyclotomicInflationKernelResidualCompatibility_of_primitiveVanishing` this closes
the implication chain among all four formulations of the remaining stage obligation. -/
theorem stageResidual_primitiveVanishing_of_kernelResidualCompatibility
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (H : SharpCyclotomicInflationKernelResidualCompatibility T hk W hfg) :
    SharpCyclotomicInflationPrimitiveResidualVanishing T hk W hfg := by
  let G := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G k
  letI : DiscreteTopology Q :=
    discreteTopology_levelQuot G hfg isProP_maxProPQuotient k
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  unfold SharpCyclotomicInflationPrimitiveResidualVanishing
  dsimp only
  intro eta heta z b hz hdb n hn
  have hzero := H eta heta
  change (lowerTwoCentralTransgressionEquivAt G k (by omega) hfg
      isProP_maxProPQuotient).symm eta
        (Additive.ofMul (sharpNeutralResidualElement T hk W)) = 0 at hzero
  have hr : sharpNeutralResidualElement T hk W =
      ⟨levelMk G (k + 1) n.1, ⟨n.1, n.2, rfl⟩⟩ := Subtype.ext hn.symm
  rw [hr, lowerTwoCentralTransgressionEquivAt_symm_apply_eq_primitive
    G k (by omega) hfg isProP_maxProPQuotient eta z hz b hdb n] at hzero
  exact hzero

/-- All four formulations are equivalent; in particular the primitive-residual capstone premise
is *exactly* the defect supply, not a strengthening of it. -/
theorem stageResidual_primitiveVanishing_iff_kernelResidualCompatibility
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    SharpCyclotomicInflationPrimitiveResidualVanishing T hk W hfg ↔
      SharpCyclotomicInflationKernelResidualCompatibility T hk W hfg :=
  ⟨fun H ↦
    sharpCyclotomicInflationKernelResidualCompatibility_of_primitiveVanishing W hfg H,
   fun H ↦ stageResidual_primitiveVanishing_of_kernelResidualCompatibility W hfg H⟩

/-! ## Existence of a vanishing-residual base point from the defect form -/

/-- A defect-reachable stage admits a sharp-admissible base point with vanishing primitive
residual.  The witness is the sharp upgrade of the defect-killing correction itself: its
residual element is literally `1`, so span membership and the two boundary formulations follow
from the proven equivalences. -/
theorem stageResidual_exists_primitiveVanishing_of_defectReachable
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} (hk : 3 ≤ k)
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (H : DefectReachable T) :
    ∃ W : SharpAdmissibleCorrection T (by omega),
      SharpCyclotomicInflationPrimitiveResidualVanishing T hk W hfg := by
  obtain ⟨W0, hW0⟩ := H
  let W : SharpAdmissibleCorrection T (by omega) :=
    stageResidualSharpOfAdmissible (by omega) W0
  have hword : sqCoreHandleDbarWord
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
      W.correction =
        (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ := by
    change sqCoreHandleDbarWord
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
      W0.correction = _
    rw [sqCoreHandleDbarWord, ← stageShift_eq_dbarWordR2_mul_sqHandleDbarWord h k hk
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
      W0.correction W0.depth]
    exact hW0
  have hres : sharpNeutralResidualElement T hk W = 1 := by
    apply Subtype.ext
    change (sqCoreHandleDbarWord
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
        W.correction)⁻¹ *
      (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ = 1
    rw [hword]
    group
  have hmem : sharpNeutralResidualElement T hk W ∈ sharpNeutralBracketSpan T hk := by
    rw [hres]
    exact Subgroup.one_mem _
  have hcompat :=
    (sharpCyclotomicInflationKernelResidualCompatibility_iff_mem_bracketSpan
      W hfg).mpr hmem
  exact ⟨W, stageResidual_primitiveVanishing_of_kernelResidualCompatibility W hfg hcompat⟩

/-- The explicit core-plus-handle supply, in any of its equivalent forms, already yields the
primitive-residual capstone premise; no exact-fibre lifting input is consumed.  Consequently
the single remaining obligation of the forward capstone is exactly
`RawDefectSharpCharacterMatchSupply` (equivalently, nonemptiness of the sharp actual-defect
supply) at every stage. -/
theorem stageResidual_exists_primitiveVanishing_of_actualDefectSupply
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (H : Nonempty (CoreHandleSharpActualDefectSupply T hk)) :
    ∃ W : SharpAdmissibleCorrection T (by omega),
      SharpCyclotomicInflationPrimitiveResidualVanishing T hk W hfg := by
  obtain ⟨S⟩ := H
  have hmem : sharpNeutralResidualElement T hk S.correction ∈
      sharpNeutralBracketSpan T hk :=
    (nonempty_coreHandleSharpActualDefectSupply_iff_mem_bracketSpan S.correction).mp ⟨S⟩
  exact ⟨S.correction,
    stageResidual_primitiveVanishing_of_kernelResidualCompatibility S.correction hfg
      ((sharpCyclotomicInflationKernelResidualCompatibility_iff_mem_bracketSpan
        S.correction hfg).mpr hmem)⟩

end SqCyclotomicStageTuple

/-! ## The `h = 0`, `K = ⊥` primitive-residual regression -/

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **The primitive-residual capstone premise is a theorem at the bottom field.**  This is the
first verified instance of the primitive-residual formulation itself, obtained from the
unconditional rank-one defect theorem through the (now two-way) transgression chain. -/
theorem sqCyclotomicStageTuple_bot_primitiveResidualVanishing
    (k : ℕ) (hk : 3 ≤ k)
    (T : SqCyclotomicStageTuple
      (⊥ : IntermediateField ℚ_[2] ℚ̄₂) 0 k) :
    ∃ W : T.SharpAdmissibleCorrection (by omega),
      SqCyclotomicStageTuple.SharpCyclotomicInflationPrimitiveResidualVanishing T hk W
        (maxProTwoGalK_isTopologicallyFinGen
          (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) :=
  SqCyclotomicStageTuple.stageResidual_exists_primitiveVanishing_of_defectReachable hk
    (maxProTwoGalK_isTopologicallyFinGen (⊥ : IntermediateField ℚ_[2] ℚ̄₂))
    (sqCyclotomicStageTuple_bot_all_defectReachable k hk T)

/-- Full-circle regression: the forward capstone consumes the primitive-residual premise at the
bottom field and reproduces the oriented rank-one classification.  This certifies that the
chain-level Prop family in the capstone signature is consistent and correctly oriented before
any variable-rank investment. -/
theorem nonempty_orientedEquiv_bot_of_primitiveResidualVanishing :
    Nonempty (OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2]
        (⊥ : IntermediateField ℚ_[2] ℚ̄₂) - 1) / 2))
      (chiCycKTwo (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂)))) := by
  have hodd : Odd (Module.finrank ℚ_[2]
      (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) := by
    rw [IntermediateField.finrank_bot]
    exact odd_one
  have hhandles : ((Module.finrank ℚ_[2]
      (⊥ : IntermediateField ℚ_[2] ℚ̄₂) - 1) / 2) = 0 := by
    simp [IntermediateField.finrank_bot]
  obtain ⟨base⟩ := sqCyclotomicStageTuple_bot_three_nonempty
  have base' : SqCyclotomicStageTuple
      (⊥ : IntermediateField ℚ_[2] ℚ̄₂)
      ((Module.finrank ℚ_[2]
        (⊥ : IntermediateField ℚ_[2] ℚ̄₂) - 1) / 2) 3 := by
    rw [hhandles]
    exact base
  apply nonempty_orientedEquiv_oddDegree_of_stageBase_and_primitiveResidualVanishing
    (markedRecipAt _) hodd base'
  rw [hhandles]
  intro k hk T
  exact sqCyclotomicStageTuple_bot_primitiveResidualVanishing k hk T

#print axioms SqCyclotomicStageTuple.stageResidualSharpOfAdmissible
#print axioms SqCyclotomicStageTuple.stageResidual_nonempty_actualDefectSupply_of_defectReachable
#print axioms SqCyclotomicStageTuple.stageResidual_primitiveVanishing_of_kernelResidualCompatibility
#print axioms SqCyclotomicStageTuple.stageResidual_primitiveVanishing_iff_kernelResidualCompatibility
#print axioms SqCyclotomicStageTuple.stageResidual_exists_primitiveVanishing_of_defectReachable
#print axioms SqCyclotomicStageTuple.stageResidual_exists_primitiveVanishing_of_actualDefectSupply
#print axioms sqCyclotomicStageTuple_bot_primitiveResidualVanishing
#print axioms nonempty_orientedEquiv_bot_of_primitiveResidualVanishing

end

end GQ2.Dyadic.LSquare
