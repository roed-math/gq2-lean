/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenRawSpan

/-!
# W51-EV3F1, part 2: the even defect-reachability bridge and the augmented span step

Ticket **EV-3f** of `docs/dyadic/ev4b-stage-abstraction.md` §4, span half, continued from
`StageAbstractionEvenRawSpan.lean`.  The chain map is
`docs/dyadic/w51-ev3f-seam.md`; this file corresponds to
`GammaLSylowPreimageFieldLabuteRawSpanStep.lean`, preceded by the `Tuple`-level bridge that
the L template keeps at the end of its `RawSpan` file (moved here only because part 1 reached
its line budget).

## Contents

* §1 the bridge from the generic `rawDefectReachable` to membership in `evenRawShiftSpan`,
  at both even word data, plus the pure-square sufficiency statement.  These are the
  declarations the assembly half (**EV-3F2**) consumes; see the seam note §4.
* §2 axiom pins.

## The `α` hypothesis

Everything in §1 is stated at the lane's standing **`2 ≤ α`**, inherited from
`evenRawStageShift_n` / `evenRawStageShift_m`, together with the word datum's own `1 ≤ α`
taken as a separate argument so that the caller's `nStageWord α h hα₁` appears verbatim.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2
open GQ2.Roe.Labute

/-! ## §1 From the literal span to generic defect reachability

`rawDefectReachable` (the generic clone of `sqRawDefectReachable`,
`StageAbstraction.lean` §2) asks for one depth-`k-1` correction whose relator shift kills the
current defect.  By §4 of part 1 that shift *is* `evenRawDbarWord`, so reachability is exactly
membership of the inverse defect in `evenRawShiftSpan`.  No character refinement is hidden in
either direction. -/

section Bridge

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {α h k : ℕ}

/-- The canonical lift of a marking generates the next level, given that the marking
generates its own.  Extracted from the L template's
`sqRawDefectReachable_of_pureSquareSpan`. -/
theorem evenRawClosure_canonLift_eq_top
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) (hk : 3 ≤ k)
    {T : Fin (MarkedCore.coreRank h) → levelQuot G k}
    (htop : Subgroup.closure (Set.range T) = ⊤) :
    Subgroup.closure (Set.range fun i ↦ canonLift G k (T i)) = ⊤ := by
  refine eq_top_of_map_levelProj_eq_top G hfg hpro (by omega) ?_
  have himg : (GQ2.Roe.Labute.levelProj G k) '' Set.range (fun i ↦ canonLift G k (T i)) =
      Set.range T := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun i ↦ levelProj_canonLift G k (T i))
  rw [MonoidHom.map_closure, himg, htop]

/-- **The `N_α` bridge**: raw defect reachability is exactly membership of the current inverse
defect in the literal raw shift span. -/
theorem evenRawDefectReachable_n_iff (hα : 2 ≤ α) (hα₁ : 1 ≤ α) (hk : 3 ≤ k)
    (T : Fin (MarkedCore.coreRank h) → levelQuot G k) :
    rawDefectReachable (nStageWord α h hα₁) G k T ↔
      (stageDefect (nStageWord α h hα₁) G k T)⁻¹ ∈
        evenRawShiftSpan (fun i ↦ canonLift G k (T i)) hk := by
  constructor
  · rintro ⟨correction, hdepth, hkill⟩
    have hmem := evenRawDepthShift_mem_shiftSpan (fun i ↦ canonLift G k (T i)) hk
      (⟨correction, hdepth⟩ : EvenRawDepthCorrection G h k)
    change evenRawDbarWord (fun i ↦ canonLift G k (T i)) correction ∈ _ at hmem
    rwa [← evenRawStageShift_n hα hα₁ h k hk _ correction hdepth, hkill] at hmem
  · intro hmem
    obtain ⟨z, ⟨V, hV⟩, hz⟩ := hmem
    subst z
    refine ⟨V.correction, V.depth, ?_⟩
    rw [evenRawStageShift_n hα hα₁ h k hk _ V.correction V.depth]
    exact hz

/-- **The `M_α` bridge**, identical because both even words share `evenRawDbarWord` (part 1
§4). -/
theorem evenRawDefectReachable_m_iff (hα : 2 ≤ α) (hα₁ : 1 ≤ α) (hk : 3 ≤ k)
    (T : Fin (MarkedCore.coreRank h) → levelQuot G k) :
    rawDefectReachable (mStageWord α h hα₁) G k T ↔
      (stageDefect (mStageWord α h hα₁) G k T)⁻¹ ∈
        evenRawShiftSpan (fun i ↦ canonLift G k (T i)) hk := by
  constructor
  · rintro ⟨correction, hdepth, hkill⟩
    have hmem := evenRawDepthShift_mem_shiftSpan (fun i ↦ canonLift G k (T i)) hk
      (⟨correction, hdepth⟩ : EvenRawDepthCorrection G h k)
    change evenRawDbarWord (fun i ↦ canonLift G k (T i)) correction ∈ _ at hmem
    rwa [← evenRawStageShift_m hα hα₁ h k hk _ correction hdepth, hkill] at hmem
  · intro hmem
    obtain ⟨z, ⟨V, hV⟩, hz⟩ := hmem
    subst z
    refine ⟨V.correction, V.depth, ?_⟩
    rw [evenRawStageShift_m hα hα₁ h k hk _ V.correction V.depth]
    exact hz

/-- **The pure-square supply is enough for `N_α` raw defect reachability.**  An honest
reduction: generic tower generation handles every square and bracket atom, and the literal
handle rows handle every hyperbolic pair.  Stated against `stageZero` membership (relation
plus generation) rather than a `Tuple`, so it applies to any marking; a `Tuple`'s generators
qualify by `Tuple.generators_mem_stageZero`. -/
theorem evenRawDefectReachable_n_of_pureSquareSpan (hα : 2 ≤ α) (hα₁ : 1 ≤ α) (hk : 3 ≤ k)
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G)
    {T : Fin (MarkedCore.coreRank h) → levelQuot G k}
    (hT : T ∈ stageZero (nStageWord α h hα₁) G k)
    (Hsq : EvenRawPureSquareSpanSupply (fun i ↦ canonLift G k (T i)) hk) :
    rawDefectReachable (nStageWord α h hα₁) G k T := by
  rw [evenRawDefectReachable_n_iff hα hα₁ hk T,
    evenRawShiftSpan_eq_zLayer_of_pureSquares _ hk hfg hpro
      (evenRawClosure_canonLift_eq_top hfg hpro hk hT.2) Hsq]
  exact Subgroup.inv_mem _ (stageZero_defect_mem_zLayer (nStageWord α h hα₁) k hT)

/-- **The pure-square supply is enough for `M_α` raw defect reachability.** -/
theorem evenRawDefectReachable_m_of_pureSquareSpan (hα : 2 ≤ α) (hα₁ : 1 ≤ α) (hk : 3 ≤ k)
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G)
    {T : Fin (MarkedCore.coreRank h) → levelQuot G k}
    (hT : T ∈ stageZero (mStageWord α h hα₁) G k)
    (Hsq : EvenRawPureSquareSpanSupply (fun i ↦ canonLift G k (T i)) hk) :
    rawDefectReachable (mStageWord α h hα₁) G k T := by
  rw [evenRawDefectReachable_m_iff hα hα₁ hk T,
    evenRawShiftSpan_eq_zLayer_of_pureSquares _ hk hfg hpro
      (evenRawClosure_canonLift_eq_top hfg hpro hk hT.2) Hsq]
  exact Subgroup.inv_mem _ (stageZero_defect_mem_zLayer (mStageWord α h hα₁) k hT)

end Bridge

end

end GQ2.Dyadic.StageGeneric

/-! ## §2 Axiom pins

Every public declaration of the file, all at std-3
`[propext, Classical.choice, Quot.sound]`, matching the corresponding L template
`GammaLSylowPreimageFieldLabuteRawSpan.lean`'s two `SqCyclotomicStageTuple` endpoints
(`sqRawDefectReachable_iff_defect_mem_rawShiftSpan`,
`sqRawDefectReachable_of_pureSquareSpan`), which are std-3. -/

#print axioms GQ2.Dyadic.StageGeneric.evenRawClosure_canonLift_eq_top
#print axioms GQ2.Dyadic.StageGeneric.evenRawDefectReachable_n_iff
#print axioms GQ2.Dyadic.StageGeneric.evenRawDefectReachable_m_iff
#print axioms GQ2.Dyadic.StageGeneric.evenRawDefectReachable_n_of_pureSquareSpan
#print axioms GQ2.Dyadic.StageGeneric.evenRawDefectReachable_m_of_pureSquareSpan
