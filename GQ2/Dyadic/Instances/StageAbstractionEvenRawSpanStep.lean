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
* §2 the augmented span, its cubic base case through the committed
  `span_base_core_of_generators`, and the base supply at the two even cores `D_N`, `D_M`.
  The even twisted index is `1`, not the L template's `2` and not the coordinate `0` that
  physically carries the square; see the §2 header.
* §3 axiom pins.

## The `α` hypothesis

Everything in §1 is stated at the lane's standing **`2 ≤ α`**, inherited from
`evenRawStageShift_n` / `evenRawStageShift_m`, together with the word datum's own `1 ≤ α`
taken as a separate argument so that the caller's `nStageWord α h hα₁` appears verbatim.
§2 is `α`-free: the augmented span is a statement about a marking, and the relator enters
only through the coordinate rows of part 1, which are already proved.
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

/-! ## §2 The augmented span and its cubic base

The clone of `GammaLSylowPreimageFieldLabuteRawSpanStep.lean`'s augmented target.  One
structural constant changes, and it is not cosmetic.

The committed generic engine `span_base_core_of_generators`
(`GQ2/Roe/Labute/GradedLie/SpanBase.lean`) takes a distinguished *twisted* index `t` and asks
for `v² · [v, marked t]` at `t`, bare brackets `[v, marked i]` away from `t`, and fourth-power
tails away from `t`.  For the L word `t` is the index `2` whose row literally reads
`v² · [v, x₁]`.

**At the even words the twisted index is `1`, not `0`.**  The square physically sits on the
coordinate-`0` row, but that row reads `v² · [v, base 0] · [v, base 1]`, which is not of the
engine's shape for any single letter.  What *is* available is the quotient of that row by the
coordinate-`1` row `[v, base 0]`, namely `v² · [v, base 1]`.  So the letter that cannot be
separated from the square is `base 1`, and the tails must omit index `1`.  This is the same
phenomenon as the extra division in part 1's `evenRawBracket_base_mem_shiftSpan`, seen one
level up. -/

section Augmented

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {h : ℕ}

/-- The coherent displayed tuple in `Q_(k+1)` attached to fixed ambient generators. -/
noncomputable def evenRawMarkedBase (generators : Fin (MarkedCore.coreRank h) → G) (k : ℕ) :
    Fin (MarkedCore.coreRank h) → levelQuot G (k + 1) :=
  fun i ↦ levelMk G (k + 1) (generators i)

/-- Topological generation upstairs gives ordinary generation by the marked classes in every
finite discrete level quotient. -/
theorem evenRawClosure_markedBase_eq_top
    (generators : Fin (MarkedCore.coreRank h) → G)
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G)
    (htop : (Subgroup.closure (Set.range generators)).topologicalClosure = ⊤)
    (k : ℕ) : Subgroup.closure (Set.range (evenRawMarkedBase generators k)) = ⊤ := by
  haveI := discreteTopology_levelQuot G hfg hpro (k + 1)
  have himg : (Subgroup.closure (Set.range generators)).map (levelMk G (k + 1)) =
      Subgroup.closure (Set.range (evenRawMarkedBase generators k)) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  rw [← himg, ← map_topologicalClosure_eq_of_discrete G _ _
      (continuous_levelMk G (k + 1)), htop]
  exact Subgroup.map_top_of_surjective _ (levelMk_surjective G (k + 1))

/-- Relator-adapted tails: every generator except the twisted slot `1` (see the section
header; the L template omits its slot `2`). -/
def evenRawTailAtomSet (generators : Fin (MarkedCore.coreRank h) → G) (k : ℕ) :
    Set (levelQuot G (k + 1)) :=
  {z | ∃ i : Fin (MarkedCore.coreRank h), i ≠ 1 ∧
    z = evenRawMarkedBase generators k i ^ 2 ^ (k - 1)}

/-- The span of the non-twisted tails. -/
noncomputable def evenRawTailSpan (generators : Fin (MarkedCore.coreRank h) → G) (k : ℕ) :
    Subgroup (levelQuot G (k + 1)) :=
  Subgroup.closure (evenRawTailAtomSet generators k)

/-- The even variable-rank target: literal raw shifts plus every non-twisted tail. -/
noncomputable def evenRawAugmentedSpan
    (generators : Fin (MarkedCore.coreRank h) → G) (k : ℕ) (hk : 3 ≤ k) :
    Subgroup (levelQuot G (k + 1)) :=
  evenRawShiftSpan (evenRawMarkedBase generators k) hk ⊔ evenRawTailSpan generators k

/-- The cubic base proposition, isolated from the uniform successor step. -/
def EvenRawAugmentedSpanBaseSupply (generators : Fin (MarkedCore.coreRank h) → G) : Prop :=
  zLayer G 3 ≤ evenRawAugmentedSpan generators 3 (by omega)

theorem evenRawShiftSpan_le_augmentedSpan
    (generators : Fin (MarkedCore.coreRank h) → G) {k : ℕ} (hk : 3 ≤ k) :
    evenRawShiftSpan (evenRawMarkedBase generators k) hk ≤
      evenRawAugmentedSpan generators k hk := le_sup_left

theorem evenRawTailSpan_le_augmentedSpan
    (generators : Fin (MarkedCore.coreRank h) → G) {k : ℕ} (hk : 3 ≤ k) :
    evenRawTailSpan generators k ≤ evenRawAugmentedSpan generators k hk := le_sup_right

theorem evenRawTail_mem_augmentedSpan
    (generators : Fin (MarkedCore.coreRank h) → G) {k : ℕ} (hk : 3 ≤ k)
    (i : Fin (MarkedCore.coreRank h)) (hi : i ≠ 1) :
    evenRawMarkedBase generators k i ^ 2 ^ (k - 1) ∈
      evenRawAugmentedSpan generators k hk :=
  evenRawTailSpan_le_augmentedSpan generators hk (Subgroup.subset_closure ⟨i, hi, rfl⟩)

/-- **The cubic base case at the even words, for every rank.**  The only ambient input beyond
finite generation and the pro-`2` property is that the displayed generator classes generate
`Q₄`.  The `hcol` branch is where the even lane differs from the L template: the engine's
diagonal shape `v² · [v, marked 1]` is obtained by dividing the coordinate-`0` row by the
coordinate-`1` row, both of which are literal rows. -/
theorem evenRawAugmentedSpanBaseSupply_of_generates
    (generators : Fin (MarkedCore.coreRank h) → G)
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G)
    (hgen : Subgroup.closure (Set.range (evenRawMarkedBase generators 3)) = ⊤) :
    EvenRawAugmentedSpanBaseSupply generators := by
  apply span_base_core_of_generators (evenRawMarkedBase generators 3) hgen hfg hpro
    (evenRawAugmentedSpan generators 3 (by omega)) (1 : Fin (MarkedCore.coreRank h))
  · intro v hv
    apply evenRawShiftSpan_le_augmentedSpan generators (by omega)
    let p : lambdaImage G 2 4 := ⟨v, hv⟩
    have hA := evenRawDepthShift_mem_shiftSpan (evenRawMarkedBase generators 3) (by omega)
      (evenRawDepthCoordinateCorrection 1 p : EvenRawDepthCorrection G h 3)
    rw [evenRawDepthShiftHom_one_apply (evenRawMarkedBase generators 3) (by omega) p] at hA
    have hB := evenRawDepthShift_mem_shiftSpan (evenRawMarkedBase generators 3) (by omega)
      (evenRawDepthCoordinateCorrection 0 p : EvenRawDepthCorrection G h 3)
    rw [evenRawDepthShiftHom_zero_apply (evenRawMarkedBase generators 3) (by omega) p] at hB
    have hcen : ∀ t, Commute (commP p.1 (evenRawMarkedBase generators 3 0)) t :=
      zLayer_commute (commP_mem_zLayer 3 (by omega) p.2 _)
    have hrw : (commP p.1 (evenRawMarkedBase generators 3 0))⁻¹ *
        (p.1 ^ 2 * commP p.1 (evenRawMarkedBase generators 3 0) *
          commP p.1 (evenRawMarkedBase generators 3 1)) =
        p.1 ^ 2 * commP p.1 (evenRawMarkedBase generators 3 1) := by
      rw [← (hcen (p.1 ^ 2)).eq]
      group
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ hA) hB
    rwa [hrw] at h
  · intro i hi v hv
    let p : lambdaImage G 2 4 := ⟨v, hv⟩
    apply evenRawShiftSpan_le_augmentedSpan generators (by omega)
    refine evenIndex_cases
      (P := fun i ↦ i ≠ 1 → commP p.1 (evenRawMarkedBase generators 3 i) ∈
        evenRawShiftSpan (evenRawMarkedBase generators 3) (by omega))
      ?_ ?_ ?_ ?_ ?_ ?_ i hi
    · intro _
      have hmem := evenRawDepthShift_mem_shiftSpan (evenRawMarkedBase generators 3) (by omega)
        (evenRawDepthCoordinateCorrection 1 p : EvenRawDepthCorrection G h 3)
      rwa [evenRawDepthShiftHom_one_apply (evenRawMarkedBase generators 3) (by omega) p]
        at hmem
    · intro hcontra
      exact (hcontra rfl).elim
    · intro _
      have hmem := evenRawDepthShift_mem_shiftSpan (evenRawMarkedBase generators 3) (by omega)
        (evenRawDepthCoordinateCorrection 3 p : EvenRawDepthCorrection G h 3)
      rwa [evenRawDepthShiftHom_three_apply (evenRawMarkedBase generators 3) (by omega) p]
        at hmem
    · intro _
      have hmem := evenRawDepthShift_mem_shiftSpan (evenRawMarkedBase generators 3) (by omega)
        (evenRawDepthCoordinateCorrection 2 p : EvenRawDepthCorrection G h 3)
      rwa [evenRawDepthShiftHom_two_apply (evenRawMarkedBase generators 3) (by omega) p]
        at hmem
    · intro j _
      have hmem := evenRawDepthShift_mem_shiftSpan (evenRawMarkedBase generators 3) (by omega)
        (evenRawDepthCoordinateCorrection (MarkedCore.handleIdxV j) p :
          EvenRawDepthCorrection G h 3)
      rwa [evenRawDepthShiftHom_handleV_apply
        (evenRawMarkedBase generators 3) (by omega) j p] at hmem
    · intro j _
      have hmem := evenRawDepthShift_mem_shiftSpan (evenRawMarkedBase generators 3) (by omega)
        (evenRawDepthCoordinateCorrection (MarkedCore.handleIdxU j) p :
          EvenRawDepthCorrection G h 3)
      rwa [evenRawDepthShiftHom_handleU_apply
        (evenRawMarkedBase generators 3) (by omega) j p] at hmem
  · intro i hi
    simpa using evenRawTail_mem_augmentedSpan generators (k := 3) (by omega) i hi

/-- The cubic base proposition for the actual `D_N` presentation, uniformly in `α` and in the
number `h` of hyperbolic handle pairs. -/
theorem evenRawAugmentedSpanBaseSupply_dn (α h : ℕ) :
    EvenRawAugmentedSpanBaseSupply (MarkedCore.dnGen α h) :=
  evenRawAugmentedSpanBaseSupply_of_generates (MarkedCore.dnGen α h)
    (dnFinsetTopGen α h) (MarkedCore.isProP_DN α h)
    (evenRawClosure_markedBase_eq_top (MarkedCore.dnGen α h) (dnFinsetTopGen α h)
      (MarkedCore.isProP_DN α h) (MarkedCore.dn_topGen α h) 3)

/-- The cubic base proposition for the actual `D_M` presentation. -/
theorem evenRawAugmentedSpanBaseSupply_dm (α h : ℕ) :
    EvenRawAugmentedSpanBaseSupply (MarkedCore.dmGen α h) :=
  evenRawAugmentedSpanBaseSupply_of_generates (MarkedCore.dmGen α h)
    (dmFinsetTopGen α h) (MarkedCore.isProP_DM α h)
    (evenRawClosure_markedBase_eq_top (MarkedCore.dmGen α h) (dmFinsetTopGen α h)
      (MarkedCore.isProP_DM α h) (MarkedCore.dm_topGen α h) 3)

end Augmented

end

end GQ2.Dyadic.StageGeneric

/-! ## §3 Axiom pins

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
#print axioms GQ2.Dyadic.StageGeneric.evenRawMarkedBase
#print axioms GQ2.Dyadic.StageGeneric.evenRawClosure_markedBase_eq_top
#print axioms GQ2.Dyadic.StageGeneric.evenRawTailAtomSet
#print axioms GQ2.Dyadic.StageGeneric.evenRawTailSpan
#print axioms GQ2.Dyadic.StageGeneric.evenRawAugmentedSpan
#print axioms GQ2.Dyadic.StageGeneric.EvenRawAugmentedSpanBaseSupply
#print axioms GQ2.Dyadic.StageGeneric.evenRawShiftSpan_le_augmentedSpan
#print axioms GQ2.Dyadic.StageGeneric.evenRawTailSpan_le_augmentedSpan
#print axioms GQ2.Dyadic.StageGeneric.evenRawTail_mem_augmentedSpan
#print axioms GQ2.Dyadic.StageGeneric.evenRawAugmentedSpanBaseSupply_of_generates
#print axioms GQ2.Dyadic.StageGeneric.evenRawAugmentedSpanBaseSupply_dn
#print axioms GQ2.Dyadic.StageGeneric.evenRawAugmentedSpanBaseSupply_dm
