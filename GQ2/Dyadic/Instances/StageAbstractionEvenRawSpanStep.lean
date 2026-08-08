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
* §3 the successor engine: depth and square transport for the even shift word, the
  lift-with-square subgroup, the uniform step, and the induction.  Endpoint: the augmented
  span theorem at both even cores.  §3.1 records why `EvenRawPureSquareSpanSupply` is not and
  cannot be the endpoint, and pins the exact residual.
* §4 axiom pins.

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

/-! ## §3 The successor engine

The clone of `GammaLSylowPreimageFieldLabuteRawSpanStep.lean`'s lift-with-square engine,
closing the induction that §2's base case starts.

**What this achieves, and what it provably cannot.**  The endpoint is
`zLayer G k ≤ evenRawAugmentedSpan generators k hk` for every `k ≥ 3`: the literal even shifts
*together with* the relator-adapted tails span every central layer.  It is **not**
`EvenRawPureSquareSpanSupply`, and that is not a gap in the port.  The committed L file
`GammaLSylowPreimageFieldLabuteRawSpanObstruction.lean` proves
`¬ RawPureSquareSpanSupply (rawMarkedBase (SqCore.sqGen h) 3) _` outright, and its module
docstring records that "the augmented span theorem cannot be sharpened by simply deleting its
tails".  The pure-square supply is therefore *false* at the free core of the L word, and the
augmented span is the strongest true statement of this shape.  §3.1 records the exact residual
obligation in the even case. -/

section Engine

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {h k : ℕ}

private theorem evenRawSq_mem_lambdaImage_succ {j m : ℕ} {q : levelQuot G m}
    (hq : q ∈ lambdaImage G j m) : q ^ 2 ∈ lambdaImage G (j + 1) m := by
  obtain ⟨x, hx, rfl⟩ := hq
  exact ⟨x ^ 2, sq_mem_twoCentralSeries_succ G hx, by rw [map_pow]⟩

private theorem evenRawCommP_mem_lambdaImage_succ {j m : ℕ}
    {v : levelQuot G m} (hv : v ∈ lambdaImage G j m) (g : levelQuot G m) :
    commP v g ∈ lambdaImage G (j + 1) m :=
  commP_mem_lambdaImage_add hv (by rw [lambdaImage_one_eq_top]; trivial)

/-- The core block gains one unit of depth over its correction. -/
private theorem evenRawCoreDbar_mem_lambdaImage_succ (k : ℕ) {j : ℕ}
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G j (k + 1)) :
    evenRawCoreDbarWord base correction ∈ lambdaImage G (j + 1) (k + 1) :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (evenRawSq_mem_lambdaImage_succ (hdepth 0))
      (evenRawCommP_mem_lambdaImage_succ (hdepth 0) _))
    (Subgroup.mul_mem _ (evenRawCommP_mem_lambdaImage_succ (hdepth 1) _)
      (evenRawCommP_mem_lambdaImage_succ (hdepth 0) _)))
    (Subgroup.mul_mem _ (evenRawCommP_mem_lambdaImage_succ (hdepth 3) _)
      (evenRawCommP_mem_lambdaImage_succ (hdepth 2) _))

/-- The handle block gains one unit of depth over its correction. -/
private theorem evenRawHandleDbar_mem_lambdaImage_succ (k : ℕ) {j : ℕ}
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G j (k + 1)) :
    evenRawHandleDbarWord base correction ∈ lambdaImage G (j + 1) (k + 1) := by
  rw [evenRawHandleDbarWord]
  apply Subgroup.list_prod_mem
  intro z hz
  simp only [List.mem_map] at hz
  obtain ⟨l, _, rfl⟩ := hz
  exact Subgroup.mul_mem _
    (evenRawCommP_mem_lambdaImage_succ (hdepth (MarkedCore.handleIdxV l)) _)
    (evenRawCommP_mem_lambdaImage_succ (hdepth (MarkedCore.handleIdxU l)) _)

/-- **The even shift word gains one unit of depth over its correction.**  Used at `j = k - 2`
for square transport and at `j = k - 1` for the lift engine. -/
theorem evenRawDbar_mem_lambdaImage_succ (k : ℕ) {j : ℕ}
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G j (k + 1)) :
    evenRawDbarWord base correction ∈ lambdaImage G (j + 1) (k + 1) :=
  Subgroup.mul_mem _ (evenRawCoreDbar_mem_lambdaImage_succ k base correction hdepth)
    (evenRawHandleDbar_mem_lambdaImage_succ k base correction hdepth)

/-! ### Square transport -/

private theorem evenRaw_list_prod_sq_of_mem_lambdaImage_pred
    {k : ℕ} (hk : 3 ≤ k) {Ι : Type*} (l : List Ι) (f : Ι → levelQuot G (k + 1))
    (hf : ∀ i ∈ l, f i ∈ lambdaImage G (k - 1) (k + 1)) :
    (l.map f).prod ^ 2 = (l.map fun i ↦ f i ^ 2).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
      have hi := hf i (by simp)
      have htail : (l.map f).prod ∈ lambdaImage G (k - 1) (k + 1) := by
        apply Subgroup.list_prod_mem
        intro z hz
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
        exact hf j (List.mem_cons_of_mem _ hj)
      rw [List.map_cons, List.prod_cons,
        sq_mul_of_mem_lambdaImage_pred k hk hi htail,
        ih (fun j hj ↦ hf j (List.mem_cons_of_mem _ hj)),
        List.map_cons, List.prod_cons]

/-- Square transport for the even handle block. -/
theorem evenRawHandleDbarWord_sq [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (h k : ℕ) (hk : 4 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 2) (k + 1)) :
    evenRawHandleDbarWord base correction ^ 2 =
      evenRawHandleDbarWord base (fun i ↦ correction i ^ 2) := by
  have hc : ∀ i j, commP (correction i) (base j) ∈ lambdaImage G (k - 1) (k + 1) := by
    intro i j
    have hmem := evenRawCommP_mem_lambdaImage_succ (hdepth i) (base j)
    rwa [show k - 2 + 1 = k - 1 by omega] at hmem
  rw [evenRawHandleDbarWord,
    evenRaw_list_prod_sq_of_mem_lambdaImage_pred (by omega) (List.finRange h) _
      (fun l _ ↦ Subgroup.mul_mem _ (hc (MarkedCore.handleIdxV l) _)
        (hc (MarkedCore.handleIdxU l) _)),
    evenRawHandleDbarWord]
  congr 1
  apply List.map_congr_left
  intro l _
  rw [sq_mul_of_mem_lambdaImage_pred k (by omega)
      (hc (MarkedCore.handleIdxV l) _) (hc (MarkedCore.handleIdxU l) _),
    commP_sq_of_mem_lambdaImage k hk _ (hdepth (MarkedCore.handleIdxV l)),
    commP_sq_of_mem_lambdaImage k hk _ (hdepth (MarkedCore.handleIdxU l))]

/-- Square transport for the even core block. -/
theorem evenRawCoreDbarWord_sq [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (h k : ℕ) (hk : 4 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 2) (k + 1)) :
    evenRawCoreDbarWord base correction ^ 2 =
      evenRawCoreDbarWord base (fun i ↦ correction i ^ 2) := by
  have hd : ∀ i, correction i ^ 2 ∈ lambdaImage G (k - 1) (k + 1) := by
    intro i
    have hmem := evenRawSq_mem_lambdaImage_succ (hdepth i)
    rwa [show k - 2 + 1 = k - 1 by omega] at hmem
  have hc : ∀ i j, commP (correction i) (base j) ∈ lambdaImage G (k - 1) (k + 1) := by
    intro i j
    have hmem := evenRawCommP_mem_lambdaImage_succ (hdepth i) (base j)
    rwa [show k - 2 + 1 = k - 1 by omega] at hmem
  rw [evenRawCoreDbarWord, evenRawCoreDbarWord,
    sq_mul_of_mem_lambdaImage_pred k (by omega)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hd 0) (hc 0 0))
        (Subgroup.mul_mem _ (hc 1 0) (hc 0 1)))
      (Subgroup.mul_mem _ (hc 3 2) (hc 2 3)),
    sq_mul_of_mem_lambdaImage_pred k (by omega)
      (Subgroup.mul_mem _ (hd 0) (hc 0 0)) (Subgroup.mul_mem _ (hc 1 0) (hc 0 1)),
    sq_mul_of_mem_lambdaImage_pred k (by omega) (hd 0) (hc 0 0),
    sq_mul_of_mem_lambdaImage_pred k (by omega) (hc 1 0) (hc 0 1),
    sq_mul_of_mem_lambdaImage_pred k (by omega) (hc 3 2) (hc 2 3)]
  simp only [commP_sq_of_mem_lambdaImage k hk _ (hdepth 0),
    commP_sq_of_mem_lambdaImage k hk _ (hdepth 1),
    commP_sq_of_mem_lambdaImage k hk _ (hdepth 2),
    commP_sq_of_mem_lambdaImage k hk _ (hdepth 3)]

/-- **Square transport for the complete even shift word**, the variable-rank replacement for
the fixed-rank `dbarWordR2_sq`. -/
theorem evenRawDbarWord_sq [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (h k : ℕ) (hk : 4 ≤ k)
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hdepth : ∀ i, correction i ∈ lambdaImage G (k - 2) (k + 1)) :
    evenRawDbarWord base correction ^ 2 =
      evenRawDbarWord base (fun i ↦ correction i ^ 2) := by
  have hcore : evenRawCoreDbarWord base correction ∈ lambdaImage G (k - 1) (k + 1) := by
    have hmem := evenRawCoreDbar_mem_lambdaImage_succ k base correction hdepth
    rwa [show k - 2 + 1 = k - 1 by omega] at hmem
  have hhandle : evenRawHandleDbarWord base correction ∈ lambdaImage G (k - 1) (k + 1) := by
    have hmem := evenRawHandleDbar_mem_lambdaImage_succ k base correction hdepth
    rwa [show k - 2 + 1 = k - 1 by omega] at hmem
  rw [evenRawDbarWord, sq_mul_of_mem_lambdaImage_pred k (by omega) hcore hhandle,
    evenRawCoreDbarWord_sq h k hk base correction hdepth,
    evenRawHandleDbarWord_sq h k hk base correction hdepth, evenRawDbarWord]

/-- Projection through the tower commutes with the even shift word. -/
theorem levelProj_evenRawDbarWord
    (base correction : Fin (MarkedCore.coreRank h) → levelQuot G (k + 2)) :
    GQ2.Roe.Labute.levelProj G (k + 1) (evenRawDbarWord base correction) =
      evenRawDbarWord (fun i ↦ GQ2.Roe.Labute.levelProj G (k + 1) (base i))
        (fun i ↦ GQ2.Roe.Labute.levelProj G (k + 1) (correction i)) := by
  rw [evenRawDbarWord, evenRawDbarWord, map_mul]
  congr 1
  · simp only [evenRawCoreDbarWord, commP, map_mul, map_inv, map_pow]
  · rw [evenRawHandleDbarWord, evenRawHandleDbarWord, map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro l _
    simp only [Function.comp_apply, commP, map_mul, map_inv]


/-! ### The lift-with-square engine -/

section Lift

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Classes at level `k+1` possessing a depth-`k` lift whose square lies in `T`. -/
private noncomputable def evenRawLiftSq (k : ℕ) (hk : 3 ≤ k)
    (T : Subgroup (levelQuot G (k + 2))) : Subgroup (levelQuot G (k + 1)) where
  carrier := {q | ∃ q' ∈ lambdaImage G k (k + 2),
    GQ2.Roe.Labute.levelProj G (k + 1) q' = q ∧ q' ^ 2 ∈ T}
  one_mem' := ⟨1, Subgroup.one_mem _, map_one _, by simp⟩
  mul_mem' := by
    rintro x y ⟨x', hx', hxp, hxs⟩ ⟨y', hy', hyp, hys⟩
    refine ⟨x' * y', Subgroup.mul_mem _ hx' hy', by rw [map_mul, hxp, hyp], ?_⟩
    rw [sq_mul_of_mem_lambdaImage_pred (k + 1) (by omega) hx' hy']
    exact Subgroup.mul_mem _ hxs hys
  inv_mem' := by
    rintro x ⟨x', hx', hxp, hxs⟩
    exact ⟨x'⁻¹, Subgroup.inv_mem _ hx', by rw [map_inv, hxp], by
      rw [inv_pow]
      exact Subgroup.inv_mem _ hxs⟩

private theorem evenRawTail_mem_liftSq (generators : Fin (MarkedCore.coreRank h) → G)
    (k : ℕ) (hk : 3 ≤ k) (i : Fin (MarkedCore.coreRank h)) (hi : i ≠ 1) :
    evenRawMarkedBase generators k i ^ 2 ^ (k - 1) ∈
      evenRawLiftSq k hk (evenRawAugmentedSpan generators (k + 1) (by omega)) := by
  refine ⟨evenRawMarkedBase generators (k + 1) i ^ 2 ^ (k - 1), ?_, ?_, ?_⟩
  · have hmem := pow_two_pow_mem_lambdaImage
      (evenRawMarkedBase generators (k + 1) i) (k - 1)
    rwa [show 1 + (k - 1) = k by omega] at hmem
  · simp [evenRawMarkedBase]
  · rw [← pow_mul, show (2 : ℕ) ^ (k - 1) * 2 = 2 ^ k by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]]
    exact evenRawTail_mem_augmentedSpan generators (by omega) i hi

/-- Every old raw-shift value lifts to a depth-`k` element whose square is a next-level
raw-shift value.  The handle-general square-transport step. -/
private theorem evenRawShiftSpan_le_liftSq (generators : Fin (MarkedCore.coreRank h) → G)
    (k : ℕ) (hk : 3 ≤ k) :
    evenRawShiftSpan (evenRawMarkedBase generators k) hk ≤
      evenRawLiftSq k hk (evenRawAugmentedSpan generators (k + 1) (by omega)) := by
  rintro _ ⟨_, ⟨V, rfl⟩, rfl⟩
  choose correction' hdepth' hproj using fun i ↦
    exists_levelProj_preimage_lambdaImage (k - 1) (k + 1) (V.depth i)
  have hnext : evenRawDbarWord (evenRawMarkedBase generators (k + 1)) correction' ∈
      lambdaImage G k (k + 2) := by
    have hmem := evenRawDbar_mem_lambdaImage_succ (k + 1)
      (evenRawMarkedBase generators (k + 1)) correction' hdepth'
    rwa [show k - 1 + 1 = k by omega] at hmem
  refine ⟨evenRawDbarWord (evenRawMarkedBase generators (k + 1)) correction', hnext, ?_, ?_⟩
  · change GQ2.Roe.Labute.levelProj G (k + 1)
      (evenRawDbarWord (evenRawMarkedBase generators (k + 1)) correction') =
        evenRawDbarWord (evenRawMarkedBase generators k) V.correction
    rw [levelProj_evenRawDbarWord]
    have hbaseProj :
        (fun i ↦ GQ2.Roe.Labute.levelProj G (k + 1)
          (evenRawMarkedBase generators (k + 1) i)) = evenRawMarkedBase generators k := by
      funext i
      rfl
    have hcorrProj :
        (fun i ↦ GQ2.Roe.Labute.levelProj G (k + 1) (correction' i)) = V.correction := by
      funext i
      exact hproj i
    rw [hbaseProj, hcorrProj]
  · have hsqDepth : ∀ i, correction' i ^ 2 ∈ lambdaImage G k (k + 2) := by
      intro i
      have hmem := evenRawSq_mem_lambdaImage_succ (hdepth' i)
      rwa [show k - 1 + 1 = k by omega] at hmem
    have hmem := evenRawDepthShift_mem_shiftSpan
      (evenRawMarkedBase generators (k + 1)) (by omega)
      (⟨fun i ↦ correction' i ^ 2, hsqDepth⟩ : EvenRawDepthCorrection G h (k + 1))
    have hmem' := evenRawShiftSpan_le_augmentedSpan generators (by omega) hmem
    rwa [show evenRawDbarWord (evenRawMarkedBase generators (k + 1)) correction' ^ 2 =
        evenRawDbarWord (evenRawMarkedBase generators (k + 1))
          (fun i ↦ correction' i ^ 2) from
      evenRawDbarWord_sq h (k + 1) (by omega)
        (evenRawMarkedBase generators (k + 1)) correction' hdepth']

/-- The whole old augmented target sits inside the lift-with-square subgroup. -/
private theorem evenRawAugmentedSpan_le_liftSq
    (generators : Fin (MarkedCore.coreRank h) → G) (k : ℕ) (hk : 3 ≤ k) :
    evenRawAugmentedSpan generators k hk ≤
      evenRawLiftSq k hk (evenRawAugmentedSpan generators (k + 1) (by omega)) := by
  apply sup_le
  · exact evenRawShiftSpan_le_liftSq generators k hk
  · rw [evenRawTailSpan, Subgroup.closure_le]
    rintro z ⟨i, hi, rfl⟩
    exact evenRawTail_mem_liftSq generators k hk i hi

/-- The induction hypothesis at layer `k` supplies every pure-square atom needed at layer
`k+1`. -/
theorem evenRawSquare_mem_augmentedSpan_succ
    (generators : Fin (MarkedCore.coreRank h) → G) (k : ℕ) (hk : 3 ≤ k)
    (prev : zLayer G k ≤ evenRawAugmentedSpan generators k hk) :
    ∀ v ∈ twoCentralSeries G k,
      levelMk G (k + 2) (v ^ 2) ∈ evenRawAugmentedSpan generators (k + 1) (by omega) := by
  intro v hv
  have hold : levelMk G (k + 1) v ∈ evenRawAugmentedSpan generators k hk := prev ⟨v, hv, rfl⟩
  obtain ⟨q', hq'depth, hq'proj, hq'sq⟩ :=
    evenRawAugmentedSpan_le_liftSq generators k hk hold
  have hproj : GQ2.Roe.Labute.levelProj G (k + 1) (levelMk G (k + 2) v) =
      GQ2.Roe.Labute.levelProj G (k + 1) q' := by
    rw [levelProj_levelMk, hq'proj]
  obtain ⟨z, hz, hzeq⟩ := exists_zLayer_mul hproj
  rw [map_pow, hzeq, (zLayer_commute hz q').eq, sq_mul_zLayer (k + 1) hz]
  exact hq'sq

/-- Bracket recovery inside the augmented span.  As in part 1, coordinate `1` delivers
`[p, base 0]` first and only then does the coordinate-`0` row yield `[p, base 1]`. -/
private theorem evenRawBracket_base_mem_augmentedSpan
    (generators : Fin (MarkedCore.coreRank h) → G) (k : ℕ) (hk : 3 ≤ k)
    (Hsq : ∀ p : lambdaImage G (k - 1) (k + 1),
      p.1 ^ 2 ∈ evenRawAugmentedSpan generators k hk)
    (p : lambdaImage G (k - 1) (k + 1)) (i : Fin (MarkedCore.coreRank h)) :
    commP p.1 (evenRawMarkedBase generators k i) ∈
      evenRawAugmentedSpan generators k hk := by
  have hraw : evenRawShiftSpan (evenRawMarkedBase generators k) hk ≤
      evenRawAugmentedSpan generators k hk := evenRawShiftSpan_le_augmentedSpan generators hk
  have hb0 : commP p.1 (evenRawMarkedBase generators k 0) ∈
      evenRawAugmentedSpan generators k hk := by
    apply hraw
    have hmem := evenRawDepthShift_mem_shiftSpan (evenRawMarkedBase generators k) hk
      (evenRawDepthCoordinateCorrection 1 p : EvenRawDepthCorrection G h k)
    rwa [evenRawDepthShiftHom_one_apply (evenRawMarkedBase generators k) hk p] at hmem
  refine evenIndex_cases
    (P := fun i ↦ commP p.1 (evenRawMarkedBase generators k i) ∈
      evenRawAugmentedSpan generators k hk) hb0 ?_ ?_ ?_ ?_ ?_ i
  · have hdiag : p.1 ^ 2 * commP p.1 (evenRawMarkedBase generators k 0) *
        commP p.1 (evenRawMarkedBase generators k 1) ∈
          evenRawAugmentedSpan generators k hk := by
      apply hraw
      have hmem := evenRawDepthShift_mem_shiftSpan (evenRawMarkedBase generators k) hk
        (evenRawDepthCoordinateCorrection 0 p : EvenRawDepthCorrection G h k)
      rwa [evenRawDepthShiftHom_zero_apply (evenRawMarkedBase generators k) hk p] at hmem
    have hmem := Subgroup.mul_mem _
      (Subgroup.inv_mem _ (Subgroup.mul_mem _ (Hsq p) hb0)) hdiag
    simpa only [inv_mul_cancel_left] using hmem
  · apply hraw
    have hmem := evenRawDepthShift_mem_shiftSpan (evenRawMarkedBase generators k) hk
      (evenRawDepthCoordinateCorrection 3 p : EvenRawDepthCorrection G h k)
    rwa [evenRawDepthShiftHom_three_apply (evenRawMarkedBase generators k) hk p] at hmem
  · apply hraw
    have hmem := evenRawDepthShift_mem_shiftSpan (evenRawMarkedBase generators k) hk
      (evenRawDepthCoordinateCorrection 2 p : EvenRawDepthCorrection G h k)
    rwa [evenRawDepthShiftHom_two_apply (evenRawMarkedBase generators k) hk p] at hmem
  · intro j
    apply hraw
    have hmem := evenRawDepthShift_mem_shiftSpan (evenRawMarkedBase generators k) hk
      (evenRawDepthCoordinateCorrection (MarkedCore.handleIdxV j) p :
        EvenRawDepthCorrection G h k)
    rwa [evenRawDepthShiftHom_handleV_apply (evenRawMarkedBase generators k) hk j p] at hmem
  · intro j
    apply hraw
    have hmem := evenRawDepthShift_mem_shiftSpan (evenRawMarkedBase generators k) hk
      (evenRawDepthCoordinateCorrection (MarkedCore.handleIdxU j) p :
        EvenRawDepthCorrection G h k)
    rwa [evenRawDepthShiftHom_handleU_apply (evenRawMarkedBase generators k) hk j p] at hmem

open scoped commutatorElement in
private theorem evenRawCommutator_eq_commP_inv_step {H' : Type*} [Group H'] (v g : H') :
    ⁅v, g⁆ = commP v⁻¹ g⁻¹ := by
  simp only [commutatorElement_def, commP, inv_inv]

/-- **The uniform successor step.**  The only induction hypothesis is the preceding augmented
span inclusion; the handle rows need no extra assumption. -/
theorem evenRawAugmentedSpan_step (generators : Fin (MarkedCore.coreRank h) → G)
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) (k : ℕ) (hk : 3 ≤ k)
    (hgen : Subgroup.closure (Set.range (evenRawMarkedBase generators (k + 1))) = ⊤)
    (prev : zLayer G k ≤ evenRawAugmentedSpan generators k hk) :
    zLayer G (k + 1) ≤ evenRawAugmentedSpan generators (k + 1) (by omega) := by
  intro q hq
  refine lambdaImage_induction G hfg hpro (j := k) (by omega)
    (p := fun z ↦ z ∈ evenRawAugmentedSpan generators (k + 1) (by omega)) ?_ ?_
    (Subgroup.one_mem _) (fun _ _ ↦ Subgroup.mul_mem _) (fun _ ↦ Subgroup.inv_mem _) hq
  · exact evenRawSquare_mem_augmentedSpan_succ generators k hk prev
  · intro v hv g
    let p : lambdaImage G k (k + 2) :=
      ⟨(levelMk G (k + 2) v)⁻¹, ⟨v⁻¹, Subgroup.inv_mem _ hv, by rw [map_inv]⟩⟩
    have Hsq : ∀ p : lambdaImage G k (k + 2),
        p.1 ^ 2 ∈ evenRawAugmentedSpan generators (k + 1) (by omega) := by
      rintro ⟨p, hp⟩
      obtain ⟨x, hx, hxp⟩ := hp
      subst p
      simpa only [map_pow] using
        evenRawSquare_mem_augmentedSpan_succ generators k hk prev x hx
    have hp : ∀ z : levelQuot G (k + 2),
        commP p.1 z ∈ evenRawAugmentedSpan generators (k + 1) (by omega) := by
      intro z
      have hz : z ∈ Subgroup.closure
          (Set.range (evenRawMarkedBase generators (k + 1))) := by rw [hgen]; trivial
      refine Subgroup.closure_induction
        (p := fun x _ ↦ commP p.1 x ∈
          evenRawAugmentedSpan generators (k + 1) (by omega)) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨i, rfl⟩
        exact evenRawBracket_base_mem_augmentedSpan generators (k + 1) (by omega) Hsq p i
      · simp [commP]
      · intro x y _ _ hx hy
        rw [commP_mul_right_of_mem (k + 1) (by omega) p.2 x y]
        exact Subgroup.mul_mem _ hx hy
      · intro x _ hx
        rw [commP_inv_right_of_mem (k + 1) (by omega) p.2 x]
        exact Subgroup.inv_mem _ hx
    rw [map_commutatorElement, evenRawCommutator_eq_commP_inv_step]
    exact hp (levelMk G (k + 2) g)⁻¹

/-- **Base plus step gives every augmented span inclusion.**  The per-level generation
hypothesis stays explicit, so this applies both to free generators and to any coherent
displayed tuple. -/
theorem evenRawAugmentedSpan_of_base_of_step (generators : Fin (MarkedCore.coreRank h) → G)
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G)
    (hgen : ∀ k, 3 ≤ k →
      Subgroup.closure (Set.range (evenRawMarkedBase generators (k + 1))) = ⊤)
    (hbase : EvenRawAugmentedSpanBaseSupply generators) :
    ∀ (k : ℕ) (hk : 3 ≤ k), zLayer G k ≤ evenRawAugmentedSpan generators k hk := by
  intro k hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction n with
  | zero => simpa only [EvenRawAugmentedSpanBaseSupply] using hbase
  | succ n ih =>
      have hkn : 3 ≤ 3 + n := by omega
      simpa only [Nat.add_succ] using
        evenRawAugmentedSpan_step generators hfg hpro (3 + n) hkn (hgen (3 + n) hkn) (ih hkn)

end Lift


/-! ### The endpoints at the two even cores -/

section Cores

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- **The even `D_N` augmented span theorem.**  The literal `N_α` shifts together with the
relator-adapted non-twisted tails span every central layer from degree three onward, uniformly
in `α` and in the number of handle pairs.  This is the even analogue of the committed
`sqCore_rawAugmentedSpan_all`, and it is the strongest true statement of this shape: see the
§3 header on the L obstruction. -/
theorem evenRawAugmentedSpan_all_dn (α h : ℕ) :
    ∀ (k : ℕ) (hk : 3 ≤ k),
      zLayer (MarkedCore.DN α h : Type) k ≤
        evenRawAugmentedSpan (MarkedCore.dnGen α h) k hk := by
  apply evenRawAugmentedSpan_of_base_of_step (MarkedCore.dnGen α h)
    (dnFinsetTopGen α h) (MarkedCore.isProP_DN α h)
  · intro k _
    exact evenRawClosure_markedBase_eq_top (MarkedCore.dnGen α h)
      (dnFinsetTopGen α h) (MarkedCore.isProP_DN α h) (MarkedCore.dn_topGen α h) (k + 1)
  · exact evenRawAugmentedSpanBaseSupply_dn α h

/-- **The even `D_M` augmented span theorem.** -/
theorem evenRawAugmentedSpan_all_dm (α h : ℕ) :
    ∀ (k : ℕ) (hk : 3 ≤ k),
      zLayer (MarkedCore.DM α h : Type) k ≤
        evenRawAugmentedSpan (MarkedCore.dmGen α h) k hk := by
  apply evenRawAugmentedSpan_of_base_of_step (MarkedCore.dmGen α h)
    (dmFinsetTopGen α h) (MarkedCore.isProP_DM α h)
  · intro k _
    exact evenRawClosure_markedBase_eq_top (MarkedCore.dmGen α h)
      (dmFinsetTopGen α h) (MarkedCore.isProP_DM α h) (MarkedCore.dm_topGen α h) (k + 1)
  · exact evenRawAugmentedSpanBaseSupply_dm α h

/-! ### §3.1 The exact residual obligation

`EvenRawPureSquareSpanSupply` is **not** delivered, and the L obstruction file shows it must
not be expected: `¬ RawPureSquareSpanSupply (rawMarkedBase (SqCore.sqGen h) 3) _` is a
committed theorem.  What the augmented span theorem does buy is that the whole gap is the
tail span, and nothing else.  So any future attempt at the even lane knows exactly what it
would have to prove, and the statement below is the honest replacement for the requested
`evenRawPureSquareSpanSupply_holds`. -/

/-- **The residual, exactly.**  Given the augmented span theorem at level `k`, the pure-square
supply is *equivalent* to the augmented span collapsing onto the literal shift span, i.e. to
the relator-adapted tails already being literal shifts.  Forward: each tail
`base i ^ 2 ^ (k-1)` is the square of the depth-`k-1` element `base i ^ 2 ^ (k-2)`, so the
supply covers it.  Backward: squares of depth-`k-1` elements are central, hence in `zLayer`,
hence in the augmented span, hence in the shift span. -/
theorem evenRawPureSquareSpanSupply_iff_augmentedSpan_le_shiftSpan
    (generators : Fin (MarkedCore.coreRank h) → G) (k : ℕ) (hk : 3 ≤ k)
    (hall : zLayer G k ≤ evenRawAugmentedSpan generators k hk) :
    EvenRawPureSquareSpanSupply (evenRawMarkedBase generators k) hk ↔
      evenRawAugmentedSpan generators k hk ≤
        evenRawShiftSpan (evenRawMarkedBase generators k) hk := by
  constructor
  · intro Hsq
    rw [evenRawAugmentedSpan]
    refine sup_le le_rfl ?_
    rw [evenRawTailSpan, Subgroup.closure_le]
    rintro z ⟨i, _, rfl⟩
    have hmem : evenRawMarkedBase generators k i ^ 2 ^ (k - 2) ∈
        lambdaImage G (k - 1) (k + 1) := by
      have hp := pow_two_pow_mem_lambdaImage (evenRawMarkedBase generators k i) (k - 2)
      rwa [show 1 + (k - 2) = k - 1 by omega] at hp
    have hsq := Hsq ⟨_, hmem⟩
    rwa [← pow_mul, show (2 : ℕ) ^ (k - 2) * 2 = 2 ^ (k - 1) by
      rw [← pow_succ]
      congr 1
      omega] at hsq
  · intro hle p
    exact hle (hall (sq_mem_zLayer k hk p.2))

end Cores

end Engine

end

end GQ2.Dyadic.StageGeneric

/-! ## §4 Axiom pins

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
#print axioms GQ2.Dyadic.StageGeneric.evenRawDbar_mem_lambdaImage_succ
#print axioms GQ2.Dyadic.StageGeneric.evenRawHandleDbarWord_sq
#print axioms GQ2.Dyadic.StageGeneric.evenRawCoreDbarWord_sq
#print axioms GQ2.Dyadic.StageGeneric.evenRawDbarWord_sq
#print axioms GQ2.Dyadic.StageGeneric.levelProj_evenRawDbarWord
#print axioms GQ2.Dyadic.StageGeneric.evenRawSquare_mem_augmentedSpan_succ
#print axioms GQ2.Dyadic.StageGeneric.evenRawAugmentedSpan_step
#print axioms GQ2.Dyadic.StageGeneric.evenRawAugmentedSpan_of_base_of_step
#print axioms GQ2.Dyadic.StageGeneric.evenRawAugmentedSpan_all_dn
#print axioms GQ2.Dyadic.StageGeneric.evenRawAugmentedSpan_all_dm
#print axioms GQ2.Dyadic.StageGeneric.evenRawPureSquareSpanSupply_iff_augmentedSpan_le_shiftSpan
