/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteFinite
import GQ2.Roe.Labute.Levelwise

/-!
# Variable-rank stage foundation for the improved square Labute word

This file lifts the rank-three defect calculus to the literal variable-rank word
`SqCore.sqRelWord` on `Fin (SqCore.sqRank h)`.  It supplies the presentation-independent part
of a future Labute stage argument:

* relator-killing generating tuples in the lower two-central tower;
* restriction down the tower;
* invariance of the full core-and-handles word under the central exponent-two kernel;
* a canonical variable-rank defect, independent of all coordinate lifts; and
* the fact that a relator-killing tuple's defect lies in the next graded layer.

The remaining hard theorem is now sharply isolated: a variable-rank span/correction result
must kill `sqStageDefect` while preserving the five cyclotomic value fibres.  The handle block
below is the improved presentation's genuine product of commutators, not an obsolete collector
word.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Level sets and restriction -/

/-- A relator-killing generating marking of the `k`-th lower two-central quotient. -/
def sqStageZero
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h k : ℕ) : Set (Fin (SqCore.sqRank h) → levelQuot G k) :=
  {T | SqCore.sqRelWord T = 1 ∧ Subgroup.closure (Set.range T) = ⊤}

/-- Restriction of a variable-rank improved marking down one level preserves both its literal
relation and generation. -/
theorem sqStageZero_levelProj
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ} {T : Fin (SqCore.sqRank h) → levelQuot G (k + 1)}
    (hT : T ∈ sqStageZero G h (k + 1)) :
    (fun i ↦ levelProj G k (T i)) ∈ sqStageZero G h k := by
  obtain ⟨hrel, hgen⟩ := hT
  refine ⟨?_, closure_range_levelProj hgen⟩
  rw [← SqCore.map_sqRelWord (levelProj G k) T, hrel, map_one]

/-! ## Central-kernel invariance of the improved word -/

/-- The full hyperbolic handle block is insensitive to coordinatewise central shifts. -/
theorem handleWord_central_shift
    {H : Type*} [Group H] {h : ℕ}
    (u v zu zv : Fin h → H)
    (hzu : ∀ j t, Commute (zu j) t)
    (hzv : ∀ j t, Commute (zv j) t) :
    GQ2.Dyadic.MarkedCore.handleWord (fun j ↦ zu j * u j) (fun j ↦ zv j * v j) =
      GQ2.Dyadic.MarkedCore.handleWord u v := by
  rw [GQ2.Dyadic.MarkedCore.handleWord, GQ2.Dyadic.MarkedCore.handleWord]
  apply congrArg List.prod
  apply List.map_congr_left
  intro j _
  rw [commP_central_left (hzu j), commP_central_right (hzv j)]

/-- The literal improved square relator is insensitive to arbitrary coordinatewise shifts from
the central exponent-two layer `Z_k`.  The rank-three core uses the existing exact `drWord`
calculus; every appended handle is handled as an honest commutator. -/
theorem sqRelWord_zLayer_shift
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ}
    (z m : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hz : ∀ i, z i ∈ zLayer G k) :
    SqCore.sqRelWord (fun i ↦ z i * m i) = SqCore.sqRelWord m := by
  have hcore : SqCore.sqWord (z 0 * m 0) (z 1 * m 1) (z 2 * m 2) =
      SqCore.sqWord (m 0) (m 1) (m 2) := by
    exact drWord_zLayer_shift (hz 0) (hz 1) (hz 2) _ _ _
  have hhandles :
      GQ2.Dyadic.MarkedCore.handleWord
          (fun j ↦ z (SqCore.sqHandleIdxU j) * m (SqCore.sqHandleIdxU j))
          (fun j ↦ z (SqCore.sqHandleIdxV j) * m (SqCore.sqHandleIdxV j)) =
        GQ2.Dyadic.MarkedCore.handleWord
          (fun j ↦ m (SqCore.sqHandleIdxU j))
          (fun j ↦ m (SqCore.sqHandleIdxV j)) := by
    apply handleWord_central_shift
    · intro j t
      exact zLayer_commute (hz (SqCore.sqHandleIdxU j)) t
    · intro j t
      exact zLayer_commute (hz (SqCore.sqHandleIdxV j)) t
  rw [SqCore.sqRelWord, SqCore.sqRelWord, hcore, hhandles]

/-! ## The variable-rank defect -/

/-- The improved-relator defect of the canonical coordinatewise lift to level `k+1`. -/
noncomputable def sqStageDefect
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h k : ℕ) (T : Fin (SqCore.sqRank h) → levelQuot G k) :
    levelQuot G (k + 1) :=
  SqCore.sqRelWord (fun i ↦ canonLift G k (T i))

/-- Any coordinatewise lift computes the same variable-rank defect. -/
theorem sqStageDefect_eq_of_lift
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h k : ℕ) (T : Fin (SqCore.sqRank h) → levelQuot G k)
    (T' : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hT' : ∀ i, levelProj G k (T' i) = T i) :
    SqCore.sqRelWord T' = sqStageDefect G h k T := by
  choose z hz heq using fun i ↦ exists_zLayer_mul (G := G)
    (show levelProj G k (T' i) = levelProj G k (canonLift G k (T i)) by
      rw [hT', levelProj_canonLift])
  have hfun : T' = fun i ↦ z i * canonLift G k (T i) := funext heq
  rw [hfun, sqStageDefect]
  exact sqRelWord_zLayer_shift z (fun i ↦ canonLift G k (T i)) hz

/-- The defect of a relator-killing variable-rank marking lies in the graded kernel `Z_k`. -/
theorem sqStageDefect_mem_zLayer
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h k : ℕ) {T : Fin (SqCore.sqRank h) → levelQuot G k}
    (hrel : SqCore.sqRelWord T = 1) :
    sqStageDefect G h k T ∈ zLayer G k := by
  rw [zLayer_eq_ker_levelProj, MonoidHom.mem_ker, sqStageDefect,
    SqCore.map_sqRelWord]
  simpa only [levelProj_canonLift] using hrel

/-- A tuple in `sqStageZero` has a graded-layer defect. -/
theorem sqStageZero_defect_mem_zLayer
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h k : ℕ) {T : Fin (SqCore.sqRank h) → levelQuot G k}
    (hT : T ∈ sqStageZero G h k) :
    sqStageDefect G h k T ∈ zLayer G k :=
  sqStageDefect_mem_zLayer h k hT.1

/-- Vanishing of the canonical defect is equivalent to the literal improved relation for any
chosen coordinatewise lift. -/
theorem sqStageDefect_eq_one_iff_lift_relation
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h k : ℕ) (T : Fin (SqCore.sqRank h) → levelQuot G k)
    (T' : Fin (SqCore.sqRank h) → levelQuot G (k + 1))
    (hT' : ∀ i, levelProj G k (T' i) = T i) :
    sqStageDefect G h k T = 1 ↔ SqCore.sqRelWord T' = 1 := by
  rw [sqStageDefect_eq_of_lift h k T T' hT']

/-! ## Oriented stage tuples and descent to arbitrary finite quotients -/

/-- A level-`k` marking for the improved square presentation, with the orientation conditions
stated by liftability to the exact cyclotomic fibres.  This is the variable-rank analogue of
the rank-three sets `sPR0`/`sPR2`, stripped of presentation-dependent auxiliary invariants.

Using exact fibre liftability here is important: congruences for a truncated character would
not by themselves imply the value-fibre clauses required by finite-level compactness. -/
structure SqCyclotomicStageTuple
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (h k : ℕ) where
  generators : Fin (SqCore.sqRank h) →
    levelQuot (maxProPQuotient 2 (GalK K)) k
  sigma : ∃ x : maxProPQuotient 2 (GalK K),
    chiCycKTwo (K := K) x = GQ2.Roe.SvalUnit ∧
      generators 0 = levelMk (maxProPQuotient 2 (GalK K)) k x
  x0 : ∃ x : maxProPQuotient 2 (GalK K),
    chiCycKTwo (K := K) x = GQ2.Roe.rootXUnit ∧
      generators 1 = levelMk (maxProPQuotient 2 (GalK K)) k x
  x1 : ∃ x : maxProPQuotient 2 (GalK K),
    chiCycKTwo (K := K) x = GQ2.Roe.YvalUnit ∧
      generators 2 = levelMk (maxProPQuotient 2 (GalK K)) k x
  handleU : ∀ j : Fin h, ∃ x : maxProPQuotient 2 (GalK K),
    x ∈ (chiCycKTwo (K := K)).toMonoidHom.ker ∧
      generators (SqCore.sqHandleIdxU j) =
        levelMk (maxProPQuotient 2 (GalK K)) k x
  handleV : ∀ j : Fin h, ∃ x : maxProPQuotient 2 (GalK K),
    x ∈ (chiCycKTwo (K := K)).toMonoidHom.ker ∧
      generators (SqCore.sqHandleIdxV j) =
        levelMk (maxProPQuotient 2 (GalK K)) k x
  relation : SqCore.sqRelWord generators = 1
  topGen : Subgroup.closure (Set.range generators) = ⊤

namespace SqCyclotomicStageTuple

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-- Restriction down the two-central tower preserves the literal improved relation,
generation, and all exact cyclotomic fibres. -/
noncomputable def levelProj {h k : ℕ}
    (T : SqCyclotomicStageTuple K h (k + 1)) :
    SqCyclotomicStageTuple K h k where
  generators i := GQ2.Roe.Labute.levelProj _ k (T.generators i)
  sigma := by
    obtain ⟨x, hxchi, hx⟩ := T.sigma
    exact ⟨x, hxchi, by rw [hx, levelProj_levelMk]⟩
  x0 := by
    obtain ⟨x, hxchi, hx⟩ := T.x0
    exact ⟨x, hxchi, by rw [hx, levelProj_levelMk]⟩
  x1 := by
    obtain ⟨x, hxchi, hx⟩ := T.x1
    exact ⟨x, hxchi, by rw [hx, levelProj_levelMk]⟩
  handleU := by
    intro j
    obtain ⟨x, hxchi, hx⟩ := T.handleU j
    exact ⟨x, hxchi, by rw [hx, levelProj_levelMk]⟩
  handleV := by
    intro j
    obtain ⟨x, hxchi, hx⟩ := T.handleV j
    exact ⟨x, hxchi, by rw [hx, levelProj_levelMk]⟩
  relation := by
    rw [← SqCore.map_sqRelWord (GQ2.Roe.Labute.levelProj _ k) T.generators,
      T.relation, map_one]
  topGen := closure_range_levelProj T.topGen

/-- The underlying tuple of an oriented stage belongs to `sqStageZero`. -/
theorem generators_mem_sqStageZero {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) :
    T.generators ∈ sqStageZero (maxProPQuotient 2 (GalK K)) h k :=
  ⟨T.relation, T.topGen⟩

/-- The plain homomorphism from a tower quotient to a coarser quotient.  Unlike `projMap`,
this algebraic form needs no temporary discrete-topology instance. -/
noncomputable def toOpenMap (k : ℕ)
    (U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))))
    (hle : twoCentralSeries (maxProPQuotient 2 (GalK K)) k ≤ U.toSubgroup) :
    levelQuot (maxProPQuotient 2 (GalK K)) k →*
      (maxProPQuotient 2 (GalK K) ⧸ U.toSubgroup) :=
  QuotientGroup.lift (twoCentralSeries (maxProPQuotient 2 (GalK K)) k)
    (QuotientGroup.mk' U.toSubgroup) (by
      rw [QuotientGroup.ker_mk']
      exact hle)

@[simp] theorem toOpenMap_levelMk (k : ℕ)
    (U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))))
    (hle : twoCentralSeries (maxProPQuotient 2 (GalK K)) k ≤ U.toSubgroup)
    (x : maxProPQuotient 2 (GalK K)) :
    toOpenMap (K := K) k U hle
        (levelMk (maxProPQuotient 2 (GalK K)) k x) = QuotientGroup.mk x :=
  rfl

theorem toOpenMap_surjective (k : ℕ)
    (U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))))
    (hle : twoCentralSeries (maxProPQuotient 2 (GalK K)) k ≤ U.toSubgroup) :
    Function.Surjective (toOpenMap (K := K) k U hle) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨levelMk (maxProPQuotient 2 (GalK K)) k x, rfl⟩

/-- A single oriented stage at any tower level contained in `U` produces the corrected
finite-level datum for `U`.  Thus all cofinality/compactness work after the stage lemma is now
independent of the arithmetic correction calculation. -/
noncomputable def toFiniteLevelEpiData {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k)
    (U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))))
    (hle : twoCentralSeries (maxProPQuotient 2 (GalK K)) k ≤ U.toSubgroup) :
    SqCyclotomicFiniteLevelEpiData (K := K) h U := by
  let p := toOpenMap (K := K) k U hle
  let generators := fun i ↦ p (T.generators i)
  apply finiteLevelEpiDataOfTuple h U generators
  · obtain ⟨x, hxchi, hx⟩ := T.sigma
    refine ⟨x, hxchi, ?_⟩
    change p (T.generators 0) = QuotientGroup.mk x
    rw [hx]
    exact toOpenMap_levelMk (K := K) k U hle x
  · obtain ⟨x, hxchi, hx⟩ := T.x0
    refine ⟨x, hxchi, ?_⟩
    change p (T.generators 1) = QuotientGroup.mk x
    rw [hx]
    exact toOpenMap_levelMk (K := K) k U hle x
  · obtain ⟨x, hxchi, hx⟩ := T.x1
    refine ⟨x, hxchi, ?_⟩
    change p (T.generators 2) = QuotientGroup.mk x
    rw [hx]
    exact toOpenMap_levelMk (K := K) k U hle x
  · intro j
    obtain ⟨x, hxchi, hx⟩ := T.handleU j
    refine ⟨x, hxchi, ?_⟩
    change p (T.generators (SqCore.sqHandleIdxU j)) = QuotientGroup.mk x
    rw [hx]
    exact toOpenMap_levelMk (K := K) k U hle x
  · intro j
    obtain ⟨x, hxchi, hx⟩ := T.handleV j
    refine ⟨x, hxchi, ?_⟩
    change p (T.generators (SqCore.sqHandleIdxV j)) = QuotientGroup.mk x
    rw [hx]
    exact toOpenMap_levelMk (K := K) k U hle x
  · exact (SqCore.map_sqRelWord p T.generators).symm.trans (by rw [T.relation, map_one])
  · have h := congrArg (Subgroup.map p) T.topGen
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _
      (toOpenMap_surjective (K := K) k U hle), ← Set.range_comp] at h
    exact h

/-! The following regressions deliberately restate the six load-bearing output fields.  They
prevent a future stage refactor from silently reverting either to the obsolete collector word
or to arbitrarily pinned core representatives. -/

/-- Regression: stage descent records the literal improved core-plus-handle relator. -/
theorem toFiniteLevelEpiData_sqRelWord_regression {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k)
    (U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))))
    (hle : twoCentralSeries (maxProPQuotient 2 (GalK K)) k ≤ U.toSubgroup) :
    SqCore.sqRelWord (fun i ↦
      (T.toFiniteLevelEpiData U hle).epi.1 (SqCore.sqGen h i)) = 1 :=
  (T.toFiniteLevelEpiData U hle).relation

/-- Regression: the `sigma` row remains liftability to the `SvalUnit` fibre. -/
theorem toFiniteLevelEpiData_sigma_fibre_regression {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k)
    (U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))))
    (hle : twoCentralSeries (maxProPQuotient 2 (GalK K)) k ≤ U.toSubgroup) :
    ∃ x : maxProPQuotient 2 (GalK K),
      chiCycKTwo (K := K) x = GQ2.Roe.SvalUnit ∧
        (T.toFiniteLevelEpiData U hle).epi.1 (SqCore.dsqSigma h) = QuotientGroup.mk x :=
  (T.toFiniteLevelEpiData U hle).sigma

/-- Regression: the `x0` row remains liftability to the `rootXUnit` fibre. -/
theorem toFiniteLevelEpiData_x0_fibre_regression {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k)
    (U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))))
    (hle : twoCentralSeries (maxProPQuotient 2 (GalK K)) k ≤ U.toSubgroup) :
    ∃ x : maxProPQuotient 2 (GalK K),
      chiCycKTwo (K := K) x = GQ2.Roe.rootXUnit ∧
        (T.toFiniteLevelEpiData U hle).epi.1 (SqCore.dsqX0 h) = QuotientGroup.mk x :=
  (T.toFiniteLevelEpiData U hle).x0

/-- Regression: the `x1` row remains liftability to the `YvalUnit` fibre. -/
theorem toFiniteLevelEpiData_x1_fibre_regression {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k)
    (U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))))
    (hle : twoCentralSeries (maxProPQuotient 2 (GalK K)) k ≤ U.toSubgroup) :
    ∃ x : maxProPQuotient 2 (GalK K),
      chiCycKTwo (K := K) x = GQ2.Roe.YvalUnit ∧
        (T.toFiniteLevelEpiData U hle).epi.1 (SqCore.dsqX1 h) = QuotientGroup.mk x :=
  (T.toFiniteLevelEpiData U hle).x1

/-- Regression: every `U`-handle row remains liftability to `ker χ`. -/
theorem toFiniteLevelEpiData_handleU_fibre_regression {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k)
    (U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))))
    (hle : twoCentralSeries (maxProPQuotient 2 (GalK K)) k ≤ U.toSubgroup) :
    ∀ j : Fin h, ∃ x : maxProPQuotient 2 (GalK K),
      x ∈ (chiCycKTwo (K := K)).toMonoidHom.ker ∧
        (T.toFiniteLevelEpiData U hle).epi.1
          (SqCore.sqGen h (SqCore.sqHandleIdxU j)) = QuotientGroup.mk x :=
  (T.toFiniteLevelEpiData U hle).handleU

/-- Regression: every `V`-handle row remains liftability to `ker χ`. -/
theorem toFiniteLevelEpiData_handleV_fibre_regression {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k)
    (U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))))
    (hle : twoCentralSeries (maxProPQuotient 2 (GalK K)) k ≤ U.toSubgroup) :
    ∀ j : Fin h, ∃ x : maxProPQuotient 2 (GalK K),
      x ∈ (chiCycKTwo (K := K)).toMonoidHom.ker ∧
        (T.toFiniteLevelEpiData U hle).epi.1
          (SqCore.sqGen h (SqCore.sqHandleIdxV j)) = QuotientGroup.mk x :=
  (T.toFiniteLevelEpiData U hle).handleV

/-! ## The exact variable-rank correction interface -/

/-- Coordinatewise right modification of a level-`k+1` marking. -/
def stageModified
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ}
    (base correction : Fin (SqCore.sqRank h) → levelQuot G (k + 1)) :=
  fun i ↦ base i * correction i

/-- The exact relator shift caused by a coordinatewise modification.  This definition is
presentation-independent, but because it evaluates `SqCore.sqRelWord`, it includes every
hyperbolic handle commutator of the improved presentation. -/
def stageShift
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ}
    (base correction : Fin (SqCore.sqRank h) → levelQuot G (k + 1)) :
    levelQuot G (k + 1) :=
  (SqCore.sqRelWord base)⁻¹ * SqCore.sqRelWord (stageModified base correction)

/-- Tautological but load-bearing shift identity: it fixes the multiplication orientation used
by the future crossed-derivation/span calculation. -/
theorem sqRelWord_stageModified
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {h k : ℕ}
    (base correction : Fin (SqCore.sqRank h) → levelQuot G (k + 1)) :
    SqCore.sqRelWord (stageModified base correction) =
      SqCore.sqRelWord base * stageShift base correction := by
  simp only [stageShift]
  group

/-- A depth-`k-1` correction whose modified canonical lifts remain in all five exact
cyclotomic fibres.  This is the affine domain on which the arithmetic span theorem must be
surjective.  In particular, handle corrections are not silently discarded. -/
structure AdmissibleCorrection {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) where
  correction : Fin (SqCore.sqRank h) →
    levelQuot (maxProPQuotient 2 (GalK K)) (k + 1)
  depth : ∀ i, correction i ∈
    lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1)
  sigma : ∃ x : maxProPQuotient 2 (GalK K),
    chiCycKTwo (K := K) x = GQ2.Roe.SvalUnit ∧
      stageModified (fun i ↦ canonLift _ k (T.generators i)) correction 0 =
        levelMk (maxProPQuotient 2 (GalK K)) (k + 1) x
  x0 : ∃ x : maxProPQuotient 2 (GalK K),
    chiCycKTwo (K := K) x = GQ2.Roe.rootXUnit ∧
      stageModified (fun i ↦ canonLift _ k (T.generators i)) correction 1 =
        levelMk (maxProPQuotient 2 (GalK K)) (k + 1) x
  x1 : ∃ x : maxProPQuotient 2 (GalK K),
    chiCycKTwo (K := K) x = GQ2.Roe.YvalUnit ∧
      stageModified (fun i ↦ canonLift _ k (T.generators i)) correction 2 =
        levelMk (maxProPQuotient 2 (GalK K)) (k + 1) x
  handleU : ∀ j : Fin h, ∃ x : maxProPQuotient 2 (GalK K),
    x ∈ (chiCycKTwo (K := K)).toMonoidHom.ker ∧
      stageModified (fun i ↦ canonLift _ k (T.generators i)) correction
          (SqCore.sqHandleIdxU j) =
        levelMk (maxProPQuotient 2 (GalK K)) (k + 1) x
  handleV : ∀ j : Fin h, ∃ x : maxProPQuotient 2 (GalK K),
    x ∈ (chiCycKTwo (K := K)).toMonoidHom.ker ∧
      stageModified (fun i ↦ canonLift _ k (T.generators i)) correction
          (SqCore.sqHandleIdxV j) =
        levelMk (maxProPQuotient 2 (GalK K)) (k + 1) x

/-- The exact presentation-independent replacement for the rank-three span calculation:
every element of the graded defect layer is the literal improved-relator shift of an
admissible depth-`k-1` correction.  Proving this predicate is the remaining arithmetic theorem;
all group-theoretic stage work is downstream of it. -/
def CorrectionSurjective {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) : Prop :=
  ∀ δ ∈ zLayer (maxProPQuotient 2 (GalK K)) k,
    ∃ W : AdmissibleCorrection T,
      stageShift (fun i ↦ canonLift _ k (T.generators i)) W.correction = δ

/-- A correction selected from surjectivity at the inverse defect. -/
structure DefectKillingCorrection {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) extends AdmissibleCorrection T where
  kills : stageShift (fun i ↦ canonLift _ k (T.generators i)) correction =
    (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹

/-- Surjectivity on `zLayer` supplies a defect-killing admissible correction. -/
noncomputable def CorrectionSurjective.defectKillingCorrection {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (H : CorrectionSurjective T) :
    DefectKillingCorrection T := by
  have hδ : (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ ∈
      zLayer (maxProPQuotient 2 (GalK K)) k :=
    Subgroup.inv_mem _ (sqStageDefect_mem_zLayer h k T.relation)
  let W := Classical.choose (H _ hδ)
  exact { W with kills := Classical.choose_spec (H _ hδ) }

/-- Every non-arithmetic part of the variable-rank stage step.  Once the exact correction map
is surjective on the graded defect layer, the inverse defect kills the literal improved
relator; depth preserves generation by the Frattini argument; and admissibility preserves the
three core fibres and both handle families. -/
noncomputable def DefectKillingCorrection.toNext
    {h k : ℕ} (T : SqCyclotomicStageTuple K h k)
    (W : DefectKillingCorrection T) (hk : 3 ≤ k)
    (hfg : ∃ s : Finset (maxProPQuotient 2 (GalK K)),
      (Subgroup.closure (s : Set (maxProPQuotient 2 (GalK K)))).topologicalClosure = ⊤) :
    SqCyclotomicStageTuple K h (k + 1) where
  generators := stageModified (fun i ↦ canonLift _ k (T.generators i)) W.correction
  sigma := W.sigma
  x0 := W.x0
  x1 := W.x1
  handleU := W.handleU
  handleV := W.handleV
  relation := by
    rw [sqRelWord_stageModified, sqStageDefect_eq_of_lift h k T.generators
      (fun i ↦ canonLift _ k (T.generators i)) (fun i ↦ levelProj_canonLift _ k _), W.kills]
    exact mul_inv_cancel _
  topGen := by
    have hbase : Subgroup.closure
        (Set.range fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) = ⊤ := by
      refine eq_top_of_map_levelProj_eq_top (maxProPQuotient 2 (GalK K)) hfg
        isProP_maxProPQuotient (by omega) ?_
      have himg : (GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k) ''
          (Set.range fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k
            (T.generators i)) = Set.range T.generators := by
        rw [← Set.range_comp]
        exact congrArg Set.range (funext fun i ↦ levelProj_canonLift _ k (T.generators i))
      rw [MonoidHom.map_closure, himg, T.topGen]
    exact closure_range_mul_eq_top_of_mem_lambdaImage_two
      (maxProPQuotient 2 (GalK K)) hfg isProP_maxProPQuotient _ _ hbase
      (fun i ↦ lambdaImage_le_of_le (by omega) (W.depth i))

/-- The sharp stage theorem exposed to arithmetic: exact correction surjectivity alone implies
existence of the next oriented stage. -/
noncomputable def CorrectionSurjective.toNext
    {h k : ℕ} (T : SqCyclotomicStageTuple K h k) (H : CorrectionSurjective T)
    (hk : 3 ≤ k)
    (hfg : ∃ s : Finset (maxProPQuotient 2 (GalK K)),
      (Subgroup.closure (s : Set (maxProPQuotient 2 (GalK K)))).topologicalClosure = ⊤) :
    SqCyclotomicStageTuple K h (k + 1) :=
  (H.defectKillingCorrection T).toNext T hk hfg

end SqCyclotomicStageTuple

#print axioms sqStageZero_levelProj
#print axioms handleWord_central_shift
#print axioms sqRelWord_zLayer_shift
#print axioms sqStageDefect_eq_of_lift
#print axioms sqStageDefect_mem_zLayer
#print axioms sqStageDefect_eq_one_iff_lift_relation
#print axioms SqCyclotomicStageTuple.levelProj
#print axioms SqCyclotomicStageTuple.toFiniteLevelEpiData
#print axioms SqCyclotomicStageTuple.toFiniteLevelEpiData_sqRelWord_regression
#print axioms SqCyclotomicStageTuple.sqRelWord_stageModified
#print axioms SqCyclotomicStageTuple.CorrectionSurjective.toNext

end

end GQ2.Dyadic.LSquare
