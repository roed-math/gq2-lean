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

/-- Maximal honest use of the existing constructor table at the base level.  The table supplies
the three exceptional value fibres.  What remains, and is therefore displayed explicitly in
the premise, is a generating level-three tuple killing the literal improved relator together
with kernel lifts for all handles. -/
def ofCoreTable
    (T : OddDegreeGalKSqCyclotomicCoreTable K) (h : ℕ)
    (generators : Fin (SqCore.sqRank h) →
      levelQuot (maxProPQuotient 2 (GalK K)) 3)
    (hsigma : generators 0 = levelMk (maxProPQuotient 2 (GalK K)) 3 T.sigma)
    (hx0 : generators 1 = levelMk (maxProPQuotient 2 (GalK K)) 3 T.x0)
    (hx1 : generators 2 = levelMk (maxProPQuotient 2 (GalK K)) 3 T.x1)
    (hhandleU : ∀ j : Fin h, ∃ x : maxProPQuotient 2 (GalK K),
      x ∈ (chiCycKTwo (K := K)).toMonoidHom.ker ∧
        generators (SqCore.sqHandleIdxU j) =
          levelMk (maxProPQuotient 2 (GalK K)) 3 x)
    (hhandleV : ∀ j : Fin h, ∃ x : maxProPQuotient 2 (GalK K),
      x ∈ (chiCycKTwo (K := K)).toMonoidHom.ker ∧
        generators (SqCore.sqHandleIdxV j) =
          levelMk (maxProPQuotient 2 (GalK K)) 3 x)
    (hrelation : SqCore.sqRelWord generators = 1)
    (htopGen : Subgroup.closure (Set.range generators) = ⊤) :
    SqCyclotomicStageTuple K h 3 where
  generators := generators
  sigma := ⟨T.sigma, T.sigma_value, hsigma⟩
  x0 := ⟨T.x0, T.x0_value, hx0⟩
  x1 := ⟨T.x1, T.x1_value, hx1⟩
  handleU := hhandleU
  handleV := hhandleV
  relation := hrelation
  topGen := htopGen

/-- Regression: the constructor-table base adapter retains the improved `sqRelWord`. -/
theorem ofCoreTable_sqRelWord_regression
    (T : OddDegreeGalKSqCyclotomicCoreTable K) (h : ℕ)
    (generators : Fin (SqCore.sqRank h) →
      levelQuot (maxProPQuotient 2 (GalK K)) 3)
    (hsigma : generators 0 = levelMk (maxProPQuotient 2 (GalK K)) 3 T.sigma)
    (hx0 : generators 1 = levelMk (maxProPQuotient 2 (GalK K)) 3 T.x0)
    (hx1 : generators 2 = levelMk (maxProPQuotient 2 (GalK K)) 3 T.x1)
    (hhandleU : ∀ j : Fin h, ∃ x : maxProPQuotient 2 (GalK K),
      x ∈ (chiCycKTwo (K := K)).toMonoidHom.ker ∧
        generators (SqCore.sqHandleIdxU j) =
          levelMk (maxProPQuotient 2 (GalK K)) 3 x)
    (hhandleV : ∀ j : Fin h, ∃ x : maxProPQuotient 2 (GalK K),
      x ∈ (chiCycKTwo (K := K)).toMonoidHom.ker ∧
        generators (SqCore.sqHandleIdxV j) =
          levelMk (maxProPQuotient 2 (GalK K)) 3 x)
    (hrelation : SqCore.sqRelWord generators = 1)
    (htopGen : Subgroup.closure (Set.range generators) = ⊤) :
    SqCore.sqRelWord
      (ofCoreTable T h generators hsigma hx0 hx1 hhandleU hhandleV hrelation htopGen).generators =
      1 :=
  hrelation

/-- The carrier of an oriented square equivalence, named separately to keep coercion elaboration
stable inside quotient-word calculations. -/
def orientedCarrier {h : ℕ}
    (e : OrientedContinuousMulEquiv (SqCore.chiSq h) (chiCycKTwo (K := K))) :
    ContinuousMulEquiv (SqCore.DSq h : Type) (maxProPQuotient 2 (GalK K)) :=
  e.1

/-- Any already-proved oriented square equivalence gives an exact oriented stage at every
tower level.  This transport theorem is primarily a regression tool for `h = 0`: it confirms
that the new stage architecture really specializes to the existing `Q₂` classification. -/
noncomputable def ofOrientedEquiv {h k : ℕ}
    (e : OrientedContinuousMulEquiv (SqCore.chiSq h) (chiCycKTwo (K := K))) :
    SqCyclotomicStageTuple K h k where
  generators i := levelMk (maxProPQuotient 2 (GalK K)) k
    (orientedCarrier e (SqCore.sqGen h i))
  sigma := by
    refine ⟨orientedCarrier e (SqCore.sqGen h 0), ?_, rfl⟩
    exact (e.2 _).trans (SqCore.chiSq_sigma h)
  x0 := by
    refine ⟨orientedCarrier e (SqCore.sqGen h 1), ?_, rfl⟩
    exact (e.2 _).trans (SqCore.chiSq_x0 h)
  x1 := by
    refine ⟨orientedCarrier e (SqCore.sqGen h 2), ?_, rfl⟩
    exact (e.2 _).trans (SqCore.chiSq_x1 h)
  handleU := by
    intro j
    refine ⟨orientedCarrier e (SqCore.sqGen h (SqCore.sqHandleIdxU j)), ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    exact (e.2 _).trans (SqCore.chiSq_handleU h j)
  handleV := by
    intro j
    refine ⟨orientedCarrier e (SqCore.sqGen h (SqCore.sqHandleIdxV j)), ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    exact (e.2 _).trans (SqCore.chiSq_handleV h j)
  relation := by
    calc
      SqCore.sqRelWord (fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) k
          (orientedCarrier e (SqCore.sqGen h i))) =
          levelMk (maxProPQuotient 2 (GalK K)) k
            (SqCore.sqRelWord (fun i ↦ orientedCarrier e (SqCore.sqGen h i))) :=
        (SqCore.map_sqRelWord (levelMk (maxProPQuotient 2 (GalK K)) k)
          (fun i ↦ orientedCarrier e (SqCore.sqGen h i))).symm
      _ = levelMk (maxProPQuotient 2 (GalK K)) k
          (orientedCarrier e (SqCore.sqRelWord (SqCore.sqGen h))) :=
        congrArg (levelMk (maxProPQuotient 2 (GalK K)) k)
          (SqCore.map_sqRelWord (orientedCarrier e).toMonoidHom (SqCore.sqGen h)).symm
      _ = 1 := by rw [SqCore.dsq_relation, map_one, map_one]
  topGen := by
    let Q := maxProPQuotient 2 (GalK K)
    let f := orientedCarrier e
    have hfgQ : IsTopologicallyFinGen Q :=
      IsTopologicallyFinGen.of_surjective f.toMonoidHom f.continuous_toFun
        f.surjective (dsqFinsetTopGen h)
    letI := discreteTopology_levelQuot Q hfgQ isProP_maxProPQuotient k
    let p : ContinuousMonoidHom (SqCore.DSq h : Type) (levelQuot Q k) :=
      ⟨(levelMk Q k).comp f.toMonoidHom,
        (continuous_levelMk Q k).comp f.continuous_toFun⟩
    have hp : Function.Surjective p :=
      (levelMk_surjective Q k).comp f.surjective
    let H : Subgroup (levelQuot Q k) :=
      Subgroup.closure (Set.range fun i ↦ p (SqCore.sqGen h i))
    have hclosed : IsClosed (H : Set (levelQuot Q k)) := isClosed_discrete _
    have hgen : Subgroup.closure (Set.range (SqCore.sqGen h)) ≤
        Subgroup.comap p.toMonoidHom H := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.subset_closure ⟨i, rfl⟩
    have hpreclosed : IsClosed
        (Subgroup.comap p.toMonoidHom H : Set (SqCore.DSq h : Type)) :=
      hclosed.preimage p.continuous_toFun
    have htoppre :
        (Subgroup.closure (Set.range (SqCore.sqGen h))).topologicalClosure ≤
          Subgroup.comap p.toMonoidHom H :=
      Subgroup.topologicalClosure_minimal _ hgen hpreclosed
    rw [SqCore.dsq_topGen] at htoppre
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := hp y
    exact htoppre (by trivial)

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
    GQ2.Dyadic.LSquare.SqCyclotomicFiniteLevelEpiData (K := K) h U := by
  let p := toOpenMap (K := K) k U hle
  let generators := fun i ↦ p (T.generators i)
  apply GQ2.Dyadic.LSquare.finiteLevelEpiDataOfTuple h U generators
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

/-- The exact arithmetic premise needed by one stage step: the inverse of the *current*
literal improved-relator defect is realized by an admissible depth-`k-1` correction.  This is
strictly weaker than surjectivity of the entire correction map, and matches the conclusion of
the existing rank-three `stageSL1R2` theorem. -/
def DefectReachable {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) : Prop :=
  ∃ W : AdmissibleCorrection T,
    stageShift (fun i ↦ canonLift _ k (T.generators i)) W.correction =
      (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹

/-- A stronger, reusable span statement: every element of the graded defect layer is the
literal improved-relator shift of an admissible depth-`k-1` correction.  The stage induction
does not require this full surjectivity; it is retained as a convenient sufficient interface
for a future crossed-derivation calculation. -/
def CorrectionSurjective {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) : Prop :=
  ∀ δ ∈ zLayer (maxProPQuotient 2 (GalK K)) k,
    ∃ W : AdmissibleCorrection T,
      stageShift (fun i ↦ canonLift _ k (T.generators i)) W.correction = δ

/-- A reusable crossed-derivation/span package.  An implementation may take `Parameter` to be
a finite-dimensional coefficient space and `shiftValue` its linear crossed-derivation map.
The adapter below needs only its mathematical output: every parameter yields an admissible
literal-word correction, the computed shift agrees with `stageShift`, and the shift map is
onto the graded layer. -/
structure CrossedDerivationSpanSupply {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) where
  Parameter : Type
  correction : Parameter → AdmissibleCorrection T
  shiftValue : Parameter → zLayer (maxProPQuotient 2 (GalK K)) k
  realizes : ∀ v,
    stageShift (fun i ↦ canonLift _ k (T.generators i)) (correction v).correction =
      (shiftValue v : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1))
  onto : Function.Surjective shiftValue

/-- A surjective crossed-derivation span calculation implies the exact correction premise used
by the stage theorem. -/
theorem CrossedDerivationSpanSupply.toCorrectionSurjective {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} (S : CrossedDerivationSpanSupply T) :
    CorrectionSurjective T := by
  intro δ hδ
  obtain ⟨v, hv⟩ := S.onto ⟨δ, hδ⟩
  refine ⟨S.correction v, ?_⟩
  rw [S.realizes v]
  exact congrArg Subtype.val hv

/-- Full correction surjectivity is sufficient for the sharp, actual-defect premise. -/
theorem CorrectionSurjective.toDefectReachable {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} (H : CorrectionSurjective T) :
    DefectReachable T := by
  have hδ : (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ ∈
      zLayer (maxProPQuotient 2 (GalK K)) k :=
    Subgroup.inv_mem _ (sqStageDefect_mem_zLayer h k T.relation)
  exact H _ hδ

/-- A crossed-derivation supply covering the whole graded layer in particular reaches the
actual defect. -/
theorem CrossedDerivationSpanSupply.toDefectReachable {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} (S : CrossedDerivationSpanSupply T) :
    DefectReachable T :=
  S.toCorrectionSurjective.toDefectReachable

/-- Regression for the corrected seam: the level-`k` stage transported from an oriented
equivalence has a reachable actual defect.  The witness is the coordinatewise difference
between the canonical lift of the level-`k` marking and the same oriented marking at level
`k+1`.  It lies in `Z_k`, hence already has the required depth `k-1`; its modified marking is
literally the level-`k+1` oriented marking, so all exact fibres and the relation are automatic.

This theorem is deliberately independent of the stage induction: it starts from an already
proved global oriented equivalence and serves as the noncircular `h = 0`/`Q_2` regression. -/
theorem ofOrientedEquiv_defectReachable {h k : ℕ}
    (e : OrientedContinuousMulEquiv (SqCore.chiSq h) (chiCycKTwo (K := K))) :
    DefectReachable (ofOrientedEquiv (k := k) e) := by
  let T : SqCyclotomicStageTuple K h k := ofOrientedEquiv e
  let Tnext : SqCyclotomicStageTuple K h (k + 1) := ofOrientedEquiv e
  let base := fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)
  let correction := fun i ↦ (base i)⁻¹ * Tnext.generators i
  have hproj : ∀ i,
      GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k
        (Tnext.generators i) = T.generators i := by
    intro i
    simp only [T, Tnext, ofOrientedEquiv, levelProj_levelMk]
  have hmodified : stageModified base correction = Tnext.generators := by
    funext i
    simp only [stageModified, correction, base]
    group
  have hdepth : ∀ i, correction i ∈
      lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1) := by
    intro i
    apply lambdaImage_le_of_le (Nat.sub_le k 1)
    change correction i ∈ zLayer (maxProPQuotient 2 (GalK K)) k
    rw [zLayer_eq_ker_levelProj, MonoidHom.mem_ker]
    simp only [correction, map_mul, map_inv, base, levelProj_canonLift, hproj]
    exact inv_mul_cancel _
  let W : AdmissibleCorrection T :=
    { correction := correction
      depth := hdepth
      sigma := by
        change ∃ x, chiCycKTwo (K := K) x = GQ2.Roe.SvalUnit ∧
          stageModified base correction 0 = levelMk _ (k + 1) x
        rw [hmodified]
        exact Tnext.sigma
      x0 := by
        change ∃ x, chiCycKTwo (K := K) x = GQ2.Roe.rootXUnit ∧
          stageModified base correction 1 = levelMk _ (k + 1) x
        rw [hmodified]
        exact Tnext.x0
      x1 := by
        change ∃ x, chiCycKTwo (K := K) x = GQ2.Roe.YvalUnit ∧
          stageModified base correction 2 = levelMk _ (k + 1) x
        rw [hmodified]
        exact Tnext.x1
      handleU := by
        intro j
        change ∃ x, x ∈ (chiCycKTwo (K := K)).toMonoidHom.ker ∧
          stageModified base correction (SqCore.sqHandleIdxU j) = levelMk _ (k + 1) x
        rw [hmodified]
        exact Tnext.handleU j
      handleV := by
        intro j
        change ∃ x, x ∈ (chiCycKTwo (K := K)).toMonoidHom.ker ∧
          stageModified base correction (SqCore.sqHandleIdxV j) = levelMk _ (k + 1) x
        rw [hmodified]
        exact Tnext.handleV j }
  refine ⟨W, ?_⟩
  change stageShift base correction =
    (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹
  rw [stageShift, hmodified, Tnext.relation, mul_one]
  rfl

/-- An admissible correction equipped with the exact equation that kills the current defect. -/
structure DefectKillingCorrection {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) extends AdmissibleCorrection T where
  kills : stageShift (fun i ↦ canonLift _ k (T.generators i)) correction =
    (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹

/-- Actual-defect reachability supplies a defect-killing admissible correction. -/
noncomputable def DefectReachable.defectKillingCorrection {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (H : DefectReachable T) :
    DefectKillingCorrection T := by
  let W := Classical.choose H
  exact { W with kills := Classical.choose_spec H }

/-- Every non-arithmetic part of the variable-rank stage step.  Once the inverse defect is
reachable, it kills the literal improved relator; depth preserves generation by the Frattini
argument; and admissibility preserves the three core fibres and both handle families. -/
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

/-- The sharp stage theorem exposed to arithmetic: reaching the inverse of the current defect
alone implies existence of the next oriented stage. -/
noncomputable def DefectReachable.toNext
    {h k : ℕ} (T : SqCyclotomicStageTuple K h k) (H : DefectReachable T)
    (hk : 3 ≤ k)
    (hfg : ∃ s : Finset (maxProPQuotient 2 (GalK K)),
      (Subgroup.closure (s : Set (maxProPQuotient 2 (GalK K)))).topologicalClosure = ⊤) :
    SqCyclotomicStageTuple K h (k + 1) :=
  (H.defectKillingCorrection T).toNext T hk hfg

/-- Backward-compatible strong adapter: full correction surjectivity still yields the next
stage, but only through `DefectReachable`. -/
noncomputable def CorrectionSurjective.toNext
    {h k : ℕ} (T : SqCyclotomicStageTuple K h k) (H : CorrectionSurjective T)
    (hk : 3 ≤ k)
    (hfg : ∃ s : Finset (maxProPQuotient 2 (GalK K)),
      (Subgroup.closure (s : Set (maxProPQuotient 2 (GalK K)))).topologicalClosure = ⊤) :
    SqCyclotomicStageTuple K h (k + 1) :=
  H.toDefectReachable.toNext T hk hfg

/-! ## Base, induction, and all-finite-level assembly -/

/-- Restrict a nonempty oriented stage through an arbitrary finite number of tower maps. -/
private theorem stage_nonempty_of_add (h : ℕ) :
    ∀ (d k : ℕ), Nonempty (SqCyclotomicStageTuple K h (k + d)) →
      Nonempty (SqCyclotomicStageTuple K h k)
  | 0, _, H => by simpa using H
  | d + 1, k, H => by
      apply stage_nonempty_of_add h d k
      exact H.elim fun T ↦ ⟨T.levelProj⟩

/-- Upward induction from the precise base premise: one exact oriented level-three tuple.
The only inductive arithmetic input is reachability of the actual defect for every oriented
stage at every level at least three. -/
private theorem stage_nonempty_three_add
    (h : ℕ) (base : SqCyclotomicStageTuple K h 3)
    (hfg : ∃ s : Finset (maxProPQuotient 2 (GalK K)),
      (Subgroup.closure (s : Set (maxProPQuotient 2 (GalK K)))).topologicalClosure = ⊤)
    (Hcorr : ∀ (k : ℕ), 3 ≤ k → ∀ T : SqCyclotomicStageTuple K h k,
      DefectReachable T) :
    ∀ d : ℕ, Nonempty (SqCyclotomicStageTuple K h (3 + d))
  | 0 => ⟨base⟩
  | d + 1 => by
      exact (stage_nonempty_three_add h base hfg Hcorr d).elim fun T ↦
        ⟨by simpa only [Nat.add_assoc] using
          (Hcorr (3 + d) (by omega) T).toNext T (by omega) hfg⟩

/-- Exact levelwise nonemptiness.  Above level three this is the correction induction; below
level three it is restriction from a higher stage. -/
theorem stage_nonempty_all_levels
    (h : ℕ) (base : SqCyclotomicStageTuple K h 3)
    (hfg : ∃ s : Finset (maxProPQuotient 2 (GalK K)),
      (Subgroup.closure (s : Set (maxProPQuotient 2 (GalK K)))).topologicalClosure = ⊤)
    (Hcorr : ∀ (k : ℕ), 3 ≤ k → ∀ T : SqCyclotomicStageTuple K h k,
      DefectReachable T)
    (k : ℕ) : Nonempty (SqCyclotomicStageTuple K h k) := by
  apply stage_nonempty_of_add h 3 k
  simpa only [Nat.add_comm] using stage_nonempty_three_add h base hfg Hcorr k

/-- Cofinality endpoint: the exact level-three base and the correction theorem produce the
corrected finite datum at every open normal quotient.  This is the complete bridge required by
`SqCyclotomicFiniteLevelEpiData` compactness; no presentation-dependent arithmetic remains
after the actual-defect premise `Hcorr`. -/
theorem finiteLevelEpiData_nonempty_of_base_and_corrections
    (h : ℕ) (base : SqCyclotomicStageTuple K h 3)
    (hfg : ∃ s : Finset (maxProPQuotient 2 (GalK K)),
      (Subgroup.closure (s : Set (maxProPQuotient 2 (GalK K)))).topologicalClosure = ⊤)
    (Hcorr : ∀ (k : ℕ), 3 ≤ k → ∀ T : SqCyclotomicStageTuple K h k,
      DefectReachable T)
    (U : OpenNormalSubgroup
      (ProfiniteGrp.of (maxProPQuotient 2 (GalK K)))) :
    Nonempty (GQ2.Dyadic.LSquare.SqCyclotomicFiniteLevelEpiData (K := K) h U) := by
  obtain ⟨k, hk⟩ := exists_twoCentralSeries_le (maxProPQuotient 2 (GalK K)) hfg
    isProP_maxProPQuotient U.isOpen'
  exact (stage_nonempty_all_levels h base hfg Hcorr k).elim fun T ↦
    ⟨T.toFiniteLevelEpiData U hk⟩

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
#print axioms SqCyclotomicStageTuple.ofOrientedEquiv
#print axioms SqCyclotomicStageTuple.sqRelWord_stageModified
#print axioms SqCyclotomicStageTuple.DefectReachable.toNext
#print axioms SqCyclotomicStageTuple.CorrectionSurjective.toNext
#print axioms SqCyclotomicStageTuple.ofCoreTable_sqRelWord_regression
#print axioms SqCyclotomicStageTuple.CrossedDerivationSpanSupply.toCorrectionSurjective
#print axioms SqCyclotomicStageTuple.CrossedDerivationSpanSupply.toDefectReachable
#print axioms SqCyclotomicStageTuple.ofOrientedEquiv_defectReachable
#print axioms SqCyclotomicStageTuple.stage_nonempty_all_levels
#print axioms SqCyclotomicStageTuple.finiteLevelEpiData_nonempty_of_base_and_corrections

end

end GQ2.Dyadic.LSquare
