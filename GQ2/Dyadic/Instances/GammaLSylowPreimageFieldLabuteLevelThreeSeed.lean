/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.CyclotomicKummerBridgeModEight
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStage
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteHilbertTail

/-!
# The exact arbitrary odd-degree level-three seed

This file separates the desired level-three seed into the two finite statements which the
current cohomological normal form is meant to prove.

* A `SqCyclotomicFrattiniFrame` is a tuple of actual elements of `G_K(2)` with the improved
  constructor-table values whose images generate `G_K(2)/lambda_2`.
* `SqCyclotomicFrattiniFrame.LevelThreeRelation` is the single assertion that the literal
  improved word `Y^2 [S,X] prod_j [U_j,V_j]` vanishes modulo `lambda_3` on that tuple.

The adapter below proves everything after those statements: exact value fibres are tautological,
and generation at level three follows from the existing Frattini non-generation theorem.  Thus
the remaining relation theorem does not conceal a presentation or an oriented equivalence.

The arithmetic coordinate inputs are now complete and non-circular: the mod-four row is `[-1]`,
the independent mod-eight row is `[2]` (`CyclotomicKummerBridgeModEight`), the two are orthogonal,
and `FieldData.exists_cupFormK_normalForm` gives the full odd-degree cup table.  What is still
absent is the finite transgression realization theorem carrying a dual Frattini basis with that
cup table to the displayed relation in `lambda_2/lambda_3`.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 ContCoh
open GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- Actual generators with the five improved cyclotomic rows and a generating image in the
Frattini quotient.  In contrast to `SqCyclotomicStageTuple`, no relation in level three is part
of this structure. -/
structure SqCyclotomicFrattiniFrame
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] (h : ℕ) where
  generators : Fin (SqCore.sqRank h) → maxProPQuotient 2 (GalK K)
  sigma : chiCycKTwo (K := K) (generators 0) = GQ2.Roe.SvalUnit
  x0 : chiCycKTwo (K := K) (generators 1) = GQ2.Roe.rootXUnit
  x1 : chiCycKTwo (K := K) (generators 2) = GQ2.Roe.YvalUnit
  handleU : ∀ j : Fin h,
    generators (SqCore.sqHandleIdxU j) ∈ (chiCycKTwo (K := K)).toMonoidHom.ker
  handleV : ∀ j : Fin h,
    generators (SqCore.sqHandleIdxV j) ∈ (chiCycKTwo (K := K)).toMonoidHom.ker
  levelTwoGen : Subgroup.closure
    (Set.range fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) 2 (generators i)) = ⊤

namespace SqCyclotomicFrattiniFrame

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- The sole level-three relation assertion left after constructing a Frattini frame. -/
def LevelThreeRelation {h : ℕ} (F : SqCyclotomicFrattiniFrame K h) : Prop :=
  SqCore.sqRelWord
    (fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) 3 (F.generators i)) = 1

/-- The degree-one class attached to a continuous mod-two character of `G_K(2)`. -/
noncomputable def characterClass
    (c : ContinuousMonoidHom (maxProPQuotient 2 (GalK K))
      (Multiplicative (ZMod 2))) :
    H1 (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  H1mk _ _ (Count.homEquivZ1 c)

/-- A Frattini frame is cup-adapted when evaluation on its actual generators identifies the
field cup form with the constructor table of the literal improved quadratic relator.  This is
the basis-free statement delivered by a dual Frattini basis; it quantifies over all continuous
characters, so it does not assume named coordinate classes or a presentation. -/
def IsCupAdapted {h : ℕ} (F : SqCyclotomicFrattiniFrame K h) : Prop :=
  ∀ c d : ContinuousMonoidHom (maxProPQuotient 2 (GalK K))
      (Multiplicative (ZMod 2)),
    FieldData.cupFormK K
        (h1MaxProTwoEquivGalK (K := K) (characterClass (K := K) c))
        (h1MaxProTwoEquivGalK (K := K) (characterClass (K := K) d)) =
      GQ2.ContCoh.sqRelatorQuadraticInitialGram h
        (fun i j ↦ Multiplicative.toAdd (c (F.generators i)) *
          Multiplicative.toAdd (d (F.generators j)))

/-- The improved reciprocity constructor table supplies the exceptional entries of a Frattini
frame.  The caller chooses kernel handles and proves only generation in the Frattini quotient. -/
def ofCoreTable
    (T : OddDegreeGalKSqCyclotomicCoreTable K) (h : ℕ)
    (generators : Fin (SqCore.sqRank h) → maxProPQuotient 2 (GalK K))
    (hsigma : generators 0 = T.sigma)
    (hx0 : generators 1 = T.x0)
    (hx1 : generators 2 = T.x1)
    (hhandleU : ∀ j : Fin h,
      generators (SqCore.sqHandleIdxU j) ∈ (chiCycKTwo (K := K)).toMonoidHom.ker)
    (hhandleV : ∀ j : Fin h,
      generators (SqCore.sqHandleIdxV j) ∈ (chiCycKTwo (K := K)).toMonoidHom.ker)
    (htop : Subgroup.closure
      (Set.range fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) 2 (generators i)) = ⊤) :
    SqCyclotomicFrattiniFrame K h where
  generators := generators
  sigma := by rw [hsigma]; exact T.sigma_value
  x0 := by rw [hx0]; exact T.x0_value
  x1 := by rw [hx1]; exact T.x1_value
  handleU := hhandleU
  handleV := hhandleV
  levelTwoGen := htop

/-- A Frattini frame satisfying the literal improved relation gives the exact level-three stage.
The `topGen` proof is derived, not assumed: its image in level two is `F.levelTwoGen`, and the
kernel of `Q_3 -> Q_2` is Frattini. -/
noncomputable def toLevelThree {h : ℕ} (F : SqCyclotomicFrattiniFrame K h)
    (hrel : F.LevelThreeRelation) : SqCyclotomicStageTuple K h 3 where
  generators i := levelMk (maxProPQuotient 2 (GalK K)) 3 (F.generators i)
  sigma := ⟨F.generators 0, F.sigma, rfl⟩
  x0 := ⟨F.generators 1, F.x0, rfl⟩
  x1 := ⟨F.generators 2, F.x1, rfl⟩
  handleU j := ⟨F.generators (SqCore.sqHandleIdxU j), F.handleU j, rfl⟩
  handleV j := ⟨F.generators (SqCore.sqHandleIdxV j), F.handleV j, rfl⟩
  relation := hrel
  topGen := by
    let G := maxProPQuotient 2 (GalK K)
    let H : Subgroup (levelQuot G 3) :=
      Subgroup.closure (Set.range fun i ↦ levelMk G 3 (F.generators i))
    change H = ⊤
    refine eq_top_of_map_levelProj_eq_top G
      (maxProTwoGalK_isTopologicallyFinGen K) isProP_maxProPQuotient (by omega) ?_
    change (Subgroup.closure (Set.range fun i ↦ levelMk G 3 (F.generators i))).map
      (GQ2.Roe.Labute.levelProj G 2) = ⊤
    rw [MonoidHom.map_closure]
    have himage : (GQ2.Roe.Labute.levelProj G 2) ''
        (Set.range fun i ↦ levelMk G 3 (F.generators i)) =
      Set.range fun i ↦ levelMk G 2 (F.generators i) := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun i ↦ levelProj_levelMk G 2 (F.generators i))
    rw [himage]
    exact F.levelTwoGen

@[simp] theorem toLevelThree_generators {h : ℕ}
    (F : SqCyclotomicFrattiniFrame K h) (hrel : F.LevelThreeRelation) :
    (F.toLevelThree hrel).generators =
      fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) 3 (F.generators i) := rfl

/-- Regression: the seed adapter retains the improved variable-rank word literally. -/
theorem toLevelThree_sqRelWord_regression {h : ℕ}
    (F : SqCyclotomicFrattiniFrame K h) (hrel : F.LevelThreeRelation) :
    SqCore.sqRelWord (F.toLevelThree hrel).generators = 1 :=
  hrel

end SqCyclotomicFrattiniFrame

/-! ## Exact remaining supplies -/

/-- The missing finite Frattini-frame realization.  The proved `[-1]` and `[2]` cyclotomic
bridges plus the odd-degree cup normal form are designed to discharge this statement by finite
elementary-abelian duality.  The output explicitly carries the improved relator's cup table.

The marked bundle `_B` is a **binder, not an axiom**.  The construction uses marked reciprocity
at `K` only through cyclotomic surjectivity and sharp fibre lifting, and both of those are
generic in the bundle; carrying the bundle here is what lets every consumer pass its own
`MarkedRecip` rather than summon `markedRecipAt` (B5-K), which is what keeps the odd-degree
endpoints' axiom prints inside the frozen `ℚ₂` capstone's nine. -/
def OddDegreeSqCyclotomicFrattiniFrameSupply : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    {R : LocalReciprocity} (_B : MarkedRecip R K),
    Odd (Module.finrank ℚ_[2] K) →
      ∃ F : SqCyclotomicFrattiniFrame K ((Module.finrank ℚ_[2] K - 1) / 2),
        F.IsCupAdapted

/-- The exact missing transgression theorem.  It says that every correctly oriented Frattini
frame obtained from the cup-normal-form construction kills the literal improved quadratic word
modulo `lambda_3`.  It is a finite-quotient statement, not a global presentation. -/
def OddDegreeSqLevelThreeRelationRealization : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (_hodd : Odd (Module.finrank ℚ_[2] K))
    (F : SqCyclotomicFrattiniFrame K ((Module.finrank ℚ_[2] K - 1) / 2)),
      F.IsCupAdapted → F.LevelThreeRelation

/-- Sharp seed reduction: the two finite supplies imply the arbitrary odd-degree level-three
base used by the direct rigidity capstone. -/
theorem oddDegree_sqCyclotomicStageTuple_levelThree_of_finiteRealization
    (hframe : OddDegreeSqCyclotomicFrattiniFrameSupply)
    (hrelation : OddDegreeSqLevelThreeRelationRealization)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    {R : LocalReciprocity} (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    Nonempty (SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) 3) := by
  obtain ⟨F, hcup⟩ := hframe K B hodd
  exact ⟨F.toLevelThree (hrelation K hodd F hcup)⟩

#print axioms SqCyclotomicFrattiniFrame.toLevelThree
#print axioms oddDegree_sqCyclotomicStageTuple_levelThree_of_finiteRealization

end

end GQ2.Dyadic.LSquare
