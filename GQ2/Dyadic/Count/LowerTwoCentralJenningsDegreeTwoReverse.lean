/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.LowerTwoCentralJenningsDegreeOneReverse
import GQ2.Dyadic.Count.H3CompletedQuadraticRelation

/-!
# Quadratic moments for the reverse degree-two Jennings containment

This file begins the reverse containment `D_3 <= lambda_3` for the improved square
presentation.  Its first reusable ingredient is independent of that presentation: a central
extension defined by a cup cocycle has trivial third lower two-central subgroup.  Consequently
every admissible quadratic detector of `DSq h` factors through the quotient by `lambda_3`.

The second ingredient converts membership of a group-like difference in the augmentation cube
into vanishing of the detector's fibre coordinate.  The remaining step is the finite quadratic
separation theorem on `lambda_2/lambda_3`.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2.Roe.Labute
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.MarkedCore
open scoped commutatorElement

variable {L : Type} [Group L] {c : GQ2.DRCoh.TwoCocycle L}

/-- The second lower two-central subgroup of a cup-cocycle central extension lies in its
central fibre. -/
theorem twoCentralSeries_two_le_centExtProj_ker (hc : IsCupCocycle c) :
    twoCentralSeries (GQ2.DRCoh.CentExt c) 2 ≤
      (GQ2.DRCoh.CentExt.proj c).ker := by
  rw [twoCentralSeries_succ (GQ2.DRCoh.CentExt c) (by omega), twoCentralSucc]
  refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) ?_
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨p, -, rfl⟩
    change (p ^ 2).base = 1
    rw [centExt_pow_base, pow_two]
    exact hc.expTwo p.base
  · rw [Subgroup.commutator_le]
    intro p hp q hq
    change (⁅p, q⁆).base = 1
    change ⁅p.base, q.base⁆ = 1
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hc.comm p.base q.base)
  · have hset : ((GQ2.DRCoh.CentExt.proj c).ker :
        Set (GQ2.DRCoh.CentExt c)) =
        (GQ2.DRCoh.CentExt.proj c) ⁻¹' {1} := by
      ext p
      simp [MonoidHom.mem_ker]
    rw [hset]
    exact isClosed_discrete _

/-- The central fibre of a normalized central extension is central. -/
theorem centExtProj_ker_le_center :
    (GQ2.DRCoh.CentExt.proj c).ker ≤
      Subgroup.center (GQ2.DRCoh.CentExt c) := by
  intro p hp
  have hbase := MonoidHom.mem_ker.mp hp
  change p.base = 1 at hbase
  rw [Subgroup.mem_center_iff]
  intro q
  apply GQ2.DRCoh.CentExt.ext
  · change q.base * p.base = p.base * q.base
    rw [hbase, one_mul, mul_one]
  · rw [GQ2.DRCoh.CentExt.mul_fib, GQ2.DRCoh.CentExt.mul_fib]
    rw [hbase, c.κ_one_left, c.κ_one_right]
    abel

/-- Every element of the central fibre has order dividing two. -/
theorem centExtProj_ker_sq_eq_one {p : GQ2.DRCoh.CentExt c}
    (hp : p ∈ (GQ2.DRCoh.CentExt.proj c).ker) : p ^ 2 = 1 := by
  have hbase := MonoidHom.mem_ker.mp hp
  change p.base = 1 at hbase
  apply GQ2.DRCoh.CentExt.ext
  · rw [centExt_pow_base, centExt_one_base, hbase, one_pow]
  · rw [pow_two, GQ2.DRCoh.CentExt.mul_fib]
    change p.fib + p.fib + c.κ p.base p.base = 0
    rw [hbase, c.κ_one_left, add_zero]
    exact CharTwo.add_self_eq_zero p.fib

/-- A central extension by a cup cocycle has lower two-central length at most two. -/
theorem twoCentralSeries_three_centExt_eq_bot (hc : IsCupCocycle c) :
    twoCentralSeries (GQ2.DRCoh.CentExt c) 3 = ⊥ := by
  rw [twoCentralSeries_succ (GQ2.DRCoh.CentExt c) (by omega)]
  apply twoCentralSucc_eq_bot_of_le_center
  · exact (twoCentralSeries_two_le_centExtProj_ker hc).trans
      centExtProj_ker_le_center
  · intro p hp
    exact centExtProj_ker_sq_eq_one
      (twoCentralSeries_two_le_centExtProj_ker hc hp)

/-- Every admissible quadratic detector kills `lambda_3(DSq h)`. -/
theorem twoCentralSeries_three_le_sqQuadraticDetectorHom_ker (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2)
    (hκ : sqRelatorQuadraticInitialGram h κ = 0) :
    twoCentralSeries (DSq h : Type) 3 ≤
      (sqQuadraticDetectorHom h κ hκ).toMonoidHom.ker := by
  intro g hg
  have himage : sqQuadraticDetectorHom h κ hκ g ∈
      twoCentralSeries
        (GQ2.DRCoh.CentExt (sqQuadraticDetectorCocycle h κ)) 3 :=
    map_twoCentralSeries_le
      (sqQuadraticDetectorHom h κ hκ).toMonoidHom
      (sqQuadraticDetectorHom h κ hκ).continuous_toFun 3 ⟨g, hg, rfl⟩
  rw [twoCentralSeries_three_centExt_eq_bot
    (sqQuadraticDetectorCocycle_isCup h κ)] at himage
  exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp himage)

/-- An admissible quadratic detector factored through `DSq h / lambda_3`. -/
noncomputable def sqQuadraticDetectorLevelThreeHom (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2)
    (hκ : sqRelatorQuadraticInitialGram h κ = 0) :
    levelQuot (DSq h : Type) 3 →*
      GQ2.DRCoh.CentExt (sqQuadraticDetectorCocycle h κ) :=
  QuotientGroup.lift (twoCentralSeries (DSq h : Type) 3)
    (sqQuadraticDetectorHom h κ hκ).toMonoidHom
    (twoCentralSeries_three_le_sqQuadraticDetectorHom_ker h κ hκ)

@[simp] theorem sqQuadraticDetectorLevelThreeHom_levelMk (h : ℕ)
    (κ : Fin (sqRank h) → Fin (sqRank h) → ZMod 2)
    (hκ : sqRelatorQuadraticInitialGram h κ = 0) (g : DSq h) :
    sqQuadraticDetectorLevelThreeHom h κ hκ
        (levelMk (DSq h : Type) 3 g) =
      sqQuadraticDetectorHom h κ hκ g :=
  rfl

/-- A cup-cocycle fibre coordinate vanishes on a group element whose group-like difference
has augmentation order at least three. -/
theorem centExtFib_eq_zero_of_groupDifference_mem_augmentation_cube
    {Q : Type} [Group Q] [Fintype Q]
    (hc : IsCupCocycle c) (φ : Q →* GQ2.DRCoh.CentExt c) (q : Q)
    (hq : modTwoFiniteGroupDifference Q q ∈
      modTwoFiniteAugmentationIdeal Q ^ 3) :
    (φ q).fib = 0 := by
  have hzero :=
    modTwoGroupAlgebraFunctionMoment_eq_zero_of_mem_augmentation_cube
      hc φ (modTwoFiniteGroupDifference Q q) hq
  rw [modTwoFiniteGroupDifference, map_sub,
    ] at hzero
  change modTwoGroupAlgebraFunctionMoment (fun q => (φ q).fib)
      (MonoidAlgebra.single q 1) -
      modTwoGroupAlgebraFunctionMoment (fun q => (φ q).fib) 1 = 0 at hzero
  rw [modTwoGroupAlgebraFunctionMoment_single, one_mul] at hzero
  have hone : (φ (1 : Q)).fib = 0 := by simp
  rw [MonoidAlgebra.one_def,
    modTwoGroupAlgebraFunctionMoment_single, one_mul, hone, sub_zero] at hzero
  exact hzero

#print axioms twoCentralSeries_three_centExt_eq_bot
#print axioms twoCentralSeries_three_le_sqQuadraticDetectorHom_ker
#print axioms centExtFib_eq_zero_of_groupDifference_mem_augmentation_cube

end

end GQ2.ContCoh
