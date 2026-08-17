/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcFixedCRelativeBracketObstruction
import GQ2.Dyadic.SqCore.GradedTwo

/-!
# The fixed-C neutral-bracket obstruction

The one-handle Mpc inverse-limit climb once isolated a repaired fixed-`C`
bracket-surjectivity premise by restricting residuals to the relative,
abelian-neutral layer.  This module proves that repair is still impossible:
for every `c : DM 2 1`, a finite Heisenberg quotient detects a relative,
abelian-neutral commutator outside the image of `[c, -]` modulo `lambda_3`.

The construction chooses orthogonal handle and core covectors in the six
mod-two marked coordinates.  They kill both `c` and the even relator Gram,
while their mixed wedge detects a relative commutator.  Since the Heisenberg
test group has trivial third two-central-series term, fixed-`C` surjectivity
would force its nonzero central detector to vanish.

Consequently the remaining honest one-handle route is balanced multi-slot
finite-class lifting; neither unrestricted nor abelian-neutral fixed-`C`
one-slot adjoint surjectivity can supply the climb.
-/

namespace GQ2.Dyadic.Instances.MpcFixedCNeutralBracketObstruction

noncomputable section

open GQ2 GQ2.Dyadic Multiplicative
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.SqCore
open GQ2.Dyadic.EvenModel
open GQ2.Dyadic.Instances.MpcGeneralHandleDefectAbsorption
open GQ2.Dyadic.Instances.MpcGeneralHandleStandardStabilization
open GQ2.Dyadic.Instances.MpcFixedCRelativeBracketObstruction
open GQ2.Roe.Labute
open scoped commutatorElement

private abbrev TestHeis := SqHeis (ZMod 2)

private def dot6 (v w : Fin (coreRank 1) → ZMod 2) : ZMod 2 :=
  ∑ i, v i * w i

private def orthFirst (_x y : ZMod 2) : ZMod 2 := y

private def orthSecond (x y : ZMod 2) : ZMod 2 :=
  if x = 0 ∧ y = 0 then 1 else x

private theorem orthPair_dot (x y : ZMod 2) :
    orthFirst x y * x + orthSecond x y * y = 0 := by
  fin_cases x <;> fin_cases y <;> decide

private theorem orthPair_nonzero (x y : ZMod 2) :
    orthFirst x y = 1 ∨ orthSecond x y = 1 := by
  fin_cases x <;> fin_cases y <;> decide

private theorem dot6_single (i : Fin (coreRank 1)) (x : ZMod 2)
    (c : Fin (coreRank 1) → ZMod 2) :
    dot6 (Pi.single i x) c = x * c i := by
  rw [dot6, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, zero_mul]
  · simp

private theorem dot6_add (l m c : Fin (coreRank 1) → ZMod 2) :
    dot6 (l + m) c = dot6 l c + dot6 m c := by
  simp [dot6, Finset.sum_add_distrib, add_mul]

private def relativePairDetected (l m : Fin (coreRank 1) → ZMod 2) : Prop :=
  ∃ i j : Fin (coreRank 1),
    (4 ≤ (i : ℕ) ∨ 4 ≤ (j : ℕ)) ∧ l i * m j - m i * l j = 1

private def detectorL (c : Fin (coreRank 1) → ZMod 2) :
    Fin (coreRank 1) → ZMod 2 :=
  Pi.single (handleIdxU (0 : Fin 1))
      (orthFirst (c (handleIdxU (0 : Fin 1))) (c (handleIdxV (0 : Fin 1)))) +
    Pi.single (handleIdxV (0 : Fin 1))
      (orthSecond (c (handleIdxU (0 : Fin 1))) (c (handleIdxV (0 : Fin 1))))

private def detectorM (c : Fin (coreRank 1) → ZMod 2) :
    Fin (coreRank 1) → ZMod 2 :=
  Pi.single (2 : Fin (coreRank 1))
      (orthFirst (c (2 : Fin (coreRank 1))) (c (3 : Fin (coreRank 1)))) +
    Pi.single (3 : Fin (coreRank 1))
      (orthSecond (c (2 : Fin (coreRank 1))) (c (3 : Fin (coreRank 1))))

@[simp] theorem detectorL_handleU (c : Fin (coreRank 1) → ZMod 2) :
    detectorL c (handleIdxU (0 : Fin 1)) =
      orthFirst (c (handleIdxU (0 : Fin 1))) (c (handleIdxV (0 : Fin 1))) := by
  rw [detectorL, Pi.add_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (Fin.ne_of_val_ne (by
      simp only [handleIdxU_val, handleIdxV_val]
      omega)), add_zero]

@[simp] theorem detectorL_handleV (c : Fin (coreRank 1) → ZMod 2) :
    detectorL c (handleIdxV (0 : Fin 1)) =
      orthSecond (c (handleIdxU (0 : Fin 1))) (c (handleIdxV (0 : Fin 1))) := by
  rw [detectorL, Pi.add_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (Fin.ne_of_val_ne (by
      simp only [handleIdxU_val, handleIdxV_val]
      omega)), zero_add]

@[simp] theorem detectorL_core (c : Fin (coreRank 1) → ZMod 2)
    (i : Fin (coreRank 1)) (hi : (i : ℕ) < 4) : detectorL c i = 0 := by
  rw [detectorL, Pi.add_apply,
    Pi.single_eq_of_ne (Fin.ne_of_val_ne (by simp only [handleIdxU_val]; omega)),
    Pi.single_eq_of_ne (Fin.ne_of_val_ne (by simp only [handleIdxV_val]; omega)),
    zero_add]

@[simp] theorem detectorL_zero (c : Fin (coreRank 1) → ZMod 2) : detectorL c 0 = 0 :=
  detectorL_core c 0 (by norm_num [coreRank])

@[simp] theorem detectorL_one (c : Fin (coreRank 1) → ZMod 2) : detectorL c 1 = 0 :=
  detectorL_core c 1 (by norm_num [coreRank])

@[simp] theorem detectorL_two (c : Fin (coreRank 1) → ZMod 2) : detectorL c 2 = 0 :=
  detectorL_core c 2 (by norm_num [coreRank])

@[simp] theorem detectorL_three (c : Fin (coreRank 1) → ZMod 2) : detectorL c 3 = 0 :=
  detectorL_core c 3 (by norm_num [coreRank])

@[simp] theorem detectorM_two (c : Fin (coreRank 1) → ZMod 2) :
    detectorM c 2 = orthFirst (c 2) (c 3) := by
  simp [detectorM]

@[simp] theorem detectorM_three (c : Fin (coreRank 1) → ZMod 2) :
    detectorM c 3 = orthSecond (c 2) (c 3) := by
  simp [detectorM]

@[simp] theorem detectorM_handleU (c : Fin (coreRank 1) → ZMod 2) :
    detectorM c (handleIdxU (0 : Fin 1)) = 0 := by
  rw [detectorM, Pi.add_apply,
    Pi.single_eq_of_ne (by decide),
    Pi.single_eq_of_ne (by decide),
    zero_add]

@[simp] theorem detectorM_handleV (c : Fin (coreRank 1) → ZMod 2) :
    detectorM c (handleIdxV (0 : Fin 1)) = 0 := by
  rw [detectorM, Pi.add_apply,
    Pi.single_eq_of_ne (by decide),
    Pi.single_eq_of_ne (by decide),
    zero_add]

@[simp] theorem detectorM_zero (c : Fin (coreRank 1) → ZMod 2) : detectorM c 0 = 0 := by
  simp [detectorM]

@[simp] theorem detectorM_one (c : Fin (coreRank 1) → ZMod 2) : detectorM c 1 = 0 := by
  simp [detectorM]

private theorem exists_relative_pair_detector (c : Fin (coreRank 1) → ZMod 2) :
    ∃ l m : Fin (coreRank 1) → ZMod 2,
      dot6 l c = 0 ∧ dot6 m c = 0 ∧ evenCupForm l m = 0 ∧
        relativePairDetected l m := by
  refine ⟨detectorL c, detectorM c, ?_, ?_, ?_, ?_⟩
  · rw [detectorL, dot6_add, dot6_single, dot6_single]
    exact orthPair_dot _ _
  · rw [detectorM, dot6_add, dot6_single, dot6_single]
    exact orthPair_dot _ _
  · simp [evenCupForm]
  · rcases orthPair_nonzero (c (handleIdxU (0 : Fin 1)))
      (c (handleIdxV (0 : Fin 1))) with hU | hV
    · rcases orthPair_nonzero (c 2) (c 3) with hC | hD
      · refine ⟨handleIdxU (0 : Fin 1), 2, ?_, ?_⟩
        · left
          simp only [handleIdxU_val, Fin.val_eq_zero]
          omega
        simp [hU, hC]
      · refine ⟨handleIdxU (0 : Fin 1), 3, ?_, ?_⟩
        · left
          simp only [handleIdxU_val, Fin.val_eq_zero]
          omega
        simp [hU, hD]
    · rcases orthPair_nonzero (c 2) (c 3) with hC | hD
      · refine ⟨handleIdxV (0 : Fin 1), 2, ?_, ?_⟩
        · left
          simp only [handleIdxV_val, Fin.val_eq_zero]
          omega
        simp [hV, hC]
      · refine ⟨handleIdxV (0 : Fin 1), 3, ?_, ?_⟩
        · left
          simp only [handleIdxV_val, Fin.val_eq_zero]
          omega
        simp [hV, hD]

private def detectorMark (l m : Fin (coreRank 1) → ZMod 2) :
    Fin (coreRank 1) → TestHeis :=
  fun i => ⟨l i, m i, 0⟩

private theorem detectorMark_rel (l m : Fin (coreRank 1) → ZMod 2)
    (hgram : evenCupForm l m = 0) : mRelWord 2 (detectorMark l m) = 1 := by
  rw [mRelWord, handleWord_one]
  apply SqHeis.ext
  · simp [mWord, detectorMark, SqHeis.pow_a,
      CharTwo.two_eq_zero]
    exact Or.inl (by decide)
  · simp [mWord, detectorMark, SqHeis.pow_b,
      CharTwo.two_eq_zero]
    exact Or.inl (by decide)
  · simp [mWord, detectorMark, SqHeis.pow_c]
    have h2 : (2 : ZMod 2) = 0 := by decide
    have h4 : (4 : ZMod 2) = 0 := by decide
    have hchoose : ((Nat.choose 4 2 : ℕ) : ZMod 2) = 0 := by decide
    rw [h2, h4, hchoose]
    simp only [mul_zero, zero_mul, add_zero]
    rw [evenCupForm] at hgram
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hgram
    simp [sub_eq_add_neg, CharTwo.neg_eq]

private theorem one_le_two : 1 ≤ 2 := by omega

private def modTwoCoordinate (c : DM 2 1) (i : Fin (coreRank 1)) : ZMod 2 :=
  Multiplicative.toAdd
    (dmCoordinateCharacter 2 1 one_le_two (Pi.single i 1) c)

private theorem dmCoordinateCharacter_add (v w : Fin (coreRank 1) → ZMod 2) :
    dmCoordinateCharacter 2 1 one_le_two (v + w) =
      dmCoordinateCharacter 2 1 one_le_two v *
        dmCoordinateCharacter 2 1 one_le_two w := by
  apply dm_hom_ext
  intro i
  simp [dmCoordinateCharacter_gen]

private theorem dmCoordinateCharacter_single_eval (c : DM 2 1)
    (i : Fin (coreRank 1)) (x : ZMod 2) :
    Multiplicative.toAdd
        (dmCoordinateCharacter 2 1 one_le_two (Pi.single i x) c) =
      x * modTwoCoordinate c i := by
  fin_cases x
  · change Multiplicative.toAdd
        (dmCoordinateCharacter 2 1 one_le_two (Pi.single i 0) c) =
      0 * modTwoCoordinate c i
    have hzero : dmCoordinateCharacter 2 1 one_le_two
        (Pi.single i (0 : ZMod 2)) = 1 := by
      apply dm_hom_ext
      intro j
      simp [dmCoordinateCharacter_gen]
    rw [hzero]
    simp
  · change Multiplicative.toAdd
        (dmCoordinateCharacter 2 1 one_le_two (Pi.single i 1) c) =
      1 * modTwoCoordinate c i
    simp [modTwoCoordinate]

private theorem dmCoordinateCharacter_detectorL (c : DM 2 1) :
    Multiplicative.toAdd
        (dmCoordinateCharacter 2 1 one_le_two
          (detectorL (modTwoCoordinate c)) c) = 0 := by
  rw [detectorL, dmCoordinateCharacter_add]
  simp only [ContinuousMonoidHom.mul_apply, toAdd_mul,
    dmCoordinateCharacter_single_eval]
  exact orthPair_dot _ _

private theorem dmCoordinateCharacter_detectorM (c : DM 2 1) :
    Multiplicative.toAdd
        (dmCoordinateCharacter 2 1 one_le_two
          (detectorM (modTwoCoordinate c)) c) = 0 := by
  rw [detectorM, dmCoordinateCharacter_add]
  simp only [ContinuousMonoidHom.mul_apply, toAdd_mul,
    dmCoordinateCharacter_single_eval]
  exact orthPair_dot _ _

private noncomputable def detectorHom (l m : Fin (coreRank 1) → ZMod 2)
    (hgram : evenCupForm l m = 0) :
    ContinuousMonoidHom (DM 2 1) TestHeis :=
  mLiftHom 2 1 (SqHeis.isProP_two (m := 1) (by rw [Nat.card_zmod]; norm_num))
    (detectorMark l m) (detectorMark_rel l m hgram)

@[simp] theorem detectorHom_gen (l m : Fin (coreRank 1) → ZMod 2)
    (hgram : evenCupForm l m = 0) (i : Fin (coreRank 1)) :
    detectorHom l m hgram (dmGen 2 1 i) = detectorMark l m i := by
  rw [detectorHom, mLiftHom_gen]

private noncomputable def detectorACharacter (l m : Fin (coreRank 1) → ZMod 2)
  (hgram : evenCupForm l m = 0) :
    ContinuousMonoidHom (DM 2 1) (Multiplicative (ZMod 2)) :=
  ⟨SqHeis.aHom.comp (detectorHom l m hgram).toMonoidHom,
    (continuous_of_discreteTopology : Continuous
      (SqHeis.aHom : TestHeis → Multiplicative (ZMod 2))).comp
        (detectorHom l m hgram).continuous_toFun⟩

private noncomputable def detectorBCharacter (l m : Fin (coreRank 1) → ZMod 2)
  (hgram : evenCupForm l m = 0) :
    ContinuousMonoidHom (DM 2 1) (Multiplicative (ZMod 2)) :=
  ⟨SqHeis.bHom.comp (detectorHom l m hgram).toMonoidHom,
    (continuous_of_discreteTopology : Continuous
      (SqHeis.bHom : TestHeis → Multiplicative (ZMod 2))).comp
        (detectorHom l m hgram).continuous_toFun⟩

private theorem detectorACharacter_eq (l m : Fin (coreRank 1) → ZMod 2)
    (hgram : evenCupForm l m = 0) :
    detectorACharacter l m hgram = dmCoordinateCharacter 2 1 one_le_two l := by
  apply dm_hom_ext
  intro i
  rw [dmCoordinateCharacter_gen]
  change SqHeis.aHom (detectorHom l m hgram (dmGen 2 1 i)) =
    Multiplicative.ofAdd (l i)
  rw [detectorHom_gen]
  rfl

private theorem detectorBCharacter_eq (l m : Fin (coreRank 1) → ZMod 2)
    (hgram : evenCupForm l m = 0) :
    detectorBCharacter l m hgram = dmCoordinateCharacter 2 1 one_le_two m := by
  apply dm_hom_ext
  intro i
  rw [dmCoordinateCharacter_gen]
  change SqHeis.bHom (detectorHom l m hgram (dmGen 2 1 i)) =
    Multiplicative.ofAdd (m i)
  rw [detectorHom_gen]
  rfl

private theorem detectorHom_a (l m : Fin (coreRank 1) → ZMod 2)
    (hgram : evenCupForm l m = 0) (c : DM 2 1) :
    (detectorHom l m hgram c).a = Multiplicative.toAdd
      (dmCoordinateCharacter 2 1 one_le_two l c) := by
  have h := DFunLike.congr_fun (detectorACharacter_eq l m hgram) c
  change Multiplicative.ofAdd (detectorHom l m hgram c).a = _ at h
  have h' := congrArg Multiplicative.toAdd h
  simpa using h'

private theorem detectorHom_b (l m : Fin (coreRank 1) → ZMod 2)
    (hgram : evenCupForm l m = 0) (c : DM 2 1) :
    (detectorHom l m hgram c).b = Multiplicative.toAdd
      (dmCoordinateCharacter 2 1 one_le_two m c) := by
  have h := DFunLike.congr_fun (detectorBCharacter_eq l m hgram) c
  change Multiplicative.ofAdd (detectorHom l m hgram c).b = _ at h
  have h' := congrArg Multiplicative.toAdd h
  simpa using h'

private theorem detectorCup_zero (c : Fin (coreRank 1) → ZMod 2) :
    evenCupForm (detectorL c) (detectorM c) = 0 := by
  simp [evenCupForm]

private theorem detectorPair_relative (c : Fin (coreRank 1) → ZMod 2) :
    relativePairDetected (detectorL c) (detectorM c) := by
  rcases orthPair_nonzero (c (handleIdxU (0 : Fin 1)))
      (c (handleIdxV (0 : Fin 1))) with hU | hV
  · rcases orthPair_nonzero (c 2) (c 3) with hC | hD
    · refine ⟨handleIdxU (0 : Fin 1), 2, ?_, ?_⟩
      · left
        simp only [handleIdxU_val, Fin.val_eq_zero]
        omega
      · simp [hU, hC]
    · refine ⟨handleIdxU (0 : Fin 1), 3, ?_, ?_⟩
      · left
        simp only [handleIdxU_val, Fin.val_eq_zero]
        omega
      · simp [hU, hD]
  · rcases orthPair_nonzero (c 2) (c 3) with hC | hD
    · refine ⟨handleIdxV (0 : Fin 1), 2, ?_, ?_⟩
      · left
        simp only [handleIdxV_val, Fin.val_eq_zero]
        omega
      · simp [hV, hC]
    · refine ⟨handleIdxV (0 : Fin 1), 3, ?_, ?_⟩
      · left
        simp only [handleIdxV_val, Fin.val_eq_zero]
        omega
      · simp [hV, hD]

private theorem dmForgetHandles_gen_eq_one_of_four_le
    (i : Fin (coreRank 1)) (hi : 4 ≤ (i : ℕ)) :
    dmForgetHandles 2 1 (dmGen 2 1 i) = 1 := by
  rcases nCoreIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp only [Fin.val_zero] at hi
    omega
  · simp only [coreVal_one] at hi
    omega
  · simp only [coreVal_two] at hi
    omega
  · simp only [coreVal_three] at hi
    omega
  · exact dmForgetHandles_handleU 2 1 j
  · exact dmForgetHandles_handleV 2 1 j

private def testX : TestHeis := ⟨1, 0, 0⟩
private def testY : TestHeis := ⟨0, 1, 0⟩

private theorem testHeis_mem_center_of_ab_zero {p : TestHeis}
    (ha : p.a = 0) (hb : p.b = 0) : p ∈ Subgroup.center TestHeis := by
  rw [Subgroup.mem_center_iff]
  intro q
  apply SqHeis.ext
  · simp [ha]
  · simp [hb]
  · simp [ha, hb]
    abel

private theorem testHeis_sq_mem_center (p : TestHeis) :
    p ^ 2 ∈ Subgroup.center TestHeis := by
  apply testHeis_mem_center_of_ab_zero
  · simp [SqHeis.pow_a, CharTwo.two_eq_zero]
  · simp [SqHeis.pow_b, CharTwo.two_eq_zero]

private theorem testHeis_twoCentralSeries_two_le_center :
    twoCentralSeries TestHeis 2 ≤ Subgroup.center TestHeis := by
  rw [twoCentralSeries_succ TestHeis (by omega), twoCentralSucc]
  refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) (isClosed_discrete _)
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨p, -, rfl⟩
    exact testHeis_sq_mem_center p
  · rw [Subgroup.commutator_le]
    intro p _ q _
    apply testHeis_mem_center_of_ab_zero
    · simp only [commutatorElement_def, SqHeis.mul_a, SqHeis.inv_a]
      rw [CharTwo.neg_eq, CharTwo.neg_eq]
      calc
        p.a + q.a + p.a + q.a = (p.a + p.a) + (q.a + q.a) := by abel
        _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add]
    · simp only [commutatorElement_def, SqHeis.mul_b, SqHeis.inv_b]
      rw [CharTwo.neg_eq, CharTwo.neg_eq]
      calc
        p.b + q.b + p.b + q.b = (p.b + p.b) + (q.b + q.b) := by abel
        _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add]

private theorem testHeis_center_sq_eq_one (p : TestHeis)
    (hp : p ∈ Subgroup.center TestHeis) : p ^ 2 = 1 := by
  have hcommX := Subgroup.mem_center_iff.mp hp testX
  have hcommY := Subgroup.mem_center_iff.mp hp testY
  have hb : p.b = 0 := by
    have h := congrArg SqHeis.c hcommX
    simpa [testX] using h
  have ha : p.a = 0 := by
    have h := congrArg SqHeis.c hcommY
    simpa [testY] using h
  apply SqHeis.ext
  · simp [SqHeis.pow_a, ha]
  · simp [SqHeis.pow_b, hb]
  · rw [SqHeis.pow_c]
    simp [ha, hb, CharTwo.two_eq_zero]

private theorem testHeis_twoCentralSeries_three_eq_bot :
    twoCentralSeries TestHeis 3 = ⊥ := by
  rw [twoCentralSeries_succ TestHeis (by omega)]
  exact twoCentralSucc_eq_bot_of_le_center
    testHeis_twoCentralSeries_two_le_center
    (fun p hp => testHeis_center_sq_eq_one p
      (testHeis_twoCentralSeries_two_le_center hp))

private def testMark : Fin (coreRank 1) → TestHeis :=
  fullMark testX testY 1 1 (fun _ => testX) (fun _ => testY)

@[simp] theorem testMark_zero : testMark 0 = testX := by
  simp [testMark]

@[simp] theorem testMark_one : testMark 1 = testY := by
  simp [testMark]

@[simp] theorem testMark_two : testMark 2 = 1 := by
  simp [testMark]

@[simp] theorem testMark_three : testMark 3 = 1 := by
  simp [testMark]

@[simp] theorem testMark_handleU :
    testMark (handleIdxU (0 : Fin 1)) = testX := by
  simp [testMark]

@[simp] theorem testMark_handleV :
    testMark (handleIdxV (0 : Fin 1)) = testY := by
  simp [testMark]

private theorem testMark_rel : mRelWord 2 testMark = 1 := by
  apply SqHeis.ext <;>
    simp [mRelWord, mWord, handleWord, testX, testY, testMark, commP,
      SqHeis.pow_c, CharTwo.two_eq_zero] <;> decide

private noncomputable def testHom :
    ContinuousMonoidHom (DM 2 1) TestHeis :=
  mLiftHom 2 1 (SqHeis.isProP_two (m := 1) (by rw [Nat.card_zmod]; norm_num))
    testMark testMark_rel

@[simp] theorem testHom_dmC : testHom (dmC 2 1) = 1 := by
  change testHom (dmGen 2 1 2) = 1
  rw [testHom, mLiftHom_gen, testMark_two]

@[simp] theorem testHom_handleU :
    testHom (dmGen 2 1 (handleIdxU (0 : Fin 1))) = testX := by
  rw [testHom, mLiftHom_gen, testMark_handleU]

@[simp] theorem testHom_handleV :
    testHom (dmGen 2 1 (handleIdxV (0 : Fin 1))) = testY := by
  rw [testHom, mLiftHom_gen, testMark_handleV]

private def neutralWitness : DM 2 1 :=
  commP (dmGen 2 1 (handleIdxU (0 : Fin 1)))
    (dmGen 2 1 (handleIdxV (0 : Fin 1)))

private theorem neutralWitness_mem_two :
    neutralWitness ∈ twoCentralSeries (DM 2 1) 2 := by
  exact commP_mem_twoCentralSucc (Subgroup.mem_top _) _

private theorem neutralWitness_forget : dmForgetHandles 2 1 neutralWitness = 1 := by
  simp [neutralWitness, commP]

private theorem neutralWitness_neutral : OneHandleAbelianNeutral neutralWitness := by
  intro f
  exact map_commP_eq_one f.toMonoidHom _ _

private theorem testHom_neutralWitness : (testHom neutralWitness).c = 1 := by
  rw [neutralWitness, map_commP, SqHeis.commP_c, testHom_handleU,
    testHom_handleV]
  simp [testX, testY]

private theorem not_fixedCRelativeNeutralBracketSurjective_dmC :
    ¬ FixedCRelativeNeutralBracketSurjective (dmC 2 1) := by
  intro Had
  obtain ⟨epsilon, _, _, heq⟩ := Had 1 neutralWitness neutralWitness_mem_two
    neutralWitness_forget neutralWitness_neutral
  have hdiff : neutralWitness * (commP (dmC 2 1) epsilon)⁻¹ ∈
      twoCentralSeries (DM 2 1) 3 := by
    rw [lim_mem_twoCentralSeries_iff_levelMk, map_mul, map_inv]
    rw [heq, mul_inv_cancel]
  have him : testHom (neutralWitness * (commP (dmC 2 1) epsilon)⁻¹) ∈
      twoCentralSeries TestHeis 3 :=
    map_twoCentralSeries_le testHom.toMonoidHom testHom.continuous_toFun 3
      ⟨_, hdiff, rfl⟩
  rw [testHeis_twoCentralSeries_three_eq_bot] at him
  have hone : testHom (neutralWitness * (commP (dmC 2 1) epsilon)⁻¹) = 1 :=
    Subgroup.mem_bot.mp him
  have hcomm : testHom (commP (dmC 2 1) epsilon) = 1 := by
    rw [map_commP, testHom_dmC]
    simp [commP]
  have hwitness : testHom neutralWitness = 1 := by
    rw [map_mul, map_inv, hcomm, inv_one, mul_one] at hone
    exact hone
  have hc := congrArg SqHeis.c hwitness
  rw [testHom_neutralWitness, SqHeis.one_c] at hc
  exact one_ne_zero hc

theorem not_fixedCRelativeNeutralBracketSurjective (c : DM 2 1) :
    ¬ FixedCRelativeNeutralBracketSurjective c := by
  let cv := modTwoCoordinate c
  let l := detectorL cv
  let m := detectorM cv
  have hgram : evenCupForm l m = 0 := detectorCup_zero cv
  obtain ⟨i, j, hij, hdet⟩ := detectorPair_relative cv
  let H := detectorHom l m hgram
  let r := commP (dmGen 2 1 i) (dmGen 2 1 j)
  have hrTwo : r ∈ twoCentralSeries (DM 2 1) 2 := by
    exact commP_mem_twoCentralSucc (Subgroup.mem_top _) _
  have hrForget : dmForgetHandles 2 1 r = 1 := by
    rcases hij with hi | hj
    · simp [r, commP, dmForgetHandles_gen_eq_one_of_four_le i hi]
    · simp [r, commP, dmForgetHandles_gen_eq_one_of_four_le j hj]
  have hrNeutral : OneHandleAbelianNeutral r := by
    intro f
    exact map_commP_eq_one f.toMonoidHom _ _
  have hca : (H c).a = 0 := by
    rw [detectorHom_a]
    exact dmCoordinateCharacter_detectorL c
  have hcb : (H c).b = 0 := by
    rw [detectorHom_b]
    exact dmCoordinateCharacter_detectorM c
  have hrDetect : (H r).c = 1 := by
    dsimp [r]
    rw [map_commP, SqHeis.commP_c, detectorHom_gen, detectorHom_gen]
    simp only [detectorMark, l, m]
    rw [mul_comm (detectorL cv j) (detectorM cv i)]
    exact hdet
  intro Had
  obtain ⟨epsilon, _, _, heq⟩ := Had 1 r hrTwo hrForget hrNeutral
  have hdiff : r * (commP c epsilon)⁻¹ ∈ twoCentralSeries (DM 2 1) 3 := by
    rw [lim_mem_twoCentralSeries_iff_levelMk, map_mul, map_inv]
    rw [heq, mul_inv_cancel]
  have him : H (r * (commP c epsilon)⁻¹) ∈ twoCentralSeries TestHeis 3 :=
    map_twoCentralSeries_le H.toMonoidHom H.continuous_toFun 3 ⟨_, hdiff, rfl⟩
  rw [testHeis_twoCentralSeries_three_eq_bot] at him
  have hone : H (r * (commP c epsilon)⁻¹) = 1 := Subgroup.mem_bot.mp him
  have hcomm : H (commP c epsilon) = 1 := by
    rw [map_commP]
    apply SqHeis.ext
    · simp
    · simp
    · simp [SqHeis.commP_c, hca, hcb]
  have hrOne : H r = 1 := by
    rw [map_mul, map_inv, hcomm, inv_one, mul_one] at hone
    exact hone
  have hc := congrArg SqHeis.c hrOne
  rw [hrDetect, SqHeis.one_c] at hc
  exact one_ne_zero hc

#print axioms not_fixedCRelativeNeutralBracketSurjective

end
end GQ2.Dyadic.Instances.MpcFixedCNeutralBracketObstruction
