/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStageFunctionals
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteForwardCapstone

/-!
# The kernel-adapted supply from a coordinate derivation family

This file reduces the sole remaining input of the odd-degree forward presentation theorem,
`SqKernelAdaptedDefectSupply K h`, to two sharply isolated per-stage data:

* **a coordinate derivation family** (`SqStageCoordinateDerivationFamily`): for each
  non-twisted generator slot, one continuous homomorphism of the field group into the finite
  lift group `WL (k+1)` whose base component is the mod-`2^(k+1)` cyclotomic shadow and whose
  offsets on a fixed tuple of exact-fibre ambient lifts have the Kronecker parity pattern.
  Only offset *parities* are constrained, and the twisted `x₁` slot is left entirely free;
* **a handle-digit repair supply** (`SqStageHandleDigitRepairSupply`): any depth correction
  killing the defect can be replaced by one that also has trivial mod-`2^(k+1)` cyclotomic
  digits at all handle coordinates.  At `h = 0` this is vacuous.

The mathematical content of the reduction: every family functional kills the whole literal
raw shift span (the row computations of `StageFunctionals`), and kills the actual stage
defect **unconditionally** — the ambient improved relator value is annihilated because the
improved word is universally closed in `WL (k+1)` at the canonical orientation.  Against the
proven field-side augmented span theorem, whose tail atoms the family separates diagonally,
this forces the tail factor of the defect to be trivial
(`stageResidual_mem_rawShiftSpan_of_forall_derivKer`), i.e. raw defect reachability.  The family criterion is exact: membership in the raw shift
span is *equivalent* to simultaneous vanishing of all family functionals
(`SqStageCoordinateDerivationFamily.mem_rawShiftSpan_iff`), the all-`k` field-side form of
the model's cubic cokernel theorem.

The base cyclotomic digits at handle slots are trivial for free
(`stageSupply_chiLevel_canonLift_handle`), so the repair supply is exactly the handle-row
clause of the kernel-adapted supply.  The reduction is calibrated at `h = 0`, where the
repair is a theorem and the capstone consequently needs only the family.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.FoxH

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-! ## Exact-fibre ambient lifts of a stage tuple -/

/-- Every stage tuple has ambient lifts with the exact per-slot cyclotomic targets: the
tuple's own fibre witnesses. -/
theorem SqCyclotomicStageTuple.exists_exactChiLift {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) :
    ∃ x : Fin (SqCore.sqRank h) → maxProPQuotient 2 (GalK K),
      (∀ i, chiCycKTwo (K := K) (x i) = sqStageChiTargetUnit h i) ∧
      ∀ i, levelMk (maxProPQuotient 2 (GalK K)) k (x i) = T.generators i := by
  have hpick : ∀ i : Fin (SqCore.sqRank h), ∃ x : maxProPQuotient 2 (GalK K),
      chiCycKTwo (K := K) x = sqStageChiTargetUnit h i ∧
        levelMk (maxProPQuotient 2 (GalK K)) k x = T.generators i := by
    intro i
    rcases SqCore.sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · obtain ⟨x, hxchi, hx⟩ := T.sigma
      exact ⟨x, by rw [hxchi, sqStageChiTargetUnit_zero], hx.symm⟩
    · obtain ⟨x, hxchi, hx⟩ := T.x0
      exact ⟨x, by rw [hxchi, sqStageChiTargetUnit_one], hx.symm⟩
    · obtain ⟨x, hxchi, hx⟩ := T.x1
      exact ⟨x, by rw [hxchi, sqStageChiTargetUnit_two], hx.symm⟩
    · obtain ⟨x, hxker, hx⟩ := T.handleU j
      have hx1 : chiCycKTwo (K := K) x = 1 := MonoidHom.mem_ker.mp hxker
      exact ⟨x, by rw [hx1, sqStageChiTargetUnit_handleU], hx.symm⟩
    · obtain ⟨x, hxker, hx⟩ := T.handleV j
      have hx1 : chiCycKTwo (K := K) x = 1 := MonoidHom.mem_ker.mp hxker
      exact ⟨x, by rw [hx1, sqStageChiTargetUnit_handleV], hx.symm⟩
  choose x hchi hlvl using hpick
  exact ⟨x, hchi, hlvl⟩

/-! ## The coordinate derivation family -/

/-- **A coordinate derivation family at a stage.**  A tuple of exact-fibre ambient lifts of
the stage generators together with, for each non-twisted slot `i₀`, a continuous χ-shadowed
homomorphism into `WL (k+1)` whose offsets at the lifts have odd parity exactly at `i₀`
among the non-twisted slots.  The twisted slot `2` carries no offset constraint, and only
parities are prescribed.  This is the Lean form of "`2h+2` χ-twisted crossed derivations
separating the non-twisted tails". -/
structure SqStageCoordinateDerivationFamily {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) where
  lifts : Fin (SqCore.sqRank h) → maxProPQuotient 2 (GalK K)
  lifts_chi : ∀ i, chiCycKTwo (K := K) (lifts i) = sqStageChiTargetUnit h i
  lifts_level : ∀ i, levelMk (maxProPQuotient 2 (GalK K)) k (lifts i) = T.generators i
  deriv : ∀ i₀ : Fin (SqCore.sqRank h), i₀ ≠ 2 →
    ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (WL (k + 1))
  deriv_base : ∀ (i₀ : Fin (SqCore.sqRank h)) (hi₀ : i₀ ≠ 2),
    IsChiShadowDeriv (chiCycKTwo (K := K)) (deriv i₀ hi₀)
  deriv_diag : ∀ (i₀ : Fin (SqCore.sqRank h)) (hi₀ : i₀ ≠ 2),
    ¬ (2 : ZMod (2 ^ (k + 1))) ∣ ((deriv i₀ hi₀) (lifts i₀)).u
  deriv_off : ∀ (i₀ : Fin (SqCore.sqRank h)) (hi₀ : i₀ ≠ 2)
    (j : Fin (SqCore.sqRank h)), j ≠ 2 → j ≠ i₀ →
    (2 : ZMod (2 ^ (k + 1))) ∣ ((deriv i₀ hi₀) (lifts j)).u

namespace SqStageCoordinateDerivationFamily

variable {h k : ℕ} {T : SqCyclotomicStageTuple K h k}

/-- The canonical-lift base differs from the family base by coordinatewise central
classes. -/
theorem exists_central_shift (F : SqStageCoordinateDerivationFamily T) :
    ∃ z : Fin (SqCore.sqRank h) → levelQuot (maxProPQuotient 2 (GalK K)) (k + 1),
      (∀ i, z i ∈ zLayer (maxProPQuotient 2 (GalK K)) k) ∧
      ∀ i, canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i) =
        z i * levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (F.lifts i) := by
  have hproj : ∀ i, GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k
      (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) =
      GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k
        (levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (F.lifts i)) := by
    intro i
    rw [levelProj_canonLift, levelProj_levelMk, F.lifts_level i]
  choose z hz heq using fun i ↦
    exists_zLayer_mul (G := maxProPQuotient 2 (GalK K)) (hproj i)
  exact ⟨z, hz, heq⟩

/-- The literal core-plus-handle shift word over the canonical-lift base equals the one over
the family base. -/
theorem dbarWord_eq (F : SqStageCoordinateDerivationFamily T)
    (c : Fin (SqCore.sqRank h) → levelQuot (maxProPQuotient 2 (GalK K)) (k + 1)) :
    sqCoreHandleDbarWord
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) c =
      sqCoreHandleDbarWord
        (fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (F.lifts i)) c := by
  obtain ⟨z, hz, heq⟩ := F.exists_central_shift
  rw [show (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) =
      fun i ↦ z i * levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (F.lifts i) from
        funext heq]
  exact sqCoreHandleDbarWord_central_base_shift hz c

/-- Non-twisted tails over the canonical-lift base are level classes of ambient tail powers
of the family lifts: the central discrepancy dies because `Z_k` has exponent two and the
tail exponent is even. -/
theorem tail_eq (F : SqStageCoordinateDerivationFamily T) (hk : 3 ≤ k)
    (i : Fin (SqCore.sqRank h)) :
    canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i) ^ 2 ^ (k - 1) =
      levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (F.lifts i ^ 2 ^ (k - 1)) := by
  obtain ⟨z, hz, heq⟩ := F.exists_central_shift
  rw [map_pow, heq i]
  have hcomm : Commute (z i)
      (levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (F.lifts i)) :=
    zLayer_commute (hz i) _
  rw [hcomm.mul_pow]
  have hzpow : z i ^ 2 ^ (k - 1) = 1 := by
    have h2 : (2 : ℕ) ^ (k - 1) = 2 * 2 ^ (k - 2) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h2, pow_mul, zLayer_sq _ (hz i), one_pow]
  rw [hzpow, one_mul]

/-- **Every family functional kills the actual stage defect.**  The defect is the level
class of the ambient improved relator value at the exact-fibre lifts, and the improved word
is universally closed in the lift group at the canonical orientation. -/
theorem defect_mem_derivKer (F : SqStageCoordinateDerivationFamily T)
    (i₀ : Fin (SqCore.sqRank h)) (hi₀ : i₀ ≠ 2) :
    sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators ∈
      derivKer (F.deriv i₀ hi₀) k := by
  have hdef : sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators =
      levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (SqCore.sqRelWord F.lifts) := by
    rw [SqCore.map_sqRelWord (levelMk (maxProPQuotient 2 (GalK K)) (k + 1)) F.lifts]
    exact (sqStageDefect_eq_of_lift h k T.generators _ (fun i ↦ by
      rw [levelProj_levelMk, F.lifts_level i])).symm
  rw [hdef]
  refine stageDeriv_relWord_mem_derivKer (F.deriv_base i₀ hi₀) F.lifts F.lifts_chi ?_
  rw [show (fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) k (F.lifts i)) = T.generators from
    funext F.lifts_level]
  exact T.relation

/-- **Every family functional kills the whole raw shift span over the canonical-lift
base.** -/
theorem rawShiftSpan_le_derivKer (F : SqStageCoordinateDerivationFamily T) (hk : 3 ≤ k)
    (i₀ : Fin (SqCore.sqRank h)) (hi₀ : i₀ ≠ 2) :
    rawShiftSpan
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk ≤
      derivKer (F.deriv i₀ hi₀) k := by
  rintro z ⟨q, ⟨V, rfl⟩, rfl⟩
  have hword : ((rawDepthShiftHom
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk) V).1 =
      sqCoreHandleDbarWord
        (fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (F.lifts i))
        V.correction := by
    change sqCoreHandleDbarWord
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) V.correction = _
    exact F.dbarWord_eq V.correction
  show ((rawDepthShiftHom
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk) V).1 ∈
    derivKer (F.deriv i₀ hi₀) k
  rw [hword]
  exact stageDeriv_rawShiftSpan_le_derivKer hk (F.deriv_base i₀ hi₀) F.lifts F.lifts_chi
    (rawDepthShift_mem_rawShiftSpan
      (fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) (k + 1) (F.lifts i)) hk V)

end SqStageCoordinateDerivationFamily

/-! ## Squarefree normal form for the canonical tail span -/

/-- A relator-adapted non-twisted tail of a stage, bundled in the graded layer. -/
def stageTailLayer {h k : ℕ} (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    (i : {i : Fin (SqCore.sqRank h) // i ≠ 2}) :
    ↥(zLayer (maxProPQuotient 2 (GalK K)) k) :=
  ⟨canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i.1) ^ 2 ^ (k - 1), by
    have h := pow_two_pow_mem_lambdaImage
      (canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i.1)) (k - 1)
    rwa [show 1 + (k - 1) = k by omega] at h⟩

local instance stageSupplyZLayerCommGroup (k : ℕ) :
    CommGroup ↥(zLayer (maxProPQuotient 2 (GalK K)) k) :=
  { (inferInstance : Group ↥(zLayer (maxProPQuotient 2 (GalK K)) k)) with
    mul_comm := fun a b ↦ Subtype.ext (zLayer_commute a.2 b.1).eq }

private theorem stageSupply_prod_mul_prod_eq_prod_symmDiff
    {I H : Type*} [DecidableEq I] [CommGroup H]
    (f : I → H) (hsq : ∀ i, f i * f i = 1) (s t : Finset I) :
    (∏ i ∈ s, f i) * (∏ i ∈ t, f i) = ∏ i ∈ symmDiff s t, f i := by
  induction s using Finset.induction generalizing t with
  | empty => simp [Finset.symmDiff_def]
  | @insert a s ha ih =>
      by_cases hat : a ∈ t
      · let t' := t.erase a
        have hat' : a ∉ t' := by simp [t']
        have ht : insert a t' = t := Finset.insert_erase hat
        have hsd : symmDiff (insert a s) t = symmDiff s t' := by
          ext x
          simp only [Finset.mem_symmDiff, Finset.mem_insert]
          by_cases hxa : x = a
          · subst x
            simp [ha, hat, t']
          · simp [hxa, t']
        calc
          (∏ i ∈ insert a s, f i) * (∏ i ∈ t, f i) =
              (f a * ∏ i ∈ s, f i) * (f a * ∏ i ∈ t', f i) := by
                rw [Finset.prod_insert ha, ← ht, Finset.prod_insert hat']
          _ = (f a * f a) * ((∏ i ∈ s, f i) * (∏ i ∈ t', f i)) := by ac_rfl
          _ = (∏ i ∈ s, f i) * (∏ i ∈ t', f i) := by rw [hsq, one_mul]
          _ = ∏ i ∈ symmDiff s t', f i := ih t'
          _ = ∏ i ∈ symmDiff (insert a s) t, f i := by rw [hsd]
      · have hnot : a ∉ symmDiff s t := by simp [Finset.mem_symmDiff, ha, hat]
        have hsd : symmDiff (insert a s) t = insert a (symmDiff s t) := by
          ext x
          simp only [Finset.mem_symmDiff, Finset.mem_insert]
          by_cases hxa : x = a
          · subst x
            simp [ha, hat]
          · simp [hxa]
        calc
          (∏ i ∈ insert a s, f i) * (∏ i ∈ t, f i) =
              (f a * ∏ i ∈ s, f i) * (∏ i ∈ t, f i) := by
                rw [Finset.prod_insert ha]
          _ = f a * ((∏ i ∈ s, f i) * (∏ i ∈ t, f i)) := by rw [mul_assoc]
          _ = f a * ∏ i ∈ symmDiff s t, f i := by rw [ih t]
          _ = ∏ i ∈ insert a (symmDiff s t), f i := (Finset.prod_insert hnot).symm
          _ = ∏ i ∈ symmDiff (insert a s) t, f i := by rw [hsd]

private theorem stageTailLayer_mul_self {h k : ℕ} (T : SqCyclotomicStageTuple K h k)
    (hk : 3 ≤ k) (i : {i : Fin (SqCore.sqRank h) // i ≠ 2}) :
    stageTailLayer T hk i * stageTailLayer T hk i = 1 := by
  apply Subtype.ext
  simpa [pow_two] using
    zLayer_sq (maxProPQuotient 2 (GalK K)) (stageTailLayer T hk i).2

/-- Every element of the canonical tail span is a squarefree finset product of the bundled
tails. -/
theorem stageResidualTailSpan_exists_finset_prod {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k)
    {t : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1)}
    (ht : t ∈ SqCyclotomicStageTuple.stageResidualTailSpan T) :
    ∃ (hmem : t ∈ zLayer (maxProPQuotient 2 (GalK K)) k)
      (s : Finset {i : Fin (SqCore.sqRank h) // i ≠ 2}),
      (⟨t, hmem⟩ : ↥(zLayer (maxProPQuotient 2 (GalK K)) k)) =
        ∏ i ∈ s, stageTailLayer T hk i := by
  classical
  have hmem : t ∈ zLayer (maxProPQuotient 2 (GalK K)) k :=
    SqCyclotomicStageTuple.stageResidualTailSpan_le_zLayer T (by omega) ht
  refine ⟨hmem, ?_⟩
  let P : Subgroup ↥(zLayer (maxProPQuotient 2 (GalK K)) k) :=
    { carrier := {x | ∃ s : Finset {i : Fin (SqCore.sqRank h) // i ≠ 2},
          x = ∏ i ∈ s, stageTailLayer T hk i}
      one_mem' := ⟨∅, by simp⟩
      mul_mem' := by
        rintro x y ⟨s, rfl⟩ ⟨u, rfl⟩
        exact ⟨symmDiff s u, (stageSupply_prod_mul_prod_eq_prod_symmDiff
          (stageTailLayer T hk) (stageTailLayer_mul_self T hk) s u).symm ▸ rfl⟩
      inv_mem' := by
        rintro x ⟨s, rfl⟩
        refine ⟨s, ?_⟩
        apply inv_eq_of_mul_eq_one_right
        rw [stageSupply_prod_mul_prod_eq_prod_symmDiff
          (stageTailLayer T hk) (stageTailLayer_mul_self T hk) s s, symmDiff_self]
        simp }
  suffices hsuff : ∀ x, x ∈ SqCyclotomicStageTuple.stageResidualTailSpan T →
      x ∈ zLayer (maxProPQuotient 2 (GalK K)) k ∧
        ∀ hx : x ∈ zLayer (maxProPQuotient 2 (GalK K)) k,
          (⟨x, hx⟩ : ↥(zLayer (maxProPQuotient 2 (GalK K)) k)) ∈ P by
    exact (hsuff t ht).2 hmem
  intro x hx
  refine Subgroup.closure_induction (p := fun y _ ↦
      y ∈ zLayer (maxProPQuotient 2 (GalK K)) k ∧
        ∀ hy : y ∈ zLayer (maxProPQuotient 2 (GalK K)) k,
          (⟨y, hy⟩ : ↥(zLayer (maxProPQuotient 2 (GalK K)) k)) ∈ P)
    ?_ ?_ ?_ ?_ hx
  · rintro y ⟨i, hi, rfl⟩
    refine ⟨(stageTailLayer T hk ⟨i, hi⟩).2, fun hy ↦ ⟨{⟨i, hi⟩}, ?_⟩⟩
    rw [Finset.prod_singleton]
    exact Subtype.ext rfl
  · exact ⟨Subgroup.one_mem _, fun hy ↦ ⟨∅, Subtype.ext (by simp)⟩⟩
  · rintro a b _ _ ⟨haz, hap⟩ ⟨hbz, hbp⟩
    refine ⟨Subgroup.mul_mem _ haz hbz, fun hy ↦ ?_⟩
    have hprod : (⟨a * b, hy⟩ : ↥(zLayer (maxProPQuotient 2 (GalK K)) k)) =
        (⟨a, haz⟩ : ↥(zLayer (maxProPQuotient 2 (GalK K)) k)) * ⟨b, hbz⟩ :=
      Subtype.ext rfl
    rw [hprod]
    exact P.mul_mem (hap haz) (hbp hbz)
  · rintro a _ ⟨haz, hap⟩
    refine ⟨Subgroup.inv_mem _ haz, fun hy ↦ ?_⟩
    have hinv : (⟨a⁻¹, hy⟩ : ↥(zLayer (maxProPQuotient 2 (GalK K)) k)) =
        (⟨a, haz⟩ : ↥(zLayer (maxProPQuotient 2 (GalK K)) k))⁻¹ :=
      Subtype.ext rfl
    rw [hinv]
    exact P.inv_mem (hap haz)

/-! ## The span criterion at the field -/

/-- **Span membership from simultaneous kernel membership.**  A central class killed by
every family functional lies in the literal raw shift span over the canonical-lift base:
decompose it as shift times tail word by the proven augmented span theorem, put the tail
word in squarefree normal form, and separate with the diagonal offset pattern.  This is the
all-stage field-side generalization of the model's cubic cokernel theorem. -/
theorem stageResidual_mem_rawShiftSpan_of_forall_derivKer {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} (hk : 3 ≤ k)
    (F : SqStageCoordinateDerivationFamily T)
    {zc : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1)}
    (hzc : zc ∈ zLayer (maxProPQuotient 2 (GalK K)) k)
    (hker : ∀ (i₀ : Fin (SqCore.sqRank h)) (hi₀ : i₀ ≠ 2),
      zc ∈ derivKer (F.deriv i₀ hi₀) k) :
    zc ∈ rawShiftSpan
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk := by
  classical
  obtain ⟨V, t, ht, hdec⟩ := SqCyclotomicStageTuple.stageResidual_exists_shift_mul_tail T hk hzc
  have hshift_ker : ∀ (i₀ : Fin (SqCore.sqRank h)) (hi₀ : i₀ ≠ 2),
      sqCoreHandleDbarWord
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
        V.correction ∈ derivKer (F.deriv i₀ hi₀) k := by
    intro i₀ hi₀
    refine F.rawShiftSpan_le_derivKer hk i₀ hi₀ ?_
    exact rawDepthShift_mem_rawShiftSpan
      (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk V
  have ht_ker : ∀ (i₀ : Fin (SqCore.sqRank h)) (hi₀ : i₀ ≠ 2),
      t ∈ derivKer (F.deriv i₀ hi₀) k := by
    intro i₀ hi₀
    have h1 : t = (sqCoreHandleDbarWord
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i))
        V.correction)⁻¹ * zc := by
      rw [hdec]
      group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hshift_ker i₀ hi₀)) (hker i₀ hi₀)
  obtain ⟨hmem, s, hs⟩ := stageResidualTailSpan_exists_finset_prod T hk ht
  have hsempty : s = ∅ := by
    by_contra hne
    obtain ⟨i₀, hi₀s⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hKb : ∀ j : {i : Fin (SqCore.sqRank h) // i ≠ 2}, j ≠ i₀ →
        stageTailLayer T hk j ∈
          (derivKer (F.deriv i₀.1 i₀.2) k).comap
            (zLayer (maxProPQuotient 2 (GalK K)) k).subtype := by
      intro j hj
      rw [Subgroup.mem_comap]
      show canonLift (maxProPQuotient 2 (GalK K)) k (T.generators j.1) ^ 2 ^ (k - 1) ∈
        derivKer (F.deriv i₀.1 i₀.2) k
      rw [F.tail_eq hk j.1]
      refine stageDeriv_tail_mem_derivKer_of_even hk (F.deriv_base i₀.1 i₀.2) ?_ ?_
      · rw [F.lifts_chi j.1]
        exact sqStageChiTargetUnit_sub_one_dvd_four h j.1 j.2
      · exact F.deriv_off i₀.1 i₀.2 j.1 j.2 (fun hv ↦ hj (Subtype.ext hv))
    have htb : (⟨t, hmem⟩ : ↥(zLayer (maxProPQuotient 2 (GalK K)) k)) ∈
        (derivKer (F.deriv i₀.1 i₀.2) k).comap
          (zLayer (maxProPQuotient 2 (GalK K)) k).subtype := by
      rw [Subgroup.mem_comap]
      exact ht_ker i₀.1 i₀.2
    have hprodb : (∏ j ∈ s.erase i₀, stageTailLayer T hk j) ∈
        (derivKer (F.deriv i₀.1 i₀.2) k).comap
          (zLayer (maxProPQuotient 2 (GalK K)) k).subtype := by
      refine Subgroup.prod_mem _ fun j hj ↦ ?_
      exact hKb j (Finset.mem_erase.mp hj).1
    have hdiag : stageTailLayer T hk i₀ ∈
        (derivKer (F.deriv i₀.1 i₀.2) k).comap
          (zLayer (maxProPQuotient 2 (GalK K)) k).subtype := by
      have hsplit : stageTailLayer T hk i₀ =
          (⟨t, hmem⟩ : ↥(zLayer (maxProPQuotient 2 (GalK K)) k)) *
            (∏ j ∈ s.erase i₀, stageTailLayer T hk j)⁻¹ := by
        rw [hs, ← Finset.mul_prod_erase s _ hi₀s]
        group
      rw [hsplit]
      exact Subgroup.mul_mem _ htb (Subgroup.inv_mem _ hprodb)
    rw [Subgroup.mem_comap] at hdiag
    have hdiag' : canonLift (maxProPQuotient 2 (GalK K)) k
        (T.generators i₀.1) ^ 2 ^ (k - 1) ∈ derivKer (F.deriv i₀.1 i₀.2) k := hdiag
    rw [F.tail_eq hk i₀.1] at hdiag'
    refine stageDeriv_tail_not_mem_derivKer_of_odd hk (F.deriv_base i₀.1 i₀.2) ?_
      (F.deriv_diag i₀.1 i₀.2) hdiag'
    rw [F.lifts_chi i₀.1]
    exact sqStageChiTargetUnit_sub_one_dvd_four h i₀.1 i₀.2
  have ht1 : t = 1 := by
    have hval := hs
    rw [hsempty, Finset.prod_empty] at hval
    exact congrArg Subtype.val hval
  rw [hdec, ht1, mul_one]
  exact rawDepthShift_mem_rawShiftSpan
    (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk V

/-- **The exact criterion**: over a coordinate derivation family, membership of a central
class in the literal raw shift span is equivalent to simultaneous vanishing of all family
functionals. -/
theorem SqStageCoordinateDerivationFamily.mem_rawShiftSpan_iff {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} (hk : 3 ≤ k)
    (F : SqStageCoordinateDerivationFamily T)
    {zc : levelQuot (maxProPQuotient 2 (GalK K)) (k + 1)}
    (hzc : zc ∈ zLayer (maxProPQuotient 2 (GalK K)) k) :
    zc ∈ rawShiftSpan
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) hk ↔
      ∀ (i₀ : Fin (SqCore.sqRank h)) (hi₀ : i₀ ≠ 2),
        zc ∈ derivKer (F.deriv i₀ hi₀) k :=
  ⟨fun hmem i₀ hi₀ ↦ F.rawShiftSpan_le_derivKer hk i₀ hi₀ hmem,
   fun hker ↦ stageResidual_mem_rawShiftSpan_of_forall_derivKer hk F hzc hker⟩

/-- **Raw defect reachability from a coordinate derivation family.**  The family kills the
defect through the universal relator identity and kills the span by the row computations,
so the defect's tail factor is trivial. -/
theorem sqRawDefectReachable_of_coordinateDerivationFamily {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} (hk : 3 ≤ k)
    (F : SqStageCoordinateDerivationFamily T) :
    SqCyclotomicStageTuple.sqRawDefectReachable
      (maxProPQuotient 2 (GalK K)) h k T.generators := by
  rw [SqCyclotomicStageTuple.sqRawDefectReachable_iff_defect_mem_rawShiftSpan T hk]
  refine stageResidual_mem_rawShiftSpan_of_forall_derivKer hk F
    (Subgroup.inv_mem _ (sqStageDefect_mem_zLayer h k T.relation)) ?_
  intro i₀ hi₀
  exact Subgroup.inv_mem _ (F.defect_mem_derivKer i₀ hi₀)

/-! ## The handle digits of the canonical base are trivial -/

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
private theorem stageSupply_chiLevel_canonLift_eq_one {k : ℕ} (hk : 2 ≤ k)
    {q : levelQuot (maxProPQuotient 2 (GalK K)) k}
    (hq : ∃ x : maxProPQuotient 2 (GalK K),
      chiCycKTwo (K := K) x = 1 ∧
        q = levelMk (maxProPQuotient 2 (GalK K)) k x) :
    chiLevel (chiCycKTwo (K := K)) (k + 1)
      (canonLift (maxProPQuotient 2 (GalK K)) k q) = 1 := by
  obtain ⟨x, hx1, rfl⟩ := hq
  have hproj : GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k
      (canonLift (maxProPQuotient 2 (GalK K)) k
        (levelMk (maxProPQuotient 2 (GalK K)) k x)) =
      GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k
        (levelMk (maxProPQuotient 2 (GalK K)) (k + 1) x) := by
    rw [levelProj_canonLift, levelProj_levelMk]
  obtain ⟨z, hz, heq⟩ := exists_zLayer_mul (G := maxProPQuotient 2 (GalK K)) hproj
  rw [heq, map_mul, chiLevel_levelMk, hx1, map_one, mul_one]
  obtain ⟨g, hg, rfl⟩ := hz
  rw [chiLevel_levelMk]
  have hdvd := dvd_chi_of_mem_twoCentralSeries (chiCycKTwo (K := K)) hk hg
  exact MonoidHom.mem_ker.mp (mem_ker_units_toZModPow_iff.mpr (by exact_mod_cast hdvd))

/-- The canonical-lift base has trivial next-precision cyclotomic digit at every `U`-handle
slot. -/
theorem stageSupply_chiLevel_canonLift_handleU {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 2 ≤ k) (j : Fin h) :
    chiLevel (chiCycKTwo (K := K)) (k + 1)
      (canonLift (maxProPQuotient 2 (GalK K)) k
        (T.generators (SqCore.sqHandleIdxU j))) = 1 := by
  obtain ⟨x, hxker, hx⟩ := T.handleU j
  exact stageSupply_chiLevel_canonLift_eq_one hk ⟨x, MonoidHom.mem_ker.mp hxker, hx⟩

/-- The canonical-lift base has trivial next-precision cyclotomic digit at every `V`-handle
slot. -/
theorem stageSupply_chiLevel_canonLift_handleV {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 2 ≤ k) (j : Fin h) :
    chiLevel (chiCycKTwo (K := K)) (k + 1)
      (canonLift (maxProPQuotient 2 (GalK K)) k
        (T.generators (SqCore.sqHandleIdxV j))) = 1 := by
  obtain ⟨x, hxker, hx⟩ := T.handleV j
  exact stageSupply_chiLevel_canonLift_eq_one hk ⟨x, MonoidHom.mem_ker.mp hxker, hx⟩

/-! ## The handle-digit repair supply and the reduction -/

/-- **The handle-digit repair supply.**  Any depth-`k-1` correction killing the current
defect can be replaced by a defect-killing correction whose own handle coordinates have
trivial next-precision cyclotomic digits.  This is exactly the handle-row clause of the
kernel-adapted supply, since the base digits are trivial for free; at `h = 0` it is a
theorem.  The two design findings are encoded here: the clause cannot be discharged by
bracket-free moves, so it is stated as a repair of the kill rather than a separate row. -/
def SqStageHandleDigitRepairSupply {h k : ℕ} (T : SqCyclotomicStageTuple K h k) : Prop :=
  ∀ c : Fin (SqCore.sqRank h) → levelQuot (maxProPQuotient 2 (GalK K)) (k + 1),
    (∀ i, c i ∈ lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1)) →
    SqCyclotomicStageTuple.stageShift
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) c =
      (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ →
    ∃ c' : Fin (SqCore.sqRank h) → levelQuot (maxProPQuotient 2 (GalK K)) (k + 1),
      (∀ i, c' i ∈ lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1)) ∧
      SqCyclotomicStageTuple.stageShift
          (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) c' =
        (sqStageDefect (maxProPQuotient 2 (GalK K)) h k T.generators)⁻¹ ∧
      (∀ j : Fin h, chiLevel (chiCycKTwo (K := K)) (k + 1)
        (c' (SqCore.sqHandleIdxU j)) = 1) ∧
      (∀ j : Fin h, chiLevel (chiCycKTwo (K := K)) (k + 1)
        (c' (SqCore.sqHandleIdxV j)) = 1)

/-- At handle count zero the repair supply is a theorem. -/
theorem sqStageHandleDigitRepairSupply_of_rank_zero {k : ℕ}
    (T : SqCyclotomicStageTuple K 0 k) :
    SqStageHandleDigitRepairSupply T :=
  fun c hdepth hkill ↦ ⟨c, hdepth, hkill, fun j ↦ j.elim0, fun j ↦ j.elim0⟩

/-- **The kernel-adapted supply from a family and a repair at every stage.**  The family
yields the raw kill through the span criterion; the repair fixes the correction's handle
digits; the base digits are trivial, so the modified handle rows are trivial. -/
theorem sqKernelAdaptedDefectSupply_of_family_of_digitRepair {h : ℕ}
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : SqCyclotomicStageTuple K h k,
      Nonempty (SqStageCoordinateDerivationFamily T))
    (Hrepair : ∀ (k : ℕ), 3 ≤ k → ∀ T : SqCyclotomicStageTuple K h k,
      SqStageHandleDigitRepairSupply T) :
    SqKernelAdaptedDefectSupply K h := by
  intro k hk T
  obtain ⟨F⟩ := Hfam k hk T
  obtain ⟨c, hdepth, hkill⟩ := sqRawDefectReachable_of_coordinateDerivationFamily hk F
  obtain ⟨c', hdepth', hkill', hU, hV⟩ := Hrepair k hk T c hdepth hkill
  refine ⟨c', hdepth', hkill', ?_, ?_⟩
  · intro j
    rw [show SqCyclotomicStageTuple.stageModified
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) c'
          (SqCore.sqHandleIdxU j) =
        canonLift (maxProPQuotient 2 (GalK K)) k (T.generators (SqCore.sqHandleIdxU j)) *
          c' (SqCore.sqHandleIdxU j) from rfl,
      map_mul, stageSupply_chiLevel_canonLift_handleU T (by omega) j, hU j, mul_one]
  · intro j
    rw [show SqCyclotomicStageTuple.stageModified
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) k (T.generators i)) c'
          (SqCore.sqHandleIdxV j) =
        canonLift (maxProPQuotient 2 (GalK K)) k (T.generators (SqCore.sqHandleIdxV j)) *
          c' (SqCore.sqHandleIdxV j) from rfl,
      map_mul, stageSupply_chiLevel_canonLift_handleV T (by omega) j, hV j, mul_one]

/-- At `h = 0` the family alone suffices: the repair supply is vacuous. -/
theorem sqKernelAdaptedDefectSupply_of_family_rank_zero
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : SqCyclotomicStageTuple K 0 k,
      Nonempty (SqStageCoordinateDerivationFamily T)) :
    SqKernelAdaptedDefectSupply K 0 :=
  sqKernelAdaptedDefectSupply_of_family_of_digitRepair Hfam
    (fun _ _ T ↦ sqStageHandleDigitRepairSupply_of_rank_zero T)

/-- **The forward presentation theorem over the family and the repair.**  For an odd-degree
field, a coordinate derivation family and a handle-digit repair at every stage of the field's
handle count deliver the oriented presentation equivalence. -/
theorem nonempty_orientedEquiv_oddDegree_of_family_of_digitRepair
    {Rec : LocalReciprocity} (B : MarkedRecip Rec K)
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (Hfam : ∀ (k : ℕ), 3 ≤ k →
      ∀ T : SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) k,
        Nonempty (SqStageCoordinateDerivationFamily T))
    (Hrepair : ∀ (k : ℕ), 3 ≤ k →
      ∀ T : SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) k,
        SqStageHandleDigitRepairSupply T) :
    Nonempty (OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (chiCycKTwo (K := K))) :=
  nonempty_orientedEquiv_oddDegree_of_kernelAdaptedSupply B hodd
    (sqKernelAdaptedDefectSupply_of_family_of_digitRepair Hfam Hrepair)

#print axioms SqCyclotomicStageTuple.exists_exactChiLift
#print axioms SqStageCoordinateDerivationFamily.defect_mem_derivKer
#print axioms SqStageCoordinateDerivationFamily.rawShiftSpan_le_derivKer
#print axioms stageResidualTailSpan_exists_finset_prod
#print axioms stageResidual_mem_rawShiftSpan_of_forall_derivKer
#print axioms SqStageCoordinateDerivationFamily.mem_rawShiftSpan_iff
#print axioms sqRawDefectReachable_of_coordinateDerivationFamily
#print axioms stageSupply_chiLevel_canonLift_handleU
#print axioms sqKernelAdaptedDefectSupply_of_family_of_digitRepair
#print axioms sqKernelAdaptedDefectSupply_of_family_rank_zero
#print axioms nonempty_orientedEquiv_oddDegree_of_family_of_digitRepair

end

end GQ2.Dyadic.LSquare
