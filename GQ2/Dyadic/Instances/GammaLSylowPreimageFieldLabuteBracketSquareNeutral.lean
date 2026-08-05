/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStageDigitFlipDamage
import GQ2.Roe.Labute.GradedLie.SpanIdentities

/-!
# Tower descent of the bracket-square residual

This file resolves the level structure of `SqStageBracketSquareNeutralSupply`: the residual
at stage `k + 1` follows from the neutral damage supply at stage `k`, so the whole per-stage
supply tower collapses onto the single cubic stage `k = 3`.

* **The neutral square transport**: the literal core-plus-handle shift word of a
  coordinatewise `λ_{k-2}`-modification squares to the shift word of the squared
  modification (`k ≥ 4`, the GL-campaign transport identity `sqCoreHandleDbarWord_sq`),
  and — the new arithmetic point — squaring a correction moves its cyclotomic digit **one
  precision deeper**: a mod-`2^k` neutral digit becomes a mod-`2^(k+1)` neutral digit, so
  neutrality is preserved up the tower (`stageBracketSquare_chiLevel_sq`).
* **The descent step** (`sqStageBracketSquareNeutralSupply_of_proj_neutralDamage`): a stage
  tuple at level `k + 1` projects to a stage tuple at level `k` (`SqCyclotomicStageTuple.proj`),
  and the half-damage bracket `B = [σ̄^(2^(k-2)), z̄]` at level `k + 1` projects to the *full*
  damage bracket at level `k`.  A neutral realization of the level-`k` damage lifts and
  squares to a neutral realization of `B²`.
* **The collapse** (`sqStageNeutralDamageSupply_of_cubic`,
  `sqStageBracketSquareNeutralSupply_of_cubic`): with the same-stage equivalence
  `sqStageBracketSquareNeutralSupply_iff_neutralDamage` this yields, by induction on the
  level, both supplies at every stage `k ≥ 3` from the cubic neutral damage supply
  (`SqCubicNeutralDamageSupply`) alone; the forward presentation capstone now consumes a
  derivation family and one mod-16 statement per handle
  (`nonempty_orientedEquiv_oddDegree_of_family_of_cubicNeutralDamage`).
* **The borderline digit verdict** (`stageFlip_headU_correction_not_neutral`): the
  tautological realization of the damage — the σ-power head placed at the handle slot — is
  *not* a neutral correction: `χ(σ)^(2^(k-2)) = Sval^(2^(k-2)) = 1 + 2^k·odd` is sharp, one
  digit short of neutrality.  Route (α) of the design memo is therefore closed; every
  neutral realization must be genuinely multi-coordinate, and the sole remaining input of
  the forward route is the cubic supply.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## The neutral square transport for the shift word -/

section Transport

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A central left factor in the second argument does not change the commutator. -/
private theorem stageBracketSquare_commP_central_right {H : Type*} [Group H] {z : H}
    (hz : ∀ t : H, z * t = t * z) (w b : H) : commP w (z * b) = commP w b := by
  have hzi : ∀ t : H, z⁻¹ * t = t * z⁻¹ := by
    intro t
    calc z⁻¹ * t = z⁻¹ * (t * z) * z⁻¹ := by group
      _ = z⁻¹ * (z * t) * z⁻¹ := by rw [← hz t]
      _ = t * z⁻¹ := by group
  simp only [commP, mul_inv_rev]
  calc w⁻¹ * (b⁻¹ * z⁻¹) * w * (z * b)
      = w⁻¹ * b⁻¹ * (z⁻¹ * w) * z * b := by group
    _ = w⁻¹ * b⁻¹ * (w * z⁻¹) * z * b := by rw [hzi w]
    _ = w⁻¹ * b⁻¹ * w * b := by group

/-- Naturality of the handle shift word under the tower projection. -/
private theorem stageBracketSquare_levelProj_handleWord {h k : ℕ}
    (base c : Fin (SqCore.sqRank h) → levelQuot G (k + 1 + 1)) :
    GQ2.Roe.Labute.levelProj G (k + 1) (sqHandleDbarWord base c) =
      sqHandleDbarWord (fun i ↦ GQ2.Roe.Labute.levelProj G (k + 1) (base i))
        (fun i ↦ GQ2.Roe.Labute.levelProj G (k + 1) (c i)) := by
  rw [sqHandleDbarWord, sqHandleDbarWord, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply, commP, map_mul, map_inv]

/-- Naturality of the literal core-plus-handle shift word under the tower projection. -/
private theorem stageBracketSquare_levelProj_word {h k : ℕ}
    (base c : Fin (SqCore.sqRank h) → levelQuot G (k + 1 + 1)) :
    GQ2.Roe.Labute.levelProj G (k + 1) (sqCoreHandleDbarWord base c) =
      sqCoreHandleDbarWord (fun i ↦ GQ2.Roe.Labute.levelProj G (k + 1) (base i))
        (fun i ↦ GQ2.Roe.Labute.levelProj G (k + 1) (c i)) := by
  rw [sqCoreHandleDbarWord, sqCoreHandleDbarWord, map_mul,
    stageBracketSquare_levelProj_handleWord, map_dbarWordR2]
  congr 2
  funext i
  fin_cases i <;> simp

/-- Squaring an ambient class moves a trivial cyclotomic digit one precision deeper: a
mod-`2^(k+1)` neutral witness squares to a mod-`2^(k+2)` neutral class. -/
private theorem stageBracketSquare_chiLevel_sq (χ : ContinuousMonoidHom G ℤ_[2]ˣ) {k : ℕ}
    {w : G} (hw : chiLevel χ (k + 1) (levelMk G (k + 1) w) = 1) :
    chiLevel χ (k + 1 + 1) (levelMk G (k + 1 + 1) w ^ 2) = 1 := by
  have hdvd : ((2 : ℕ) : ℤ_[2]) ^ (k + 1) ∣ ((χ w : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    rw [chiLevel_levelMk] at hw
    exact mem_ker_units_toZModPow_iff.mp (MonoidHom.mem_ker.mpr hw)
  have htwo : ((2 : ℕ) : ℤ_[2]) ∣ ((χ w : ℤ_[2]ˣ) : ℤ_[2]) + 1 := by
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨1 + 2 ^ k * c, ?_⟩
    push_cast at hc ⊢
    linear_combination hc
  have hdvd2 : ((2 : ℕ) : ℤ_[2]) ^ (k + 1 + 1) ∣ ((χ w ^ 2 : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    obtain ⟨c, hc⟩ := hdvd
    obtain ⟨d, hd⟩ := htwo
    refine ⟨c * d, ?_⟩
    have hval : ((χ w ^ 2 : ℤ_[2]ˣ) : ℤ_[2]) - 1 =
        (((χ w : ℤ_[2]ˣ) : ℤ_[2]) - 1) * (((χ w : ℤ_[2]ˣ) : ℤ_[2]) + 1) := by
      push_cast
      ring
    rw [hval, hc, hd]
    push_cast
    ring
  rw [← map_pow, chiLevel_levelMk]
  refine MonoidHom.mem_ker.mp (mem_ker_units_toZModPow_iff.mpr ?_)
  rw [map_pow]
  exact hdvd2

end Transport

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-! ## Projection of a stage tuple down the tower -/

/-- **The projected stage tuple**: the level-`k` shadow of a level-`(k+1)` stage tuple.  All
fibre witnesses, the improved relation, and generation descend along `levelProj`. -/
def SqCyclotomicStageTuple.proj {h k : ℕ} (T : SqCyclotomicStageTuple K h (k + 1)) :
    SqCyclotomicStageTuple K h k where
  generators := fun i ↦
    GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k (T.generators i)
  sigma := by
    obtain ⟨x, hxchi, hxgen⟩ := T.sigma
    exact ⟨x, hxchi, by rw [hxgen, levelProj_levelMk]⟩
  x0 := by
    obtain ⟨x, hxchi, hxgen⟩ := T.x0
    exact ⟨x, hxchi, by rw [hxgen, levelProj_levelMk]⟩
  x1 := by
    obtain ⟨x, hxchi, hxgen⟩ := T.x1
    exact ⟨x, hxchi, by rw [hxgen, levelProj_levelMk]⟩
  handleU := fun j ↦ by
    obtain ⟨x, hxker, hxgen⟩ := T.handleU j
    exact ⟨x, hxker, by rw [hxgen, levelProj_levelMk]⟩
  handleV := fun j ↦ by
    obtain ⟨x, hxker, hxgen⟩ := T.handleV j
    exact ⟨x, hxker, by rw [hxgen, levelProj_levelMk]⟩
  relation := by
    have h := congrArg
      (GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k) T.relation
    rwa [SqCore.map_sqRelWord, map_one] at h
  topGen := closure_range_levelProj T.topGen

@[simp] theorem SqCyclotomicStageTuple.proj_generators {h k : ℕ}
    (T : SqCyclotomicStageTuple K h (k + 1)) (i : Fin (SqCore.sqRank h)) :
    T.proj.generators i =
      GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) k (T.generators i) := rfl

/-! ## The descent step -/

/-- One slot of the descent: a neutral realization of the level-`k` damage bracket at the
letter `t` lifts and squares to a neutral realization of the level-`(k+1)` half-damage
bracket square at `t`. -/
private theorem stageBracketSquare_component {h k : ℕ}
    (T : SqCyclotomicStageTuple K h (k + 1)) (hk : 3 ≤ k) (t : Fin (SqCore.sqRank h))
    (Hdam : commP
        ((canonLift (maxProPQuotient 2 (GalK K)) k (T.proj.generators 0)) ^ 2 ^ (k - 2))
        (canonLift (maxProPQuotient 2 (GalK K)) k (T.proj.generators t)) ∈
      stageNeutralShiftSpan T.proj hk) :
    commP
        ((canonLift (maxProPQuotient 2 (GalK K)) (k + 1) (T.generators 0)) ^ 2 ^ (k - 2))
        (canonLift (maxProPQuotient 2 (GalK K)) (k + 1) (T.generators t)) ^ 2 ∈
      stageNeutralShiftSpan T (show 3 ≤ k + 1 by omega) := by
  -- a neutral level-`k` correction realizing the damage, with ambient witnesses
  obtain ⟨V', hV'mem, hV'word⟩ := exists_of_mem_stageNeutralShiftSpan Hdam
  choose w hwmem hwmk using fun i ↦ V'.depth i
  -- the lifted correction one level up
  have hWdepth : ∀ i, levelMk (maxProPQuotient 2 (GalK K)) (k + 1 + 1) (w i) ∈
      lambdaImage (maxProPQuotient 2 (GalK K)) (k - 1) (k + 1 + 1) :=
    fun i ↦ ⟨w i, hwmem i, rfl⟩
  have hWproj : ∀ i, GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) (k + 1)
      (levelMk (maxProPQuotient 2 (GalK K)) (k + 1 + 1) (w i)) = V'.correction i := by
    intro i
    rw [levelProj_levelMk]
    exact hwmk i
  -- the central discrepancy between the two level-`(k+1)` bases
  have hzshift : ∀ i, ∃ z ∈ zLayer (maxProPQuotient 2 (GalK K)) k,
      T.generators i = z * canonLift (maxProPQuotient 2 (GalK K)) k
        (T.proj.generators i) := by
    intro i
    exact exists_zLayer_mul (by rw [levelProj_canonLift, SqCyclotomicStageTuple.proj_generators])
  choose z hzmem hzeq using hzshift
  -- projection of the lifted shift word is the level-`k` damage
  have hproj_word : GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) (k + 1)
      (sqCoreHandleDbarWord
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) (k + 1) (T.generators i))
        (fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) (k + 1 + 1) (w i))) =
      commP
        ((canonLift (maxProPQuotient 2 (GalK K)) k (T.proj.generators 0)) ^ 2 ^ (k - 2))
        (canonLift (maxProPQuotient 2 (GalK K)) k (T.proj.generators t)) := by
    rw [stageBracketSquare_levelProj_word]
    have hbase : (fun i ↦ GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) (k + 1)
        (canonLift (maxProPQuotient 2 (GalK K)) (k + 1) (T.generators i))) =
        fun i ↦ z i * canonLift (maxProPQuotient 2 (GalK K)) k (T.proj.generators i) := by
      funext i
      rw [levelProj_canonLift]
      exact hzeq i
    have hcorr : (fun i ↦ GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) (k + 1)
        (levelMk (maxProPQuotient 2 (GalK K)) (k + 1 + 1) (w i))) = V'.correction :=
      funext hWproj
    rw [hbase, hcorr, sqCoreHandleDbarWord_central_base_shift hzmem, hV'word]
  -- projection of the half-damage bracket is the same level-`k` damage
  have hproj_B : GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) (k + 1)
      (commP
        ((canonLift (maxProPQuotient 2 (GalK K)) (k + 1) (T.generators 0)) ^ 2 ^ (k - 2))
        (canonLift (maxProPQuotient 2 (GalK K)) (k + 1) (T.generators t))) =
      commP
        ((canonLift (maxProPQuotient 2 (GalK K)) k (T.proj.generators 0)) ^ 2 ^ (k - 2))
        (canonLift (maxProPQuotient 2 (GalK K)) k (T.proj.generators t)) := by
    have hmap : GQ2.Roe.Labute.levelProj (maxProPQuotient 2 (GalK K)) (k + 1)
        (commP
          ((canonLift (maxProPQuotient 2 (GalK K)) (k + 1) (T.generators 0)) ^ 2 ^ (k - 2))
          (canonLift (maxProPQuotient 2 (GalK K)) (k + 1) (T.generators t))) =
        commP ((T.generators 0) ^ 2 ^ (k - 2)) (T.generators t) := by
      simp only [commP, map_mul, map_inv, map_pow, levelProj_canonLift]
    have hzpow : z 0 ^ 2 ^ (k - 2) = 1 := by
      rw [show k - 2 = k - 3 + 1 by omega, pow_succ', pow_mul,
        zLayer_sq _ (hzmem 0), one_pow]
    rw [hmap, hzeq 0, hzeq t,
      (zLayer_commute (hzmem 0)
        (canonLift (maxProPQuotient 2 (GalK K)) k (T.proj.generators 0))).mul_pow,
      hzpow, one_mul]
    exact stageBracketSquare_commP_central_right
      (fun s ↦ (zLayer_commute (hzmem t) s).eq) _ _
  -- the two lifts differ by a central class, so their squares agree
  obtain ⟨ζ, hζmem, hζeq⟩ := exists_zLayer_mul (G := maxProPQuotient 2 (GalK K))
    (hproj_word.trans hproj_B.symm)
  have htrans := sqCoreHandleDbarWord_sq h (k + 1) (by omega)
    (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) (k + 1) (T.generators i))
    (fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) (k + 1 + 1) (w i)) hWdepth
  have hBsq : commP
      ((canonLift (maxProPQuotient 2 (GalK K)) (k + 1) (T.generators 0)) ^ 2 ^ (k - 2))
      (canonLift (maxProPQuotient 2 (GalK K)) (k + 1) (T.generators t)) ^ 2 =
      sqCoreHandleDbarWord
        (fun i ↦ canonLift (maxProPQuotient 2 (GalK K)) (k + 1) (T.generators i))
        (fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) (k + 1 + 1) (w i) ^ 2) := by
    rw [← htrans, hζeq, (zLayer_commute hζmem _).mul_pow, zLayer_sq _ hζmem, one_mul]
  -- the squared lifted correction is a neutral depth correction at level `k + 1`
  have hdepthSq : ∀ i, levelMk (maxProPQuotient 2 (GalK K)) (k + 1 + 1) (w i) ^ 2 ∈
      lambdaImage (maxProPQuotient 2 (GalK K)) k (k + 1 + 1) := by
    intro i
    refine ⟨w i ^ 2, ?_, map_pow _ _ _⟩
    have h := sq_mem_twoCentralSeries_succ (maxProPQuotient 2 (GalK K)) (hwmem i)
    rwa [show k - 1 + 1 = k by omega] at h
  have hneutral : (⟨fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) (k + 1 + 1) (w i) ^ 2,
      hdepthSq⟩ : RawDepthCorrection (maxProPQuotient 2 (GalK K)) h (k + 1)) ∈
      stageNeutralCorrections := by
    constructor
    · intro j
      refine stageBracketSquare_chiLevel_sq (chiCycKTwo (K := K)) ?_
      rw [hwmk (SqCore.sqHandleIdxU j)]
      exact hV'mem.1 j
    · intro j
      refine stageBracketSquare_chiLevel_sq (chiCycKTwo (K := K)) ?_
      rw [hwmk (SqCore.sqHandleIdxV j)]
      exact hV'mem.2 j
  have hmem := stageNeutral_word_mem_shiftSpan (T := T) (show 3 ≤ k + 1 by omega) hneutral
  rw [hBsq]
  exact hmem

/-- **The tower descent of the bracket-square residual.**  The neutral damage supply at
level `k` yields the bracket-square residual supply at level `k + 1`: the half-damage
bracket at level `k + 1` projects to the full damage bracket at level `k`, whose neutral
realization lifts and squares through the transport identity, gaining one digit of
cyclotomic precision exactly as required. -/
theorem sqStageBracketSquareNeutralSupply_of_proj_neutralDamage {h k : ℕ}
    (T : SqCyclotomicStageTuple K h (k + 1)) (hk : 3 ≤ k)
    (Hdam : SqStageNeutralDamageSupply T.proj hk) :
    SqStageBracketSquareNeutralSupply T (show 3 ≤ k + 1 by omega) := by
  intro j
  exact ⟨stageBracketSquare_component T hk _ (Hdam j).1,
    stageBracketSquare_component T hk _ (Hdam j).2⟩

/-! ## The same-stage equivalence and the collapse to the cubic stage -/

/-- The bracket-square residual supply from the neutral damage supply at the *same* stage:
the exact square collapse divides the damage by the neutral junk. -/
theorem sqStageBracketSquareNeutralSupply_of_neutralDamage {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} (hk : 3 ≤ k)
    (Hdam : SqStageNeutralDamageSupply T hk) :
    SqStageBracketSquareNeutralSupply T hk := by
  intro j
  constructor
  · have hmem := Subgroup.mul_mem _ ((Hdam j).1)
      (Subgroup.inv_mem _ (stageDamage_junk_mem_neutralShiftSpan T hk
        (canonLift (maxProPQuotient 2 (GalK K)) k
          (T.generators (SqCore.sqHandleIdxV j)))))
    rw [stageDamage_decomposition T hk] at hmem
    simpa using hmem
  · have hmem := Subgroup.mul_mem _ ((Hdam j).2)
      (Subgroup.inv_mem _ (stageDamage_junk_mem_neutralShiftSpan T hk
        (canonLift (maxProPQuotient 2 (GalK K)) k
          (T.generators (SqCore.sqHandleIdxU j)))))
    rw [stageDamage_decomposition T hk] at hmem
    simpa using hmem

/-- At a fixed stage the bracket-square residual and the neutral damage supply are
equivalent: the square collapse converts between them through the neutral junk. -/
theorem sqStageBracketSquareNeutralSupply_iff_neutralDamage {h k : ℕ}
    {T : SqCyclotomicStageTuple K h k} (hk : 3 ≤ k) :
    SqStageBracketSquareNeutralSupply T hk ↔ SqStageNeutralDamageSupply T hk :=
  ⟨sqStageNeutralDamageSupply_of_bracketSquare hk,
    sqStageBracketSquareNeutralSupply_of_neutralDamage hk⟩

/-- **The cubic neutral damage supply**: the neutral damage supply at the single stage
`k = 3`.  By the tower descent this is the exact remaining per-`K` input of the forward
presentation route: `2h` brackets `[σ̄², z̄]` realized by mod-16-neutral corrections. -/
def SqCubicNeutralDamageSupply (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] (h : ℕ) : Prop :=
  ∀ T : SqCyclotomicStageTuple K h 3, SqStageNeutralDamageSupply T (by norm_num)

/-- At handle count zero the cubic supply is a theorem: the rank-one oracle for the new
interface. -/
theorem sqCubicNeutralDamageSupply_rank_zero : SqCubicNeutralDamageSupply K 0 :=
  fun T ↦ sqStageNeutralDamageSupply_of_rank_zero T (by norm_num)

/-- **The collapse of the supply tower.**  The cubic neutral damage supply propagates to
every stage `k ≥ 3`: ascend by the descent step and the same-stage square collapse. -/
theorem sqStageNeutralDamageSupply_of_cubic {h : ℕ}
    (Hcubic : SqCubicNeutralDamageSupply K h) :
    ∀ (k : ℕ) (hk : 3 ≤ k) (T : SqCyclotomicStageTuple K h k),
      SqStageNeutralDamageSupply T hk := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact fun T ↦ Hcubic T
  | succ n hn ih =>
    intro T
    exact sqStageNeutralDamageSupply_of_bracketSquare (by omega)
      (sqStageBracketSquareNeutralSupply_of_proj_neutralDamage T hn (ih T.proj))

/-- The bracket-square residual supply at every stage from the cubic supply alone. -/
theorem sqStageBracketSquareNeutralSupply_of_cubic {h : ℕ}
    (Hcubic : SqCubicNeutralDamageSupply K h) :
    ∀ (k : ℕ) (hk : 3 ≤ k) (T : SqCyclotomicStageTuple K h k),
      SqStageBracketSquareNeutralSupply T hk :=
  fun k hk T ↦ sqStageBracketSquareNeutralSupply_of_neutralDamage hk
    (sqStageNeutralDamageSupply_of_cubic Hcubic k hk T)

/-! ## Assembly against the capstone -/

/-- **The kernel-adapted supply from a family and the cubic supply.** -/
theorem sqKernelAdaptedDefectSupply_of_family_of_cubic {h : ℕ}
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : SqCyclotomicStageTuple K h k,
      Nonempty (SqStageCoordinateDerivationFamily T))
    (Hcubic : SqCubicNeutralDamageSupply K h) :
    SqKernelAdaptedDefectSupply K h :=
  sqKernelAdaptedDefectSupply_of_family_of_neutralDamage Hfam
    (fun k hk T ↦ sqStageNeutralDamageSupply_of_cubic Hcubic k hk T)

/-- **The forward presentation theorem over the family and the cubic supply.**  For an
odd-degree field, a coordinate derivation family at every stage and the mod-16 neutral
damage supply at the cubic stage alone deliver the oriented presentation equivalence. -/
theorem nonempty_orientedEquiv_oddDegree_of_family_of_cubicNeutralDamage
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (Hfam : ∀ (k : ℕ), 3 ≤ k →
      ∀ T : SqCyclotomicStageTuple K ((Module.finrank ℚ_[2] K - 1) / 2) k,
        Nonempty (SqStageCoordinateDerivationFamily T))
    (Hcubic : SqCubicNeutralDamageSupply K ((Module.finrank ℚ_[2] K - 1) / 2)) :
    Nonempty (OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (chiCycKTwo (K := K))) :=
  nonempty_orientedEquiv_oddDegree_of_kernelAdaptedSupply hodd
    (sqKernelAdaptedDefectSupply_of_family_of_cubic Hfam Hcubic)

/-! ## The borderline digit verdict

The design memo's route (α) proposed that the σ-power head itself might be a neutral
correction.  It is not: `χ(σ̄^(2^(k-2))) = Sval^(2^(k-2))` has `v₂(Sval - 1) = 2`, hence
`v₂(Sval^(2^(k-2)) - 1) = k`, one digit short of the `2^(k+1)` neutrality threshold.  The
tautological one-coordinate realization of the damage is therefore never neutral, at any
stage; the theorems below record this as membership refutations. -/

/-- The σ-power head placed at a `U`-handle slot is not a neutral correction. -/
theorem stageFlip_headU_correction_not_neutral {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k) (j : Fin h) :
    rawDepthCoordinateCorrection (SqCore.sqHandleIdxU j)
        ⟨(canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 2),
          stageFlip_move_depth T hk⟩ ∉
      stageNeutralCorrections (K := K) (h := h) (k := k) := by
  intro hmem
  have h1 := hmem.1 j
  rw [rawDepthCoordinateCorrection_apply, if_pos rfl] at h1
  exact stageFlip_move_digit_ne_one T hk h1

/-- The σ-power head placed at a `V`-handle slot is not a neutral correction. -/
theorem stageFlip_headV_correction_not_neutral {h k : ℕ}
    (T : SqCyclotomicStageTuple K h k) (hk : 3 ≤ k) (j : Fin h) :
    rawDepthCoordinateCorrection (SqCore.sqHandleIdxV j)
        ⟨(canonLift (maxProPQuotient 2 (GalK K)) k (T.generators 0)) ^ 2 ^ (k - 2),
          stageFlip_move_depth T hk⟩ ∉
      stageNeutralCorrections (K := K) (h := h) (k := k) := by
  intro hmem
  have h1 := hmem.2 j
  rw [rawDepthCoordinateCorrection_apply, if_pos rfl] at h1
  exact stageFlip_move_digit_ne_one T hk h1

#print axioms SqCyclotomicStageTuple.proj
#print axioms sqStageBracketSquareNeutralSupply_of_proj_neutralDamage
#print axioms sqStageBracketSquareNeutralSupply_of_neutralDamage
#print axioms sqStageBracketSquareNeutralSupply_iff_neutralDamage
#print axioms sqCubicNeutralDamageSupply_rank_zero
#print axioms sqStageNeutralDamageSupply_of_cubic
#print axioms sqStageBracketSquareNeutralSupply_of_cubic
#print axioms sqKernelAdaptedDefectSupply_of_family_of_cubic
#print axioms nonempty_orientedEquiv_oddDegree_of_family_of_cubicNeutralDamage
#print axioms stageFlip_headU_correction_not_neutral
#print axioms stageFlip_headV_correction_not_neutral

end

end GQ2.Dyadic.LSquare
