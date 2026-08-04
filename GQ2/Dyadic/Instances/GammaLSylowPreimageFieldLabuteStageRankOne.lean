/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStage
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldCoreRankOne
import GQ2.Roe.Labute.StageLemma.StageTwo

/-!
# Rank-one regression for the variable-rank Labute stage

The already-proved oriented classification of `G_Q2(2)` transports the literal improved
square marking to every lower two-central quotient.  In particular, the general campaign's
level-three base premise is a theorem when `h = 0`; the `Q_2` case is not an additional input
to the variable-rank induction.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe.Labute

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Functoriality of the lower two-central tower under equivalence -/

/-- A continuous group equivalence induces an equivalence at every lower two-central
quotient. -/
noncomputable def levelQuotCongr {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (e : ContinuousMulEquiv G H) (k : ℕ) : levelQuot G k ≃* levelQuot H k :=
  QuotientGroup.congr (twoCentralSeries G k) (twoCentralSeries H k) e.toMulEquiv
    (map_twoCentralSeries_eq e.toMonoidHom e.continuous_toFun e.surjective k)

/-- The induced quotient equivalence carries the class of `g` to the class of `e g`. -/
@[simp] theorem levelQuotCongr_levelMk {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (e : ContinuousMulEquiv G H) (k : ℕ) (g : G) :
    levelQuotCongr e k (levelMk G k g) = levelMk H k (e g) := rfl

/-- Quotient transport commutes with the transition maps in the lower two-central tower. -/
theorem levelQuotCongr_levelProj {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (e : ContinuousMulEquiv G H) (k : ℕ) (q : levelQuot G (k + 1)) :
    levelQuotCongr e k (levelProj G k q) =
      levelProj H k (levelQuotCongr e (k + 1) q) := by
  obtain ⟨g, rfl⟩ := levelMk_surjective G (k + 1) q
  rw [levelProj_levelMk, levelQuotCongr_levelMk,
    levelQuotCongr_levelMk, levelProj_levelMk]

/-- Quotient transport identifies every two-index filtration image. -/
theorem levelQuotCongr_map_lambdaImage {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (e : ContinuousMulEquiv G H) (j k : ℕ) :
    (lambdaImage G j k).map (levelQuotCongr e k).toMonoidHom =
      lambdaImage H j k := by
  rw [lambdaImage, lambdaImage, Subgroup.map_map]
  have hcomp : (levelQuotCongr e k).toMonoidHom.comp (levelMk G k) =
      (levelMk H k).comp e.toMonoidHom := by
    ext g
    exact levelQuotCongr_levelMk e k g
  rw [hcomp, ← Subgroup.map_map,
    map_twoCentralSeries_eq e.toMonoidHom e.continuous_toFun e.surjective j]

/-- The literal improved square relator is natural under lower-tower transport. -/
theorem levelQuotCongr_sqRelWord {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (e : ContinuousMulEquiv G H) (h k : ℕ)
    (T : Fin (SqCore.sqRank h) → levelQuot G k) :
    levelQuotCongr e k (SqCore.sqRelWord T) =
      SqCore.sqRelWord (fun i ↦ levelQuotCongr e k (T i)) :=
  SqCore.map_sqRelWord (levelQuotCongr e k) T

/-- Ordinary finite character shadows are natural under an oriented equivalence. -/
theorem chiLevel_levelQuotCongr {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (e : ContinuousMulEquiv G H)
    (chiG : ContinuousMonoidHom G ℤ_[2]ˣ) (chiH : ContinuousMonoidHom H ℤ_[2]ˣ)
    (horient : ∀ g, chiH (e g) = chiG g) (k : ℕ) (q : levelQuot G k) :
    chiLevel chiH k (levelQuotCongr e k q) = chiLevel chiG k q := by
  obtain ⟨g, rfl⟩ := levelMk_surjective G k q
  rw [levelQuotCongr_levelMk, chiLevel_levelMk, chiLevel_levelMk, horient]

/-- The one-extra-digit character shadows are natural under an oriented equivalence. -/
theorem sharpChiLevel_levelQuotCongr {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (e : ContinuousMulEquiv G H)
    (chiG : ContinuousMonoidHom G ℤ_[2]ˣ) (chiH : ContinuousMonoidHom H ℤ_[2]ˣ)
    (horient : ∀ g, chiH (e g) = chiG g) (k : ℕ) (hk : 2 ≤ k)
    (q : levelQuot G k) :
    SqCyclotomicStageTuple.sharpChiLevel chiH k hk (levelQuotCongr e k q) =
      SqCyclotomicStageTuple.sharpChiLevel chiG k hk q := by
  obtain ⟨g, rfl⟩ := levelMk_surjective G k q
  rw [levelQuotCongr_levelMk, SqCyclotomicStageTuple.sharpChiLevel_levelMk,
    SqCyclotomicStageTuple.sharpChiLevel_levelMk, horient]

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The presentation-side character used by the Labute stage calculation is the canonical
Galois-side character transported to `D₀`.  The two constructions are kept separate in their
home files to preserve the census-free Labute lane; at the rank-one bridge they agree because
they have the same values on the three topological generators. -/
theorem chiD0pres_eq_chiD0G : chiD0pres = chiD0G := by
  apply GQ2.d0Hom_ext
  · rw [chiD0pres_d0A, chiD0G_values.1]
  · rw [chiD0pres_d0S, chiD0G_values.2.1]
  · rw [chiD0pres_d0Y, chiD0G_values.2.2]
    rfl

/-- The direct continuous equivalence from the presentation group `D₀` to the maximal
pro-`2` quotient of the bottom-field Galois group. -/
noncomputable def d0EquivBotMaxProTwo :
    ContinuousMulEquiv (D0 : Type)
      (maxProPQuotient 2 (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) :=
  orientBundle.equiv.symm.trans
    (maxProPQuotientCongr (p := 2) botGalContinuousMulEquiv).symm

/-- The direct bottom-field equivalence preserves the presentation-side cyclotomic
orientation. -/
theorem d0EquivBotMaxProTwo_orientation (d : D0) :
    chiCycKTwo (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂))
        (d0EquivBotMaxProTwo d) = chiD0pres d := by
  let eBot := maxProPQuotientCongr (p := 2) botGalContinuousMulEquiv
  have hcompat := dyadicChiTwo_maxProPQuotientCongr_bot
    (eBot.symm (orientBundle.equiv.symm d))
  rw [eBot.apply_symm_apply] at hcompat
  calc
    chiCycKTwo (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂))
        (d0EquivBotMaxProTwo d) =
        dyadicChiTwoContinuous (orientBundle.equiv.symm d) := hcompat.symm
    _ = chiD0G d := rfl
    _ = chiD0pres d := (DFunLike.congr_fun chiD0pres_eq_chiD0G d).symm

/-- Every lower two-central level of the bottom field has an exact oriented square marking,
obtained from the proved oriented `Q_2` equivalence. -/
theorem sqCyclotomicStageTuple_bot_nonempty (k : ℕ) :
    Nonempty (SqCyclotomicStageTuple
      (⊥ : IntermediateField ℚ_[2] ℚ̄₂) 0 k) := by
  obtain ⟨e⟩ := orientedSqZeroEquivGalKBot
  exact ⟨SqCyclotomicStageTuple.ofOrientedEquiv e⟩

/-- Regression theorem at the exact base level consumed by the general stage induction. -/
theorem sqCyclotomicStageTuple_bot_three_nonempty :
    Nonempty (SqCyclotomicStageTuple
      (⊥ : IntermediateField ℚ_[2] ℚ̄₂) 0 3) :=
  sqCyclotomicStageTuple_bot_nonempty 3

/-- Strongest noncircular correction regression currently available at `Q_2`: at every
level, the exact oriented stage transported from the already-proved global classification has
its actual defect reachable by an admissible correction. -/
theorem sqCyclotomicStageTuple_bot_defectReachable (k : ℕ) :
    ∃ T : SqCyclotomicStageTuple
        (⊥ : IntermediateField ℚ_[2] ℚ̄₂) 0 k,
      T.DefectReachable := by
  obtain ⟨e⟩ := orientedSqZeroEquivGalKBot
  exact ⟨SqCyclotomicStageTuple.ofOrientedEquiv e,
    SqCyclotomicStageTuple.ofOrientedEquiv_defectReachable e⟩

/-- The preceding correction regression at the base level used by stage induction. -/
theorem sqCyclotomicStageTuple_bot_three_defectReachable :
    ∃ T : SqCyclotomicStageTuple
        (⊥ : IntermediateField ℚ_[2] ℚ̄₂) 0 3,
      T.DefectReachable :=
  sqCyclotomicStageTuple_bot_defectReachable 3

/-! ## Exact comparison with the rank-three stage calculation -/

/-- `stageSL1R2` is exactly raw actual-defect reachability for the literal improved square
word at `h = 0`.  Thus the rank-three crossed-derivation/span calculation itself aligns with
the new presentation; what it does not provide is the separate exact-fibre strictification
required by `AdmissibleCorrection`. -/
theorem stageSL1R2_sqRawDefectReachable (k : ℕ) (hk : 3 ≤ k)
    {T : Fin 3 → levelQuot (D0 : Type) k} (hT : T ∈ sPR2 k) :
    SqCyclotomicStageTuple.sqRawDefectReachable (D0 : Type) 0 k T := by
  obtain ⟨w, hw, hshift⟩ := stageSL1R2 k hk hT
  refine ⟨w, hw, ?_⟩
  calc
    SqCyclotomicStageTuple.stageShift (h := 0) (k := k)
        (fun i : Fin 3 ↦ canonLift (D0 : Type) k (T i)) w =
        dbarWordR2 (canonLift (D0 : Type) k (T 0))
          (canonLift (D0 : Type) k (T 1))
          (canonLift (D0 : Type) k (T 2)) w := by
      exact SqCyclotomicStageTuple.stageShift_zero_eq_dbarWordR2
        k hk _ w hw
    _ = (defectR2 k T)⁻¹ := hshift
    _ = (sqStageDefect (D0 : Type) 0 k T)⁻¹ := by
      rw [sqStageDefect, SqCore.sqRelWord_zero, SqCore.sqWord_eq_drWord]
      rfl

/-- The existing rank-three `SL1` and `SL2` calculations compose to a single correction
of the original canonical lift.  That correction has the depth required by the general
stage interface, kills the literal improved-word defect, and leaves a tuple satisfying the
full next-level finite-precision presentation conditions. -/
theorem stageSL12R2_truncatedCorrection (k : ℕ) (hk : 3 ≤ k)
    {T : Fin 3 → levelQuot (D0 : Type) k} (hT : T ∈ sPR2 k) :
    ∃ correction : Fin 3 → levelQuot (D0 : Type) (k + 1),
      (∀ i, correction i ∈ lambdaImage (D0 : Type) (k - 1) (k + 1)) ∧
      SqCyclotomicStageTuple.stageShift (h := 0)
          (fun i : Fin 3 ↦ canonLift (D0 : Type) k (T i)) correction =
        (sqStageDefect (D0 : Type) 0 k T)⁻¹ ∧
      SqCyclotomicStageTuple.stageModified (G := (D0 : Type)) (h := 0) (k := k)
          (fun i : Fin 3 ↦ canonLift (D0 : Type) k (T i)) correction ∈ sPR2 (k + 1) := by
  obtain ⟨w, hw, hd⟩ := stageSL1R2 k hk hT
  let T₁ : Fin 3 → levelQuot (D0 : Type) k :=
    fun i ↦ T i * GQ2.Roe.Labute.levelProj (D0 : Type) k (w i)
  have hT₁ : T₁ ∈ sPR2 k := by
    exact sPR2_mul_mem k hk hT fun i ↦ levelProj_mem_lambdaImage (D0 : Type) (hw i)
  have hδ₁ : defectR2 k T₁ = 1 := by
    dsimp only [T₁]
    rw [defectR2_mul k hk hw, hd, mul_inv_cancel]
  obtain ⟨w', hw', _hker, hnext⟩ := stageSL2R2 k hk hT₁ hδ₁
  let base : Fin 3 → levelQuot (D0 : Type) (k + 1) :=
    fun i ↦ canonLift (D0 : Type) k (T i)
  let next : Fin 3 → levelQuot (D0 : Type) (k + 1) :=
    fun i ↦ canonLift (D0 : Type) k (T₁ i) * w' i
  let correction : Fin 3 → levelQuot (D0 : Type) (k + 1) :=
    fun i ↦ (base i)⁻¹ * next i
  have hmodified : SqCyclotomicStageTuple.stageModified
      (G := (D0 : Type)) (h := 0) (k := k) base correction = next := by
    funext i
    dsimp only [SqCyclotomicStageTuple.stageModified, correction]
    group
  have hdepth : ∀ i, correction i ∈
      lambdaImage (D0 : Type) (k - 1) (k + 1) := by
    intro i
    apply SqCyclotomicStageTuple.mem_lambdaImage_succ_of_levelProj_mem (by omega)
    have hwproj : GQ2.Roe.Labute.levelProj (D0 : Type) k (w i) ∈
        lambdaImage (D0 : Type) (k - 1) k :=
      levelProj_mem_lambdaImage (D0 : Type) (hw i)
    have hw'proj : GQ2.Roe.Labute.levelProj (D0 : Type) k (w' i) ∈
        lambdaImage (D0 : Type) (k - 1) k :=
      levelProj_mem_lambdaImage (D0 : Type) (hw' i)
    have hprod := Subgroup.mul_mem _ hwproj hw'proj
    simpa only [correction, base, next, map_mul, map_inv, levelProj_canonLift,
      T₁, mul_assoc, inv_mul_cancel_left] using hprod
  refine ⟨correction, hdepth, ?_, ?_⟩
  · have hnextrel : SqCore.sqRelWord (h := 0) next = 1 := by
      rw [SqCore.sqRelWord_zero, SqCore.sqWord_eq_drWord]
      exact hnext.1.1
    rw [SqCyclotomicStageTuple.stageShift, hmodified, hnextrel, mul_one]
    rfl
  · rw [hmodified]
    exact hnext

/-- One additional look-ahead stage supplies the fresh character digit without changing the
already-killed word shift.  Concretely, a level-`k+2` `S^P` tuple is projected back to
`Q_(k+1)`; its ordinary mod-`2^(k+2)` rows become the sharp rows of that projection.  Both
the first corrected tuple and the projected look-ahead tuple satisfy the relation in
`Q_(k+1)`, so their shifts from the original canonical lift agree. -/
theorem stageSL12R2_sharpCorrection (k : ℕ) (hk : 3 ≤ k)
    {T : Fin 3 → levelQuot (D0 : Type) k} (hT : T ∈ sPR2 k) :
    ∃ correction : Fin 3 → levelQuot (D0 : Type) (k + 1),
      (∀ i, correction i ∈ lambdaImage (D0 : Type) (k - 1) (k + 1)) ∧
      SqCyclotomicStageTuple.stageShift (h := 0)
          (fun i : Fin 3 ↦ canonLift (D0 : Type) k (T i)) correction =
        (sqStageDefect (D0 : Type) 0 k T)⁻¹ ∧
      ∀ i, SqCyclotomicStageTuple.sharpChiLevel chiD0pres (k + 1) (by omega)
          (SqCyclotomicStageTuple.stageModified
            (G := (D0 : Type)) (h := 0) (k := k)
            (fun i : Fin 3 ↦ canonLift (D0 : Type) k (T i)) correction i) =
        chiTargetR2 (k + 2) i := by
  obtain ⟨c, hcdepth, _hckill, hT₁⟩ := stageSL12R2_truncatedCorrection k hk hT
  let base : Fin 3 → levelQuot (D0 : Type) (k + 1) :=
    fun i ↦ canonLift (D0 : Type) k (T i)
  let T₁ : Fin 3 → levelQuot (D0 : Type) (k + 1) :=
    SqCyclotomicStageTuple.stageModified
      (G := (D0 : Type)) (h := 0) (k := k) base c
  have hT₁' : T₁ ∈ sPR2 (k + 1) := by
    simpa only [SqCore.sqRank_zero, T₁, base] using hT₁
  obtain ⟨c', hc'depth, _hc'kill, hT₂⟩ :=
    stageSL12R2_truncatedCorrection (k + 1) (by omega) hT₁'
  let deep : Fin 3 → levelQuot (D0 : Type) (k + 2) :=
    SqCyclotomicStageTuple.stageModified
      (G := (D0 : Type)) (h := 0) (k := k + 1)
      (fun i ↦ canonLift (D0 : Type) (k + 1) (T₁ i)) c'
  have hdeep : deep ∈ sPR2 (k + 2) := by
    simpa only [SqCore.sqRank_zero, Nat.add_assoc, deep] using hT₂
  let next : Fin 3 → levelQuot (D0 : Type) (k + 1) :=
    fun i ↦ GQ2.Roe.Labute.levelProj (D0 : Type) (k + 1) (deep i)
  let correction : Fin 3 → levelQuot (D0 : Type) (k + 1) :=
    fun i ↦ (base i)⁻¹ * next i
  have hmodified : SqCyclotomicStageTuple.stageModified
      (G := (D0 : Type)) (h := 0) (k := k) base correction = next := by
    funext i
    dsimp only [SqCyclotomicStageTuple.stageModified, correction]
    group
  have hdepth : ∀ i, correction i ∈
      lambdaImage (D0 : Type) (k - 1) (k + 1) := by
    intro i
    have hc'proj0 := levelProj_mem_lambdaImage (D0 : Type) (hc'depth i)
    have hc'proj : GQ2.Roe.Labute.levelProj (D0 : Type) (k + 1) (c' i) ∈
        lambdaImage (D0 : Type) k (k + 1) := by
      simpa only [Nat.add_sub_cancel] using hc'proj0
    have hc'pred : GQ2.Roe.Labute.levelProj (D0 : Type) (k + 1) (c' i) ∈
        lambdaImage (D0 : Type) (k - 1) (k + 1) :=
      lambdaImage_le_of_le (by omega) hc'proj
    have hprod := Subgroup.mul_mem _ (hcdepth i) hc'pred
    have hcorr : correction i =
        c i * GQ2.Roe.Labute.levelProj (D0 : Type) (k + 1) (c' i) := by
      dsimp only [correction, next, deep, SqCyclotomicStageTuple.stageModified]
      rw [map_mul, levelProj_canonLift]
      dsimp only [T₁, SqCyclotomicStageTuple.stageModified]
      group
    rwa [hcorr]
  have hnext : next ∈ sPR2 (k + 1) := by
    simpa only [next] using sPR2_levelProj hdeep
  refine ⟨correction, hdepth, ?_, ?_⟩
  · have hnextrel : SqCore.sqRelWord (h := 0) next = 1 := by
      rw [SqCore.sqRelWord_zero, SqCore.sqWord_eq_drWord]
      exact hnext.1.1
    rw [SqCyclotomicStageTuple.stageShift, hmodified, hnextrel, mul_one]
    rfl
  · intro i
    rw [congrFun hmodified i]
    exact (SqCyclotomicStageTuple.sharpChiLevel_levelProj_eq_chiLevel_succ
      chiD0pres (k + 1) (by omega) (deep i)).trans (hdeep.2 i)

/-! ## Transport of the sharp correction to the bottom field -/

/-- Every rank-one bottom-field stage tuple has a sharp depth correction realizing the
inverse of its actual literal improved-word defect.  The corrected `D₀` tuple is transported
across the lower-tower equivalence and then rebased against the bottom field's own
`canonLift`; no naturality assertion about the chosen `canonLift` is needed. -/
set_option maxHeartbeats 800000 in
theorem sqCyclotomicStageTuple_bot_sharpDefectReachable
    (k : ℕ) (hk : 3 ≤ k)
    (T : SqCyclotomicStageTuple
      (⊥ : IntermediateField ℚ_[2] ℚ̄₂) 0 k) :
    ∃ W : T.SharpAdmissibleCorrection (by omega),
      SqCyclotomicStageTuple.stageShift (h := 0) (k := k)
          (fun i ↦ canonLift
            (maxProPQuotient 2 (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) k
            (T.generators i)) W.correction =
        (sqStageDefect
          (maxProPQuotient 2 (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂)))
          0 k T.generators)⁻¹ := by
  let F := maxProPQuotient 2
    (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂))
  let e : ContinuousMulEquiv (D0 : Type) F := d0EquivBotMaxProTwo
  let E : levelQuot (D0 : Type) k ≃* levelQuot F k := levelQuotCongr e k
  let pull : Fin 3 → levelQuot (D0 : Type) k :=
    fun i ↦ E.symm (T.generators i)
  have hpullRelSq : SqCore.sqRelWord (h := 0) pull = 1 := by
    apply E.injective
    rw [map_one]
    calc
      E (SqCore.sqRelWord (h := 0) pull) =
          SqCore.sqRelWord (h := 0) (fun i ↦ E (pull i)) :=
        SqCore.map_sqRelWord (h := 0) E pull
      _ = SqCore.sqRelWord (h := 0) T.generators := by
        congr 1
        funext i
        exact E.apply_symm_apply (T.generators i)
      _ = 1 := T.relation
  have hpullRel : drWord (pull 0) (pull 1) (pull 2) = 1 := by
    rw [SqCore.sqRelWord_zero, SqCore.sqWord_eq_drWord] at hpullRelSq
    exact hpullRelSq
  have hpullGen : Subgroup.closure (Set.range pull) = ⊤ := by
    have hinj : Function.Injective (Subgroup.map E.toMonoidHom) :=
      Subgroup.map_injective E.injective
    apply hinj
    have himg : E '' Set.range pull = Set.range T.generators := by
      rw [← Set.range_comp]
      congr 1
      funext i
      exact E.apply_symm_apply (T.generators i)
    change (Subgroup.closure (Set.range pull)).map E.toMonoidHom =
      (⊤ : Subgroup (levelQuot (D0 : Type) k)).map E.toMonoidHom
    rw [MonoidHom.map_closure, himg, T.topGen,
      Subgroup.map_top_of_surjective _ E.surjective]
  have hTchi : ∀ i, chiLevel
      (chiCycKTwo (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) k
      (T.generators i) = chiTargetR2 k i := by
    have h0 : chiLevel
        (chiCycKTwo (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) k
        (T.generators 0) = chiTargetR2 k 0 := by
      obtain ⟨x, hxchi, hx⟩ := T.sigma
      rw [hx, chiLevel_levelMk, hxchi]
      rfl
    have h1 : chiLevel
        (chiCycKTwo (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) k
        (T.generators 1) = chiTargetR2 k 1 := by
      obtain ⟨x, hxchi, hx⟩ := T.x0
      rw [hx, chiLevel_levelMk, hxchi]
      rfl
    have h2 : chiLevel
        (chiCycKTwo (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) k
        (T.generators 2) = chiTargetR2 k 2 := by
      obtain ⟨x, hxchi, hx⟩ := T.x1
      rw [hx, chiLevel_levelMk, hxchi]
      rfl
    intro i
    fin_cases i <;> assumption
  have hpullChi : ∀ i, chiLevel chiD0pres k (pull i) = chiTargetR2 k i := by
    intro i
    have htransport := chiLevel_levelQuotCongr e chiD0pres
      (chiCycKTwo (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂)))
      d0EquivBotMaxProTwo_orientation k (pull i)
    rw [show levelQuotCongr e k (pull i) = T.generators i by
      exact E.apply_symm_apply (T.generators i)] at htransport
    exact htransport.symm.trans (hTchi i)
  have hpull : pull ∈ sPR2 k := ⟨⟨hpullRel, hpullGen⟩, hpullChi⟩
  obtain ⟨cD, hdepthD, hkillD, hsharpD⟩ :=
    stageSL12R2_sharpCorrection k hk hpull
  let baseD : Fin 3 → levelQuot (D0 : Type) (k + 1) :=
    fun i ↦ canonLift (D0 : Type) k (pull i)
  let nextD : Fin 3 → levelQuot (D0 : Type) (k + 1) :=
    SqCyclotomicStageTuple.stageModified
      (G := (D0 : Type)) (h := 0) (k := k) baseD cD
  let E1 : levelQuot (D0 : Type) (k + 1) ≃* levelQuot F (k + 1) :=
    levelQuotCongr e (k + 1)
  let nextF : Fin 3 → levelQuot F (k + 1) := fun i ↦ E1 (nextD i)
  let baseF : Fin 3 → levelQuot F (k + 1) :=
    fun i ↦ canonLift F k (T.generators i)
  let correctionF : Fin 3 → levelQuot F (k + 1) :=
    fun i ↦ (baseF i)⁻¹ * nextF i
  have hmodifiedF : SqCyclotomicStageTuple.stageModified
      (G := F) (h := 0) (k := k) baseF correctionF = nextF := by
    funext i
    dsimp only [SqCyclotomicStageTuple.stageModified, correctionF]
    group
  have hnextDrel : SqCore.sqRelWord (h := 0) nextD = 1 := by
    have h := hkillD
    change (SqCore.sqRelWord baseD)⁻¹ * SqCore.sqRelWord nextD =
      (SqCore.sqRelWord baseD)⁻¹ at h
    calc
      SqCore.sqRelWord nextD = SqCore.sqRelWord baseD *
          ((SqCore.sqRelWord baseD)⁻¹ * SqCore.sqRelWord nextD) := by group
      _ = SqCore.sqRelWord baseD * (SqCore.sqRelWord baseD)⁻¹ := by rw [h]
      _ = 1 := by group
  have hnextFrel : SqCore.sqRelWord (h := 0) nextF = 1 := by
    rw [← levelQuotCongr_sqRelWord e 0 (k + 1) nextD, hnextDrel, map_one]
  have hdepthF : ∀ i, correctionF i ∈ lambdaImage F (k - 1) (k + 1) := by
    intro i
    apply SqCyclotomicStageTuple.mem_lambdaImage_succ_of_levelProj_mem (by omega)
    have hprojD := levelProj_mem_lambdaImage (D0 : Type) (hdepthD i)
    have hmapped : E (levelProj (D0 : Type) k (cD i)) ∈
        lambdaImage F (k - 1) k := by
      rw [← levelQuotCongr_map_lambdaImage e (k - 1) k]
      exact ⟨levelProj (D0 : Type) k (cD i), hprojD, rfl⟩
    simpa only [correctionF, baseF, nextF, nextD,
      SqCyclotomicStageTuple.stageModified, map_mul, map_inv,
      levelProj_canonLift, ← levelQuotCongr_levelProj,
      pull, E.apply_symm_apply, mul_assoc, inv_mul_cancel_left] using hmapped
  have hsharpF : ∀ i, SqCyclotomicStageTuple.sharpChiLevel
      (chiCycKTwo (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) (k + 1) (by omega)
      (nextF i) = chiTargetR2 (k + 2) i := by
    intro i
    exact (sharpChiLevel_levelQuotCongr e chiD0pres
      (chiCycKTwo (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂)))
      d0EquivBotMaxProTwo_orientation (k + 1) (by omega) (nextD i)).trans (hsharpD i)
  let W : T.SharpAdmissibleCorrection (by omega) := {
    correction := correctionF
    depth := hdepthF
    sigma := by
      rw [congrFun hmodifiedF 0]
      simpa [chiTargetR2, chiTargetUnitsR2] using hsharpF 0
    x0 := by
      rw [congrFun hmodifiedF 1]
      simpa [chiTargetR2, chiTargetUnitsR2] using hsharpF 1
    x1 := by
      rw [congrFun hmodifiedF 2]
      simpa [chiTargetR2, chiTargetUnitsR2] using hsharpF 2
    handleU := fun j ↦ Fin.elim0 j
    handleV := fun j ↦ Fin.elim0 j }
  refine ⟨W, ?_⟩
  rw [SqCyclotomicStageTuple.stageShift, congrFun hmodifiedF, hnextFrel, mul_one]
  rfl

#print axioms sqCyclotomicStageTuple_bot_nonempty
#print axioms chiD0pres_eq_chiD0G
#print axioms sqCyclotomicStageTuple_bot_three_nonempty
#print axioms sqCyclotomicStageTuple_bot_defectReachable
#print axioms sqCyclotomicStageTuple_bot_three_defectReachable
#print axioms stageSL1R2_sqRawDefectReachable
#print axioms stageSL12R2_truncatedCorrection
#print axioms stageSL12R2_sharpCorrection
#print axioms sqCyclotomicStageTuple_bot_sharpDefectReachable

end

end GQ2.Dyadic.LSquare
