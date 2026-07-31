/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Recursion.Recursion
import GQ2.MStageCount

/-!
# Count transport and the degenerate head at the `K`-boundary (dyadic campaign, ticket SD-R2)

Clone of the **`b`-typed layer** of `GQ2/MStageCount.lean` (713 ln), re-typed at the general
`K`-boundary.  SD-R1 measured 38/713 `b`-typed lines here; the measurement understated how
little is spine, for the reason in the next section.

## Finding: only the first 160 lines of the model are spine at all

`GQ2/MStageCount.lean` splits cleanly in two:

* **:44-224, the generic count layer** — six `b`-typed declarations (cloned below) plus two
  boundary-free ones consumed by import: `MarkedTarget.top_head_surjective` (:94) and
  `card_stratum_mStage_lt` (:176, the (145a)-based `M`-stage stratum bound, which mentions only
  `blockFrameImpl`).
* **:226-711, `section LocalCount`** — the `G_ℚ₂` **instantiation**
  (`RecursionFrame.liftsOver_card_local` at `AbsGalQ2`, with its `MBModulePack` of five
  `private` helpers and the `H²`/`Z¹` cocycle computation).  By the SD1 memo §4.3 this is *not*
  spine: it is `*Local`-class supply data, and its `K`-analogue belongs to the memo's §3.3
  supply package (the "LG6"/"ASK" line item), **not** to the SD-R wave.  It is skipped here.

So the memo's §4.3 table entry "`MStageCount.lean` — 713 ln" overstates the SD-R surface by
roughly 4.5×: the spine part is the ~120 lines below.  Recorded as a budget correction.

## Parameterization delta versus the `ℚ₂` model

Only the types of `b` and `F` move (`boundarySubgroup → boundarySubgroupQ q nuP`,
`BoundaryFrame → BoundaryFrameK q P H E`, and the counts to their SD-R1 clones); every proof is
verbatim.  `MarkedTarget`, `MarkedTarget.stratum`, `RecursionFrame` and `CentralCover` are the
model's own, by import.

Plain-import (memo §5).

Axioms: none beyond std-3.  Print check performed for every declaration in this file: each
prints `[propext, Classical.choice, Quot.sound]`, equal to its model's print — hence a subset.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight GQ2.SectionSeven

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}

/-! ## Count transport along an iso of marked targets -/

/-- **The boundary-lift bijection along an isomorphism of marked targets** at the `K`-boundary.
Clone of `GQ2.boundaryLiftsCongr` (`GQ2/MStageCount.lean:49`) — verbatim. -/
noncomputable def boundaryLiftsCongrK {Y₁ Y₂ : Type}
    [Group Y₁] [TopologicalSpace Y₁] [DiscreteTopology Y₁] [Finite Y₁]
    [Group Y₂] [TopologicalSpace Y₂] [DiscreteTopology Y₂] [Finite Y₂]
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (T₁ : MarkedTarget H E Y₁) (T₂ : MarkedTarget H E Y₂) (e : Y₁ ≃* Y₂)
    (hhead : ∀ y : Y₁, T₂.piY (e y) = T₁.piY y)
    (htheta : ∀ y : Y₁, T₂.thetaY (e y) = T₁.thetaY y) :
    BoundaryLiftsK b F T₁ ≃ BoundaryLiftsK b F T₂ where
  toFun f :=
    ⟨⟨⟨e.toMonoidHom.comp f.1.1.toMonoidHom,
        (continuous_of_discreteTopology (f := ⇑e)).comp f.1.1.continuous_toFun⟩,
      e.surjective.comp f.1.2⟩,
    fun γ => by
      show (T₂.piY (e (f.1.1 γ)), T₂.thetaY (e (f.1.1 γ))) = F.frameMap (b γ)
      rw [hhead, htheta]
      exact f.2 γ⟩
  invFun g :=
    ⟨⟨⟨e.symm.toMonoidHom.comp g.1.1.toMonoidHom,
        (continuous_of_discreteTopology (f := ⇑e.symm)).comp g.1.1.continuous_toFun⟩,
      e.symm.surjective.comp g.1.2⟩,
    fun γ => by
      show (T₁.piY (e.symm (g.1.1 γ)), T₁.thetaY (e.symm (g.1.1 γ))) = F.frameMap (b γ)
      rw [← hhead (e.symm (g.1.1 γ)), ← htheta (e.symm (g.1.1 γ)), e.apply_symm_apply]
      exact g.2 γ⟩
  left_inv f := Subtype.ext (Subtype.ext (ContinuousMonoidHom.ext fun γ =>
    e.symm_apply_apply _))
  right_inv g := Subtype.ext (Subtype.ext (ContinuousMonoidHom.ext fun γ =>
    e.apply_symm_apply _))

/-- **Exact-image counts transport along an isomorphism of marked targets** at the
`K`-boundary.  Clone of `GQ2.exactImageCount_congr` (`GQ2/MStageCount.lean:81`). -/
theorem exactImageCountK_congr {Y₁ Y₂ : Type}
    [Group Y₁] [TopologicalSpace Y₁] [DiscreteTopology Y₁] [Finite Y₁]
    [Group Y₂] [TopologicalSpace Y₂] [DiscreteTopology Y₂] [Finite Y₂]
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (T₁ : MarkedTarget H E Y₁) (T₂ : MarkedTarget H E Y₂) (e : Y₁ ≃* Y₂)
    (hhead : ∀ y : Y₁, T₂.piY (e y) = T₁.piY y)
    (htheta : ∀ y : Y₁, T₂.thetaY (e y) = T₁.thetaY y) :
    exactImageCountK b F T₁ = exactImageCountK b F T₂ :=
  Nat.card_congr (boundaryLiftsCongrK b F T₁ T₂ e hhead htheta)

/-- **Evaluation of the totalized stratum count at `⊤`** at the `K`-boundary.  Clone of
`GQ2.SectionEight.exactImageCountOn_top` (`GQ2/MStageCount.lean:102`).
`MarkedTarget.top_head_surjective` is the model's, by import. -/
theorem exactImageCountOnK_top {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (T : MarkedTarget H E Y) :
    exactImageCountOnK b F T ⊤ = exactImageCountK b F T := by
  simp only [exactImageCountOnK]
  rw [dif_pos T.top_head_surjective]
  exact exactImageCountK_congr b F _ T Subgroup.topEquiv (fun y => rfl) (fun y => rfl)

/-- **`R = ⊥` collapses the `B`-stage** at the `K`-boundary.  Clone of
`GQ2.SectionEight.RecursionFrame.exactImageCount_TB_of_R_bot` (`GQ2/MStageCount.lean:113`). -/
theorem exactImageCountK_TB_of_R_bot {Y : Type} [Group Y]
    [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (hR : Blk.frattiniK = ⊥) :
    exactImageCountK b F RF.TB = exactImageCountK b F T := by
  have hinj : Function.Injective RF.piB := by
    rw [← MonoidHom.ker_eq_bot_iff, RF.ker_piB]
    exact hR
  exact (exactImageCountK_congr b F T RF.TB (MulEquiv.ofBijective RF.piB ⟨hinj, RF.piB_surj⟩)
    (fun y => DFunLike.congr_fun RF.TB_head y) (fun y => DFunLike.congr_fun RF.TB_theta y)).symm

/-- **The phase count is the `⊤`-stratum liftable count** at the `K`-boundary (the `hphase`
feed).  Clone of `GQ2.SectionEight.RecursionFrame.nPhase_eq_liftableCount_top`
(`GQ2/MStageCount.lean:130`). -/
theorem nPhaseK_eq_liftableCountK_top {Y : Type} [Group Y]
    [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (Cζ : CentralCover RF.YC) :
    nPhaseK RF b F Cζ = liftableCountK b F RF.TC Cζ ⊤ RF.TC.top_head_surjective :=
  (Nat.card_congr (Equiv.subtypeEquiv
    (boundaryLiftsCongrK b F (RF.TC.stratum ⊤ RF.TC.top_head_surjective) RF.TC
      Subgroup.topEquiv (fun _ => rfl) (fun _ => rfl))
    (fun _ => Iff.rfl))).symm

/-! ## The degenerate-head case -/

/-- **Degenerate head ⟹ zero count** (any source) at the `K`-boundary.  Clone of
`GQ2.exactImageCount_eq_zero_of_not_headSurj` (`GQ2/MStageCount.lean:148`) — this is how the
`M`-stage lane discharges `mStage_partitionK`'s `hhead` hypothesis, and it kills both sources
simultaneously. -/
theorem exactImageCountK_eq_zero_of_not_headSurj {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (T : MarkedTarget H E Y)
    (hns : ¬ Function.Surjective
      (fun x : ↥(boundarySubgroupQ q nuP) => (F.frameMap x).1)) :
    exactImageCountK b F T = 0 := by
  haveI : IsEmpty (BoundaryLiftsK b F T) := by
    refine ⟨fun f => hns ?_⟩
    have hsurj : Function.Surjective (fun γ : Γ => T.piY (f.1.1 γ)) :=
      T.piY_surjective.comp f.1.2
    have heq : (fun γ : Γ => T.piY (f.1.1 γ))
        = (fun x : ↥(boundarySubgroupQ q nuP) => (F.frameMap x).1) ∘ ⇑b := by
      funext γ
      exact congrArg Prod.fst (f.2 γ)
    exact (heq ▸ hsurj).of_comp
  rw [exactImageCountK]
  exact Nat.card_of_isEmpty

/-! ## The `n = 1` refl-bridges -/

section RegressionN1

variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]

/-- At `n = 1` the transport equiv **is** the model's — `rfl`. -/
theorem boundaryLiftsCongrK_eq {Y₂ : Type}
    [Group Y₂] [TopologicalSpace Y₂] [DiscreteTopology Y₂] [Finite Y₂]
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ 2 nuTwo)) (F : BoundaryFrameK 2 PiBd H E)
    (T₁ : MarkedTarget H E Y) (T₂ : MarkedTarget H E Y₂) (e : Y ≃* Y₂)
    (hhead : ∀ y : Y, T₂.piY (e y) = T₁.piY y)
    (htheta : ∀ y : Y, T₂.thetaY (e y) = T₁.thetaY y) :
    boundaryLiftsCongrK b F T₁ T₂ e hhead htheta
      = boundaryLiftsCongr b F.toBoundaryFrame T₁ T₂ e hhead htheta := rfl

end RegressionN1

end GQ2.Dyadic
