/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Recursion.Recursion
import GQ2.RStage.ObstructionBuild

/-!
# The `R`-stage obstruction module at the `K`-boundary (dyadic campaign, ticket SD-R3)

Clone of the **`b`-typed layer** of `GQ2/RStage/Obstruction.lean` (110 ln) and
`GQ2/RStage/ObstructionBuild.lean` (764 ln), re-typed at the general `K`-boundary.

## Finding: 8 of the models' 40 declarations are spine (~245 of 874 ln)

SD-R2 measured 38/874 `b`-dense lines across the pair.  The declaration-level split is even more
lopsided than that number suggests, and it is clean:

* **`b`-typed (cloned below, 8 decls)** — `stageR136_ofObstruction`; `lifts_scalarCover_of_liftB`;
  `hmB_holds`; `stageR136_ofRObstructionData`; `fibreCocycleEquiv`; `hfib_holds`;
  `liftB_fibre_nonempty_of_homLift`; `stageR136_ofRSepData`.
* **boundary-free (consumed by import)** — the *entire* obstruction-theory core: `RCoverData`,
  `RObstructionData`, `slift`, `rDefect`, the `Cohomology` section's `obsLiftFam` /
  `obCocOf_obsLiftFam` / `pairDefect_mem_Z2` / `homOb_eq_H2mk_pair` / `obsMapAdd` / `obs` /
  `obs_zero_iff_lifts` / `obs_zero_iff_pairClass_zero`, the `RCocycle` structure and its API,
  `R_le_ker_piY`, `R_le_ker_thetaY`, `piB_eq_one_of_mem_R`, `surj_of_piB_surj`, and
  `homLift_of_split`.

In particular **`obs` itself is boundary-free**: the whole `H²(Γ,R)`-obstruction construction is
untouched by the boundary and is the model's, by import.  What the boundary sees is only the
*indexing* of lifts (`BoundaryLiftsK` in place of `BoundaryLifts`).  Recorded as a budget
correction — the memo's §4.3 line "`RStage/Obstruction,ObstructionBuild` 110+764" overstates the
SD-R surface by roughly 3.5×.

## One private-helper copy

`RCocycle.twistHom_apply` (`ObstructionBuild.lean:566`) is `private` and is needed by
`fibreCocycleEquivK`.  It is `rfl`, so the copy is three lines (`twistHomK_apply` below).  This is
the only copy in this file.

## Parameterization delta versus the `ℚ₂` model

Types only: `boundarySubgroup → boundarySubgroupQ q nuP`, `BoundaryFrame → BoundaryFrameK q P H E`,
and the counts to their SD-R1 clones (`exactImageCountK`, `mBK`, `liftBK`, `stageR136_ofK`).  No
numeric parameterization reaches this file — eq. (136)'s `2` and `z_R` are degree-independent
(memo §4.1 non-movers), so every proof is verbatim.

Plain-import (memo §5).

Axioms: none beyond std-3.  Print check performed for every declaration in this file: each
prints `[propext, Classical.choice, Quot.sound]`, equal to its model's print — hence a subset.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight GQ2.SectionSeven
open ContCoh CentralObstruction

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
variable {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
variable (RF : RecursionFrame T Blk)

/-! ## The obstruction-module reduction to (136) -/

/-- **The R-stage obstruction module → (136)** at the `K`-boundary.  Clone of
`GQ2.SectionEight.stageR136_ofObstruction` (`GQ2/RStage/Obstruction.lean:69`) — verbatim, over
SD-R1's `stageR136_ofK` (`Recursion.lean:498`).  The double-dual identification is
boundary-independent. -/
theorem stageR136_ofObstructionK
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (DRmod : Type) [AddCommGroup DRmod] [Module (ZMod 2) DRmod] [Finite DRmod]
    (toDR : DRmod ≃ RF.DR) (h0 : toDR.symm RF.zeroDR = 0)
    (obs : BoundaryLiftsK b F RF.TB → Module.Dual (ZMod 2) DRmod)
    (hmB : ∀ (l : RF.DR), l ≠ RF.zeroDR →
      mBK RF b F l = Nat.card {g : BoundaryLiftsK b F RF.TB // obs g (toDR.symm l) = 0})
    (hobs : ∀ g : BoundaryLiftsK b F RF.TB,
      obs g = 0 ↔ ∃ f : BoundaryLiftsK b F T, liftBK RF b F f = g)
    (hfib : ∀ g : BoundaryLiftsK b F RF.TB, obs g = 0 →
      Nat.card {f : BoundaryLiftsK b F T // liftBK RF b F f = g} = RF.zR) :
    (Nat.card RF.DR : ℤ) * exactImageCountK b F T
      = RF.zR * ∑ᶠ l : RF.DR,
          (2 * (mBK RF b F l : ℤ) - exactImageCountK b F RF.TB) := by
  classical
  set e : RF.DR ≃ Module.Dual (ZMod 2) (Module.Dual (ZMod 2) DRmod) :=
    toDR.symm.trans (Module.evalEquiv (ZMod 2) DRmod).toEquiv with he_def
  have heval : ∀ (l : RF.DR) (φ : Module.Dual (ZMod 2) DRmod),
      e l φ = φ (toDR.symm l) := by
    intro l φ
    simp [he_def, Equiv.trans_apply, Module.evalEquiv_apply, Module.Dual.eval_apply]
  have he0 : e RF.zeroDR = 0 := by
    ext φ
    rw [heval, h0]; simp
  refine stageR136_ofK RF hfg b F (Module.Dual (ZMod 2) DRmod) obs e he0 ?_ hobs hfib
  intro l hl
  rw [hmB l hl]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by rw [heval l (obs g)])

/-! ## Step 1 — the easy `hobs` direction -/

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] in
/-- **Easy `hobs` direction** at the `K`-boundary.  Clone of
`GQ2.SectionEight.RCoverData.lifts_scalarCover_of_liftB` (`GQ2/RStage/ObstructionBuild.lean:143`)
— verbatim.  `RCoverData` and `coverMapC` are boundary-free and are the model's, by import. -/
theorem lifts_scalarCover_of_liftBK (D : RCoverData RF)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (l : RF.DR) (h : l ≠ RF.zeroDR) (fY : BoundaryLiftsK b F T) :
    ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
      ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = (liftBK RF b F fY).1.1 γ := by
  refine ⟨(D.coverMapC l h).comp fY.1.1, fun γ => ?_⟩
  show (RF.scalarCover l h).p (D.coverMap l h (fY.1.1 γ)) = RF.piB (fY.1.1 γ)
  rw [← MonoidHom.comp_apply, D.coverMap_lifts l h]

/-! ## Step 2 — `hmB`, and the reduction modulo the two classical cores -/

section Cohomology

variable [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

omit [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace Y] [DiscreteTopology Y]
  [ContinuousSMul Γ (ZMod 2)] in
/-- **`hmB`** at the `K`-boundary.  Clone of `GQ2.SectionEight.hmB_holds`
(`GQ2/RStage/ObstructionBuild.lean:417`) — verbatim; `obs` and `obs_zero_iff_lifts` are
boundary-free and are the model's, by import. -/
theorem hmB_holdsK (D : RObstructionData RF)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (l : RF.DR) (h : l ≠ RF.zeroDR) :
    mBK RF b F l = Nat.card {f : BoundaryLiftsK b F RF.TB //
      obs RF D htriv hcard f.1.1 (D.toDR.symm l) = 0} := by
  have hne : D.toDR (D.toDR.symm l) ≠ RF.zeroDR := by
    rw [Equiv.apply_symm_apply]; exact h
  rw [mBK, dif_neg h]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_).symm
  rw [obs_zero_iff_lifts RF D htriv hcard f.1.1 (D.toDR.symm l) hne]
  have hcov : RF.scalarCover (D.toDR (D.toDR.symm l)) hne = RF.scalarCover l h := by
    congr 1; exact Equiv.apply_symm_apply _ _
  rw [hcov]

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **(136) from an `RObstructionData`, modulo the two hard classical cores** at the
`K`-boundary.  Clone of `GQ2.SectionEight.stageR136_ofRObstructionData`
(`GQ2/RStage/ObstructionBuild.lean:449`) — verbatim. -/
theorem stageR136_ofRObstructionDataK (D : RObstructionData RF)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (hsep : ∀ g : BoundaryLiftsK b F RF.TB,
      obs RF D htriv hcard g.1.1 = 0 → ∃ f : BoundaryLiftsK b F T, liftBK RF b F f = g)
    (hfib : ∀ g : BoundaryLiftsK b F RF.TB, obs RF D htriv hcard g.1.1 = 0 →
      Nat.card {f : BoundaryLiftsK b F T // liftBK RF b F f = g} = RF.zR) :
    (Nat.card RF.DR : ℤ) * exactImageCountK b F T
      = RF.zR * ∑ᶠ l : RF.DR,
          (2 * (mBK RF b F l : ℤ) - exactImageCountK b F RF.TB) := by
  refine stageR136_ofObstructionK RF hfg b F D.DRmod D.toDR D.h0
    (fun g => obs RF D htriv hcard g.1.1) ?_ ?_ hfib
  · exact hmB_holdsK RF D htriv hcard b F
  · intro g
    refine ⟨hsep g, ?_⟩
    rintro ⟨f, hf⟩
    show obs RF D htriv hcard g.1.1 = 0
    refine LinearMap.ext fun d => ?_
    rw [LinearMap.zero_apply]
    by_cases h : D.toDR d = RF.zeroDR
    · have hd : d = 0 := by rw [← D.toDR.symm_apply_apply d, h, D.h0]
      rw [hd]; exact map_zero _
    · rw [obs_zero_iff_lifts RF D htriv hcard g.1.1 d h]
      obtain ⟨gc, hgc⟩ :=
        lifts_scalarCover_of_liftBK RF D.toRCoverData b F (D.toDR d) h f
      exact ⟨gc, fun γ => by rw [hgc γ, hf]⟩

end Cohomology

/-! ## Step 4 — the `R`-fibre torsor -/

section RFibre

variable (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace H]
  [DiscreteTopology H] [Finite H] [TopologicalSpace E] [DiscreteTopology E] [Finite E] in
/-- Copy of the `private` `GQ2.SectionEight.RCocycle.twistHom_apply`
(`GQ2/RStage/ObstructionBuild.lean:566`); `rfl`, and the only private-helper copy in this
file. -/
@[simp] private theorem twistHomK_apply {f₀ : ContinuousMonoidHom Γ Y}
    (c : RCocycle RF f₀) (γ : Γ) : c.twistHom γ = c.u γ * f₀ γ := rfl

/-- **The R-stage fibre torsor** at the `K`-boundary.  Clone of
`GQ2.SectionEight.fibreCocycleEquiv` (`GQ2/RStage/ObstructionBuild.lean:601`) — verbatim; the
`RCocycle` structure, `surj_of_piB_surj`, `piB_eq_one_of_mem_R`, `R_le_ker_piY` and
`R_le_ker_thetaY` are boundary-free and are the model's, by import. -/
noncomputable def fibreCocycleEquivK (hE2 : ∀ e : E, e ^ 2 = 1)
    (g : BoundaryLiftsK b F RF.TB) (f₀ : BoundaryLiftsK b F T) (hf₀ : liftBK RF b F f₀ = g) :
    RCocycle RF f₀.1.1 ≃ {f : BoundaryLiftsK b F T // liftBK RF b F f = g} where
  toFun c :=
    ⟨⟨⟨c.twistHom, by
        apply surj_of_piB_surj RF
        have hfun : (fun γ => RF.piB (c.twistHom γ)) = fun γ => g.1.1 γ := by
          funext γ
          rw [twistHomK_apply, map_mul, piB_eq_one_of_mem_R RF (c.mem γ), one_mul]
          exact congrArg (fun z : BoundaryLiftsK b F RF.TB => z.1.1 γ) hf₀
        rw [hfun]; exact g.1.2⟩,
      by
        intro γ
        have hpi : T.piY (c.twistHom γ) = T.piY (f₀.1.1 γ) := by
          rw [twistHomK_apply, map_mul, MonoidHom.mem_ker.mp (R_le_ker_piY (c.mem γ)),
            one_mul]
        have hth : T.thetaY (c.twistHom γ) = T.thetaY (f₀.1.1 γ) := by
          rw [twistHomK_apply, map_mul,
            MonoidHom.mem_ker.mp (R_le_ker_thetaY hE2 (c.mem γ)), one_mul]
        rw [hpi, hth]; exact f₀.2 γ⟩,
    by
      apply Subtype.ext; apply Subtype.ext; apply ContinuousMonoidHom.ext
      intro γ
      show RF.piB (c.twistHom γ) = g.1.1 γ
      rw [twistHomK_apply, map_mul, piB_eq_one_of_mem_R RF (c.mem γ), one_mul]
      exact congrArg (fun z : BoundaryLiftsK b F RF.TB => z.1.1 γ) hf₀⟩
  invFun f :=
    { u := fun γ => f.1.1.1 γ * (f₀.1.1 γ)⁻¹
      mem := by
        intro γ
        have hf2 : RF.piB (f.1.1.1 γ) = g.1.1 γ :=
          congrArg (fun z : BoundaryLiftsK b F RF.TB => z.1.1 γ) f.2
        have hf0' : RF.piB (f₀.1.1 γ) = g.1.1 γ :=
          congrArg (fun z : BoundaryLiftsK b F RF.TB => z.1.1 γ) hf₀
        rw [← RF.ker_piB, MonoidHom.mem_ker, map_mul, map_inv, hf2, hf0', mul_inv_cancel]
      cont := f.1.1.1.continuous_toFun.mul f₀.1.1.continuous_toFun.inv
      crossed := by
        intro γ δ
        show f.1.1.1 (γ * δ) * (f₀.1.1 (γ * δ))⁻¹
          = f.1.1.1 γ * (f₀.1.1 γ)⁻¹ *
              (f₀.1.1 γ * (f.1.1.1 δ * (f₀.1.1 δ)⁻¹) * (f₀.1.1 γ)⁻¹)
        rw [map_mul, map_mul]; group }
  left_inv c := by
    apply RCocycle.ext
    funext γ
    show c.twistHom γ * (f₀.1.1 γ)⁻¹ = c.u γ
    rw [twistHomK_apply]; group
  right_inv f := by
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; apply ContinuousMonoidHom.ext
    intro γ
    show f.1.1.1 γ * (f₀.1.1 γ)⁻¹ * f₀.1.1 γ = f.1.1.1 γ
    group

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] in
/-- **`hfib`** at the `K`-boundary.  Clone of `GQ2.SectionEight.hfib_holds`
(`GQ2/RStage/ObstructionBuild.lean:658`) — verbatim. -/
theorem hfib_holdsK (hE2 : ∀ e : E, e ^ 2 = 1)
    (g : BoundaryLiftsK b F RF.TB) (f₀ : BoundaryLiftsK b F T) (hf₀ : liftBK RF b F f₀ = g)
    (hcount : Nat.card (RCocycle RF f₀.1.1) = RF.zR) :
    Nat.card {f : BoundaryLiftsK b F T // liftBK RF b F f = g} = RF.zR := by
  rw [← Nat.card_congr (fibreCocycleEquivK RF b F hE2 g f₀ hf₀), hcount]

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] in
/-- **Frattini/framing wrapper for `hsep`** at the `K`-boundary.  Clone of
`GQ2.SectionEight.liftB_fibre_nonempty_of_homLift` (`GQ2/RStage/ObstructionBuild.lean:671`) —
verbatim. -/
theorem liftB_fibre_nonempty_of_homLiftK
    (g : BoundaryLiftsK b F RF.TB) (φ : ContinuousMonoidHom Γ Y)
    (hφ : ∀ γ, RF.piB (φ γ) = g.1.1 γ) :
    ∃ f : BoundaryLiftsK b F T, liftBK RF b F f = g := by
  refine ⟨⟨⟨φ, surj_of_piB_surj RF (by rw [funext hφ]; exact g.1.2)⟩, ?_⟩, ?_⟩
  · intro γ
    have h1 : T.piY (φ γ) = RF.TB.piY (g.1.1 γ) := by
      rw [← RF.TB_head, MonoidHom.comp_apply, hφ γ]
    have h2 : T.thetaY (φ γ) = RF.TB.thetaY (g.1.1 γ) := by
      rw [← RF.TB_theta, MonoidHom.comp_apply, hφ γ]
    rw [h1, h2]; exact g.2 γ
  · apply Subtype.ext; apply Subtype.ext; apply ContinuousMonoidHom.ext
    intro γ; exact hφ γ

/-! ## Step 5 — the assembled (136) -/

section Assemble

variable [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **(136), fully discharged modulo the two irreducible concrete inputs** (`hsep_hom` +
`hZcount`) at the `K`-boundary.  Clone of `GQ2.SectionEight.stageR136_ofRSepData`
(`GQ2/RStage/ObstructionBuild.lean:731`) — verbatim.

This is the target of the three `Block/RStage.lean` theorems moved into SD-R3 (see
`BlockRStage.lean`), and the (136) input of `RecursionInputsK.stageR136`. -/
theorem stageR136_ofRSepDataK (D : RObstructionData RF)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hsep_hom : ∀ g : BoundaryLiftsK b F RF.TB, obs RF D htriv hcard g.1.1 = 0 →
      ∃ φ : ContinuousMonoidHom Γ Y, ∀ γ, RF.piB (φ γ) = g.1.1 γ)
    (hZcount : ∀ f₀ : BoundaryLiftsK b F T, Nat.card (RCocycle RF f₀.1.1) = RF.zR) :
    (Nat.card RF.DR : ℤ) * exactImageCountK b F T
      = RF.zR * ∑ᶠ l : RF.DR,
          (2 * (mBK RF b F l : ℤ) - exactImageCountK b F RF.TB) := by
  refine stageR136_ofRObstructionDataK RF D htriv hcard hfg b F ?_ ?_
  · intro g hg
    obtain ⟨φ, hφ⟩ := hsep_hom g hg
    exact liftB_fibre_nonempty_of_homLiftK RF b F g φ hφ
  · intro g hg
    obtain ⟨φ, hφ⟩ := hsep_hom g hg
    obtain ⟨f₀, hf₀⟩ := liftB_fibre_nonempty_of_homLiftK RF b F g φ hφ
    exact hfib_holdsK RF b F hE2 g f₀ hf₀ (hZcount f₀)

end Assemble

end RFibre

end GQ2.Dyadic
