/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Recursion.RStage
import GQ2.Block.RStage

/-!
# The block frame's (136) at the `K`-boundary (dyadic campaign, ticket SD-R3)

Clone of the **three `b`-typed theorems** of `GQ2/Block/RStage.lean` (449 ln) — the ones the
board moved from SD-R1's part I into part III, because they reduce to `stageR136_ofRSepDataK`,
which is this part's `RStage.lean`.

## Finding: 3 of the model's 21 declarations are spine (~105 of 449 ln)

The model's first 310 lines build the concrete obstruction datum out of the `(R^∨)^C` character
duality — `RCharSub`, `RCharKerSub`, `RCharMulHom`, `RCharKer`, `BlockDRsub`, `RCharOfHom`,
`RCharOf`, `RChar_eq_ind`, `RCharKer_RCharOf`, `RCharKer_inj`, `blockToDR`, `RCharKer_zero`,
`blockRCoverData`, `blockRObstructionData`, `blockRChar_card`.  **Not one of them mentions the
boundary**: they are consumed here by import, `blockRObstructionData T Blk hE2` included.  The
`b`-typed surface is exactly the `StageR136` section's three theorems.

This is the same shape SD-R1 found in the other two `Block/*` files, and it is why the move into
part III cost nothing: with `stageR136_ofRSepDataK` in hand each of the three is its model's proof
term with `K`-typed names substituted.

## Parameterization delta versus the `ℚ₂` model

The frozen declarations change types only (`boundarySubgroup → boundarySubgroupQ q nuP`,
`BoundaryFrame → BoundaryFrameK q P H E`, `exactImageCount → exactImageCountK`,
`RF.mB → mBK`).  The parallel `blockStageR136CoeffK` / `blockStageR136NK` API added after the
degree audit exposes the corrected R-fibre coefficient without changing those declarations;
their proofs reuse the same block obstruction datum verbatim.

Plain-import (memo §5).

Axioms: none beyond std-3.  Print check performed for every declaration in this file: each
prints `[propext, Classical.choice, Quot.sound]`, equal to its model's print — hence a subset.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight GQ2.SectionSeven
open ContCoh

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **(136) for the concrete §7-block frame** at the `K`-boundary.  Clone of
`GQ2.blockStageR136` (`GQ2/Block/RStage.lean:341`) — verbatim, over `stageR136_ofRSepDataK`.
`blockRObstructionData` is boundary-free and is the model's, by import.

The conclusion is the `RecursionInputsK.stageR136` field (`Recursion.lean:453`) at
`RF := blockFrameImpl T Blk hE2`. -/
theorem blockStageR136K (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (hsep_hom : ∀ g : BoundaryLiftsK b F (blockFrameImpl T Blk hE2).TB,
      obs (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2) htriv hcard g.1.1 = 0 →
        ∃ φ : ContinuousMonoidHom Γ Y, ∀ γ, (blockFrameImpl T Blk hE2).piB (φ γ) = g.1.1 γ)
    (hZcount : ∀ f₀ : BoundaryLiftsK b F T,
      Nat.card (RCocycle (blockFrameImpl T Blk hE2) f₀.1.1) = (blockFrameImpl T Blk hE2).zR) :
    (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) * exactImageCountK b F T
      = (blockFrameImpl T Blk hE2).zR * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
          (2 * (mBK (blockFrameImpl T Blk hE2) b F l : ℤ)
            - exactImageCountK b F (blockFrameImpl T Blk hE2).TB) :=
  stageR136_ofRSepDataK (RF := blockFrameImpl T Blk hE2) b F
    (blockRObstructionData T Blk hE2) htriv hcard hfg hE2 hsep_hom hZcount

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **(136) for the concrete block frame with an explicit R-fibre coefficient.**  This is the
safe parameterized companion of `blockStageR136K`; the frozen theorem and `zR` definition remain
unchanged. -/
theorem blockStageR136CoeffK (z : ℕ) (T : MarkedTarget H E Y)
    (Blk : SectionSeven.MinimalBlock T.LY)
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (hsep_hom : ∀ g : BoundaryLiftsK b F (blockFrameImpl T Blk hE2).TB,
      obs (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2) htriv hcard g.1.1 = 0 →
        ∃ φ : ContinuousMonoidHom Γ Y, ∀ γ, (blockFrameImpl T Blk hE2).piB (φ γ) = g.1.1 γ)
    (hZcount : ∀ f₀ : BoundaryLiftsK b F T,
      Nat.card (RCocycle (blockFrameImpl T Blk hE2) f₀.1.1) = z) :
    (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) * exactImageCountK b F T
      = z * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
          (2 * (mBK (blockFrameImpl T Blk hE2) b F l : ℤ)
            - exactImageCountK b F (blockFrameImpl T Blk hE2).TB) :=
  stageR136_ofRSepDataCoeffK (RF := blockFrameImpl T Blk hE2) b F z
    (blockRObstructionData T Blk hE2) htriv hcard hfg hE2 hsep_hom hZcount

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **The degree-indexed block-stage identity.**  Specializes the explicit-coefficient theorem
at `zRN`, the same `SourceNumerics.tMult` value delivered by the generic R-cocycle count. -/
theorem blockStageR136NK {n : ℕ} (SN : SourceNumerics n)
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (hsep_hom : ∀ g : BoundaryLiftsK b F (blockFrameImpl T Blk hE2).TB,
      obs (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2) htriv hcard g.1.1 = 0 →
        ∃ φ : ContinuousMonoidHom Γ Y, ∀ γ, (blockFrameImpl T Blk hE2).piB (φ γ) = g.1.1 γ)
    (hZcount : ∀ f₀ : BoundaryLiftsK b F T,
      Nat.card (RCocycle (blockFrameImpl T Blk hE2) f₀.1.1)
        = zRN (blockFrameImpl T Blk hE2) SN) :
    (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) * exactImageCountK b F T
      = zRN (blockFrameImpl T Blk hE2) SN
          * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
              (2 * (mBK (blockFrameImpl T Blk hE2) b F l : ℤ)
                - exactImageCountK b F (blockFrameImpl T Blk hE2).TB) :=
  blockStageR136CoeffK (zRN (blockFrameImpl T Blk hE2) SN) T Blk hE2 htriv hcard hfg b F
    hsep_hom hZcount

/-- The degree-one block-stage theorem has exactly the frozen `blockStageR136K` conclusion. -/
theorem blockStageR136NK_standard_one
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (hsep_hom : ∀ g : BoundaryLiftsK b F (blockFrameImpl T Blk hE2).TB,
      obs (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2) htriv hcard g.1.1 = 0 →
        ∃ φ : ContinuousMonoidHom Γ Y, ∀ γ, (blockFrameImpl T Blk hE2).piB (φ γ) = g.1.1 γ)
    (hZcount : ∀ f₀ : BoundaryLiftsK b F T,
      Nat.card (RCocycle (blockFrameImpl T Blk hE2) f₀.1.1)
        = zRN (blockFrameImpl T Blk hE2) (standardNumerics 1)) :
    (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) * exactImageCountK b F T
      = (blockFrameImpl T Blk hE2).zR * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
          (2 * (mBK (blockFrameImpl T Blk hE2) b F l : ℤ)
            - exactImageCountK b F (blockFrameImpl T Blk hE2).TB) := by
  simpa only [zRN_standard_one] using
    blockStageR136NK (standardNumerics 1) T Blk hE2 htriv hcard hfg b F hsep_hom hZcount

omit [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- **The per-`Γ` residue interface: the split criterion** at the `K`-boundary.  Clone of
`GQ2.hsep_hom_of_splitCriterion` (`GQ2/Block/RStage.lean:372`) — verbatim.  Everything the proof
touches (`obs_zero_iff_pairClass_zero`, `pairDefect_mem_Z2_all`, `rDefect`, `slift`,
`homLift_of_split`) is boundary-free and is the model's, by import; only the statement's
`BoundaryLiftsK` indexing moves. -/
theorem hsep_hom_of_splitCriterionK {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (D : RObstructionData RF)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (hsplit : ∀ g : ContinuousMonoidHom Γ RF.YB,
      (∀ d : D.DRmod, H2mk Γ (ZMod 2)
          ⟨fun gd => D.pair d (Additive.ofMul (rDefect RF g gd.1 gd.2)),
            pairDefect_mem_Z2_all RF D htriv g d⟩ = 0) →
        ∃ c : Γ → ↥Blk.frattiniK, Continuous (fun γ => ((c γ : Y))) ∧
          ∀ γ δ, (c (γ * δ) : Y)
            = (c γ : Y) * (slift RF (g γ) * (c δ : Y) * (slift RF (g γ))⁻¹)
                * (rDefect RF g γ δ : Y)) :
    ∀ g : BoundaryLiftsK b F RF.TB, obs RF D htriv hcard g.1.1 = 0 →
      ∃ φ : ContinuousMonoidHom Γ Y, ∀ γ, RF.piB (φ γ) = g.1.1 γ := by
  intro g hg
  have hall : ∀ d : D.DRmod, H2mk Γ (ZMod 2)
      ⟨fun gd => D.pair d (Additive.ofMul (rDefect RF g.1.1 gd.1 gd.2)),
        pairDefect_mem_Z2_all RF D htriv g.1.1 d⟩ = 0 := by
    intro d
    by_cases h : D.toDR d = RF.zeroDR
    · have hd : d = 0 := by rw [← D.h0, ← h, Equiv.symm_apply_apply]
      subst hd
      have hz : (⟨fun gd => D.pair 0 (Additive.ofMul (rDefect RF g.1.1 gd.1 gd.2)),
          pairDefect_mem_Z2_all RF D htriv g.1.1 0⟩ : ↥(Z2 Γ (ZMod 2))) = 0 := by
        apply Subtype.ext
        funext gd
        simp only [map_zero, AddMonoidHom.zero_apply]
        rfl
      rw [hz, map_zero]
    · exact (obs_zero_iff_pairClass_zero RF D htriv hcard g.1.1 d h).mp
        (LinearMap.congr_fun hg d)
  obtain ⟨c, hc, hs⟩ := hsplit g.1.1 hall
  exact homLift_of_split RF g.1.1 c hc hs

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **(136) for the block frame, from the split criterion** at the `K`-boundary.  Clone of
`GQ2.blockStageR136_ofSplitCriterion` (`GQ2/Block/RStage.lean:415`) — verbatim.

This is the (136) leaf SD3 feeds into `RecursionInputsK.stageR136` for **each** of the two
sources; the per-source residues are `hcard`/`hfg`, the split criterion `hsplit`, and the torsor
count `hZcount`. -/
theorem blockStageR136K_ofSplitCriterion (T : MarkedTarget H E Y)
    (Blk : SectionSeven.MinimalBlock T.LY) (hE2 : ∀ e : E, e ^ 2 = 1)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (hsplit : ∀ g : ContinuousMonoidHom Γ (blockFrameImpl T Blk hE2).YB,
      (∀ d : (blockRObstructionData T Blk hE2).DRmod, H2mk Γ (ZMod 2)
          ⟨fun gd => (blockRObstructionData T Blk hE2).pair d
              (Additive.ofMul (rDefect (blockFrameImpl T Blk hE2) g gd.1 gd.2)),
            pairDefect_mem_Z2_all (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2)
              htriv g d⟩ = 0) →
        ∃ c : Γ → ↥Blk.frattiniK, Continuous (fun γ => ((c γ : Y))) ∧
          ∀ γ δ, (c (γ * δ) : Y)
            = (c γ : Y) * (slift (blockFrameImpl T Blk hE2) (g γ) * (c δ : Y)
                  * (slift (blockFrameImpl T Blk hE2) (g γ))⁻¹)
                * (rDefect (blockFrameImpl T Blk hE2) g γ δ : Y))
    (hZcount : ∀ f₀ : BoundaryLiftsK b F T,
      Nat.card (RCocycle (blockFrameImpl T Blk hE2) f₀.1.1) = (blockFrameImpl T Blk hE2).zR) :
    (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) * exactImageCountK b F T
      = (blockFrameImpl T Blk hE2).zR * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
          (2 * (mBK (blockFrameImpl T Blk hE2) b F l : ℤ)
            - exactImageCountK b F (blockFrameImpl T Blk hE2).TB) :=
  blockStageR136K T Blk hE2 htriv hcard hfg b F
    (hsep_hom_of_splitCriterionK (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2)
      htriv hcard b F hsplit) hZcount

end GQ2.Dyadic
