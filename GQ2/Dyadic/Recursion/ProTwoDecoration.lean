/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.SectionSeven.ProTwoKernel
import GQ2.Dyadic.Recursion.Induction


/-!
# Additional full pro-two decorations on exact-image lifts

This additive interface keeps a prescribed map to an arbitrary two-group, in parallel with
rather than in place of the original elementary abelian boundary decoration. The nonscalar
block vanishing theorem supplies compatible descents to both recursion quotients. All old
lifting and central-cover fibers then retain their entire multiplicity under the constraint.
No refined source-comparison theorem is claimed in this definition and transport layer.
-/

namespace GQ2.Dyadic

open GQ2.SectionEight

variable {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {Q : Type*} [Group Q]

/-- An additional complete pro-two decoration. The target `Q` need not be elementary
abelian; this is independent of the original `E`-decoration. -/
def RespectsProTwo (pro2 : ContinuousMonoidHom Γ P) (psi : P →* Q)
    (theta : Y →* Q) (f : ContinuousMonoidHom Γ Y) : Prop :=
  ∀ γ, theta (f γ) = psi (pro2 γ)

/-- Boundary lifts with a fixed, complete pro-two decoration. -/
def ProTwoBoundaryLiftsK (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (T : MarkedTarget H E Y)
    (pro2 : ContinuousMonoidHom Γ P) (psi : P →* Q) (theta : Y →* Q) : Type :=
  {f : BoundaryLiftsK b F T // RespectsProTwo pro2 psi theta f.1.1}

/-- The corresponding refined exact-image count. -/
noncomputable def proTwoExactImageCountK
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (T : MarkedTarget H E Y)
    (pro2 : ContinuousMonoidHom Γ P) (psi : P →* Q) (theta : Y →* Q) : ℕ :=
  Nat.card (ProTwoBoundaryLiftsK b F T pro2 psi theta)

variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}

/-- A two-group decoration descends through the complete nonscalar block. -/
noncomputable def proTwoThetaC (RF : RecursionFrame T Blk)
    (hQ : IsPGroup 2 Q) (theta : Y →* Q) : RF.YC →* Q :=
  RF.piC.liftOfSurjective RF.piC_surj ⟨theta, by
    rw [RF.ker_piC]
    exact Blk.le_ker_of_isPGroup hQ theta⟩

/-- The descended decoration pulls back to the original one. -/
@[simp] theorem proTwoThetaC_piC (RF : RecursionFrame T Blk)
    (hQ : IsPGroup 2 Q) (theta : Y →* Q) (y : Y) :
    proTwoThetaC RF hQ theta (RF.piC y) = theta y := by
  simp [proTwoThetaC]

/-- The B-stage decoration is pulled back from the C stage; its compatibility with both
quotients is therefore fixed, with no second arbitrary descent choice. -/
noncomputable def proTwoThetaB (RF : RecursionFrame T Blk)
    (hQ : IsPGroup 2 Q) (theta : Y →* Q) : RF.YB →* Q :=
  (proTwoThetaC RF hQ theta).comp RF.piBC

@[simp] theorem proTwoThetaB_piB (RF : RecursionFrame T Blk)
    (hQ : IsPGroup 2 Q) (theta : Y →* Q) (y : Y) :
    proTwoThetaB RF hQ theta (RF.piB y) = theta y := by
  change proTwoThetaC RF hQ theta ((RF.piBC.comp RF.piB) y) = theta y
  rw [RF.piBC_comp, proTwoThetaC_piC]

/-- The full-Q condition is constant on every existing B-over-C lift fiber. -/
theorem respectsProTwo_iff_of_over (RF : RecursionFrame T Blk)
    (pro2 : ContinuousMonoidHom Γ P) (psi : P →* Q)
    (thetaC : RF.YC →* Q) (f : ContinuousMonoidHom Γ RF.YB)
    (rho : ContinuousMonoidHom Γ RF.YC)
    (hover : ∀ γ, RF.piBC (f γ) = rho γ) :
    RespectsProTwo pro2 psi (thetaC.comp RF.piBC) f ↔
      RespectsProTwo pro2 psi thetaC rho := by
  simp only [RespectsProTwo, MonoidHom.comp_apply, hover]

/-- Projection to the R-stage quotient preserves the full-Q constraint. -/
theorem respectsProTwo_liftBK_iff (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (pro2 : ContinuousMonoidHom Γ P) (psi : P →* Q)
    (hQ : IsPGroup 2 Q) (theta : Y →* Q) (f : BoundaryLiftsK b F T) :
    RespectsProTwo pro2 psi (proTwoThetaB RF hQ theta) (liftBK RF b F f).1.1 ↔
      RespectsProTwo pro2 psi theta f.1.1 := by
  change (∀ γ, proTwoThetaB RF hQ theta (RF.piB (f.1.1 γ)) = psi (pro2 γ)) ↔ _
  simp only [proTwoThetaB_piB, RespectsProTwo]

/-- For any central cover, the inherited decoration is the pullback of the lower one.
Hence the full-Q condition does not remove any lifts in a fixed cover fiber. -/
theorem respectsProTwo_cover_iff (C : CentralCover Y)
    (pro2 : ContinuousMonoidHom Γ P) (psi : P →* Q) (theta : Y →* Q)
    (g : ContinuousMonoidHom Γ C.cover) (f : ContinuousMonoidHom Γ Y)
    (hover : ∀ γ, C.p (g γ) = f γ) :
    RespectsProTwo pro2 psi (theta.comp C.p) g ↔
      RespectsProTwo pro2 psi theta f := by
  simp only [RespectsProTwo, MonoidHom.comp_apply, hover]

#print axioms RespectsProTwo
#print axioms ProTwoBoundaryLiftsK
#print axioms proTwoExactImageCountK
#print axioms proTwoThetaC
#print axioms proTwoThetaC_piC
#print axioms proTwoThetaB
#print axioms proTwoThetaB_piB
#print axioms respectsProTwo_iff_of_over
#print axioms respectsProTwo_liftBK_iff
#print axioms respectsProTwo_cover_iff

end GQ2.Dyadic
