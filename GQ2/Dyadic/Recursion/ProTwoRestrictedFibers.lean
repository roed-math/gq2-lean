/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Recursion.ProTwoDecoration


/-!
# Full-pro-two-restricted lifting fibers

The M-stage multiplicity theorem is replayed over just those lower boundary lifts satisfying
an additional full pro-two decoration. Every fiber is the existing unrestricted `LiftsOverK`
fiber, so the original pointwise multiplicity is retained exactly. This establishes the
fibration half of the refined partition; the exact-image-stratum and R-stage refinements are
not asserted here.
-/

namespace GQ2.Dyadic

open GQ2.SectionEight

variable {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {Q : Type*} [Group Q]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}

/-- The original M-stage fiber multiplicity remains unchanged after fixing an arbitrary
additional quotient decoration. Only the lower exact-image base is restricted. -/
theorem mStage_proTwo_restricted_fibration_card
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (RF : RecursionFrame T Blk)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (pro2 : ContinuousMonoidHom Γ P) (psi : P →* Q) (thetaC : RF.YC →* Q)
    (mult : ℕ)
    (hmult : ∀ rho : BoundaryLiftsK b F RF.TC, Nat.card (LiftsOverK RF b F rho) = mult) :
    Nat.card {m : ContinuousMonoidHom Γ RF.YB //
      IsBoundaryLiftK b F RF.TB m ∧ Function.Surjective (⇑RF.piBC ∘ ⇑m) ∧
        RespectsProTwo pro2 psi (thetaC.comp RF.piBC) m}
      = mult * proTwoExactImageCountK b F RF.TC pro2 psi thetaC := by
  classical
  haveI : Finite (ContinuousMonoidHom Γ RF.YB) := finite_continuousMonoidHom hfg RF.YB
  haveI : Finite (BoundaryLiftsK b F RF.TC) := finite_boundaryLiftsK b F RF.TC hfg
  haveI : Finite (ProTwoBoundaryLiftsK b F RF.TC pro2 psi thetaC) := by
    unfold ProTwoBoundaryLiftsK
    infer_instance
  haveI : Fintype (ProTwoBoundaryLiftsK b F RF.TC pro2 psi thetaC) := Fintype.ofFinite _
  let Mset := {m : ContinuousMonoidHom Γ RF.YB //
    IsBoundaryLiftK b F RF.TB m ∧ Function.Surjective (⇑RF.piBC ∘ ⇑m) ∧
      RespectsProTwo pro2 psi (thetaC.comp RF.piBC) m}
  let Phi : Mset → ProTwoBoundaryLiftsK b F RF.TC pro2 psi thetaC := fun m =>
    ⟨⟨⟨⟨RF.piBC.comp m.1.toMonoidHom,
        (continuous_of_discreteTopology (f := ⇑RF.piBC)).comp m.1.continuous_toFun⟩,
      m.2.2.1⟩, fun γ => by
        change ((RF.TC.piY.comp RF.piBC) (m.1 γ),
          (RF.TC.thetaY.comp RF.piBC) (m.1 γ)) = _
        rw [RF.headBC, RF.thetaBC]
        exact m.2.1 γ⟩, m.2.2.2⟩
  have hfib : ∀ rho : ProTwoBoundaryLiftsK b F RF.TC pro2 psi thetaC,
      Nat.card {m : Mset // Phi m = rho} = Nat.card (LiftsOverK RF b F rho.1) := by
    intro rho
    refine Nat.card_congr
      { toFun := fun mm => ⟨mm.1.1,
          fun γ => congrArg (fun x : ProTwoBoundaryLiftsK b F RF.TC pro2 psi thetaC =>
            x.1.1.1 γ) mm.2⟩
        invFun := fun n => ⟨⟨n.1, isBoundaryLiftK_of_over RF b F n.1 rho.1 n.2,
          by
            rw [show (⇑RF.piBC ∘ ⇑n.1) = ⇑rho.1.1.1 from funext n.2]
            exact rho.1.1.2,
          (respectsProTwo_iff_of_over RF pro2 psi thetaC n.1 rho.1.1.1 n.2).mpr rho.2⟩,
          Subtype.ext (Subtype.ext (Subtype.ext (ContinuousMonoidHom.ext n.2)))⟩
        left_inv := fun mm => Subtype.ext (Subtype.ext rfl)
        right_inv := fun n => Subtype.ext rfl }
  change Nat.card Mset = _
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv Phi).symm, Nat.card_sigma]
  simp_rw [hfib, hmult]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    proTwoExactImageCountK, Nat.card_eq_fintype_card]
  exact mul_comm _ _

#print axioms mStage_proTwo_restricted_fibration_card

end GQ2.Dyadic
