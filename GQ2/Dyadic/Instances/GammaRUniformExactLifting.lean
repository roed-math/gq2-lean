/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaRUniformStokesSupply

/-!
# Corrected exact lifting for an arbitrary supplied word

No branch equation is used here. The degree is the alphabet deficiency, the resolver is
coefficient independent, and the Stokes input is tested only at markings pushed from the
candidate. This is the common lifting pipeline needed by the new tame-spliced sources.
-/

namespace GQ2.Dyadic.UniformStokesSupply
noncomputable section
open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Count
attribute [local instance] Count.heisTopologicalSpace Count.heisDiscreteTopology

variable {n q : ℕ} {R : PWord (Generator n)}
  {wOf : ℕ → Fin 2 → FreeGroup (Generator n)}

/-- The count of lifts over a recursion frame is uniform in the intrinsic word. -/
theorem liftsOver_card (S : UniformStokesSupply n q R wOf)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom ((GammaR n q R) : Type) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (rho : BoundaryLiftsK b F RF.TC) :
    Nat.card (LiftsOverK RF b F rho) = (standardNumerics n).mMult (Nat.card ↥RF.MB) := by
  letI := mbCommGroup RF
  letI := mbConjActC RF
  letI := scalarActionZmodTwo RF.YC
  exact liftsOver_cardN RF b F rho
    (isAdmissibleMarkedPresentation_gammaR n q R)
    (fun _ ↦ rfl) (isWildTwo_of_gammaGen rho.1.1 rho.1.2 (fun _ ↦ rfl))
    degree (S.resolvesWord (mb_add_self RF))
    (S.stokes RF.YC rho.1.1 (Additive ↥RF.MB) (mb_add_self RF)) (S.endpoint _)

/-- Corrected degree-n exact lifting follows from the word-independent Stokes supply. -/
theorem exactLiftingRN (S : UniformStokesSupply n q R wOf)
    (hspec : TameSpec.TameSpecializes n q R)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (GammaR n q R) n q P nuP (standardNumerics n) := by
  refine ⟨S.liftsOver_card, ?_, ?_⟩
  · intro Bg _ _ _ _ D hedge rho hrho
    exact S.lem86 D hedge rho hrho
  · intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE₂ hRK hR₂ b F
    letI := scalarActionZmodTwo ((GammaR n q R) : Type)
    haveI := scalarActionZmodTwo_continuousSMul ((GammaR n q R) : Type)
    letI : CommGroup ↑Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
    letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↑Blk.frattiniK) :=
      RStageLocal.conjC Blk hRK
    letI := scalarActionZmodTwo (Y ⧸ Blk.K)
    have hresR := S.resolvesWord (C := Y ⧸ Blk.K) (RStageLocal.frattiniK_add_self hRK hR₂)
    have hres2 := S.resolvesWord (C := Y ⧸ Blk.K)
      (by decide : ∀ a : ZMod 2, a + a = 0)
    have hpres := isAdmissibleMarkedPresentation_gammaR n q R
    exact blockStageR136NK (standardNumerics n) T Blk hE₂
      (scalarActionZmodTwo_triv _) (S.cardH2 hspec)
      (tfg_of_isAdmissibleMarkedPresentation hpres) b F
      (fun g hg ↦ by
        let qKR : (blockFrameImpl T Blk hE₂).YB →* (Y ⧸ Blk.K) :=
          QuotientGroup.map Blk.frattiniK Blk.K (MonoidHom.id Y)
            (by rw [Subgroup.comap_id]; exact SectionSeven.frattiniLike_le Blk.K)
        let rho : ContinuousMonoidHom ((GammaR n q R) : Type) (Y ⧸ Blk.K) :=
          ⟨qKR.comp g.1.1.toMonoidHom,
            (continuous_of_discreteTopology (f := qKR)).comp g.1.1.continuous_toFun⟩
        have hrho_apply (gamma : ((GammaR n q R) : Type)) :
            rho gamma = qKR (g.1.1 gamma) := rfl
        have hd : StokesDuality
            (fun i ↦ qKR (g.1.1 (gammaGen n q R i)))
            (wOf (4 * Monoid.exponent (Y ⧸ Blk.K))) (Additive ↑Blk.frattiniK) := by
          simpa only [hrho_apply] using
            (S.stokes (Y ⧸ Blk.K) rho (Additive ↑Blk.frattiniK)
              (RStageLocal.frattiniK_add_self hRK hR₂))
        exact homLift_of_obs_zero_boundaryLiftK_markingN hE₂ hRK hR₂
          (scalarActionZmodTwo_triv _) (S.cardH2 hspec) b F g hpres
          (isWildTwo_of_gammaGen g.1.1 g.1.2 (fun _ ↦ rfl)) hres2 hresR hd
          (S.endpoint _) hg)
      (fun f₀ ↦ by
        let theta : ContinuousMonoidHom ((GammaR n q R) : Type) (Y ⧸ Blk.K) :=
          ⟨(QuotientGroup.mk' Blk.K).comp f₀.1.1.toMonoidHom, by
            show Continuous fun gamma ↦ QuotientGroup.mk' Blk.K (f₀.1.1 gamma)
            exact Continuous.comp continuous_of_discreteTopology f₀.1.1.continuous_toFun⟩
        have htheta_apply (gamma : ((GammaR n q R) : Type)) :
            theta gamma = QuotientGroup.mk' Blk.K (f₀.1.1 gamma) := rfl
        have htheta_surj : Function.Surjective theta := by
          intro c
          obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective Blk.K c
          obtain ⟨gamma, hgamma⟩ := f₀.1.2 y
          exact ⟨gamma, by rw [htheta_apply, hgamma, hy]⟩
        have hd : StokesDuality
            (fun i ↦ QuotientGroup.mk' Blk.K (f₀.1.1 (gammaGen n q R i)))
            (wOf (4 * Monoid.exponent (Y ⧸ Blk.K))) (Additive ↑Blk.frattiniK) := by
          simpa only [htheta_apply] using
            (S.stokes (Y ⧸ Blk.K) theta (Additive ↑Blk.frattiniK)
              (RStageLocal.frattiniK_add_self hRK hR₂))
        exact rCocycle_card_standard_zRN hE₂ hRK hR₂ f₀.1.1 f₀.1.2 hpres
          hresR (isWildTwo_of_gammaGen theta htheta_surj (fun _ ↦ rfl))
          degree hd (S.endpoint _))

#print axioms liftsOver_card
#print axioms exactLiftingRN

end
end GQ2.Dyadic.UniformStokesSupply
