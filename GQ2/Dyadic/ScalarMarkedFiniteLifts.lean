/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.TameMarkedFiniteLifts

/-!
# Finite quotient lifts retaining tame and scalar markings

The frame also retains any prescribed elementary-abelian decoration of the
shared pro-two core.  This is deliberately not an assertion about a prescribed
nonabelian finite quotient of that core.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2

variable {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
  {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
  {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {E : Type} [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

/-- Fixed-frame count equality preserves a scalar marking whenever it descends
to the particular finite quotient being compared. -/
theorem exists_tameScalarCompatible_finiteSurj_of_sourcesRN
    (S₁ S₂ : SourceDataRN n q P hP nuP SN)
    (hq0 : q ≠ 0) (hqe : Even q) (hnuP : Function.Surjective nuP)
    (htame₂ : Function.Surjective S₂.tame)
    (hwild₂ : IsProP 2 S₂.tame.toMonoidHom.ker)
    (psi : ContinuousMonoidHom P E) (hexp : ∀ e : E, e ^ 2 = 1)
    (f₂ : ContSurj S₂.Γ Y) (theta : Y →* E)
    (htheta : ∀ y : S₂.Γ, theta (f₂.1 y) = psi (S₂.pro2 y)) :
    ∃ f₁ : ContSurj S₁.Γ Y, ∀ x : S₁.Γ, ∃ y : S₂.Γ,
      f₂.1 y = f₁.1 x ∧ S₂.tame y = S₁.tame x ∧ psi (S₂.pro2 y) = psi (S₁.pro2 x) := by
  let F : BoundaryFrameK q P (Y ⧸ finiteWildImage S₂ f₂) E :=
    { alpha := finiteTameHead S₂ f₂ htame₂
      alpha_surjective := finiteTameHead_surjective S₂ f₂ htame₂
      exponent_two := hexp
      psiBar := psi }
  let T : MarkedTarget (Y ⧸ finiteWildImage S₂ f₂) E Y :=
    { LY := finiteWildImage S₂ f₂
      normal := inferInstance
      isPGroup_two := finiteWildImage_isPGroup S₂ f₂ hwild₂
      piY := QuotientGroup.mk' (finiteWildImage S₂ f₂)
      piY_surjective := QuotientGroup.mk'_surjective _
      ker_piY := QuotientGroup.ker_mk' _
      thetaY := theta }
  have hne₂ : Nonempty (BoundaryLiftsK S₂.b F T) := by
    refine ⟨⟨f₂, fun x => Prod.ext ?_ (htheta x)⟩⟩
    exact (finiteTameHeadHom_tame S₂ f₂ htame₂ x).symm
  haveI : Finite (BoundaryLiftsK S₂.b F T) := finite_boundaryLiftsK S₂.b F T S₂.tfg
  have hpos₂ : 0 < exactImageCountK S₂.b F T := Nat.card_pos_iff.mpr ⟨hne₂, inferInstance⟩
  have hc := thm_4_2_of_sourcesRN S₁ S₂ F hq0 hqe hnuP T hexp
  rw [← hc] at hpos₂
  obtain ⟨f₁, hf₁⟩ := (Nat.card_pos_iff.mp hpos₂).1
  refine ⟨f₁, fun x => ?_⟩
  obtain ⟨y, hfy, hty⟩ := exists_simultaneous_representative_of_finiteTameHead
    S₁ S₂ f₂ htame₂ f₁ (fun x => congrArg Prod.fst (hf₁ x)) x
  refine ⟨y, hfy, hty, ?_⟩
  exact (htheta y).symm.trans ((congrArg theta hfy).trans (congrArg Prod.snd (hf₁ x)))

#print axioms exists_tameScalarCompatible_finiteSurj_of_sourcesRN

end
end GQ2.Dyadic
