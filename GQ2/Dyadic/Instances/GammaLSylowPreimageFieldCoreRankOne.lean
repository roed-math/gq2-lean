/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldCore
import GQ2.Dyadic.SqCore.Rank3

/-!
# The oriented degree-one square classification

The general odd-degree field classification remains a genuine Labute/local-field input.  At
degree one, however, the repository already contains all required ingredients: the normalized
dyadic orientation on `G_Q2(2)`, the proved rank-three Labute theorem `bLab`, and the marked
identification `DSq 0 = DR`.  This file assembles them into the exact oriented statement used by
`OddDegreeGalKSqOrientedLabuteClassification` at the bottom intermediate field.

The only non-foundational axiom in the final theorem is the repository's pre-existing B3c
`dyadicOrientation`; no new axiom is introduced.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2
open GQ2.Roe
open GQ2.Dyadic.SqCore

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-! ## The normalized rank-three equivalence over `Q_2` -/

/-- The B3c cyclotomic character, packaged continuously on `G_Q2(2)`. -/
noncomputable def dyadicChiTwoContinuous :
    ContinuousMonoidHom (maxProPQuotient 2 AbsGalQ2) ℤ_[2]ˣ :=
  ⟨orientBundle.chiTwo, orientBundle.continuous_chiTwo⟩

/-- Pulling the canonical `D0` orientation back along any rank-three Labute equivalence gives
the concrete Roe orientation. -/
theorem chiD0G_comp_rankThreeLabuteEquiv (f : ContinuousMulEquiv (DR : Type) (D0 : Type))
    (x : (DR : Type)) : chiD0G (f x) = GQ2.Roe.chiR x := by
  have hroot : ∀ a b : ℤ_[2]ˣ,
      (↑a : ℤ_[2]) ^ 3 + 2 * (↑a : ℤ_[2]) ^ 2 + 1 = 0 →
      (↑b : ℤ_[2]) ^ 3 + 2 * (↑b : ℤ_[2]) ^ 2 + 1 = 0 → a = b := by
    intro a b ha hb
    exact Units.ext ((rootX_unique ha).trans (rootX_unique hb).symm)
  have heq : chiD0G.toMonoidHom.comp f.toMulEquiv.toMonoidHom =
      GQ2.Roe.chiR.toMonoidHom :=
    isLabuteOrientation_ext hroot
      (chiD0G.continuous_toFun.comp f.continuous_toFun) GQ2.Roe.chiR.continuous_toFun
      (isLabuteOrientation_comp_iso f) isLabuteOrientation_chiR
  exact DFunLike.congr_fun heq x

/-- The proved rank-three classification, normalized by B3c, gives an equivalence
`DSq 0 ≃ G_Q2(2)` carrying `chiSq 0` to the descended cyclotomic character. -/
theorem orientedSqZeroEquivAbsGalQ2 :
    Nonempty (OrientedContinuousMulEquiv
      (chiSq 0) dyadicChiTwoContinuous) := by
  obtain ⟨f⟩ : Nonempty (ContinuousMulEquiv (DR : Type) (D0 : Type)) :=
    GQ2.Roe.Labute.bLab isDemushkin_DR demushkinRank_DR demushkinQ_DR
      ⟨GQ2.Roe.chiR.toMonoidHom, GQ2.Roe.chiR.continuous_toFun,
        isLabuteOrientation_chiR, chiR_surjective⟩
  let e : ContinuousMulEquiv (DSq 0 : Type) (maxProPQuotient 2 AbsGalQ2) :=
    (sqEquivDRMarked.trans f).trans orientBundle.equiv.symm
  refine ⟨⟨e, ?_⟩⟩
  intro x
  calc
    dyadicChiTwoContinuous (e x) = chiD0G (f (sqEquivDRMarked x)) := rfl
    _ = GQ2.Roe.chiR (sqEquivDRMarked x) :=
      chiD0G_comp_rankThreeLabuteEquiv f _
    _ = chiSq 0 x := chiR_sqEquivDRMarked x

/-! ## Transport to the bottom intermediate field -/

/-- The topological form of `G_bot = G_Q2`. -/
noncomputable def botGalContinuousMulEquiv :
    ContinuousMulEquiv (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) AbsGalQ2 where
  toFun g := g.1
  invFun g := ⟨g, by
    change g ∈ (⊥ : IntermediateField ℚ_[2] ℚ̄₂).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    exact Subgroup.mem_top g⟩
  left_inv g := Subtype.ext rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := Continuous.subtype_mk continuous_id (fun g => by
    change g ∈ (⊥ : IntermediateField ℚ_[2] ℚ̄₂).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    exact Subgroup.mem_top g)

/-- The maximal-pro-`2` transport from `G_bot` to `G_Q2` respects the two descended
cyclotomic characters. -/
theorem dyadicChiTwo_maxProPQuotientCongr_bot
    (x : maxProPQuotient 2 (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) :
    dyadicChiTwoContinuous (maxProPQuotientCongr botGalContinuousMulEquiv x) =
      chiCycKTwo (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) x := by
  obtain ⟨g, rfl⟩ := quotientMk_surjective
    (proPKernel 2 (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) x
  change dyadicChiTwoContinuous
      (maxProPQuotientCongr (p := 2) botGalContinuousMulEquiv
        (maxProPMk 2 (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) g)) =
    chiCycKTwo (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂))
      (maxProPMk 2 (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) g)
  rw [maxProPQuotientCongr_maxProPMk]
  change orientBundle.chiTwo (maxProPMk 2 AbsGalQ2 (g : AbsGalQ2)) =
    chiCycKTwo (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂))
      (maxProPMk 2 (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) g)
  rw [orientBundle.chiTwo_factors, chiCycKTwo_maxProPMk]
  rfl

/-- The transported degree-one equivalence, stated at the simplified handle count `0`. -/
theorem orientedSqZeroEquivGalKBot :
    Nonempty (OrientedContinuousMulEquiv (chiSq 0)
      (chiCycKTwo (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂)))) := by
  obtain ⟨eAbs⟩ := orientedSqZeroEquivAbsGalQ2
  let eBot := maxProPQuotientCongr (p := 2) botGalContinuousMulEquiv
  let e : ContinuousMulEquiv (DSq 0 : Type)
      (maxProPQuotient 2 (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) :=
    eAbs.1.trans eBot.symm
  have horient : OrientationMatches (chiSq 0).toMonoidHom
      (chiCycKTwo (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂))).toMonoidHom e := by
    intro x
    have hcompat := dyadicChiTwo_maxProPQuotientCongr_bot (eBot.symm (eAbs.1 x))
    rw [eBot.apply_symm_apply] at hcompat
    exact hcompat.symm.trans (eAbs.2 x)
  exact ⟨e, horient⟩

/-- **Degree-one oriented classification.**  The bottom intermediate field has degree one, so
its square presentation is `DSq 0`; the orientation equation is the actual cyclotomic equation,
not an equality of character images. -/
theorem oddDegreeGalKSqOrientedLabuteClassification_bot :
    Nonempty (OrientedContinuousMulEquiv
      (chiSq ((Module.finrank ℚ_[2] (⊥ : IntermediateField ℚ_[2] ℚ̄₂) - 1) / 2))
      (chiCycKTwo (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂)))) := by
  have hdegree : Module.finrank ℚ_[2]
      (⊥ : IntermediateField ℚ_[2] ℚ̄₂) = 1 := IntermediateField.finrank_bot
  rw [hdegree]
  exact orientedSqZeroEquivGalKBot

/-- The exact bottom-field specialization of the general classification seam; its `q = 2`
premise is unnecessary because the normalized rank-three theorem is already available. -/
theorem oddDegreeGalKSqOrientedLabuteClassification_bot_of_qTwo
    (_hq : demushkinQ
      (maxProPQuotient 2 (GalK (⊥ : IntermediateField ℚ_[2] ℚ̄₂))) = 2) :
    Nonempty (OrientedContinuousMulEquiv
      (chiSq ((Module.finrank ℚ_[2] (⊥ : IntermediateField ℚ_[2] ℚ̄₂) - 1) / 2))
      (chiCycKTwo (K := (⊥ : IntermediateField ℚ_[2] ℚ̄₂)))) :=
  oddDegreeGalKSqOrientedLabuteClassification_bot

#print axioms chiD0G_comp_rankThreeLabuteEquiv
#print axioms orientedSqZeroEquivAbsGalQ2
#print axioms dyadicChiTwo_maxProPQuotientCongr_bot
#print axioms orientedSqZeroEquivGalKBot
#print axioms oddDegreeGalKSqOrientedLabuteClassification_bot
#print axioms oddDegreeGalKSqOrientedLabuteClassification_bot_of_qTwo

end


end GQ2.Dyadic.LSquare
