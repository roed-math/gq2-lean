/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.MarkedReconstruction
import GQ2.Dyadic.ScalarMarkedFiniteLifts

/-!
# Reconstruction preserving tame and elementary scalar markings

Any finite quotient can be refined so that a prescribed elementary-abelian
core decoration descends to it.  The fixed-frame theorem then supplies
relative quotient lifts, and relative reconstruction retains both markings.
The prescribed full pro-two core map is not asserted to be fixed.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2

variable {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
  {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
  {E : Type} [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

/-- The tame coordinate together with a finite elementary scalar marking. -/
def sourceTameScalarBoundary (S : SourceDataRN n q P hP nuP SN)
    (psi : ContinuousMonoidHom P E) : ContinuousMonoidHom S.Γ (Tq q × E) :=
  S.tame.prod (psi.comp S.pro2)

/-- Relative lifts at every quotient, after refining by the scalar kernel. -/
theorem exists_tameScalarCompatible_quotientSurj_of_sourcesRN
    (S₁ S₂ : SourceDataRN n q P hP nuP SN)
    (hq0 : q ≠ 0) (hqe : Even q) (hnuP : Function.Surjective nuP)
    (htame₂ : Function.Surjective S₂.tame)
    (hwild₂ : IsProP 2 S₂.tame.toMonoidHom.ker)
    (psi : ContinuousMonoidHom P E) (hexp : ∀ e : E, e ^ 2 = 1)
    (U : OpenNormalSubgroup S₂.Γ) :
    ∃ f : ContSurj S₁.Γ (S₂.Γ ⧸ U.toSubgroup),
      f.OverQuotient (sourceTameScalarBoundary S₁ psi) (sourceTameScalarBoundary S₂ psi) U := by
  let scalar := psi.comp S₂.pro2
  let K : OpenNormalSubgroup S₂.Γ :=
    { toSubgroup := scalar.toMonoidHom.ker
      isOpen' := isOpen_discrete {1} |>.preimage scalar.continuous_toFun }
  let V : OpenNormalSubgroup S₂.Γ := U ⊓ K
  let f₂ : ContSurj S₂.Γ (S₂.Γ ⧸ V.toSubgroup) :=
    ⟨⟨QuotientGroup.mk' V.toSubgroup, QuotientGroup.continuous_mk⟩,
      QuotientGroup.mk_surjective⟩
  let theta : (S₂.Γ ⧸ V.toSubgroup) →* E :=
    QuotientGroup.lift V.toSubgroup scalar.toMonoidHom (show V.toSubgroup ≤
      scalar.toMonoidHom.ker from inf_le_right)
  have htheta : ∀ y : S₂.Γ, theta (f₂.1 y) = psi (S₂.pro2 y) := fun _ => rfl
  obtain ⟨f₁, hf₁⟩ := exists_tameScalarCompatible_finiteSurj_of_sourcesRN
    S₁ S₂ hq0 hqe hnuP htame₂ hwild₂ psi hexp f₂ theta htheta
  refine ⟨f₁.project (show V ≤ U from inf_le_left), fun x => ?_⟩
  obtain ⟨y, hfy, hty, hsy⟩ := hf₁ x
  refine ⟨y, ?_, Prod.ext hty hsy⟩
  exact congrArg (projMap (show V.toSubgroup ≤ U.toSubgroup from inf_le_left)) hfy

/-- One equivalence preserves the exact tame map and the prescribed elementary
scalar marking simultaneously. -/
theorem nonempty_tameScalarMarkedEquiv_of_sourcesRN
    (S₁ S₂ : SourceDataRN n q P hP nuP SN)
    (hq0 : q ≠ 0) (hqe : Even q) (hnuP : Function.Surjective nuP)
    (htame₁ : Function.Surjective S₁.tame) (hwild₁ : IsProP 2 S₁.tame.toMonoidHom.ker)
    (htame₂ : Function.Surjective S₂.tame) (hwild₂ : IsProP 2 S₂.tame.toMonoidHom.ker)
    (psi : ContinuousMonoidHom P E) (hexp : ∀ e : E, e ^ 2 = 1) :
    Nonempty (MarkedContinuousMulEquiv
      (sourceTameScalarBoundary S₁ psi) (sourceTameScalarBoundary S₂ psi)) := by
  apply nonempty_markedEquiv_of_quotient_lifts _ _ S₁.tfg S₂.tfg
  · exact exists_tameScalarCompatible_quotientSurj_of_sourcesRN
      S₁ S₂ hq0 hqe hnuP htame₂ hwild₂ psi hexp
  · exact exists_tameScalarCompatible_quotientSurj_of_sourcesRN
      S₂ S₁ hq0 hqe hnuP htame₁ hwild₁ psi hexp

/-- The reconstructed equivalence also preserves the full two-adic unramified character. -/
theorem exists_tameScalarNuCompatible_equiv_of_sourcesRN
    (S₁ S₂ : SourceDataRN n q P hP nuP SN)
    (hq0 : q ≠ 0) (hqe : Even q) (hnuP : Function.Surjective nuP)
    (htame₁ : Function.Surjective S₁.tame) (hwild₁ : IsProP 2 S₁.tame.toMonoidHom.ker)
    (htame₂ : Function.Surjective S₂.tame) (hwild₂ : IsProP 2 S₂.tame.toMonoidHom.ker)
    (psi : ContinuousMonoidHom P E) (hexp : ∀ e : E, e ^ 2 = 1) :
    ∃ e : ContinuousMulEquiv S₁.Γ S₂.Γ,
      (∀ x, S₂.tame (e x) = S₁.tame x) ∧
      (∀ x, psi (S₂.pro2 (e x)) = psi (S₁.pro2 x)) ∧
      (∀ x, nuP (S₂.pro2 (e x)) = nuP (S₁.pro2 x)) := by
  obtain ⟨e⟩ := nonempty_tameScalarMarkedEquiv_of_sourcesRN S₁ S₂ hq0 hqe hnuP
    htame₁ hwild₁ htame₂ hwild₂ psi hexp
  have ht : ∀ x, S₂.tame (e.equiv x) = S₁.tame x :=
    fun x => congrArg Prod.fst (e.boundary_eq x)
  refine ⟨e.equiv, ht, (fun x => congrArg Prod.snd (e.boundary_eq x)), fun x => ?_⟩
  rw [← S₂.compat, ht, S₁.compat]

#print axioms exists_tameScalarCompatible_quotientSurj_of_sourcesRN
#print axioms nonempty_tameScalarMarkedEquiv_of_sourcesRN
#print axioms exists_tameScalarNuCompatible_equiv_of_sourcesRN

end
end GQ2.Dyadic
