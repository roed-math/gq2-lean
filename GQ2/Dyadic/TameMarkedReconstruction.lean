/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.MarkedReconstruction
import GQ2.Dyadic.TameMarkedFiniteLifts

/-!
# Corrected source reconstruction over the chosen tame quotient

The fixed-frame finite lift theorem supplies compatible finite-level constraints. Relative
profinite reconstruction retains these constraints, so the resulting equivalence intertwines
the actual tame maps, and therefore the full two-adic unramified characters. This does not
assert that the two separately chosen identifications of the pro-two core agree pointwise.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2

variable {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
  {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}

/-- Corrected sources over the same slot have an equivalence preserving their chosen tame
quotient maps on the nose. -/
theorem nonempty_tameMarkedEquiv_of_sourcesRN
    (S₁ S₂ : SourceDataRN n q P hP nuP SN)
    (hq0 : q ≠ 0) (hqe : Even q) (hnuP : Function.Surjective nuP)
    (htame₁ : Function.Surjective S₁.tame) (hwild₁ : IsProP 2 S₁.tame.toMonoidHom.ker)
    (htame₂ : Function.Surjective S₂.tame) (hwild₂ : IsProP 2 S₂.tame.toMonoidHom.ker) :
    Nonempty (MarkedContinuousMulEquiv S₁.tame S₂.tame) := by
  apply nonempty_markedEquiv_of_quotient_lifts S₁.tame S₂.tame S₁.tfg S₂.tfg
  · intro U
    let f₂ : ContSurj S₂.Γ (S₂.Γ ⧸ U.toSubgroup) :=
      ⟨⟨QuotientGroup.mk' U.toSubgroup, QuotientGroup.continuous_mk⟩,
        QuotientGroup.mk_surjective⟩
    exact exists_tameCompatible_finiteSurj_of_sourcesRN S₁ S₂ hq0 hqe hnuP
      htame₂ hwild₂ f₂
  · intro U
    let f₁ : ContSurj S₁.Γ (S₁.Γ ⧸ U.toSubgroup) :=
      ⟨⟨QuotientGroup.mk' U.toSubgroup, QuotientGroup.continuous_mk⟩,
        QuotientGroup.mk_surjective⟩
    exact exists_tameCompatible_finiteSurj_of_sourcesRN S₂ S₁ hq0 hqe hnuP
      htame₁ hwild₁ f₁

/-- The same equivalence preserves the full `Ztwo` unramified character, not merely its
mod-two reduction. No identification of the fixed pro-two markings is assumed. -/
theorem exists_tameNuCompatible_equiv_of_sourcesRN
    (S₁ S₂ : SourceDataRN n q P hP nuP SN)
    (hq0 : q ≠ 0) (hqe : Even q) (hnuP : Function.Surjective nuP)
    (htame₁ : Function.Surjective S₁.tame) (hwild₁ : IsProP 2 S₁.tame.toMonoidHom.ker)
    (htame₂ : Function.Surjective S₂.tame) (hwild₂ : IsProP 2 S₂.tame.toMonoidHom.ker) :
    ∃ e : ContinuousMulEquiv S₁.Γ S₂.Γ,
      (∀ x, S₂.tame (e x) = S₁.tame x) ∧
      (∀ x, nuP (S₂.pro2 (e x)) = nuP (S₁.pro2 x)) := by
  obtain ⟨e⟩ := nonempty_tameMarkedEquiv_of_sourcesRN S₁ S₂ hq0 hqe hnuP
    htame₁ hwild₁ htame₂ hwild₂
  refine ⟨e.equiv, e.boundary_eq, fun x => ?_⟩
  rw [← S₂.compat, e.boundary_eq, S₁.compat]

#print axioms nonempty_tameMarkedEquiv_of_sourcesRN
#print axioms exists_tameNuCompatible_equiv_of_sourcesRN

end
end GQ2.Dyadic
