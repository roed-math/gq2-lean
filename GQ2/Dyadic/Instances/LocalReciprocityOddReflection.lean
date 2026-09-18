/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.ProfiniteOddReflection
import GQ2.PropOneOne
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Odd-primary reflection preserves the current local reciprocity bundle

This is an interface audit, not a new reciprocity axiom.  Composing reciprocity
with the natural odd-primary reflection preserves continuity, density, all
finite norm kernels and surjectivity, the pro-two unramified coordinate, and
the actual two-adic cyclotomic orientation.  Thus these clauses alone do not
pin the sign of a nontrivial odd-primary unramified coordinate.
-/

namespace GQ2

noncomputable section

private theorem continuous_chiCycAb_reflection : Continuous chiCycAb := by
  apply (QuotientGroup.isQuotientMap_mk commClosure).continuous_iff.mpr
  exact continuous_chiCyc

private theorem continuous_restrictAb_reflection
    (L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L]
    (hab : ∀ s t : (L ≃ₐ[ℚ_[2]] L), s * t = t * s) :
    Continuous (restrictAb L hab) := by
  apply (QuotientGroup.isQuotientMap_mk commClosure).continuous_iff.mpr
  exact InfiniteGalois.restrictNormalHom_continuous L

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

local instance : IsClosed (commClosure : Set AbsGalQ2) := isClosed_closure
local instance : T2Space AbsGalQ2ab :=
  inferInstanceAs (T2Space (AbsGalQ2 ⧸ commClosure))
local instance : TotallyDisconnectedSpace AbsGalQ2ab :=
  inferInstanceAs (TotallyDisconnectedSpace (AbsGalQ2 ⧸ commClosure))

/-- The original bundle is stable under an odd-primary reflection of reciprocity. -/
def LocalReciprocity.oddReflected (R : LocalReciprocity) : LocalReciprocity where
  recip := oddReflection.toMonoidHom.comp R.recip
  continuous_recip := oddReflection.continuous_toFun.comp R.continuous_recip
  denseRange_recip := oddReflection_involutive.surjective.denseRange.comp
    R.denseRange_recip oddReflection.continuous_toFun
  nu_ur := R.nu_ur
  continuous_nu_ur := R.continuous_nu_ur
  surjective_nu_ur := R.surjective_nu_ur
  norm_reciprocity := by
    intro L _ _ hab
    letI : CommGroup (L ≃ₐ[ℚ_[2]] L) :=
      { (inferInstance : Group (L ≃ₐ[ℚ_[2]] L)) with mul_comm := hab }
    let p : ContinuousMonoidHom AbsGalQ2ab (L ≃ₐ[ℚ_[2]] L) :=
      ⟨restrictAb L hab, continuous_restrictAb_reflection L hab⟩
    obtain ⟨hsurj, hker⟩ := R.norm_reciprocity L hab
    constructor
    · intro y
      obtain ⟨x, hx⟩ := hsurj (oddReflection y)
      refine ⟨x, ?_⟩
      change p (oddReflection (R.recip x)) = y
      rw [map_oddReflection]
      change oddReflection (((restrictAb L hab).comp R.recip) x) = y
      rw [hx, oddReflection_involutive]
    · rw [← hker]
      ext x
      change p (oddReflection (R.recip x)) = 1 ↔ p (R.recip x) = 1
      rw [map_oddReflection]
      exact oddReflection_involutive.injective.eq_iff' (map_one oddReflection)
  nu_ur_recip := by
    intro x
    change R.nu_ur (oddReflection (R.recip x)) = _
    exact (map_oddReflection_eq_self_of_isProTwo
      ⟨R.nu_ur, R.continuous_nu_ur⟩ PropOneOne.isProP_two_multPadicInt _).trans
        (R.nu_ur_recip x)
  chiCyc_recip_unit := by
    intro u
    change chiCycAb (oddReflection (R.recip (unitEmbed u))) = u⁻¹
    exact (map_oddReflection_eq_self_of_isProTwo
      ⟨chiCycAb, continuous_chiCycAb_reflection⟩ isProP_two_unitsPadicInt _).trans
        (R.chiCyc_recip_unit u)
  chiCyc_recip_uniformizer := by
    change chiCycAb (oddReflection (R.recip uniformizer)) = 1
    exact (map_oddReflection_eq_self_of_isProTwo
      ⟨chiCycAb, continuous_chiCycAb_reflection⟩ isProP_two_unitsPadicInt _).trans
        R.chiCyc_recip_uniformizer

@[simp] theorem LocalReciprocity.oddReflected_recip (R : LocalReciprocity) (x : ℚ_[2]ˣ) :
    R.oddReflected.recip x = oddReflection (R.recip x) := rfl

@[simp] theorem LocalReciprocity.oddReflected_nu (R : LocalReciprocity) :
    R.oddReflected.nu_ur = R.nu_ur := rfl

/-- Every continuous pro-two character has exactly the same reciprocity values after reflection. -/
theorem LocalReciprocity.oddReflected_proTwo_values (R : LocalReciprocity)
    {P : Type} [CommGroup P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (f : ContinuousMonoidHom AbsGalQ2ab P) (hP : IsProP 2 P) (x : ℚ_[2]ˣ) :
    f (R.oddReflected.recip x) = f (R.recip x) :=
  map_oddReflection_eq_self_of_isProTwo f hP _

#print axioms LocalReciprocity.oddReflected
#print axioms LocalReciprocity.oddReflected_proTwo_values

end
end GQ2
