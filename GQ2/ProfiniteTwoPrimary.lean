/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.ProfiniteOddReflection

/-! # Detection of the two-primary part in an abelian profinite group -/

namespace GQ2

noncomputable section

variable {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The two-primary projector as a continuous homomorphism. -/
def omegaTwoProjection : ContinuousMonoidHom G G where
  toFun x := x ^ᶻ omega2
  map_one' := by
    have h := Zhat.funext_ofInt (continuous_zpowHat (1 : G))
      (continuous_const (y := (1 : G))) (fun n => by simp)
    exact congrFun h omega2
  map_mul' x y := mul_zpowHat x y omega2
  continuous_toFun := continuous_zpowHat_base omega2

/-- Every fixed point of the projector lies in its compact image. -/
theorem isProTwo_range_omegaTwoProjection :
    IsProP 2 (omegaTwoProjection (G := G)).toMonoidHom.range := by
  let S := (omegaTwoProjection (G := G)).toMonoidHom.range
  have hclosed : IsClosed (S : Set G) :=
    omegaTwoProjection.continuous_toFun.isClosedMap.isClosed_range
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hclosed.isCompact
  let incl : ContinuousMonoidHom S G := ⟨S.subtype, continuous_subtype_val⟩
  have hfixed : ∀ y : S, y ^ᶻ omega2 = y := by
    intro y
    apply Subtype.ext
    change incl (y ^ᶻ omega2) = incl y
    rw [map_zpowHat]
    obtain ⟨x, hx⟩ := y.property
    change (y.val ^ᶻ omega2) = y.val
    change x ^ᶻ omega2 = y.val at hx
    rw [← hx, zpowHat_omega2_idempotent]
  intro U y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
  let p : ContinuousMonoidHom S (S ⧸ U.toSubgroup) :=
    ⟨QuotientGroup.mk' U.toSubgroup, continuous_quotient_mk'⟩
  have hp : powOmega2 (p z) = p z := by
    rw [← map_zpowHat_omega2, hfixed]
  refine ⟨(orderOf (p z)).factorization 2, ?_⟩
  change (p z) ^ (2 ^ (orderOf (p z)).factorization 2) = 1
  have hpw := orderOf_dvd_iff_pow_eq_one.mp
    (FoxH.orderOf_powOmega2_dvd_two_pow (p z))
  simpa only [hp] using hpw

/-- An element in the two-primary image is detected by the maximal pro-two quotient.
This holds for every abelian profinite group, not just `Zhat`. -/
theorem eq_one_of_omegaTwo_fixed_of_maxProTwo_eq_one (x : G)
    (hfixed : x ^ᶻ omega2 = x) (hzero : maxProPMk 2 G x = 1) : x = 1 := by
  let S := (omegaTwoProjection (G := G)).toMonoidHom.range
  have hclosed : IsClosed (S : Set G) :=
    omegaTwoProjection.continuous_toFun.isClosedMap.isClosed_range
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hclosed.isCompact
  let p : ContinuousMonoidHom G S :=
    ⟨omegaTwoProjection.toMonoidHom.rangeRestrict,
      omegaTwoProjection.continuous_toFun.subtype_mk _⟩
  have hx : x ∈ proPKernel 2 G := (quotientMk_eq_one_iff _).mp hzero
  have hp : p x = 1 := proPKernel_le_ker isProTwo_range_omegaTwoProjection p hx
  have hv := congrArg Subtype.val hp
  change x ^ᶻ omega2 = 1 at hv
  rwa [hfixed] at hv

#print axioms isProTwo_range_omegaTwoProjection
#print axioms eq_one_of_omegaTwo_fixed_of_maxProTwo_eq_one

end
end GQ2
