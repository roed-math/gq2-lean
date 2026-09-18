/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.AnabelianBridge.Construction
import GQ2.TameSimple

/-!
# The odd-primary reflection of an abelian profinite group

The map `x ↦ (x ^ᶻ omega2)^2 * x⁻¹` is the identity on the pro-two part
and inversion on the odd-primary part.  It is a natural continuous involution.
This separates pro-two normalization from a full profinite normalization without
choosing coordinates on an abelian profinite group.
-/

namespace GQ2

noncomputable section

section Powering

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Profinite exponentiation is continuous in its base for every fixed exponent. -/
theorem continuous_zpowHat_base (gamma : Zhat) : Continuous (fun x : G => x ^ᶻ gamma) := by
  let Q : Type := ∀ U : OpenNormalSubgroup (ProfiniteGrp.of G), G ⧸ U.toSubgroup
  let e : G →* Q := MonoidHom.pi fun U => QuotientGroup.mk' U.toSubgroup
  have he : Continuous e := continuous_pi fun _ => continuous_quotient_mk'
  have hinj : Function.Injective e := by
    intro x y hxy
    rw [← mul_inv_eq_one]
    apply eq_one_of_forall_mem_openNormalSubgroup
    intro U
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' U.toSubgroup (x * y⁻¹) = 1
    rw [map_mul, map_inv, show QuotientGroup.mk' U.toSubgroup x =
      QuotientGroup.mk' U.toSubgroup y from congrFun hxy U, mul_inv_cancel]
  rw [(he.isClosedEmbedding hinj).isEmbedding.continuous_iff]
  apply continuous_pi
  intro U
  let p : ContinuousMonoidHom G (G ⧸ U.toSubgroup) :=
    ⟨QuotientGroup.mk' U.toSubgroup, continuous_quotient_mk'⟩
  have hcont : Continuous (fun x : G => (p x) ^ᶻ gamma) :=
    (continuous_of_discreteTopology (f := fun y : G ⧸ U.toSubgroup => y ^ᶻ gamma)).comp
      p.continuous_toFun
  exact hcont.congr fun x => (map_zpowHat p x gamma).symm

/-- The profinite two-primary projector is idempotent. -/
theorem zpowHat_omega2_idempotent (x : G) :
    (x ^ᶻ omega2) ^ᶻ omega2 = x ^ᶻ omega2 := by
  rw [← mul_inv_eq_one]
  apply eq_one_of_forall_mem_openNormalSubgroup
  intro U
  let p : ContinuousMonoidHom G (G ⧸ U.toSubgroup) :=
    ⟨QuotientGroup.mk' U.toSubgroup, continuous_quotient_mk'⟩
  apply (QuotientGroup.eq_one_iff _).mp
  change p (((x ^ᶻ omega2) ^ᶻ omega2) * (x ^ᶻ omega2)⁻¹) = 1
  rw [map_mul, map_inv, map_zpowHat_omega2, map_zpowHat_omega2]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (FoxH.orderOf_powOmega2_dvd_two_pow (p x))
  rw [powOmega2_eq_self_of_orderOf_two_pow hk, mul_inv_cancel]

end Powering

section Abelian

variable {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- In an abelian profinite group, powering in a fixed profinite exponent is a homomorphism. -/
theorem mul_zpowHat (x y : G) (gamma : Zhat) :
    (x * y) ^ᶻ gamma = (x ^ᶻ gamma) * (y ^ᶻ gamma) := by
  have h := Zhat.funext_ofInt (continuous_zpowHat (x * y))
    ((continuous_zpowHat x).mul (continuous_zpowHat y)) fun n => by
      change (x * y) ^ᶻ Zhat.ofInt n = (x ^ᶻ Zhat.ofInt n) * (y ^ᶻ Zhat.ofInt n)
      simp only [zpowHat_ofInt, mul_zpow]
  exact congrFun h gamma

/-- The identity on the two-primary component and inversion on every odd-primary component. -/
def oddReflection : ContinuousMonoidHom G G where
  toFun x := (x ^ᶻ omega2) ^ 2 * x⁻¹
  map_one' := by
    have h : (1 : G) ^ᶻ omega2 = 1 := by
      have he := Zhat.funext_ofInt (continuous_zpowHat (1 : G))
        (continuous_const (y := (1 : G)))
        (fun n => by simp only [zpowHat_ofInt, one_zpow])
      exact congrFun he omega2
    simp only [h, one_pow, inv_one, mul_one]
  map_mul' x y := by
    rw [mul_zpowHat, mul_pow, mul_inv]
    ac_rfl
  continuous_toFun := ((continuous_zpowHat_base omega2).pow 2).mul continuous_inv

@[simp] theorem oddReflection_apply (x : G) :
    oddReflection x = (x ^ᶻ omega2) ^ 2 * x⁻¹ := rfl

/-- Reflecting the odd-primary component twice does nothing. -/
theorem oddReflection_involutive : Function.Involutive (oddReflection : G → G) := by
  intro x
  simp only [oddReflection_apply, mul_zpowHat, zpowHat_inv]
  have hpow : ((x ^ᶻ omega2) ^ 2) ^ᶻ omega2 = (x ^ᶻ omega2) ^ 2 := by
    simpa only [zpow_ofNat, zpowHat_omega2_idempotent] using
      (zpowHat_zpow (x ^ᶻ omega2) omega2 (2 : ℤ)).symm
  rw [hpow]
  simp [pow_two, mul_comm, mul_left_comm, mul_assoc]

/-- The odd-primary reflection is a continuous group automorphism. -/
def oddReflectionEquiv : G ≃ₜ* G where
  toFun := oddReflection
  invFun := oddReflection
  left_inv := oddReflection_involutive
  right_inv := oddReflection_involutive
  map_mul' := oddReflection.map_mul
  continuous_toFun := oddReflection.continuous_toFun
  continuous_invFun := oddReflection.continuous_toFun

variable {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/-- Reflection is natural with respect to continuous homomorphisms. -/
theorem map_oddReflection (f : ContinuousMonoidHom G H) (x : G) :
    f (oddReflection x) = oddReflection (f x) := by
  simp only [oddReflection_apply, map_mul, map_pow, map_inv, map_zpowHat]

/-- Reflection fixes every pro-two group pointwise. -/
theorem oddReflection_eq_self_of_isProTwo (hG : IsProP 2 G) (x : G) :
    oddReflection x = x := by
  rw [oddReflection_apply, zpowHat_omega2_eq_self hG]
  group

/-- Thus a continuous pro-two-valued character cannot detect this reflection. -/
theorem map_oddReflection_eq_self_of_isProTwo
    (f : ContinuousMonoidHom G H) (hH : IsProP 2 H) (x : G) :
    f (oddReflection x) = f x := by
  rw [map_oddReflection, oddReflection_eq_self_of_isProTwo hH]

end Abelian

#print axioms continuous_zpowHat_base
#print axioms zpowHat_omega2_idempotent
#print axioms oddReflection_involutive
#print axioms oddReflectionEquiv
#print axioms map_oddReflection
#print axioms map_oddReflection_eq_self_of_isProTwo

end
end GQ2
