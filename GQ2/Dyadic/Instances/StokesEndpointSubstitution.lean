/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.LScalarTrace

/-!
# Stokes endpoints under arbitrary substitutions

The Stokes endpoint is the vanishing of the total mod-two exponent vector of the relator
family.  An arbitrary free-group substitution applies a linear map to that vector, so it
preserves its vanishing.  The same statement holds before resolution for every `PWord`
substitution and every pair of integer resolvers.

No invertibility, Nielsen condition, branch datum, or finite target is required.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2
open GQ2.Dyadic.Count

/-- On the `omega2`-only fragment, `evalZ` depends only on the resolver's value at `omega2`. -/
theorem PWord.evalZ_eq_of_isOmega2Only
    {X G : Type*} [Group G] (mu : X → G)
    {E F : Zhat → ℤ} {E₂ F₂ : ℤ_[2] → ℤ}
    (hEF : E omega2 = F omega2) (w : PWord X) (hw : w.IsOmega2Only) :
    PWord.evalZ mu E E₂ w = PWord.evalZ mu F F₂ w := by
  induction w with
  | one => rfl
  | gen g => rfl
  | mul u v ihu ihv =>
      rw [PWord.evalZ_mul, PWord.evalZ_mul, ihu hw.1, ihv hw.2]
  | inv u ih => rw [PWord.evalZ_inv, PWord.evalZ_inv, ih hw]
  | conj u g ihu ihg =>
      rw [PWord.evalZ_conj, PWord.evalZ_conj, ihu hw.1, ihg hw.2]
  | comm u v ihu ihv =>
      rw [PWord.evalZ_comm, PWord.evalZ_comm, ihu hw.1, ihv hw.2]
  | zpow u k ih => rw [PWord.evalZ_zpow, PWord.evalZ_zpow, ih hw]
  | z2pow u z ih => exact hw.elim
  | profPow u gamma ih =>
      obtain ⟨rfl, hu⟩ := hw
      rw [PWord.evalZ_profPow, PWord.evalZ_profPow, hEF, ih hu]

/-- A homomorphism to the multiplicative group of `ZMod 2` is the dot product of the exponent
vector with its values on the letters. -/
theorem toAdd_freeGroup_lift_zmod2
    {X : Type*} [Fintype X] [DecidableEq X]
    (f : X → Multiplicative (ZMod 2)) (r : FreeGroup X) :
    Multiplicative.toAdd (FreeGroup.lift f r) =
      ∑ i, Multiplicative.toAdd (heisEps i r) * Multiplicative.toAdd (f i) := by
  induction r using FreeGroup.induction_on with
  | C1 => simp [heisEps]
  | of j => simp [FreeGroup.lift_apply_of, heisEps]
  | inv_of r ih =>
      rw [map_inv, toAdd_inv, ih]
      simp only [map_inv, toAdd_inv, neg_mul, Finset.sum_neg_distrib]
  | mul r s ihr ihs =>
      rw [map_mul, toAdd_mul, ihr, ihs]
      simp only [map_mul, toAdd_mul, add_mul, Finset.sum_add_distrib]

theorem sum_toAdd_lift_eq_zero_of_endpoint
    {X rho : Type*} [Fintype X] [DecidableEq X] [Fintype rho]
    {w : rho → FreeGroup X} (hend : IsStokesEndpoint w)
    (f : X → Multiplicative (ZMod 2)) :
    ∑ k, Multiplicative.toAdd (FreeGroup.lift f (w k)) = 0 := by
  simp only [toAdd_freeGroup_lift_zmod2]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← Finset.sum_mul]
  rw [hend i, zero_mul]

/-- Arbitrary free-group substitution preserves the Stokes endpoint. -/
theorem isStokesEndpoint_freeGroup_subst
    {X Y rho : Type*} [Fintype X] [DecidableEq X]
    [DecidableEq Y] [Fintype rho]
    {w : rho → FreeGroup X} (hend : IsStokesEndpoint w)
    (phi : X → FreeGroup Y) :
    IsStokesEndpoint (fun k ↦ FreeGroup.lift phi (w k)) := by
  intro j
  let f : X → Multiplicative (ZMod 2) := fun i ↦ heisEps j (phi i)
  have H := sum_toAdd_lift_eq_zero_of_endpoint hend f
  have hcomp : (heisEps j).comp (FreeGroup.lift phi) = FreeGroup.lift f := by
    apply FreeGroup.ext_hom
    intro i
    simp [f]
  calc
    ∑ k, Multiplicative.toAdd (heisEps j (FreeGroup.lift phi (w k))) =
        ∑ k, Multiplicative.toAdd (FreeGroup.lift f (w k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact congrArg Multiplicative.toAdd
        (DFunLike.congr_fun hcomp (w k))
    _ = 0 := H

/-- Resolving after an arbitrary `PWord` substitution preserves the endpoint. -/
theorem isStokesEndpoint_heisToFree_subst
    {X Y rho : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Fintype rho]
    {W : rho → PWord X} {E : Zhat → ℤ} {E₂ : ℤ_[2] → ℤ}
    (hend : IsStokesEndpoint (fun k ↦ heisToFree E E₂ (W k)))
    (phi : X → PWord Y) :
    IsStokesEndpoint (fun k ↦ heisToFree E E₂ (PWord.subst phi (W k))) := by
  have H := isStokesEndpoint_freeGroup_subst hend
    (fun i ↦ heisToFree E E₂ (phi i))
  have heq (k : rho) :
      heisToFree E E₂ (PWord.subst phi (W k)) =
        FreeGroup.lift (fun i ↦ heisToFree E E₂ (phi i))
          (heisToFree E E₂ (W k)) := by
    rw [heisToFree, PWord.evalZ_subst]
    exact evalZ_eq_lift_heisToFree
      (fun i ↦ PWord.evalZ FreeGroup.of E E₂ (phi i)) E E₂ (W k)
  intro j
  simp only [heq]
  exact H j

#print axioms toAdd_freeGroup_lift_zmod2
#print axioms PWord.evalZ_eq_of_isOmega2Only
#print axioms sum_toAdd_lift_eq_zero_of_endpoint
#print axioms isStokesEndpoint_freeGroup_subst
#print axioms isStokesEndpoint_heisToFree_subst

end

end GQ2.Dyadic
