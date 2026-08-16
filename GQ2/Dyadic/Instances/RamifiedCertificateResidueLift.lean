/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateCompatibleAt

/-!
# Residue-trivial lifts from commutators at an open dyadic source

`ResidueLift.exists_residueTrivial_tameLift` proves the `q = 2` statement over
`AbsGalQ2`: the tame relation makes `tau` a commutator, and every commutator of
`AbsGalQ2` is residue-trivial.  The residue-triviality argument itself works just as well for
a commutator in any open subgroup.  This module isolates that general part and records the
precise boundary at `Tq q`.

For a surjection to `Tq q`, the standard lifted commutator maps to
`tqTau q ^ q * (tqTau q)⁻¹`.  Thus it maps to `tqTau q` when `q = 2`, but at general
`q = 2 ^ f` it detects only the `(q - 1)`-power of tame inertia.  This is a genuine obstruction:
the existing finite-image theorem says that `c (tqTau q)` has odd order, not that its order is
coprime to `q - 1`.

The first theorem below therefore uses the narrow honest hypothesis needed by the commutator
method: the finite quotient `c` must detect `tqTau q` on some source commutator.  The next two
theorems lift this instancewise result to `CompatibleResidueLiftAt`.  The final theorem closes
the entire residue-lift residual for an arbitrary open-subgroup source at `q = 2`.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2

/-- If the finite quotient detects tame inertia on a source commutator, that commutator is the
required anchored residue-trivial lift.  No openness or surjectivity hypothesis is needed. -/
theorem exists_residueTrivial_tameLiftAt_of_detected_commutator
    {q : ℕ} {U : Subgroup AbsGalQ2}
    (tame : ContinuousMonoidHom ↑U (Tq q))
    {D : Type} [Group D] [TopologicalSpace D]
    (c : ContinuousMonoidHom (Tq q) D) (rho : ContinuousMonoidHom ↑U D)
    (hfac : ∀ g : ↑U, rho g = c (tame g))
    (hcomm : ∃ s t : ↑U,
      c (tame (s⁻¹ * t * s * t⁻¹)) = c (tqTau q)) :
    ∃ g₀ : ↑U, rho g₀ = c (tqTau q) ∧
      IsResidueTrivial (ancSubgroup (kerAnc (subtypeAnc U) rho)) (subtypeAnc U g₀) := by
  obtain ⟨s, t, hst⟩ := hcomm
  refine ⟨s⁻¹ * t * s * t⁻¹, (hfac _).trans hst, ?_⟩
  have hrt := ResidueLift.commutator_isResidueTrivial
    (ancSubgroup (kerAnc (subtypeAnc U) rho))
    ((subtypeAnc U s)⁻¹) (subtypeAnc U t)
  simpa only [map_mul, map_inv, inv_inv] using hrt

/-- A finite-quotient detected-commutator condition supplies the full compatible residue-lift
packet.  This reduction removes `rho`, its compatibility equation, and the ramification witness
from the remaining hypothesis. -/
theorem compatibleResidueLiftAt_of_detected_commutators
    (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK))
    (hcomm : ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
      (c : ContinuousMonoidHom (Tq P.qK) D),
      ∃ s t : ↑U, c (tame (s⁻¹ * t * s * t⁻¹)) = c (tqTau P.qK)) :
    CompatibleResidueLiftAt P U tame := by
  intro D _ _ _ _ V _ _ c rho hfac _hram
  exact exists_residueTrivial_tameLiftAt_of_detected_commutator tame c rho hfac (hcomm c)

/-- A source-level commutator lifting `tqTau` is a uniform producer of compatible residue
lifts. -/
theorem compatibleResidueLiftAt_of_tameTau_commutator
    (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK))
    (hcomm : ∃ s t : ↑U, tame (s⁻¹ * t * s * t⁻¹) = tqTau P.qK) :
    CompatibleResidueLiftAt P U tame := by
  apply compatibleResidueLiftAt_of_detected_commutators P U tame
  intro D _ _ _ _ c
  exact ⟨hcomm.choose, hcomm.choose_spec.choose,
    congrArg c hcomm.choose_spec.choose_spec⟩

/-- The commutator supplied by the general tame relation.  Its extra `(q - 1)`-power is the
exact point where the `q = 2` proof ceases to generalize formally. -/
theorem exists_tameCommutatorLift_tqTau_pow_mul_inv
    {q : ℕ} {U : Subgroup AbsGalQ2}
    (tame : ContinuousMonoidHom ↑U (Tq q)) (htame : Function.Surjective tame) :
    ∃ s t : ↑U,
      tame (s⁻¹ * t * s * t⁻¹) = tqTau q ^ q * (tqTau q)⁻¹ := by
  obtain ⟨s, hs⟩ := htame (tqSigma q)
  obtain ⟨t, ht⟩ := htame (tqTau q)
  refine ⟨s, t, ?_⟩
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hs, ht]
  have hrel : (tqSigma q)⁻¹ * tqTau q * tqSigma q = tqTau q ^ q :=
    tame_relation_q q
  calc
    (tqSigma q)⁻¹ * tqTau q * tqSigma q * (tqTau q)⁻¹
        = ((tqSigma q)⁻¹ * tqTau q * tqSigma q) * (tqTau q)⁻¹ := by group
    _ = tqTau q ^ q * (tqTau q)⁻¹ := by rw [hrel]

/-- At `q = 2`, every surjective tame quotient of an open subgroup supplies
`CompatibleResidueLiftAt`.  This is the open-subgroup generalization of
`ResidueLift.exists_residueTrivial_tameLift`. -/
theorem compatibleResidueLiftAt_of_qK_eq_two
    (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK))
    (htame : Function.Surjective tame) (hq : P.qK = 2) :
    CompatibleResidueLiftAt P U tame := by
  obtain ⟨s, t, hst⟩ := exists_tameCommutatorLift_tqTau_pow_mul_inv tame htame
  apply compatibleResidueLiftAt_of_tameTau_commutator P U tame
  refine ⟨s, t, hst.trans ?_⟩
  calc
    tqTau P.qK ^ P.qK * (tqTau P.qK)⁻¹
        = tqTau P.qK ^ 2 * (tqTau P.qK)⁻¹ := by rw [hq]
    _ = tqTau P.qK := by group

#print axioms exists_residueTrivial_tameLiftAt_of_detected_commutator
#print axioms compatibleResidueLiftAt_of_detected_commutators
#print axioms compatibleResidueLiftAt_of_tameTau_commutator
#print axioms exists_tameCommutatorLift_tqTau_pow_mul_inv
#print axioms compatibleResidueLiftAt_of_qK_eq_two

end
end GQ2.Dyadic
