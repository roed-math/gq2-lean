/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateResidueLift
import GQ2.Dyadic.NpcJet.Handles

/-!
# The general-q residue lift: inertia producer and commutator no-go

`RamifiedCertificateResidueLift` extends the commutator proof at `q = 2` and identifies its
general-`q` boundary: the standard tame commutator maps to `tau ^ q * tau⁻¹`, not to `tau`.
This module isolates the field-theoretic statement that closes `CompatibleResidueLiftAt` at
every `q`.

An element is *absolutely residue-trivial* here when it satisfies `IsResidueTrivial ⊥`.  Since
the trivial subgroup fixes every integral element of `AlgebraicClosure Q2`, this says exactly
that the element acts trivially on the absolute residue field.  Such a tame-`tau` lift works
simultaneously for every finite quotient `rho`: residue-triviality is monotone from `⊥` to the
anchored kernel.  More naturally, it is enough to know that the kernel of
`nuTq q ∘ tame` is absolutely residue-trivial; surjectivity then selects a lift of `tqTau`,
whose `nuTq`-value is one.

The last section shows why neither finite action nor ramification repairs the commutator method.
At `q = 4` there is an explicit surjection `Tq 4 → C3` sending `tqTau` to the order-three
generator.  This generator acts nontrivially on the existing irreducible `F2²` module
`NpcJet.PinV`, while every commutator maps to one.  Thus:

* `gcd(q - 1, order(c(tau))) = 1` is false in a genuine finite ramified action;
* the detected-commutator premise from the preceding module is not a general-`q` producer;
* the remaining input is exactly the field-side tame-inertia/residue-action bridge, not a
  finite-group or representation-theoretic consequence.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2

/-- Residue-triviality becomes weaker when the subgroup of fixed elements becomes larger. -/
theorem isResidueTrivial_mono_subgroup {N M : Subgroup AbsGalQ2}
    {g : Kummer.GaloisGroup ℚ_[2]} (hNM : N ≤ M)
    (hg : IsResidueTrivial N g) : IsResidueTrivial M g := by
  intro x hx hnorm
  exact hg x (fun m hm ↦ hx m (hNM hm)) hnorm

/-- The smallest quotient-independent residue input: one absolutely residue-trivial lift of
the tame inertia generator. -/
def TameTauAbsoluteResidueLiftAt (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) : Prop :=
  ∃ g₀ : ↑U, tame g₀ = tqTau P.qK ∧
    IsResidueTrivial (⊥ : Subgroup AbsGalQ2) (subtypeAnc U g₀)

/-- The natural field-side statement: the kernel of the unramified tame character acts
trivially on the absolute residue field. -/
def TameInertiaAbsoluteResidueTrivialAt (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) : Prop :=
  ∀ g : ↑U, nuTq P.qK (tame g) = 1 →
    IsResidueTrivial (⊥ : Subgroup AbsGalQ2) (subtypeAnc U g)

/-- One absolute tame-`tau` lift supplies the residue lift at every compatible finite quotient.
The module and ramification hypotheses of `CompatibleResidueLiftAt` are not needed. -/
theorem compatibleResidueLiftAt_of_absolute_tameTau_lift
    (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK))
    (hLift : TameTauAbsoluteResidueLiftAt P U tame) :
    CompatibleResidueLiftAt P U tame := by
  intro D _ _ _ _ V _ _ c rho hfac _hram
  obtain ⟨g₀, hg₀, hrt⟩ := hLift
  refine ⟨g₀, by rw [hfac, hg₀], ?_⟩
  exact isResidueTrivial_mono_subgroup (bot_le :
    (⊥ : Subgroup AbsGalQ2) ≤ ancSubgroup (kerAnc (subtypeAnc U) rho)) hrt

/-- Surjectivity and residue-triviality of tame inertia produce the absolute tame-`tau` lift. -/
theorem tameTauAbsoluteResidueLiftAt_of_inertia
    (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) (htame : Function.Surjective tame)
    (hI : TameInertiaAbsoluteResidueTrivialAt P U tame) :
    TameTauAbsoluteResidueLiftAt P U tame := by
  obtain ⟨g₀, hg₀⟩ := htame (tqTau P.qK)
  refine ⟨g₀, hg₀, hI g₀ ?_⟩
  rw [hg₀, nuTq_tqTau]

/-- The general-`q` producer for `CompatibleResidueLiftAt`.  Its sole arithmetic premise is
the standard field fact that tame inertia acts trivially on the absolute residue field. -/
theorem compatibleResidueLiftAt_of_inertia
    (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) (htame : Function.Surjective tame)
    (hI : TameInertiaAbsoluteResidueTrivialAt P U tame) :
    CompatibleResidueLiftAt P U tame :=
  compatibleResidueLiftAt_of_absolute_tameTau_lift P U tame
    (tameTauAbsoluteResidueLiftAt_of_inertia P U tame htame hI)

namespace ResidueLiftCounterexample

open NpcJet

local instance : CommGroup PinC :=
  inferInstanceAs (CommGroup (Multiplicative (ZMod 3)))

private theorem pin_relation_four : conjP pinG (1 : PinC) = pinG ^ 4 := by decide

/-- The ramified cyclic quotient of `Tq 4`: `sigma` maps to one and `tau` to the generator of
`C3`. -/
noncomputable def tqFourPin : ContinuousMonoidHom (Tq 4) PinC :=
  tqClassify 4 (ProfiniteGrp.of PinC) pin_relation_four

@[simp] theorem tqFourPin_tqTau : tqFourPin (tqTau 4) = pinG :=
  tqClassify_tqTau 4 (ProfiniteGrp.of PinC) pin_relation_four

theorem tqFourPin_tqTau_order : orderOf (tqFourPin (tqTau 4)) = 3 := by
  rw [tqFourPin_tqTau]
  have hdvd : orderOf pinG ∣ 3 := orderOf_dvd_of_pow_eq_one (pinPow3 pinG)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) (by decide)
  · exact h

theorem tqFourPin_surjective : Function.Surjective tqFourPin := by
  intro x
  refine ⟨tqTau 4 ^ (Multiplicative.toAdd x).val, ?_⟩
  rw [map_pow, tqFourPin_tqTau]
  change (Multiplicative.ofAdd (1 : ZMod 3)) ^ (Multiplicative.toAdd x).val = x
  revert x
  decide

/-- The tempting coprimality premise fails: both `q - 1` and the tame inertia order are three. -/
theorem tqFourPin_qPred_not_coprime :
    ¬ Nat.Coprime (4 - 1) (orderOf (tqFourPin (tqTau 4))) := by
  rw [tqFourPin_tqTau_order]
  decide

/-- Equivalently, the standard commutator image `c(tau)^q c(tau)⁻¹` is not `c(tau)`. -/
theorem tqFourPin_tqTau_pow_ne_sq :
    tqFourPin (tqTau 4) ^ 4 ≠ tqFourPin (tqTau 4) ^ 2 := by
  rw [tqFourPin_tqTau]
  decide

/-- This cyclic quotient is genuinely ramified on the existing irreducible `F2²` module. -/
theorem tqFourPin_ramified : ∃ v : PinV, tqFourPin (tqTau 4) • v ≠ v := by
  refine ⟨((1, 0) : PinV), ?_⟩
  rw [tqFourPin_tqTau]
  decide

/-- The concrete `C3`-action used by the ramified counterexample is faithful. -/
theorem pinAct_faithful :
    ∀ h : PinC, (∀ v : PinV, h • v = v) → h = 1 := by
  decide

theorem tqFourPin_commutator (x y : Tq 4) :
    tqFourPin (x⁻¹ * y * x * y⁻¹) = 1 := by
  simp only [map_mul, map_inv]
  calc
    (tqFourPin x)⁻¹ * tqFourPin y * tqFourPin x * (tqFourPin y)⁻¹
        = (tqFourPin x)⁻¹ * (tqFourPin y * tqFourPin x) * (tqFourPin y)⁻¹ := by group
    _ = (tqFourPin x)⁻¹ * (tqFourPin x * tqFourPin y) * (tqFourPin y)⁻¹ := by
      rw [mul_comm (tqFourPin y) (tqFourPin x)]
    _ = 1 := by group

/-- No source commutator can be the required lift after applying the genuine ramified quotient
`tqFourPin`.  This holds for every subgroup source and every tame map into `Tq 4`. -/
theorem no_tqFourPin_detected_commutator {U : Subgroup AbsGalQ2}
    (tame : ContinuousMonoidHom ↑U (Tq 4)) :
    ¬ ∃ s t : ↑U,
      tqFourPin (tame (s⁻¹ * t * s * t⁻¹)) = tqFourPin (tqTau 4) := by
  rintro ⟨s, t, h⟩
  have hleft : tqFourPin (tame (s⁻¹ * t * s * t⁻¹)) = 1 := by
    simpa only [map_mul, map_inv] using tqFourPin_commutator (tame s) (tame t)
  rw [hleft, tqFourPin_tqTau] at h
  exact (by decide : pinG ≠ 1) h.symm

end ResidueLiftCounterexample

#print axioms isResidueTrivial_mono_subgroup
#print axioms TameTauAbsoluteResidueLiftAt
#print axioms TameInertiaAbsoluteResidueTrivialAt
#print axioms compatibleResidueLiftAt_of_absolute_tameTau_lift
#print axioms tameTauAbsoluteResidueLiftAt_of_inertia
#print axioms compatibleResidueLiftAt_of_inertia
#print axioms ResidueLiftCounterexample.tqFourPin
#print axioms ResidueLiftCounterexample.tqFourPin_surjective
#print axioms ResidueLiftCounterexample.tqFourPin_qPred_not_coprime
#print axioms ResidueLiftCounterexample.tqFourPin_ramified
#print axioms ResidueLiftCounterexample.pinAct_faithful
#print axioms ResidueLiftCounterexample.no_tqFourPin_detected_commutator

end
end GQ2.Dyadic
