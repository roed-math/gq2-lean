/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateResidueFullInertia

/-!
# The full unramified quotient and the absolute residue action

The quotient map

`qMkQ q : Tq q → QurQ q`

has kernel exactly `inertiaPartQ q`.  It therefore transports the group-theoretic premise
`tame g ∈ inertiaPartQ q` without any extra hypothesis.  What is not present in the current
`Tq`, `MarkedRecip`, or Mathlib finite-extension inertia APIs is the field-theoretic
compatibility saying that this quotient is the absolute residue action.

This module isolates that exact seam.  `QurKernelFixesOddRootsAt` says that the kernel of
`qMkQ ∘ tame` fixes every odd-order root of unity.  It is equivalent both to the corrected
full-inertia predicate `TameFullInertiaAbsoluteResidueTrivialAt` and to the more structural
statement `OddRootActionFactorsThroughQurAt`: the action of the open subgroup on odd-order
roots factors through equality in `QurQ`.

Thus `OddRootActionFactorsThroughQurAt` is the narrow missing compatibility theorem.  Once it
is supplied, tame surjectivity gives `CompatibleResidueLiftAt` through the existing
full-inertia producer.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2

/-! ## Kernel and full inertia -/

/-- Membership in full tame inertia is exactly vanishing in the full unramified quotient. -/
theorem tame_mem_inertiaPartQ_iff_qMkQ_eq_one
    (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) (g : ↑U) :
    tame g ∈ inertiaPartQ P.qK ↔ qMkQ P.qK (tame g) = 1 :=
  (quotientMk_eq_one_iff (N := inertiaPartQ P.qK)).symm

/-- The kernel of the full unramified quotient fixes every odd-order root of unity. -/
def QurKernelFixesOddRootsAt (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) : Prop :=
  ∀ g : ↑U, qMkQ P.qK (tame g) = 1 →
    FixesOddRootsOfUnity (subtypeAnc U g)

/-- The odd-root kernel statement is exactly corrected full-inertia absolute residue
triviality. -/
theorem qurKernelFixesOddRootsAt_iff_fullInertia
    (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) :
    QurKernelFixesOddRootsAt P U tame ↔
      TameFullInertiaAbsoluteResidueTrivialAt P U tame := by
  constructor
  · intro h g hg
    apply (fixesOddRootsOfUnity_iff_isResidueTrivial_bot (subtypeAnc U g)).mp
    apply h g
    exact (tame_mem_inertiaPartQ_iff_qMkQ_eq_one P U tame g).mp hg
  · intro h g hg
    apply (fixesOddRootsOfUnity_iff_isResidueTrivial_bot (subtypeAnc U g)).mpr
    apply h g
    exact (tame_mem_inertiaPartQ_iff_qMkQ_eq_one P U tame g).mpr hg

/-! ## Factorization of the absolute odd-root action -/

/-- Equality in the full unramified quotient determines the action on every odd-order root of
unity.  This is the exact action-level compatibility between `qMkQ` and the absolute residue
action. -/
def OddRootActionFactorsThroughQurAt (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) : Prop :=
  ∀ g h : ↑U, qMkQ P.qK (tame g) = qMkQ P.qK (tame h) →
    ∀ (m : ℕ) (ζ : AlgebraicClosure ℚ_[2]), Odd m → ζ ^ m = 1 →
      subtypeAnc U g • ζ = subtypeAnc U h • ζ

/-- Factorization of the odd-root action is equivalent to triviality on the `qMkQ` kernel. -/
theorem oddRootActionFactorsThroughQurAt_iff_kernel
    (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) :
    OddRootActionFactorsThroughQurAt P U tame ↔
      QurKernelFixesOddRootsAt P U tame := by
  constructor
  · intro h g hg m ζ hm hζ
    have heq : qMkQ P.qK (tame g) = qMkQ P.qK (tame (1 : ↑U)) := by
      simpa using hg
    simpa only [map_one, one_smul] using h g 1 heq m ζ hm hζ
  · intro hker g h heq m ζ hm hζ
    have hq : qMkQ P.qK (tame (h⁻¹ * g)) = 1 := by
      simp only [map_mul, map_inv]
      rw [heq, inv_mul_cancel]
    have hfix := hker (h⁻¹ * g) hq m ζ hm hζ
    rw [map_mul, map_inv, mul_smul] at hfix
    calc
      subtypeAnc U g • ζ = subtypeAnc U h • (subtypeAnc U h⁻¹ •
          (subtypeAnc U g • ζ)) := (smul_inv_smul _ _).symm
      _ = subtypeAnc U h • ζ := congrArg
        (fun x : AlgebraicClosure ℚ_[2] => subtypeAnc U h • x) hfix

/-- The structural factorization statement is exactly corrected full-inertia absolute residue
triviality. -/
theorem oddRootActionFactorsThroughQurAt_iff_fullInertia
    (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) :
    OddRootActionFactorsThroughQurAt P U tame ↔
      TameFullInertiaAbsoluteResidueTrivialAt P U tame :=
  (oddRootActionFactorsThroughQurAt_iff_kernel P U tame).trans
    (qurKernelFixesOddRootsAt_iff_fullInertia P U tame)

/-! ## Compatible residue lifts -/

/-- Odd-root action factorization through the full unramified quotient, together with tame
surjectivity, produces the compatible residue-lift packet. -/
theorem compatibleResidueLiftAt_of_oddRootActionFactorsThroughQur
    (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (tame : ContinuousMonoidHom ↑U (Tq P.qK)) (htame : Function.Surjective tame)
    (hfac : OddRootActionFactorsThroughQurAt P U tame) :
    CompatibleResidueLiftAt P U tame :=
  compatibleResidueLiftAt_of_fullInertia P U tame htame
    ((oddRootActionFactorsThroughQurAt_iff_fullInertia P U tame).mp hfac)

#print axioms tame_mem_inertiaPartQ_iff_qMkQ_eq_one
#print axioms QurKernelFixesOddRootsAt
#print axioms qurKernelFixesOddRootsAt_iff_fullInertia
#print axioms OddRootActionFactorsThroughQurAt
#print axioms oddRootActionFactorsThroughQurAt_iff_kernel
#print axioms oddRootActionFactorsThroughQurAt_iff_fullInertia
#print axioms compatibleResidueLiftAt_of_oddRootActionFactorsThroughQur

end
end GQ2.Dyadic
