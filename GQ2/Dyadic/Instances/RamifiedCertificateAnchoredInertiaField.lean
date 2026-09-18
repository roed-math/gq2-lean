/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateInertiaFixedField
import GQ2.Dyadic.Instances.AnchoredTameInertiaPrescribedUnramified

/-!
# Anchored tame-inertia fields inside the actual unramified fixed field

If actual inertia maps into the full tame inertia subgroup, every compatible finite tame
quotient cuts out an anchored inertia field fixed by actual inertia. The exact infinite Galois
correspondence and odd-root finite-containment theorem then put each of its elements in a finite
odd cyclotomic base change.

The direction of the inertia premise is essential: this module uses actual inertia contained
in abstract tame inertia, not the reverse containment used for the residue-lift certificate.
No identification of full inertia with the kernel of the pro-two unramified character is used.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- Actual inertia containment in the full tame inertia subgroup places every compatible
anchored tame-inertia field in the actual unramified fixed field. -/
theorem anchoredTameInertiaField_le_actualInertiaFixedField
    (P : FieldParameters) (K : IntermediateField ℚ_[2] ℚ̄₂)
    {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq P.qK))
    (hinertia : ∀ g : ↑(GalKsub K),
      subtypeAnc (GalKsub K) g ∈ absoluteInertiaSubgroup →
        tame g ∈ inertiaPartQ P.qK)
    (c : ContinuousMonoidHom (Tq P.qK) D)
    (rho : ContinuousMonoidHom ↑(GalKsub K) D)
    (hfac : ∀ g : ↑(GalKsub K), rho g = c (tame g)) :
    anchoredTameInertiaField (GalKsub K) rho (c (tqTau P.qK)) ≤
      IntermediateField.fixedField (absoluteInertiaSubgroup ⊓ K.fixingSubgroup) := by
  apply IntermediateField.fixedField_le
  intro g hg
  refine Subgroup.mem_map.mpr ⟨⟨g, hg.2⟩, ?_, rfl⟩
  exact tameInertia_preimage_le_anchoredTameInertia_preimage P K tame c rho hfac
    (hinertia ⟨g, hg.2⟩ hg.1)

/-- Every element of a compatible anchored tame-inertia field is in a finite odd cyclotomic
base change, provided actual inertia maps into full tame inertia. -/
theorem anchoredTameInertiaField_exists_odd_primitive_root
    (P : FieldParameters) (K : IntermediateField ℚ_[2] ℚ̄₂)
    {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq P.qK))
    (hinertia : ∀ g : ↑(GalKsub K),
      subtypeAnc (GalKsub K) g ∈ absoluteInertiaSubgroup →
        tame g ∈ inertiaPartQ P.qK)
    (c : ContinuousMonoidHom (Tq P.qK) D)
    (rho : ContinuousMonoidHom ↑(GalKsub K) D)
    (hfac : ∀ g : ↑(GalKsub K), rho g = c (tame g))
    {x : ℚ̄₂} (hx : x ∈ anchoredTameInertiaField (GalKsub K) rho (c (tqTau P.qK))) :
    ∃ (m : ℕ) (ζ : ℚ̄₂), Odd m ∧ IsPrimitiveRoot ζ m ∧
      x ∈ K ⊔ IntermediateField.adjoin ℚ_[2] {ζ} :=
  exists_odd_primitive_root_of_inertia_fixed K
    (anchoredTameInertiaField_le_actualInertiaFixedField P K tame hinertia c rho hfac hx)

#print axioms anchoredTameInertiaField_le_actualInertiaFixedField
#print axioms anchoredTameInertiaField_exists_odd_primitive_root
end
end GQ2.Dyadic

