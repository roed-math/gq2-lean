/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.AnchoredTameInertiaPrescribedUnramified

/-!
# The relative unit-spectral reciprocity gap for prescribed tame-inertia fields

The abstract tame quotient already proves that the subgroup defining
`anchoredTameInertiaField` contains every reciprocity lift whose tame image lies in full closed
inertia.  The remaining field-theoretic input is the standard local-CFT assertion that a finite
extension fixed by all reciprocity lifts of units has relative ramification index one.

`AnchoredUnitSpectralReciprocity` isolates that missing assertion independently of a tame
quotient.  The main adapter composes it with a generic full-inertia refinement of the AX4 unit
clause and produces `AnchoredTameInertiaRelativeUnramifiedDataAt` with the original compatible
use and custom action unchanged.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The full-inertia refinement of the AX4 unit clause for an arbitrary marked tame map. -/
def TameUnitInertiaRefinementAt
    {R : LocalReciprocity} (P : FieldParameters)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (B : MarkedRecip R K)
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq P.qK)) : Prop :=
  ∀ (u : (↥K)ˣ) (g : GalK K), ‖((u : ↥K) : ℚ̄₂)‖ = 1 →
    toAbK K g = B.recip u → tame g ∈ inertiaPartQ P.qK

/-- Equivalently, the full unramified quotient kills reciprocity units. -/
theorem tameUnitInertiaRefinementAt_iff_qMkQ_recip_unit
    {R : LocalReciprocity} (P : FieldParameters)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (B : MarkedRecip R K)
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq P.qK)) :
    TameUnitInertiaRefinementAt P K B tame ↔
      ∀ (u : (↥K)ˣ) (g : GalK K), ‖((u : ↥K) : ℚ̄₂)‖ = 1 →
        toAbK K g = B.recip u → qMkQ P.qK (tame g) = 1 := by
  refine forall_congr' fun u => forall_congr' fun g => forall_congr' fun hu =>
    forall_congr' fun hg => ?_
  exact (quotientMk_eq_one_iff (N := inertiaPartQ P.qK)).symm

/-- The existing refinement for an oriented tame quotient transports to the parameter-indexed
tame map used by compatible consumers. -/
theorem tameUnitInertiaRefinementAt_tameAtParams
    {R : LocalReciprocity} (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] (B : MarkedRecip R K)
    (P : FieldParameters) {q : ℕ} (hq : P.qK = q)
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq q))
    (Hunit : ∀ (u : (↥K)ˣ) (g : GalK K), ‖((u : ↥K) : ℚ̄₂)‖ = 1 →
      toAbK K g = B.recip u → tame g ∈ inertiaPartQ q) :
    TameUnitInertiaRefinementAt P K B (tameAtParams P hq tame) := by
  subst q
  exact Hunit

/-- In particular, the existing oriented refinement supplies the parameter-indexed one. -/
theorem tameUnitInertiaRefinementAt_tameAtParams_of_oriented
    {R : LocalReciprocity} (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] (B : MarkedRecip R K)
    (FK : DyadicUnitFiltration K) (T : OrientedTameQuotientK B FK)
    (P : FieldParameters) (hq : P.qK = qOf K FK)
    (Hunit : TameUnitInertiaRefinement B FK T) :
    TameUnitInertiaRefinementAt P K B (tameAtParams P hq T.tameFK) :=
  tameUnitInertiaRefinementAt_tameAtParams K B P hq T.tameFK Hunit

/-- Surjectivity is preserved by the same parameter reindexing. -/
theorem tameAtParams_surjective_for_spectralReciprocity
    {K : IntermediateField ℚ_[2] ℚ̄₂} (P : FieldParameters) {q : ℕ}
    (hq : P.qK = q) (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq q))
    (htame : Function.Surjective tame) :
    Function.Surjective (tameAtParams P hq tame) := by
  subst q
  exact htame

/-- The missing relative unit-spectral reciprocity theorem.  It says that when every lift of a
reciprocity unit fixes a prescribed finite field, that field has relative ramification index
one.  The statement is independent of how the finite quotient was obtained. -/
def AnchoredUnitSpectralReciprocity
    {R : LocalReciprocity} (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] (B : MarkedRecip R K)
    (FK : DyadicUnitFiltration K) : Prop :=
  ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
    (rho : ContinuousMonoidHom ↑(GalKsub K) D) (t : D),
    (∀ (u : (↥K)ˣ) (g : GalK K), ‖((u : ↥K) : ℚ̄₂)‖ = 1 →
      toAbK K g = B.recip u → rho g ∈ Subgroup.zpowers t) →
    ∃ F₀F : DyadicUnitFiltration
        (anchoredTameInertiaField (GalKsub K) rho t),
      GaloisCosetNorm.relE FK F₀F
        (baseField_le_anchoredTameInertiaField K rho t) = 1

/-- Full tame-inertia control of reciprocity units, followed by the missing unit-spectral
reciprocity theorem, proves relative unramifiedness at every compatible ramified use. -/
theorem anchoredTameInertiaRelativeUnramifiedDataAt_of_unitSpectralReciprocity
    {R : LocalReciprocity} (P : FieldParameters)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (B : MarkedRecip R K) (FK : DyadicUnitFiltration K)
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq P.qK))
    (Hunit : TameUnitInertiaRefinementAt P K B tame)
    (Hspec : AnchoredUnitSpectralReciprocity K B FK) :
    AnchoredTameInertiaRelativeUnramifiedDataAt P K FK tame := by
  intro D _ _ _ _ V _ _ c rho hfac _hram
  apply Hspec rho (c (tqTau P.qK))
  intro u g hu hg
  rw [hfac]
  exact inertiaPartQ_le_comap_zpowers_tqTau P.qK c (Hunit u g hu hg)

/-- The oriented full-inertia refinement and the unit-spectral theorem give the exact residual
after reindexing the tame map along the consumer's parameter equality. -/
theorem anchoredTameInertiaRelativeUnramifiedDataAt_tameAtParams_of_unitSpectralReciprocity
    {R : LocalReciprocity} (P : FieldParameters)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (B : MarkedRecip R K) (FK : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FK) (hq : P.qK = qOf K FK)
    (Hunit : TameUnitInertiaRefinement B FK T)
    (Hspec : AnchoredUnitSpectralReciprocity K B FK) :
    AnchoredTameInertiaRelativeUnramifiedDataAt P K FK
      (tameAtParams P hq T.tameFK) :=
  anchoredTameInertiaRelativeUnramifiedDataAt_of_unitSpectralReciprocity
    P K B FK (tameAtParams P hq T.tameFK)
      (tameUnitInertiaRefinementAt_tameAtParams_of_oriented K B FK T P hq Hunit) Hspec

/-- The same two precise reciprocity inputs close the compatible involution norm packet over an
odd-degree base field. -/
theorem anchoredInvolutionEqualNormValueGroupsAt_of_unitSpectralReciprocity
    {R : LocalReciprocity} (P : FieldParameters)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (B : MarkedRecip R K) (FK : DyadicUnitFiltration K)
    (tame : ContinuousMonoidHom ↑(GalKsub K) (Tq P.qK))
    (htame : Function.Surjective tame) (hodd : Odd (Module.finrank ℚ_[2] K))
    (Hunit : TameUnitInertiaRefinementAt P K B tame)
    (Hspec : AnchoredUnitSpectralReciprocity K B FK) :
    AnchoredInvolutionEqualNormValueGroupsAt P (GalKsub K) tame :=
  anchoredInvolutionEqualNormValueGroupsAt_of_prescribedTameUnramified P K FK tame htame hodd
    (anchoredTameInertiaRelativeUnramifiedDataAt_of_unitSpectralReciprocity
      P K B FK tame Hunit Hspec)

/-- End-to-end oriented producer in the exact parameter-reindexed form used by compatible
consumers. -/
theorem anchoredInvolutionEqualNormValueGroupsAt_tameAtParams_of_unitSpectralReciprocity
    {R : LocalReciprocity} (P : FieldParameters)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (B : MarkedRecip R K) (FK : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FK) (hq : P.qK = qOf K FK)
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (Hunit : TameUnitInertiaRefinement B FK T)
    (Hspec : AnchoredUnitSpectralReciprocity K B FK) :
    AnchoredInvolutionEqualNormValueGroupsAt P (GalKsub K)
      (tameAtParams P hq T.tameFK) :=
  anchoredInvolutionEqualNormValueGroupsAt_of_unitSpectralReciprocity P K B FK
    (tameAtParams P hq T.tameFK)
    (tameAtParams_surjective_for_spectralReciprocity P hq T.tameFK
      T.tameFK_surjective) hodd
    (tameUnitInertiaRefinementAt_tameAtParams_of_oriented K B FK T P hq Hunit) Hspec

#print axioms TameUnitInertiaRefinementAt
#print axioms tameUnitInertiaRefinementAt_iff_qMkQ_recip_unit
#print axioms tameUnitInertiaRefinementAt_tameAtParams
#print axioms tameUnitInertiaRefinementAt_tameAtParams_of_oriented
#print axioms tameAtParams_surjective_for_spectralReciprocity
#print axioms AnchoredUnitSpectralReciprocity
#print axioms anchoredTameInertiaRelativeUnramifiedDataAt_of_unitSpectralReciprocity
#print axioms anchoredTameInertiaRelativeUnramifiedDataAt_tameAtParams_of_unitSpectralReciprocity
#print axioms anchoredInvolutionEqualNormValueGroupsAt_of_unitSpectralReciprocity
#print axioms anchoredInvolutionEqualNormValueGroupsAt_tameAtParams_of_unitSpectralReciprocity

end
end GQ2.Dyadic
