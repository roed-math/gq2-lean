/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLDeterminantBridge

/-!
# Linear first-slot shifts of the plus-form phase

The one-operation normal form is
`plusFormD q q (v, w) = q v + polar q v w`.  Any additive charge in its first slot can be
absorbed by an affine translation of the second slot.  Indeed, nonsingularity represents the
charge as `v ↦ polar q v y`, and translation by `y` gives the pointwise identity

`plusFormD q q (v, w) + ℓ v = plusFormD q q (v, w + y)`.

The translating map is an equivalence, though not generally an additive equivalence.  This is
exactly enough both to preserve the Gauss sum and to reindex a `SourceWordPhaseComparison` to
the unshifted target.  There is no constant term and hence no sign defect.

For a factor-set charge `dat.m g`, additivity is not automatic.  The final specialization keeps
the necessary hypothesis explicit: `g` must act trivially.  Under that hypothesis the
`m_quad` identity makes `dat.m g` additive.  In particular, this API applies to the residual
`pp = 1` charge at an unramified procyclic-M head once its resolver element is known to act
trivially.

No row-specific comparison is asserted here.  No `sorry`, new axiom, `native_decide`, heartbeat
override, or recursion override is used.
-/

namespace GQ2.Dyadic.Instances.PlusFormLinearShift

noncomputable section

open GQ2 GQ2.QuadraticFp2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.LSquare

variable {C : Type*} {V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-- When `g` acts trivially, its factor-set charge is additive.  Triviality is essential here:
for a general acting element, `m_quad` has a nonzero factor-set defect. -/
def factorSetChargeHomOfTrivial (g : C) (hg : ∀ v : V, g • v = v) : V →+ ZMod 2 :=
  AddMonoidHom.mk' (dat.m g) fun v w ↦ by
    have hm := hdat.m_quad g v w
    rw [hg v, hg w] at hm
    have hm0 : dat.m g (v + w) + dat.m g v + dat.m g w = 0 := by
      simpa only [CharTwo.add_self_eq_zero] using hm
    have key : ∀ a b c : ZMod 2, a + b + c = 0 → a = b + c := by decide
    exact key _ _ _ hm0

@[simp] theorem factorSetChargeHomOfTrivial_apply (g : C) (hg : ∀ v : V, g • v = v)
    (v : V) : factorSetChargeHomOfTrivial dat hdat g hg v = dat.m g v := rfl

/-- A first-slot linear shift of a plus form is an affine translation in the second slot. -/
theorem exists_plusFormD_firstLinear_translation [Fintype V]
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (ℓ : V →+ ZMod 2) :
    ∃ e : V × V ≃ V × V, ∀ p,
      plusFormD q q p + ℓ p.1 = plusFormD q q (e p) := by
  obtain ⟨y, hy⟩ := polar_rep_exists q hq hns ℓ
  refine ⟨Equiv.prodCongr (Equiv.refl V) (Equiv.addRight y), ?_⟩
  rintro ⟨v, w⟩
  change q v + polar q v w + ℓ v = q v + polar q v (w + y)
  rw [hq.polar_add_right, ← hy v]
  ring

/-- The second-slot translation removes the shift without changing the plus-form Gauss sum. -/
theorem gaussSum_plusFormD_firstLinear [Fintype V]
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (ℓ : V →+ ZMod 2) :
    QuadraticFp2.gaussSum (fun p : V × V ↦ plusFormD q q p + ℓ p.1) =
      Fintype.card V := by
  obtain ⟨e, he⟩ := exists_plusFormD_firstLinear_translation hq hns ℓ
  have hfun : (fun p : V × V ↦ plusFormD q q p + ℓ p.1) =
      fun p ↦ plusFormD q q (e p) := funext he
  rw [hfun, gaussSum_comp_equiv, gaussSum_plusFormD hq hq hns]

/-- Reindex a comparison for a first-slot linear shift to the unshifted plus form. -/
theorem SourceWordPhaseComparison.remove_plusFormD_firstLinear
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    {rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M)}
    [DistribMulAction Gamma (ZMod 2)]
    {htriv : ∀ (g : Gamma) (a : ZMod 2), g • a = a}
    [Fintype V] (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (ℓ : V →+ ZMod 2)
    (C : SourceWordPhaseComparison DD rho htriv (V × V)
      (fun p ↦ plusFormD q q p + ℓ p.1)) :
    Nonempty (SourceWordPhaseComparison DD rho htriv (V × V) (plusFormD q q)) := by
  obtain ⟨e, he⟩ := exists_plusFormD_firstLinear_translation hq hns ℓ
  exact ⟨{
    phaseEquiv := C.phaseEquiv.trans e
    phase_eq := fun x ↦ by rw [C.phase_eq, he]; rfl }⟩

include hdat in
/-- A source comparison carrying a factor-set charge can therefore be reindexed to the
unshifted plus form whenever the acting element is trivial on the quadratic module. -/
theorem SourceWordPhaseComparison.remove_factorSetCharge
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    {Gamma : Type} [Group Gamma] [TopologicalSpace Gamma]
    {rho : ContinuousMonoidHom Gamma (Bg ⧸ D.M)}
    [DistribMulAction Gamma (ZMod 2)]
    {htriv : ∀ (g : Gamma) (a : ZMod 2), g • a = a}
    [Fintype V] (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (g : C) (hg : ∀ v : V, g • v = v)
    (C0 : SourceWordPhaseComparison DD rho htriv (V × V)
      (fun p ↦ plusFormD q q p + dat.m g p.1)) :
    Nonempty (SourceWordPhaseComparison DD rho htriv (V × V) (plusFormD q q)) := by
  simpa only [factorSetChargeHomOfTrivial_apply] using
    SourceWordPhaseComparison.remove_plusFormD_firstLinear hq hns
      (factorSetChargeHomOfTrivial dat hdat g hg) C0

/-! ## Axiom audit -/

#print axioms factorSetChargeHomOfTrivial
#print axioms factorSetChargeHomOfTrivial_apply
#print axioms exists_plusFormD_firstLinear_translation
#print axioms gaussSum_plusFormD_firstLinear
#print axioms SourceWordPhaseComparison.remove_plusFormD_firstLinear
#print axioms SourceWordPhaseComparison.remove_factorSetCharge

end

end GQ2.Dyadic.Instances.PlusFormLinearShift
