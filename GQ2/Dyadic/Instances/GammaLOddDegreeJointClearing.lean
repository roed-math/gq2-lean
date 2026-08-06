/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLOddDegreePresentingFrame

/-!
# The residual with the field removed: joint `(χ, ν)` clearing on `D_sq(h)`

The odd-degree row now carries one residual, `MarkingAudit.SqFullNuForwardSupply B h`
(`GammaLOddDegreeSingleResidual`).  That statement still mentions `K`, `B` and `G_K(2)`.  This
file removes all three.

The χ-free clearing binder is

  `SqCore.SqNuClearHypothesis h` : for every marking `ν'` of `D_sq(h)` **whose `σ`- and
  `x₀`-rows are already `1` and `0`**, some continuous automorphism carries `ν'` to `ν_sq`.

Its two-row precondition is exactly what the frame lane was buying: the arithmetic frame of
`MarkedFrame.exists_isCupAdapted_nuRows_of_cupOne` carries those two rows, and the binder
`SqCupAdaptedFrameRelator K` is what turns that frame into an equivalence.  Replace the
precondition by a hypothesis the arithmetic supplies *without* the frame, and both binders
disappear at once:

  `SqNuJointClearing h` : for every marking `ν'` of `D_sq(h)` such that `(χ_sq, ν')` is
  **jointly surjective** onto `ℤ₂ˣ × ℤ₂`, some continuous automorphism carries `ν'` to `ν_sq`.

The joint-surjectivity hypothesis is free at odd degree (§1): transport the P3 theorem
`exists_chiCycKTwo_eq_and_nuUrKTwo_eq` — `(χ_cyc, ν_ur)` is jointly surjective on `G_K(2)` — back
along the *unconditional* oriented equivalence of `nonempty_orientedEquiv_oddDegree`.  So §2 gets
`SqFullNuForwardSupply` and §3 gets the grand assembly, over `SqNuJointClearing h` and the
packet's structural pair alone.

`SqNuJointClearing h` mentions no field, no `MarkedRecip`, no frame, no cup form and no relator
clause: it is a statement about the model group `D_sq(h)`, its canonical character `χ_sq`, its
standard marking `ν_sq`, and its continuous automorphisms.  That is the shape the χ-free seed
search wants.

## Honest pricing

`SqNuJointClearing h` is **not** implied by `SqCore.SqNuClearHypothesis h`, and does not imply
it: the two preconditions are incomparable (two exact rows do not give joint surjectivity, and
joint surjectivity does not give the rows).  So this is a *different* single residual, not a
weakening of the committed one — it buys the retirement of the frame binder by asking the
clearing lane to start from an arbitrary jointly-surjective marking instead of a pre-normalized
one.  In particular the `h = 0` proof `sqNuClearHypothesis_zero`, which is available because the
two-row precondition already pins everything at rank three, does **not** transfer, and no
`h = 0` instance of `SqNuJointClearing` is claimed here.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Dyadic SqCore Multiplicative

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 Joint `(χ_sq, ν)` surjectivity is free at odd degree -/

section JointSurjectivity

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

omit [T2Space (GalK K)] in
/-- **The transported marking is jointly surjective with `χ_sq`.**  Along an oriented
equivalence `f` the pair `(χ_sq, ν_ur ∘ f)` on `D_sq(h)` is the pair `(χ_cyc, ν_ur)` on
`G_K(2)`, which P3 proves jointly surjective at odd degree and level `r = 0`. -/
theorem jointSurjective_transportedNuUr (B : MarkedRecip Rec K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) (hr : B.r = 0) {h : ℕ}
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (horient : ∀ x, chiCycKTwo (K := K) (f x) = chiSq h x) (u : ℤ_[2]ˣ) (y : ℤ_[2]) :
    ∃ g : (DSq h : Type), chiSq h g = u ∧ transportedNuUr B f g = ofAdd y := by
  obtain ⟨q, hqchi, hqnu⟩ := exists_chiCycKTwo_eq_and_nuUrKTwo_eq B hodd hr u y
  refine ⟨f.symm q, ?_, ?_⟩
  · rw [← horient (f.symm q), f.apply_symm_apply, hqchi]
  · rw [transportedNuUr_apply, f.apply_symm_apply, hqnu]

end JointSurjectivity

/-! ## §2 The field-free residual -/

section JointClearing

/-- **The joint clearing hypothesis** — the odd-degree row's residual with the field removed.
Every marking of the `L_sq` core which is jointly surjective with `χ_sq` can be carried to the
standard marking `ν_sq` by a continuous automorphism of the core.

This is `SqCore.SqNuClearHypothesis` with its two-row precondition — the thing the frame lane
supplied — replaced by a hypothesis the arithmetic supplies for free. -/
def SqNuJointClearing (h : ℕ) : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    (∀ (u : ℤ_[2]ˣ) (y : ℤ_[2]), ∃ g : (DSq h : Type), chiSq h g = u ∧ nu' g = ofAdd y) →
      ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type), ∀ x, nu' (Ψ x) = nuSq h x

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The single residual, discharged from a field-free hypothesis.**  The oriented equivalence
is unconditional, its transported marking is jointly surjective, and the joint clearing
hypothesis normalizes it to `ν_sq`. -/
theorem sqFullNuForwardSupply_of_jointClearing (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hjoint : SqNuJointClearing h) : MarkingAudit.SqFullNuForwardSupply B h := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hr : B.r = 0 := B.level_eq_zero_of_odd_finrank FF hodd
  obtain ⟨f, horient⟩ := orientedEquiv_of_oddDegree (K := K) hdeg
  obtain ⟨Ψ, hΨ⟩ := hjoint (transportedNuUr B f)
    (jointSurjective_transportedNuUr B hodd hr f horient)
  exact ⟨Ψ.trans f, fun x ↦ hΨ x⟩

/-! ## §3 The grand assembly over a hypothesis that never mentions `K` -/

/-- **THE ODD-DEGREE ROW OVER A FIELD-FREE RESIDUAL.**  For every odd-degree ramified `K`, the
improved square presentation is `G_K` over `SqNuJointClearing h` — a statement about the model
group `D_sq(h)` alone — and the packet's structural pair `T`, `ramifiedData`. -/
theorem gammaR_lSq_equiv_galK_oddDegree_of_jointClearing (B : MarkedRecip Rec K)
    {FF : DyadicUnitFiltration K} (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (hjoint : SqNuJointClearing h)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_of_fullNu B T D hdeg
    (sqFullNuForwardSupply_of_jointClearing B FF hdeg hjoint) ramifiedData

/-- **Free corollary over the field-free residual**: the Krull open-subgroup field
identifications. -/
theorem gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_jointClearing
    (B : MarkedRecip Rec K) {FF : DyadicUnitFiltration K} (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (hjoint : SqNuJointClearing h)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    GammaLOddIndexOpenSubgroupFieldIdentificationSupply h (qOf K FF) :=
  gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_fullNu B T D hdeg
    (sqFullNuForwardSupply_of_jointClearing B FF hdeg hjoint) ramifiedData

end JointClearing

/-! ## §4 Stress pins

The two preconditions are incomparable, and the file claims no implication between them.  What
*is* recorded is that each is enough on its own side of the reconciliation. -/

section StressTests

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- Route A (the committed one): the frame binder supplies the two rows, the clearing binder
does the rest. -/
example (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (hclear : SqCore.SqNuClearHypothesis h)
    (hpres : MarkedFrame.SqCupAdaptedFramePresentation K) :
    MarkingAudit.SqFullNuForwardSupply B h :=
  sqFullNuForwardSupply_of_binders B FF hdeg hclear hpres

/-- Route B (this file): no frame binder at all. -/
example (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (hjoint : SqNuJointClearing h) :
    MarkingAudit.SqFullNuForwardSupply B h :=
  sqFullNuForwardSupply_of_jointClearing B FF hdeg hjoint

/-- Both routes land on the same object, so the two residuals are interchangeable inputs to the
grand assembly. -/
example (B : MarkedRecip Rec K) (h : ℕ) :
    MarkingAudit.SqFullNuForwardSupply B h ↔
      Nonempty (MarkedCoreRealization (K := K) (B := B) (DSq h)
        (Instances.LSquareCore.lNu h)) :=
  sqFullNuForwardSupply_iff_block B h

/-- The joint-surjectivity hypothesis of `SqNuJointClearing` is satisfiable, not vacuous: it
holds at the transported marking of the unconditional oriented equivalence. -/
example (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) :
    ∃ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      ∀ (u : ℤ_[2]ˣ) (y : ℤ_[2]), ∃ g : (DSq h : Type),
        chiSq h g = u ∧ nu' g = ofAdd y := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  obtain ⟨f, horient⟩ := orientedEquiv_of_oddDegree (K := K) hdeg
  exact ⟨transportedNuUr B f, jointSurjective_transportedNuUr B hodd
    (B.level_eq_zero_of_odd_finrank FF hodd) f horient⟩

end StressTests

end

#print axioms GQ2.Dyadic.LSquare.jointSurjective_transportedNuUr
#print axioms GQ2.Dyadic.LSquare.SqNuJointClearing
#print axioms GQ2.Dyadic.LSquare.sqFullNuForwardSupply_of_jointClearing
#print axioms GQ2.Dyadic.LSquare.gammaR_lSq_equiv_galK_oddDegree_of_jointClearing
open GQ2.Dyadic.LSquare in
#print axioms gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_jointClearing

end GQ2.Dyadic.LSquare
