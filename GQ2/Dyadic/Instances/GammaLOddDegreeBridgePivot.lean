/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLOddDegreeBridge
import GQ2.Dyadic.SqCore.PivotUnitizer

/-!
# The odd-degree row over the two one-parameter pivot subgroups

`GammaLOddDegreeBridge` reduced the odd-degree endpoint to the model-side statement
`SqCore.SqNuOrientedClear h`.  `SqCore/PivotCoreMoves.lean` and `SqCore/PivotUnitizer.lean`
reduce *that* to

```text
  SqPivotTranslation h c   (c ∈ ℤ₂)     w ↦ w,    x₀ ↦ x₀·w^c,  x₁ ↦ x₁·w^{2c}
  SqPivotScaling     h a   (a ∈ ℤ₂ˣ)    w ↦ w^a,  x₀ ↦ x₀,      x₁ ↦ x₁
  SqPivotUnitizer    h                  make the pivot row odd  (a theorem at h = 0)
  SqHandleMixFixesCore h c₀             the banked handle stratum  (a theorem at h = 0)
```

on the χ-trivial pivot `w = σ·x₀^{−c₀}`.  This file states the endpoint over exactly that list,
and — the point — over the **first two lines alone** at `h = 0`.

## The `h = 0` face

`gammaR_lSq_equiv_galK_degreeOne_of_subgroups` is the milestone shape: at `[K : ℚ₂] = 1` the
whole odd-degree row, i.e. `Γ_{R_K} ≅ G_K` through the general-`K` machine, holds as soon as the
two one-parameter automorphism subgroups of `D_sq(0) = D_R` above are constructed.  Every other
input — the oriented equivalence, joint surjectivity, the handle stratum, the unitizer, the
`x₁`-row — is discharged.  Both subgroups are `sqParamEquiv`-shaped (one-parameter, composing on
the nose), so the residual is two relator identities, not a two-parameter search; see
`PivotCoreMoves` §3 and its class-two balance, which shows the determinant condition
`IsUnit (sqPivotDet m k)` is *exactly* the class-two solvability condition and that no
obstruction lives at that depth.

## Axioms

Std-3 plus the census members carried by the frame lane and the grand assembly; this file adds
nothing of its own.  No `sorry`, no new axiom, no `native_decide`.  Census unchanged at **11**.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Dyadic SqCore Multiplicative

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

namespace NuAdapted

section Subgroups

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **The odd-degree row over the four listed model-side inputs.** -/
theorem gammaR_lSq_equiv_galK_oddDegree_of_subgroups (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hfix : SqCore.SqHandleMixFixesCore h SqCore.sqPivotExp)
    (htr : ∀ c : ℤ_[2], SqCore.SqPivotTranslation h c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqCore.SqPivotScaling h a)
    (hunit : SqCore.SqPivotUnitizer h)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_of_orientedClear B FF T D hdeg
    (SqCore.sqNuOrientedClear_of_families_of_unitizer hfix htr hsc hunit) ramifiedData

/-- **THE MILESTONE SHAPE.**  At `[K : ℚ₂] = 1` the odd-degree row holds over the **two
one-parameter pivot subgroups alone**: the handle stratum and the unitizer are theorems at
`h = 0`, joint surjectivity is free, and the oriented equivalence is unconditional. -/
theorem gammaR_lSq_equiv_galK_degreeOne_of_subgroups (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) (hdeg : Module.finrank ℚ_[2] K = 1)
    (htr : ∀ c : ℤ_[2], SqCore.SqPivotTranslation 0 c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqCore.SqPivotScaling 0 a)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma 0 (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_of_orientedClear B FF T D (by omega)
    (SqCore.sqNuOrientedClear_zero_of_two_subgroups htr hsc) ramifiedData

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The full-row supply over the model-side hypothesis — the object every free corollary of the
odd-degree row consumes. -/
theorem sqFullNuForwardSupply_of_orientedClear (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hclear : SqCore.SqNuOrientedClear h) : MarkingAudit.SqFullNuForwardSupply B h := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hh : (Module.finrank ℚ_[2] K - 1) / 2 = h := by omega
  have hsup := sqFullNuForwardSupply_of_nuAdaptedFrameRelator B hodd
    (sqNuAdaptedFrameRelator_of_orientedClear B FF hdeg hclear)
  rwa [hh] at hsup

/-- **Free corollary over the model-side hypothesis**: the Krull open-subgroup field
identifications. -/
theorem gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_orientedClear
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (hclear : SqCore.SqNuOrientedClear h)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    GammaLOddIndexOpenSubgroupFieldIdentificationSupply h (qOf K FF) :=
  gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_fullNu B T D hdeg
    (sqFullNuForwardSupply_of_orientedClear B FF hdeg hclear) ramifiedData

end Subgroups

/-! ## Stress pins -/

section StressTests

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The two subgroups give the model-side hypothesis at `h = 0`. -/
example (htr : ∀ c : ℤ_[2], SqCore.SqPivotTranslation 0 c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqCore.SqPivotScaling 0 a) : SqCore.SqNuOrientedClear 0 :=
  SqCore.sqNuOrientedClear_zero_of_two_subgroups htr hsc

/-- …hence the odd-degree residual at `[K : ℚ₂] = 1`. -/
example (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (hdeg : Module.finrank ℚ_[2] K = 1)
    (htr : ∀ c : ℤ_[2], SqCore.SqPivotTranslation 0 c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqCore.SqPivotScaling 0 a) : SqNuAdaptedFrameRelator B :=
  sqNuAdaptedFrameRelator_of_orientedClear B FF (by omega)
    (SqCore.sqNuOrientedClear_zero_of_two_subgroups htr hsc)

/-- The unitizer is *necessary*, so the `h ≥ 1` residual list is not padded. -/
example (h : ℕ) (H : SqCore.SqNuOrientedClear h) : SqCore.SqPivotUnitizer h :=
  SqCore.sqPivotUnitizer_of_orientedClear H

end StressTests

end NuAdapted

end

#print axioms GQ2.Dyadic.LSquare.NuAdapted.gammaR_lSq_equiv_galK_oddDegree_of_subgroups
#print axioms GQ2.Dyadic.LSquare.NuAdapted.gammaR_lSq_equiv_galK_degreeOne_of_subgroups
#print axioms GQ2.Dyadic.LSquare.NuAdapted.sqFullNuForwardSupply_of_orientedClear
open GQ2.Dyadic.LSquare.NuAdapted in
#print axioms gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_orientedClear

end GQ2.Dyadic.LSquare
