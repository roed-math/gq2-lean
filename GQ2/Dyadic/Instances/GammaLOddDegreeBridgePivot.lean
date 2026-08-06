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

## ⚠ STATUS: the third line is **false** at `h ≥ 1`; the list is corrected below

`SqCore/PivotClimb.lean` (W41) refutes `SqPivotUnitizer h` at every `h ≥ 1`, with an explicit
witness, so `gammaR_lSq_equiv_galK_oddDegree_of_subgroups` — which binds it — is **vacuous
above degree one**.  It is kept, marked, and superseded.

The corrected list *drops* the third line rather than replacing it:

```text
  SqPivotTranslation h c, SqPivotScaling h a, SqHandleMixFixesCore h c₀
      ⟹  SqCore.SqNuOrientedClearAtUnitPivot h        (sqNuOrientedClearAtUnitPivot_of_families)
```

and the unit-pivot side condition that the deleted line was supposed to arrange by an
automorphism is paid instead by **P3's `SqMarkedForwardSupply B h`**, whose two `ν`-rows give
`ν_ur(f w) = 1` on the nose.  `PivotClimb` §9 shows this relocation is forced: the parity of the
transported pivot row is an invariant of `G_K`, so no model-side statement could ever have
supplied it.

The two live restatements are

* `gammaR_lSq_equiv_galK_oddDegree_of_subgroups_of_markedSupply` — the three model-side binders
  plus the marked supply;
* `gammaR_lSq_equiv_galK_oddDegree_of_subgroups_of_presentation` — the same with the supply
  discharged from `MarkedFrame.SqCupAdaptedFramePresentation K`, i.e. the residual the grand
  assembly **already** carries, so the corrected endpoint costs the three pivot binders and
  nothing new.

The `h = 0` milestone `gammaR_lSq_equiv_galK_degreeOne_of_subgroups` is untouched: there the
unitizer is a theorem, so the two residuals coincide.

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

/-- **The odd-degree row over the four listed model-side inputs.**

⚠ **VACUOUS at every `h ≥ 1`.**  The binder `hunit : SqCore.SqPivotUnitizer h` is refuted by
`SqCore.not_sqPivotUnitizer`, whatever the other three binders are — `PivotClimb` §11 pins
exactly this.  Live at `h = 0`, where the unitizer is a theorem; that case is stated separately
as `gammaR_lSq_equiv_galK_degreeOne_of_subgroups` and does **not** route through here.

Kept as the record of the four-input shape.  Its live successors, over the *same first three*
binders, are `gammaR_lSq_equiv_galK_oddDegree_of_subgroups_of_markedSupply` and
`gammaR_lSq_equiv_galK_oddDegree_of_subgroups_of_presentation`. -/
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

/-- **THE LIVE ODD-DEGREE ROW OVER THE TWO PIVOT SUBGROUPS.**  The corrected restatement of
`gammaR_lSq_equiv_galK_oddDegree_of_subgroups`: the refuted `hunit` binder is **deleted**, not
replaced — `SqCore.sqNuOrientedClearAtUnitPivot_of_families` derives the corrected residual from
`hfix`, `htr`, `hsc` alone — and the unit-pivot side condition it no longer proves is paid on
the `K` side by P3's marked forward supply.  Non-vacuous at **every** handle count. -/
theorem gammaR_lSq_equiv_galK_oddDegree_of_subgroups_of_markedSupply (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hfix : SqCore.SqHandleMixFixesCore h SqCore.sqPivotExp)
    (htr : ∀ c : ℤ_[2], SqCore.SqPivotTranslation h c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqCore.SqPivotScaling h a)
    (hsupply : SqMarkedForwardSupply B h)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_of_orientedClearAtUnitPivot B FF T D hdeg
    (SqCore.sqNuOrientedClearAtUnitPivot_of_families hfix htr hsc) hsupply ramifiedData

/-- **…and the marked supply is not a new residual.**  At odd degree it costs only
`MarkedFrame.SqCupAdaptedFramePresentation K` (`sqMarkedForwardSupply_oddDegree`), which the
grand assembly already carries.  So the true `h ≥ 1` price of the odd-degree row, over the
existing stage-lane residual, is exactly the three model-side binders `hfix`, `htr`, `hsc` —
one fewer than the refuted list, not one more. -/
theorem gammaR_lSq_equiv_galK_oddDegree_of_subgroups_of_presentation (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hfix : SqCore.SqHandleMixFixesCore h SqCore.sqPivotExp)
    (htr : ∀ c : ℤ_[2], SqCore.SqPivotTranslation h c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqCore.SqPivotScaling h a)
    (hpres : MarkedFrame.SqCupAdaptedFramePresentation K)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hh : (Module.finrank ℚ_[2] K - 1) / 2 = h := by omega
  have hsup := sqMarkedForwardSupply_oddDegree B FF hodd hpres
  rw [hh] at hsup
  exact gammaR_lSq_equiv_galK_oddDegree_of_subgroups_of_markedSupply B FF T D hdeg hfix htr hsc
    hsup ramifiedData

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
odd-degree row consumes.

⚠ **Vacuous at `h ≥ 1`** (`SqCore.not_sqNuOrientedClear`); live at `h = 0`.  Replacement:
`sqFullNuForwardSupply_of_orientedClearAtUnitPivot`. -/
theorem sqFullNuForwardSupply_of_orientedClear (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hclear : SqCore.SqNuOrientedClear h) : MarkingAudit.SqFullNuForwardSupply B h := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hh : (Module.finrank ℚ_[2] K - 1) / 2 = h := by omega
  have hsup := sqFullNuForwardSupply_of_nuAdaptedFrameRelator B hodd
    (sqNuAdaptedFrameRelator_of_orientedClear B FF hdeg hclear)
  rwa [hh] at hsup

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The same full-row supply, live at every `h`: over the corrected residual and P3's marked
forward supply. -/
theorem sqFullNuForwardSupply_of_orientedClearAtUnitPivot (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hclear : SqCore.SqNuOrientedClearAtUnitPivot h) (hsupply : SqMarkedForwardSupply B h) :
    MarkingAudit.SqFullNuForwardSupply B h := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hh : (Module.finrank ℚ_[2] K - 1) / 2 = h := by omega
  have hsup := sqFullNuForwardSupply_of_nuAdaptedFrameRelator B hodd
    (sqNuAdaptedFrameRelator_of_orientedClearAtUnitPivot B FF hdeg hclear hsupply)
  rwa [hh] at hsup

/-- **Free corollary over the model-side hypothesis**: the Krull open-subgroup field
identifications.

⚠ **Vacuous at `h ≥ 1`** (`SqCore.not_sqNuOrientedClear`); live at `h = 0`.  Replacement:
`gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_orientedClearAtUnitPivot`. -/
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

/-- The same free corollary, live at every `h`. -/
theorem gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_orientedClearAtUnitPivot
    (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (T : OrientedTameQuotientK B FF) (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hclear : SqCore.SqNuOrientedClearAtUnitPivot h) (hsupply : SqMarkedForwardSupply B h)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    GammaLOddIndexOpenSubgroupFieldIdentificationSupply h (qOf K FF) :=
  gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_fullNu B T D hdeg
    (sqFullNuForwardSupply_of_orientedClearAtUnitPivot B FF hdeg hclear hsupply) ramifiedData

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

/-- The unitizer is *necessary*, so the `h ≥ 1` residual list is not padded.  **⚠ Known-vacuous
at `h ≥ 1`**: the binder is refuted by `SqCore.not_sqNuOrientedClear`.  Necessity is what turned
the refutation of the unitizer into a refutation of the residual — the list was not padded, it
was *unsatisfiable*. -/
example (h : ℕ) (H : SqCore.SqNuOrientedClear h) : SqCore.SqPivotUnitizer h :=
  SqCore.sqPivotUnitizer_of_orientedClear H

/-- **The `h ≥ 1` four-input list is unsatisfiable** — the fourth binder alone refutes it, so
`gammaR_lSq_equiv_galK_oddDegree_of_subgroups` is vacuous there. -/
example (_hfix : SqCore.SqHandleMixFixesCore 1 SqCore.sqPivotExp)
    (_htr : ∀ c : ℤ_[2], SqCore.SqPivotTranslation 1 c)
    (_hsc : ∀ a : ℤ_[2], IsUnit a → SqCore.SqPivotScaling 1 a)
    (hunit : SqCore.SqPivotUnitizer 1) : False :=
  SqCore.not_sqPivotUnitizer (by omega) hunit

/-- **…while the corrected three-input list is not**: the same three binders give the corrected
residual outright, at `h = 1` and at every other handle count. -/
example (hfix : SqCore.SqHandleMixFixesCore 1 SqCore.sqPivotExp)
    (htr : ∀ c : ℤ_[2], SqCore.SqPivotTranslation 1 c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqCore.SqPivotScaling 1 a) :
    SqCore.SqNuOrientedClearAtUnitPivot 1 :=
  SqCore.sqNuOrientedClearAtUnitPivot_of_families hfix htr hsc

/-- The corrected endpoint at `h = 1`, over the three model-side binders and the stage-lane
residual the grand assembly already carries. -/
example (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) (hdeg : Module.finrank ℚ_[2] K = 3)
    (hfix : SqCore.SqHandleMixFixesCore 1 SqCore.sqPivotExp)
    (htr : ∀ c : ℤ_[2], SqCore.SqPivotTranslation 1 c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqCore.SqPivotScaling 1 a)
    (hpres : MarkedFrame.SqCupAdaptedFramePresentation K)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma 1 (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_of_subgroups_of_presentation B FF T D (by omega) hfix htr hsc
    hpres ramifiedData

end StressTests

end NuAdapted

end

#print axioms GQ2.Dyadic.LSquare.NuAdapted.gammaR_lSq_equiv_galK_oddDegree_of_subgroups
#print axioms GQ2.Dyadic.LSquare.NuAdapted.gammaR_lSq_equiv_galK_degreeOne_of_subgroups
#print axioms GQ2.Dyadic.LSquare.NuAdapted.sqFullNuForwardSupply_of_orientedClear
open GQ2.Dyadic.LSquare.NuAdapted in
#print axioms gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_orientedClear
open GQ2.Dyadic.LSquare.NuAdapted in
#print axioms gammaR_lSq_equiv_galK_oddDegree_of_subgroups_of_markedSupply
open GQ2.Dyadic.LSquare.NuAdapted in
#print axioms gammaR_lSq_equiv_galK_oddDegree_of_subgroups_of_presentation
open GQ2.Dyadic.LSquare.NuAdapted in
#print axioms sqFullNuForwardSupply_of_orientedClearAtUnitPivot
open GQ2.Dyadic.LSquare.NuAdapted in
#print axioms gammaLOddIndexOpenSubgroupFieldIdentificationSupply_of_orientedClearAtUnitPivot

end GQ2.Dyadic.LSquare
