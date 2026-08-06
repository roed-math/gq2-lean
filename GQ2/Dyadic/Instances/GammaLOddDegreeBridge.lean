/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLNuAdaptedFrame
import GQ2.Dyadic.Instances.GammaLOddDegreeJointClearing
import GQ2.Dyadic.SqCore.JointClearing

/-!
# The odd-degree row over the **model-side oriented** clearing statement

`GammaLNuAdaptedFrame` §6 reduced the odd-degree residual to one word:

  `SqNuAdaptedFrameRelator B` ↔ *one* equivalence `D_sq(h) ≃ₜ* G_K(2)` carrying **both** the
  orientation and the whole marking (`sqNuAdaptedFrameRelator_iff_orientedFullNu`).

Orientation alone is free (`orientedEquiv_of_oddDegree`), and the marking transported along an
oriented equivalence is jointly surjective with `χ_sq` (`jointSurjective_transportedNuUr`).  So
the only thing missing is a **`χ`-preserving** automorphism of the model group correcting the
transported marking onto `ν_sq` — which is exactly `SqCore.SqNuOrientedClear h`
(`SqCore/JointClearing.lean`), a statement about `D_sq(h)`, `χ_sq`, `ν_sq` and continuous
automorphisms, with no field, no `MarkedRecip`, no frame and no cup form in it.

This file is that bridge, in three lines of mathematics:

* **§1** `exists_orientedEquiv_fullNu_of_orientedClear` — take `f` oriented, put
  `ν' := transportedNuUr B f`, feed `SqNuOrientedClear h`, and return `Ψ.trans f`.  The
  orientation survives *because* `Ψ` preserves `χ_sq`; that is the whole reason the oriented
  clearing statement, and not the plain joint one, is the right model-side hypothesis for this
  route.
* **§2** `sqNuAdaptedFrameRelator_of_orientedClear` — the same, read through §6's
  characterization, so the odd-degree residual is discharged.
* **§3** `gammaR_lSq_equiv_galK_oddDegree_of_orientedClear` — the endpoint restated over the
  model-side hypothesis, and its `h = 0` face
  `gammaR_lSq_equiv_galK_degreeOne_of_pivotMoves`, where the pivot core family
  (`SqCore.SqPivotCoreMove`) is the *only* input: at `h = 0` the handle stratum is empty and
  `sqNuOrientedClear_zero_of_pivotMoves` needs nothing else.

## Comparison with the joint route

`GammaLOddDegreeJointClearing` already runs an analogous bridge over `SqNuJointClearing h`
(= `SqCore.SqNuJointClear h`, same body), landing in `MarkingAudit.SqFullNuForwardSupply`.  That
route forgets the orientation at the first step, so it needs no `χ`-clause on `Ψ`; this one
keeps it and therefore lands on the strictly finer object `SqNuAdaptedFrameRelator B`, which
§6 shows is the *oriented* full-`ν` equivalence.  §4 pins both, and the implication
`SqNuOrientedClear h → SqNuJointClearing h` that makes the two comparable.

## Axioms

Std-3 plus the census members already carried by the frame lane and the grand assembly; the
bridge itself introduces nothing.  No `sorry`, no new axiom, no `native_decide`.  Census
unchanged at **11**.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Dyadic SqCore Multiplicative

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

namespace NuAdapted

/-! ## §1 The oriented equivalence carrying the whole marking -/

section OrientedFullNu

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The bridge.**  An oriented equivalence exists unconditionally at odd degree; its
transported marking is jointly surjective with `χ_sq`; the model-side oriented clearing
statement corrects that marking by a `χ_sq`-preserving automorphism `Ψ`.  The composite
`Ψ.trans f` is then **one** equivalence carrying the orientation *and* the whole marking. -/
theorem exists_orientedEquiv_fullNu_of_orientedClear (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hclear : SqCore.SqNuOrientedClear h) :
    ∃ f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)),
      (∀ x, chiCycKTwo (K := K) (f x) = chiSq h x) ∧
        ∀ x, nuUrKTwo B (f x) = nuSq h x := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hr : B.r = 0 := B.level_eq_zero_of_odd_finrank FF hodd
  obtain ⟨f, horient⟩ := orientedEquiv_of_oddDegree (K := K) hdeg
  obtain ⟨Ψ, hchi, hnu⟩ := hclear (transportedNuUr B f)
    (fun u y => jointSurjective_transportedNuUr B hodd hr f horient u y)
  refine ⟨Ψ.trans f, fun x => ?_, fun x => hnu x⟩
  show chiCycKTwo (K := K) (f (Ψ x)) = chiSq h x
  rw [horient (Ψ x), hchi x]

end OrientedFullNu

/-! ## §2 The minimal odd-degree residual, discharged -/

section Residual

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The odd-degree residual over the model-side hypothesis.**  `SqNuAdaptedFrameRelator B` is
the oriented full-`ν` equivalence (§6 of `GammaLNuAdaptedFrame`), and §1 builds one. -/
theorem sqNuAdaptedFrameRelator_of_orientedClear (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hclear : SqCore.SqNuOrientedClear h) : SqNuAdaptedFrameRelator B := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hh : (Module.finrank ℚ_[2] K - 1) / 2 = h := by omega
  subst hh
  exact (sqNuAdaptedFrameRelator_iff_orientedFullNu B hodd).2
    (exists_orientedEquiv_fullNu_of_orientedClear B FF hdeg hclear)

end Residual

/-! ## §3 The endpoint, and the `h = 0` face -/

section Endpoint

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **THE ODD-DEGREE ROW OVER A MODEL-SIDE HYPOTHESIS.**  `Γ_{R_K} ≅ G_K` for every odd-degree
ramified `K` at the type-`L` level `r = 0`, over `SqCore.SqNuOrientedClear h` alone (plus the
packet's structural pair `T`, `ramifiedData`).  The hypothesis mentions no field: it is a
statement about `D_sq(h)`, `χ_sq`, `ν_sq` and continuous automorphisms. -/
theorem gammaR_lSq_equiv_galK_oddDegree_of_orientedClear (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (hclear : SqCore.SqNuOrientedClear h)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_of_nuAdaptedFrameRelator B T D hdeg
    (sqNuAdaptedFrameRelator_of_orientedClear B FF hdeg hclear) ramifiedData

/-- **The `h = 0` face: the pivot core family is the only input.**  At `h = 0` there are no
handle letters and the `χ`-preserving handle stratum is a theorem, so
`sqNuOrientedClear_zero_of_pivotMoves` turns the pivot family into `SqNuOrientedClear 0`
outright; §3 then gives `Γ_{R_K} ≅ G_K` at `[K : ℚ₂] = 1`. -/
theorem gammaR_lSq_equiv_galK_degreeOne_of_pivotMoves (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) (hdeg : Module.finrank ℚ_[2] K = 1)
    (hmv : ∀ m k : ℤ_[2], IsUnit (1 + m - k * sqPivotExp) → SqCore.SqPivotCoreMove 0 m k)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma 0 (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_of_orientedClear B FF T D (by omega)
    (SqCore.sqNuOrientedClear_zero_of_pivotMoves hmv) ramifiedData

end Endpoint

/-! ## §4 Stress pins

The two model-side statements and the two routes they feed, pinned side by side. -/

section StressTests

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The oriented model statement implies the plain joint one, so this file's route subsumes
`GammaLOddDegreeJointClearing`'s. -/
example (h : ℕ) (H : SqCore.SqNuOrientedClear h) : SqNuJointClearing h :=
  SqCore.sqNuJointClear_of_orientedClear H

/-- Route B (the joint one) lands in the unoriented supply. -/
example (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (H : SqCore.SqNuOrientedClear h) :
    MarkingAudit.SqFullNuForwardSupply B h :=
  sqFullNuForwardSupply_of_jointClearing B FF hdeg (SqCore.sqNuJointClear_of_orientedClear H)

/-- Route C (this file) lands on the oriented residual itself. -/
example (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (H : SqCore.SqNuOrientedClear h) :
    SqNuAdaptedFrameRelator B :=
  sqNuAdaptedFrameRelator_of_orientedClear B FF hdeg H

/-- At `h = 0` the pivot family alone gives the model-side hypothesis. -/
example (hmv : ∀ m k : ℤ_[2], IsUnit (1 + m - k * sqPivotExp) → SqCore.SqPivotCoreMove 0 m k) :
    SqCore.SqNuOrientedClear 0 :=
  SqCore.sqNuOrientedClear_zero_of_pivotMoves hmv

/-- …and therefore the odd-degree residual at `[K : ℚ₂] = 1`. -/
example (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (hdeg : Module.finrank ℚ_[2] K = 1)
    (hmv : ∀ m k : ℤ_[2], IsUnit (1 + m - k * sqPivotExp) → SqCore.SqPivotCoreMove 0 m k) :
    SqNuAdaptedFrameRelator B :=
  sqNuAdaptedFrameRelator_of_orientedClear B FF (by omega)
    (SqCore.sqNuOrientedClear_zero_of_pivotMoves hmv)

end StressTests

end NuAdapted

end

#print axioms GQ2.Dyadic.LSquare.NuAdapted.exists_orientedEquiv_fullNu_of_orientedClear
#print axioms GQ2.Dyadic.LSquare.NuAdapted.sqNuAdaptedFrameRelator_of_orientedClear
#print axioms GQ2.Dyadic.LSquare.NuAdapted.gammaR_lSq_equiv_galK_oddDegree_of_orientedClear
#print axioms GQ2.Dyadic.LSquare.NuAdapted.gammaR_lSq_equiv_galK_degreeOne_of_pivotMoves

end GQ2.Dyadic.LSquare
