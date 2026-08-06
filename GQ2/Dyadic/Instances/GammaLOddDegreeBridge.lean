/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLNuAdaptedFrame
import GQ2.Dyadic.Instances.GammaLOddDegreeJointClearing
import GQ2.Dyadic.SqCore.JointClearing
import GQ2.Dyadic.SqCore.PivotClimb

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

## ⚠ STATUS: `SqNuOrientedClear h` is **false** at `h ≥ 1`, and §1's route cannot be repaired

`SqCore/PivotClimb.lean` (W41) proves `not_sqNuOrientedClear : 0 < h → ¬ SqNuOrientedClear h`.
So **§1–§3 below, and the two general-`h` pins in §4, are vacuous above `h = 0`**; they are true
implications, kept because the degree-one milestone runs through them.  §1′–§3′ are the live
`h ≥ 1` replacements.

The failure is *not* fixable by weakening the model-side hypothesis alone.  §1 hands
`SqNuOrientedClear h` a marking transported along an **arbitrary** `orientedEquiv_of_oddDegree`,
with no control on its pivot row, and `PivotClimb` §9
(`isUnit_toAdd_transported_sqPivot_iff`) shows why no amount of model-side work can supply that
control: any two oriented equivalences `D_sq h ≅ G_K(2)` differ by a χ-preserving automorphism,
and the parity of `ν_ur(f w)` is invariant under those — so it is an **invariant of the target**,
not a choice of `f`, and `PivotClimb` §4 says a further automorphism of the model cannot change
it either.

The repair is therefore *arithmetic*, and it already exists: **P3's `SqMarkedForwardSupply B h`**
(`GammaLSylowPreimagePivotNu` §4) selects an oriented `f` with `ν(f σ) = 1` and `ν(f x₀) = 0`,
whence `ν(f w) = 1` on the nose (`nuUrKTwo_sqMixPivotElem_eq_one`, at *every* pivot exponent).
That is exactly the hypothesis of the corrected residual `SqCore.SqNuOrientedClearAtUnitPivot h`,
which `PivotClimb.sqNuOrientedClearAtUnitPivot_of_families` derives from the handle stratum and
the two one-parameter pivot subgroups **alone** — the model-side supply list loses the unitizer
slot and gains nothing.  §1′ is that assembly, §2′/§3′ carry it to the endpoint.

At `h = 0` nothing changes: `sqPivotUnitizer_zero` makes the two residuals coincide
(`sqNuOrientedClear_zero_of_atUnitPivot`), so `gammaR_lSq_equiv_galK_degreeOne_of_pivotMoves`
stands as written.

Note also that `SqMarkedForwardSupply B h` is *not* a new residual: at odd degree it costs only
`MarkedFrame.SqCupAdaptedFramePresentation K` (`sqMarkedForwardSupply_oddDegree`), which the
grand assembly already carries.

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
`Ψ.trans f` is then **one** equivalence carrying the orientation *and* the whole marking.

⚠ **Vacuous at `h ≥ 1`** (`SqCore.not_sqNuOrientedClear`), and *unrepairable in this shape*: the
`f` it takes from `orientedEquiv_of_oddDegree` is arbitrary, so its pivot row's parity is
whatever the target says it is (`SqCore.isUnit_toAdd_transported_sqPivot_iff`), and
`hclear` is exactly the statement that promises to fix that for free.  §1′ replaces the
arbitrary `f` by P3's *selected* one and weakens `hclear` accordingly.  Live at `h = 0`. -/
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

/-! ## §1′ The live bridge: P3 selects the pivot row, the model only normalizes the rest

The `h ≥ 1` repair of §1.  Two changes, both forced by `SqCore/PivotClimb.lean`:

* the oriented equivalence is no longer arbitrary — it is **P3's selected one**, carried by
  `SqMarkedForwardSupply B h`, whose two `ν`-rows `ν(f σ) = 1`, `ν(f x₀) = 0` force
  `ν(f w) = 1` at every pivot exponent (`nuUrKTwo_sqMixPivotElem_eq_one`);
* the model-side hypothesis is correspondingly weakened from `SqNuOrientedClear h` (refuted) to
  `SqNuOrientedClearAtUnitPivot h` (not refuted, and derivable from the handle stratum plus the
  two one-parameter pivot subgroups).

Nothing here is new mathematics: both halves were already in the tree, on opposite sides of a
hypothesis that turned out to be false.  The content is that they compose. -/

section OrientedFullNuAtUnitPivot

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **P3 pays the unit-pivot hypothesis, arithmetically.**  The two `ν`-rows of the marked
forward supply give `ν_ur(f w) = 1` at the pivot exponent `c₀`, so the transported marking's
pivot row is a unit.  This is the input `SqNuOrientedClearAtUnitPivot` asks for and — by
`SqCore.isUnit_toAdd_transported_sqPivot_iff` — the input no choice of `f` and no automorphism
of the model can manufacture. -/
theorem isUnit_toAdd_transportedNuUr_sqPivot (B : MarkedRecip Rec K) {h : ℕ}
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (hsigma : nuUrKTwo B (f (dsqSigma h)) = ofAdd (1 : ℤ_[2]))
    (hx0 : nuUrKTwo B (f (dsqX0 h)) = ofAdd (0 : ℤ_[2])) :
    IsUnit (toAdd (transportedNuUr B f (SqCore.sqPivot h))) := by
  show IsUnit (toAdd (nuUrKTwo B (f (MarkedCore.sqMixPivotElem h SqCore.sqPivotExp))))
  rw [nuUrKTwo_sqMixPivotElem_eq_one B f SqCore.sqPivotExp hsigma hx0, toAdd_ofAdd]
  exact isUnit_one

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **THE LIVE BRIDGE.**  One equivalence carrying the orientation *and* the whole marking, at
**every** handle count, over the corrected model-side residual and P3's marked forward supply.

Same three steps as §1, with the arbitrary oriented `f` replaced by the supply's selected one:
its pivot row is a unit (`isUnit_toAdd_transportedNuUr_sqPivot`), which is precisely the extra
hypothesis `SqNuOrientedClearAtUnitPivot` carries, and joint surjectivity is unchanged.  Neither
binder is refuted, so unlike §1 this statement is **non-vacuous at every `h`**. -/
theorem exists_orientedEquiv_fullNu_of_orientedClearAtUnitPivot (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hclear : SqCore.SqNuOrientedClearAtUnitPivot h) (hsupply : SqMarkedForwardSupply B h) :
    ∃ f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)),
      (∀ x, chiCycKTwo (K := K) (f x) = chiSq h x) ∧
        ∀ x, nuUrKTwo B (f x) = nuSq h x := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hr : B.r = 0 := B.level_eq_zero_of_odd_finrank FF hodd
  obtain ⟨f, horient, hsigma, hx0⟩ := hsupply
  obtain ⟨Ψ, hchi, hnu⟩ := hclear (transportedNuUr B f)
    (fun u y => jointSurjective_transportedNuUr B hodd hr f horient u y)
    (isUnit_toAdd_transportedNuUr_sqPivot B f hsigma hx0)
  refine ⟨Ψ.trans f, fun x => ?_, fun x => hnu x⟩
  show chiCycKTwo (K := K) (f (Ψ x)) = chiSq h x
  rw [horient (Ψ x), hchi x]

end OrientedFullNuAtUnitPivot

/-! ## §2 The minimal odd-degree residual, discharged -/

section Residual

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The odd-degree residual over the model-side hypothesis.**  `SqNuAdaptedFrameRelator B` is
the oriented full-`ν` equivalence (§6 of `GammaLNuAdaptedFrame`), and §1 builds one.

⚠ **Vacuous at `h ≥ 1`** (`SqCore.not_sqNuOrientedClear`); live at `h = 0`.  Replacement:
`sqNuAdaptedFrameRelator_of_orientedClearAtUnitPivot`. -/
theorem sqNuAdaptedFrameRelator_of_orientedClear (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hclear : SqCore.SqNuOrientedClear h) : SqNuAdaptedFrameRelator B := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hh : (Module.finrank ℚ_[2] K - 1) / 2 = h := by omega
  subst hh
  exact (sqNuAdaptedFrameRelator_iff_orientedFullNu B hodd).2
    (exists_orientedEquiv_fullNu_of_orientedClear B FF hdeg hclear)

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **§2′: the odd-degree residual, non-vacuously.**  Same reading through §6's
characterization, over §1′'s live bridge. -/
theorem sqNuAdaptedFrameRelator_of_orientedClearAtUnitPivot (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hclear : SqCore.SqNuOrientedClearAtUnitPivot h) (hsupply : SqMarkedForwardSupply B h) :
    SqNuAdaptedFrameRelator B := by
  have hodd : Odd (Module.finrank ℚ_[2] K) := Nat.odd_iff.mpr (by omega)
  have hh : (Module.finrank ℚ_[2] K - 1) / 2 = h := by omega
  subst hh
  exact (sqNuAdaptedFrameRelator_iff_orientedFullNu B hodd).2
    (exists_orientedEquiv_fullNu_of_orientedClearAtUnitPivot B FF hdeg hclear hsupply)

end Residual

/-! ## §3 The endpoint, and the `h = 0` face -/

section Endpoint

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **THE ODD-DEGREE ROW OVER A MODEL-SIDE HYPOTHESIS.**  `Γ_{R_K} ≅ G_K` for every odd-degree
ramified `K` at the type-`L` level `r = 0`, over `SqCore.SqNuOrientedClear h` alone (plus the
packet's structural pair `T`, `ramifiedData`).  The hypothesis mentions no field: it is a
statement about `D_sq(h)`, `χ_sq`, `ν_sq` and continuous automorphisms.

⚠ **Vacuous at `h ≥ 1`** (`SqCore.not_sqNuOrientedClear`); live at `h = 0`, which is what
`gammaR_lSq_equiv_galK_degreeOne_of_pivotMoves` below uses.  The live `h ≥ 1` endpoint is
`gammaR_lSq_equiv_galK_oddDegree_of_orientedClearAtUnitPivot`; the price of non-vacuity is that
the hypothesis list is no longer purely model-side — it acquires P3's `SqMarkedForwardSupply`,
and `PivotClimb` §9 shows that acquisition is forced, not stylistic. -/
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

/-- **§3′: THE LIVE ODD-DEGREE ENDPOINT.**  `Γ_{R_K} ≅ G_K` for every odd-degree ramified `K` at
the type-`L` level `r = 0`, over the **corrected** model-side residual
`SqCore.SqNuOrientedClearAtUnitPivot h` together with P3's marked forward supply.  Neither
hypothesis is refuted, so this holds non-vacuously at every handle count — and at `h = 0` it
agrees with `gammaR_lSq_equiv_galK_oddDegree_of_orientedClear` via
`SqCore.sqNuOrientedClear_zero_of_atUnitPivot`. -/
theorem gammaR_lSq_equiv_galK_oddDegree_of_orientedClearAtUnitPivot (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hclear : SqCore.SqNuOrientedClearAtUnitPivot h) (hsupply : SqMarkedForwardSupply B h)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma h (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_oddDegree_of_nuAdaptedFrameRelator B T D hdeg
    (sqNuAdaptedFrameRelator_of_orientedClearAtUnitPivot B FF hdeg hclear hsupply) ramifiedData

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

The two model-side statements and the two routes they feed, pinned side by side.

⚠ The three pins taking `H : SqCore.SqNuOrientedClear h` at a *general* `h` are **known-vacuous**
(`SqCore.not_sqNuOrientedClear`).  In particular the first one — the
`orientedClear → jointClearing` bridge — is vacuous at `h ≥ 1`, though its **conclusion**
`SqNuJointClearing h` is *not* refuted and keeps its own live producers; only this route into it
dies.  The `h = 0` pins, and the two new `…AtUnitPivot` pins at the end, are genuine. -/

section StressTests

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The oriented model statement implies the plain joint one, so this file's route subsumes
`GammaLOddDegreeJointClearing`'s.  **⚠ Known-vacuous at `h ≥ 1`** — the *bridge* dies, the
target `SqNuJointClearing h` does not. -/
example (h : ℕ) (H : SqCore.SqNuOrientedClear h) : SqNuJointClearing h :=
  SqCore.sqNuJointClear_of_orientedClear H

/-- Route B (the joint one) lands in the unoriented supply.  **⚠ Known-vacuous at `h ≥ 1`.** -/
example (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (H : SqCore.SqNuOrientedClear h) :
    MarkingAudit.SqFullNuForwardSupply B h :=
  sqFullNuForwardSupply_of_jointClearing B FF hdeg (SqCore.sqNuJointClear_of_orientedClear H)

/-- Route C (this file) lands on the oriented residual itself.  **⚠ Known-vacuous at
`h ≥ 1`.** -/
example (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (H : SqCore.SqNuOrientedClear h) :
    SqNuAdaptedFrameRelator B :=
  sqNuAdaptedFrameRelator_of_orientedClear B FF hdeg H

/-- **Route C′ (live at every `h`)**: the corrected residual plus P3's marked supply lands on the
same object, non-vacuously. -/
example (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) (H : SqCore.SqNuOrientedClearAtUnitPivot h)
    (S : SqMarkedForwardSupply B h) : SqNuAdaptedFrameRelator B :=
  sqNuAdaptedFrameRelator_of_orientedClearAtUnitPivot B FF hdeg H S

/-- **The `h = 0` faces agree**: there the corrected residual gives the old one back, so §1′ is a
strict extension of §1, not a fork. -/
example (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (hdeg : Module.finrank ℚ_[2] K = 1) (H : SqCore.SqNuOrientedClearAtUnitPivot 0) :
    SqNuAdaptedFrameRelator B :=
  sqNuAdaptedFrameRelator_of_orientedClear B FF (by omega)
    (SqCore.sqNuOrientedClear_zero_of_atUnitPivot H)

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
#print axioms GQ2.Dyadic.LSquare.NuAdapted.isUnit_toAdd_transportedNuUr_sqPivot
open GQ2.Dyadic.LSquare.NuAdapted in
#print axioms exists_orientedEquiv_fullNu_of_orientedClearAtUnitPivot
open GQ2.Dyadic.LSquare.NuAdapted in
#print axioms sqNuAdaptedFrameRelator_of_orientedClearAtUnitPivot
open GQ2.Dyadic.LSquare.NuAdapted in
#print axioms gammaR_lSq_equiv_galK_oddDegree_of_orientedClearAtUnitPivot

end GQ2.Dyadic.LSquare
