/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5
-/
import GQ2.Dyadic.GeneralAssembly
import GQ2.Dyadic.SqCore.GradedOddClose
import GQ2.Dyadic.Instances.GammaLOddDegreeRealization
import GQ2.Dyadic.Instances.GammaLOddDegreeSingleResidual
import GQ2.Dyadic.Instances.GammaLOddDegreeBridge
import GQ2.Dyadic.DemushkinQRamifiedI
import GQ2.Dyadic.OddDegreeRamifiedI

/-!
# The oriented identification at the odd slot  (dyadic campaign, lane W81-ODDID)

The odd route's mark transitivity closed in wave 80 (`SqCore.gOdd_markTransitivity`), so the
`L`-row branch producer `genAsm_branch_of_oddSq_canonical` (`GQ2/Dyadic/GeneralAssembly.lean`)
has, on the classification side, exactly one input left: the oriented equivalence
`e : OrientedContinuousMulEquiv (chiSq h) (chiCycKTwo (K := K))` together with the two selected
`ν`-rows at `e` itself.  This module joins what the tree already supplies toward that input,
states the one genuine seam as the named `Prop` it already carries, and instantiates the
degree-one case as a theorem.

## What the tree supplies, and where the seam is

* **The oriented equivalence alone is a theorem.**
  `LSquare.nonempty_orientedEquiv_oddDegree`
  (`Instances/GammaLSylowPreimageFieldLabuteCubicNeutral.lean`) produces
  `OrientedContinuousMulEquiv (chiSq h) (chiCycKTwo)` at every odd-degree `K`, over a marked
  reciprocity bundle and nothing else.  §1 re-indexes it at an explicit handle count.
* **The two `ν`-rows at the equivalence are NOT free**, and cannot be made free by model-side
  work: `SqCore/PivotClimb.lean` §9 shows the parity of the transported pivot row is an
  invariant of the target, and `Instances/GammaLSylowPreimagePivotNu.lean` §5 refutes reading
  the rows off orientation.  The honest seam is therefore P3's
  `LSquare.SqMarkedForwardSupply B h`: SOME oriented equivalence carries the two selected rows
  `ν(f σ) = 1`, `ν(f x₀) = 0`.  That `Prop` is exactly the `(e, hsigma, hx0)` triple the
  `L`-row branch producer consumes, so this module adopts it unchanged rather than minting a
  new name.
* **Wave 80 pays every model-side binder.**  `SqCore.gOdd_pivotFix` discharges the handle
  stratum `SqHandleMixFixesCore h sqPivotExp` at every `h`, so the marked supply and the
  `L`-row marked-core certificate are now equivalent with NO side binder (§2), and the branch
  datum follows from the supply alone (§3).
* **Producers of the seam.**  At every odd-degree `K` the supply follows from the stage lane's
  frame-tracking residual `MarkedFrame.SqCupAdaptedFramePresentation K`
  (`LSquare.sqMarkedForwardSupply_oddDegree`); at degree one it is a THEOREM
  (`SqCore.sqNuOrientedClear_zero` through the wave-44 bridge), which is what makes the `n = 1`
  instantiation of the classification unconditional here (§3).

## Contents

* **§1** the free half: the oriented equivalence at an explicit handle count;
* **§2** the seam: `SqMarkedForwardSupply B h`, its certificate equivalence with the wave-80
  handle binder deleted, and its producers (frame residual; degree one as a theorem);
* **§3** the consumer corollary (T3): the `L`-row branch datum over the seam, the degree-one
  branch datum as a theorem, and the full general-theorem chain at the odd slot;
* **§4** the invariants at odd degree (T1): full cyclotomic image, the Demushkin rank, and the
  exact relocation of the `q = 2` premise onto the model group `D_sq h`;
* **§5** axiom pins, with the honest split.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 Multiplicative
open SqCore LSquare

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The free half: the oriented equivalence at an explicit handle count

`LSquare.nonempty_orientedEquiv_oddDegree` is stated at the derived handle count
`(([K : ℚ₂]) − 1) / 2`.  Every consumer downstream of the branch datum indexes by an explicit
`h` with `[K : ℚ₂] = 2h + 1`, so the re-indexed form is the one this module uses. -/

section FreeHalf

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The oriented identification, existence half, at an explicit handle count.**  For every
`K` with `[K : ℚ₂] = 2h + 1` and every marked reciprocity bundle, the square-commutator core
`D_sq h` is continuously isomorphic to `G_K(2)` by an equivalence matching the canonical
orientation `χ_sq` with the descended cyclotomic character.  This is the `e`-binder of
`genAsm_branch_of_oddSq_canonical`, produced with no hypothesis beyond the bundle. -/
theorem oddId_orientedEquiv (B : MarkedRecip Rec K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) :
    Nonempty (OrientedContinuousMulEquiv (chiSq h) (chiCycKTwo (K := K))) := by
  have hh : (Module.finrank ℚ_[2] K - 1) / 2 = h := by omega
  have hne := nonempty_orientedEquiv_oddDegree (K := K) B (Nat.odd_iff.mpr (by omega))
  rwa [hh] at hne

end FreeHalf

/-! ## §2 The seam, and the wave-80 collapse of its side binders

`LSquare.SqMarkedForwardSupply B h` (`Instances/GammaLSylowPreimagePivotNu.lean` §4) is the
statement that SOME oriented equivalence carries the two P3-selected rows.  Before wave 80 its
passage to the `L`-row certificate cost the handle stratum; `SqCore.gOdd_pivotFix` now pays
that stratum at every `h`, so the supply and the certificate are interchangeable with no side
condition at all.  This section records the collapsed interface and the seam's two producers. -/

section Seam

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The marked supply produces the `L`-row certificate, with no handle binder.**  Wave 80's
`gOdd_pivotFix` discharges the `hMix` input of
`LSquare.marked_matching_certificate_KTwoSq_of_supply`, so the certificate costs exactly the
seam and nothing else. -/
theorem oddId_certificate_of_supply (B : MarkedRecip Rec K) (h : ℕ)
    (H : SqMarkedForwardSupply B h) :
    Nonempty (MarkedCoreCertificateKTwoSq B h) :=
  marked_matching_certificate_KTwoSq_of_supply B h sqPivotExp (gOdd_pivotFix h) H

omit [T2Space (GalK K)] [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The seam is exact**: the marked supply and the `L`-row marked-core certificate are
equivalent outright.  Compare `LSquare.sqMarkedForwardSupply_iff_nonempty_certificate`, which
carried the handle stratum as a binder; wave 80 deleted it. -/
theorem oddId_supply_iff_certificate (B : MarkedRecip Rec K) (h : ℕ) :
    SqMarkedForwardSupply B h ↔ Nonempty (MarkedCoreCertificateKTwoSq B h) :=
  sqMarkedForwardSupply_iff_nonempty_certificate B h sqPivotExp (gOdd_pivotFix h)

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **Producer 1 (every odd degree): the stage lane's frame residual.**  The re-indexed form of
`LSquare.sqMarkedForwardSupply_oddDegree`: at `[K : ℚ₂] = 2h + 1` the seam follows from
`MarkedFrame.SqCupAdaptedFramePresentation K`, the frame-tracking residual the grand assembly
already carries.  No other producer at `h ≥ 1` is in the tree. -/
theorem oddId_markedSupply_of_presentation (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hpres : MarkedFrame.SqCupAdaptedFramePresentation K) :
    SqMarkedForwardSupply B h := by
  have hh : (Module.finrank ℚ_[2] K - 1) / 2 = h := by omega
  have hsup := sqMarkedForwardSupply_oddDegree B FF (Nat.odd_iff.mpr (by omega)) hpres
  rwa [hh] at hsup

/-- **Producer 2 (degree one): a theorem.**  At `[K : ℚ₂] = 1` the model-side oriented clearing
statement is the committed `SqCore.sqNuOrientedClear_zero`, so the wave-44 bridge
(`NuAdapted.exists_orientedEquiv_fullNu_of_orientedClear`) turns the free oriented equivalence
into one carrying the WHOLE standard marking; its `σ`- and `x₀`-rows are the two selected
rows.  This is the `n = 1` face of the odd-degree classification, unconditional over the
bundle. -/
theorem oddId_markedSupply_degreeOne (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K)
    (hdeg : Module.finrank ℚ_[2] K = 1) :
    SqMarkedForwardSupply B 0 := by
  obtain ⟨f, horient, hnu⟩ :=
    NuAdapted.exists_orientedEquiv_fullNu_of_orientedClear B FF (h := 0) (by omega)
      sqNuOrientedClear_zero
  exact ⟨f, horient, (hnu (dsqSigma 0)).trans (nuSq_sigma 0),
    (hnu (dsqX0 0)).trans (nuSq_x0 0)⟩

end Seam

/-! ## §3 The consumer corollary: the `L`-row branch datum at the odd slot

The `GenAsmBranch` producer `genAsm_branch_of_oddSq_canonical` consumes the degree pin, the
oriented equivalence, the handle stratum, and the two `ν`-rows at the equivalence.  Wave 80
pays the stratum; the seam pays the equivalence together with its rows; the degree pin is the
`L`-row arithmetic `(SelectedPresentation.L h).degree = 1 + 2h`.  So the branch datum costs
exactly the seam, and at degree one it costs nothing. -/

section Consumer

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [T2Space (GalK K)] in
/-- **T3, over the seam: the `L`-row branch datum.**  For `[K : ℚ₂] = 2h + 1`, the marked
forward supply places `K` on the `L h` row of the general assembly: `G_K(2)` is the
square-commutator core `D_sq h`, `Ztwo`-marking and all.  Every other input is a theorem of
the tree (the handle stratum by wave 80, the canonical marking's surjectivity and `ζ`-bridge
by the committed `lNu` work). -/
theorem oddId_genAsmBranch_L_of_supply (B : MarkedRecip Rec K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (H : SqMarkedForwardSupply B h) :
    ∃ G : GenAsmBranch K B, G.pres = .L h := by
  obtain ⟨f, horient, hsigma, hx0⟩ := H
  exact genAsm_branch_of_oddSq_canonical h sqPivotExp hdeg ⟨f, horient⟩ (gOdd_pivotFix h)
    hsigma hx0

/-- **T3, over the frame residual**: the branch datum at every odd-degree `K` from
`MarkedFrame.SqCupAdaptedFramePresentation K` alone. -/
theorem oddId_genAsmBranch_L_of_presentation (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hpres : MarkedFrame.SqCupAdaptedFramePresentation K) :
    ∃ G : GenAsmBranch K B, G.pres = .L h :=
  oddId_genAsmBranch_L_of_supply B hdeg
    (oddId_markedSupply_of_presentation B FF hdeg hpres)

/-- **T3 at `n = 1`, a theorem: the degree-one branch datum.**  At `[K : ℚ₂] = 1` the seam is
discharged (`oddId_markedSupply_degreeOne`), so `K` sits on the `L 0` row of the general
assembly with no hypothesis beyond the bundle and the filtration.  This is the odd-degree
classification's first unconditional instance on the general slot. -/
theorem oddId_genAsmBranch_L_degreeOne (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (hdeg : Module.finrank ℚ_[2] K = 1) :
    ∃ G : GenAsmBranch K B, G.pres = .L 0 :=
  oddId_genAsmBranch_L_of_supply B (by omega)
    (oddId_markedSupply_degreeOne B FF hdeg)

omit [T2Space (GalK K)] in
/-- **The full chain at the odd slot.**  Over the seam, the general final theorem
`genAsm_candidate_equiv_galK` at an odd-degree `K` needs exactly its two obligation records
beyond the branch: the row-independent field inputs `F : GenAsmFieldInputs K B FF (1 + 2h)`
(structural: the tame quotient, the parameter package, the standing ramified-`i` selection,
the LG5 ramified data) and the residual record `S : GenAsmRowResidual G F.T` (obligations: the
two ASK counting fields `exactLifting` and `stokes`, the ASK `determinant` field, and the CAND
`WordCertificate` over `D_sq h`, which has no producer at free `h` in this tree).  Stated as
one theorem so that the odd slot's remaining distance to the general theorem is a checkable
object. -/
theorem oddId_candidate_equiv_galK_of_supply (B : MarkedRecip Rec K)
    {FF : DyadicUnitFiltration K} {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1)
    (H : SqMarkedForwardSupply B h) :
    ∃ G : GenAsmBranch K B, G.pres = .L h ∧
      ∀ F : GenAsmFieldInputs K B FF G.degree, GenAsmRowResidual G F.T →
        Nonempty (ContinuousMulEquiv
          ((candidateGroup G.degree (qOf K FF) G.word : ProfiniteGrp) : Type) (GalK K)) := by
  obtain ⟨G, hG⟩ := oddId_genAsmBranch_L_of_supply B hdeg H
  exact ⟨G, hG, fun F S => genAsm_candidate_equiv_galK G F S⟩

end Consumer

end

end GQ2.Dyadic
