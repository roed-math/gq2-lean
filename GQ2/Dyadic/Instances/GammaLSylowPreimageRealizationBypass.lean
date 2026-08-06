/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageMarkedFrame
import GQ2.Dyadic.Instances.Cores
import GQ2.Dyadic.SqCore.ChiFreeClearing

/-!
# P4 — the realization bypass: the `L_sq` pro-2 block without the certificate

**The route-adjudication endpoint** (companion to `GQ2/Dyadic/SqCore/ChiFreeClearing.lean`,
which records the full verdict).  The certificate lane's downstream consumer is not the
certificate: it is `MarkedCoreRealization (DSq h) (lNu h)`
(`GQ2/Dyadic/LabuteInterface.lean`), whose two fields carry the equivalence and the full
`ν`-matching and **no χ-clause**.  Its four exported theorems are exactly the
`KExactSupplyRN` pro-2 block (`pro2`/`hpro2`/`ker_pro2`/`nu_compat`,
`GQ2/Dyadic/Instances/KAnalytic.lean`) at the L-row slot
`(DSq h, lNu h)` that `CertificateSupplyRN.ofL` and `GammaLCorrectedArithmeticInput` pin.
This file proves the bypass:

* `ztwoIota_lNu` — the `Ztwo`-normalization bridge `ι ∘ lNu = ν_sq`, the previously
  uninstantiated `hnuP` slot of `MarkedCoreRealization.ofCertificateSq`;
* `SqNuForwardSupply` — the χ-free arithmetic supply (the two selected `ν`-rows on *some*
  equivalence, no orientation clause), with `sqMarkedForwardSupply`'s forgetful map **and**
  the sharp converse `sqNuForwardSupply_of_realization`: the realization *produces* the
  χ-free supply, so modulo the clearing binder the interface is exact;
* `markedCoreRealization_of_nuSupply` / `markedCoreRealization_of_supply` — **the bypass
  theorem**: χ-free supply + `SqNuClearHypothesis` gives the realization directly.  The
  marked supply's orientation clause is *discarded* (the underscore in the proof is the
  P2-lane dissolution: the χ-preservation half of the handle stratum served only the
  certificate's χ-fields, which nothing downstream consumes);
* `markedCoreRealization_of_certificate` — the regression: the certificate still reaches
  the same endpoint through `ofCertificateSq` and the bridge, so the bypass strictly
  extends the old route;
* `markedCoreRealization_of_cupOne_of_presentation` — the frame-chain endpoint: over the
  two named `MarkedFrame` residuals and the χ-free clearing binder, odd-degree type-`L`
  fields carry the full pro-2 block.  At `h = 0` the clearing binder is a theorem
  (`sqNuClearHypothesis_zero`), so the rank-three supply alone suffices
  (`markedCoreRealization_of_supply_zero`).

## The residual surface after this file

| input | status |
|---|---|
| `SqNuForwardSupply` (two `ν`-rows) | from `SqMarkedForwardSupply`; frame chain, P3 |
| `SqNuClearHypothesis h` | **the** residual binder; χ-free seed search (`SqNuSeed`) |
| `h = 0` | no binder at all |

The χ-preserving strata (`SqHandleMixFixesCore`, `SqHandleEichler`, `SqEichlerSeed`) all
still *imply* the clearing binder (`ChiFreeClearing.lean` §1–§4), but they are no longer the
target: the seed search should be re-run on `SqNuSeed`'s strictly wider ansatz.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`.  The bridge and the bypass theorems print
**std-3**; the frame-chain endpoint prints whatever
`MarkedFrame.oddDegreeGalKSqMarkedForwardSupply` carries, exactly as recorded by the
committed `#print axioms` block.  Census unchanged at **11**.
-/

namespace GQ2.Dyadic.LSquare

open GQ2 GQ2.Dyadic SqCore MarkedCore Multiplicative

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable section

/-! ## §1 The `Ztwo`-normalization bridge

`lNu h` (`GQ2/Dyadic/Instances/Cores.lean`) is the canonical `Ztwo`-coordinate of the L-row
slot; `ν_sq` is the standard `Multiplicative ℤ_[2]`-marking of the core.  The bridge is the
generator-wise identification through `ztwoIota`, and it is the `hnuP` input that
`MarkedCoreRealization.ofCertificateSq` has been waiting for. -/

section Bridge

/-- **The bridge**: `ζ`-normalization of the canonical `Ztwo`-coordinate is the standard
marking, `ι(lNu(x)) = ν_sq(x)` for every `x`. -/
theorem ztwoIota_lNu (h : ℕ) (x : (DSq h : Type)) :
    ztwoIota (Instances.LSquareCore.lNu h x) = nuSq h x := by
  have hgen : ∀ i, Instances.LSquareCore.lNu h (sqGen h i)
      = SqCore.sqMark ztwoOne 1 1 i := fun i => by
    rw [Instances.LSquareCore.lNu, SqCore.sqLiftHom_gen]
  have hext : (⟨ztwoIota.toMulEquiv.toMonoidHom, ztwoIota.continuous_toFun⟩ :
      ContinuousMonoidHom Ztwo (Multiplicative ℤ_[2])).comp (Instances.LSquareCore.lNu h)
      = nuSq h := by
    refine dsq_hom_ext _ _ fun i => ?_
    show ztwoIota (Instances.LSquareCore.lNu h (sqGen h i)) = nuSq h (sqGen h i)
    rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [hgen, sqMark_zero, ztwoIota_ztwoOne,
        show sqGen h 0 = dsqSigma h from rfl, nuSq_sigma]
    · rw [hgen, sqMark_one, map_one, show sqGen h 1 = dsqX0 h from rfl, nuSq_x0]
      rfl
    · rw [hgen, sqMark_two, map_one, show sqGen h 2 = dsqX1 h from rfl, nuSq_x1]
      rfl
    · rw [hgen, sqMark_handleU, map_one, nuSq_handleU]
    · rw [hgen, sqMark_handleV, map_one, nuSq_handleV]
  exact DFunLike.congr_fun hext x

end Bridge

/-! ## §2 The χ-free supply, the bypass, and the sharp converse -/

section Bypass

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **The χ-free arithmetic supply** (a `def`-shaped `Prop`, never an axiom): *some*
equivalence of the `L_sq` core with `G_K(2)` carries the two selected unramified rows.  This
is `SqMarkedForwardSupply` minus its orientation clause — exactly what the realization can
still see. -/
def SqNuForwardSupply (B : MarkedRecip R K) (h : ℕ) : Prop :=
  ∃ f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)),
    nuUrKTwo B (f (dsqSigma h)) = ofAdd (1 : ℤ_[2]) ∧
      nuUrKTwo B (f (dsqX0 h)) = ofAdd (0 : ℤ_[2])

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The marked (oriented) supply forgets to the χ-free supply. -/
theorem sqNuForwardSupply_of_marked {B : MarkedRecip R K} {h : ℕ}
    (H : SqMarkedForwardSupply B h) : SqNuForwardSupply B h := by
  obtain ⟨f, _, hsigma, hx0⟩ := H
  exact ⟨f, hsigma, hx0⟩

/-- **The bypass theorem.**  The χ-free supply and the χ-free clearing binder produce the
L-row realization directly: transport the arithmetic marking through `f`, clear it onto
`ν_sq` by the binder, and read the corrected equivalence back through the bridge.  No
certificate is built, and no χ-clause is consumed anywhere. -/
theorem markedCoreRealization_of_nuSupply (B : MarkedRecip R K) (h : ℕ)
    (hclear : SqNuClearHypothesis h) (H : SqNuForwardSupply B h) :
    Nonempty (MarkedCoreRealization (K := K) (B := B) (DSq h)
      (Instances.LSquareCore.lNu h)) := by
  obtain ⟨f, hsigma, hx0⟩ := H
  obtain ⟨Ψ, hΨ⟩ := hclear (transportedNuUr B f) hsigma hx0
  exact ⟨⟨Ψ.trans f, fun x => by rw [ztwoIota_lNu h x, ← hΨ x]; rfl⟩⟩

/-- The bypass from the marked supply of P3: the orientation clause is **discarded** — this
underscore is the P2-lane dissolution in one token. -/
theorem markedCoreRealization_of_supply (B : MarkedRecip R K) (h : ℕ)
    (hclear : SqNuClearHypothesis h) (H : SqMarkedForwardSupply B h) :
    Nonempty (MarkedCoreRealization (K := K) (B := B) (DSq h)
      (Instances.LSquareCore.lNu h)) :=
  markedCoreRealization_of_nuSupply B h hclear (sqNuForwardSupply_of_marked H)

/-- **The sharp converse**: a realization *produces* the χ-free supply — its equivalence
already carries both selected rows, by the bridge.  So, modulo the clearing binder, the
χ-free supply is exactly the arithmetic residue of the pro-2 block: no weaker interface can
suffice, and no orientation clause can be extracted back out of the block. -/
theorem sqNuForwardSupply_of_realization {B : MarkedRecip R K} {h : ℕ}
    (M : MarkedCoreRealization (K := K) (B := B) (DSq h) (Instances.LSquareCore.lNu h)) :
    SqNuForwardSupply B h := by
  refine ⟨M.equiv, ?_, ?_⟩
  · rw [← M.nu_equiv (dsqSigma h), ztwoIota_lNu, nuSq_sigma]
  · rw [← M.nu_equiv (dsqX0 h), ztwoIota_lNu, nuSq_x0]

/-- **The regression**: the certificate still reaches the same endpoint, through
`ofCertificateSq` at the bridge.  The bypass strictly extends the certificate route; it does
not fork it. -/
def markedCoreRealization_of_certificate (B : MarkedRecip R K) (h : ℕ)
    (C : MarkedCoreCertificateKTwoSq B h) :
    MarkedCoreRealization (K := K) (B := B) (DSq h) (Instances.LSquareCore.lNu h) :=
  MarkedCoreRealization.ofCertificateSq (Instances.LSquareCore.lNu h) (ztwoIota_lNu h) C

/-- At `h = 0` the clearing binder is a theorem, so the rank-three pro-2 block needs only
the supply. -/
theorem markedCoreRealization_of_supply_zero (B : MarkedRecip R K)
    (H : SqMarkedForwardSupply B 0) :
    Nonempty (MarkedCoreRealization (K := K) (B := B) (DSq 0)
      (Instances.LSquareCore.lNu 0)) :=
  markedCoreRealization_of_supply B 0 sqNuClearHypothesis_zero H

/-- Pricing: the χ-preserving one-binder stratum still discharges the bypass, at any
exponent. -/
theorem markedCoreRealization_of_supply_of_fixesCore (B : MarkedRecip R K) (h : ℕ)
    (c : ℤ_[2]) (hMix : SqHandleMixFixesCore h c) (H : SqMarkedForwardSupply B h) :
    Nonempty (MarkedCoreRealization (K := K) (B := B) (DSq h)
      (Instances.LSquareCore.lNu h)) :=
  markedCoreRealization_of_supply B h (sqNuClearHypothesis_of_fixesCore hMix) H

/-- Pricing: χ-free seeds at every parameter discharge the bypass. -/
theorem markedCoreRealization_of_supply_of_seeds (B : MarkedRecip R K) (h : ℕ)
    (hseeds : ∀ (j : Fin h) (k : ℤ_[2]), Nonempty (SqNuSeed h j k))
    (H : SqMarkedForwardSupply B h) :
    Nonempty (MarkedCoreRealization (K := K) (B := B) (DSq h)
      (Instances.LSquareCore.lNu h)) :=
  markedCoreRealization_of_supply B h (sqNuClearHypothesis_of_seeds hseeds) H

end Bypass

/-! ## §3 The frame-chain endpoint

`MarkedFrame.oddDegreeGalKSqMarkedForwardSupply` supplies the marked supply over the two
named frame residuals; composing with the bypass gives the full pro-2 block over those
residuals and the χ-free clearing binder alone.  (The cup residual is discharged
unconditionally in odd degree by `GammaLNuKummerIdentification.nuUrOmegaCupOne_of_odd`;
wiring that file in is a one-line follow-up left to the next assembly pass, to keep this
file's import cone inside the warm cache.) -/

section Endpoint

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **The frame-chain endpoint**: over the cup datum, the stage-lane presentation clause,
and the χ-free clearing binder, every odd-degree type-`L` field carries the L-row pro-2
block.  The χ-preserving handle strata appear nowhere. -/
theorem markedCoreRealization_of_cupOne_of_presentation (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) (hr : B.r = 0)
    (hclear : SqNuClearHypothesis ((Module.finrank ℚ_[2] K - 1) / 2))
    (hcup : MarkedFrame.NuUrOmegaCupOne B)
    (hpres : MarkedFrame.SqCupAdaptedFramePresentation K) :
    Nonempty (MarkedCoreRealization (K := K) (B := B)
      (DSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (Instances.LSquareCore.lNu ((Module.finrank ℚ_[2] K - 1) / 2))) :=
  markedCoreRealization_of_supply B _ hclear
    (MarkedFrame.oddDegreeGalKSqMarkedForwardSupply B hodd hr hcup hpres)

end Endpoint

end

/-! ## §4 Stress pins -/

section StressTests

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The bridge at the three core letters, `h = 1`. -/
example : ztwoIota (Instances.LSquareCore.lNu 1 (dsqSigma 1)) = ofAdd (1 : ℤ_[2]) :=
  (ztwoIota_lNu 1 (dsqSigma 1)).trans (nuSq_sigma 1)

example : ztwoIota (Instances.LSquareCore.lNu 1 (dsqX0 1)) = ofAdd (0 : ℤ_[2]) :=
  (ztwoIota_lNu 1 (dsqX0 1)).trans (nuSq_x0 1)

example : ztwoIota (Instances.LSquareCore.lNu 1 (dsqX1 1)) = ofAdd (0 : ℤ_[2]) :=
  (ztwoIota_lNu 1 (dsqX1 1)).trans (nuSq_x1 1)

/-- The bypass at one handle, written out: χ-free supply + χ-free clearing, no χ-clause. -/
example (B : MarkedRecip R K) (hclear : SqNuClearHypothesis 1)
    (H : SqNuForwardSupply B 1) :
    Nonempty (MarkedCoreRealization (K := K) (B := B) (DSq 1)
      (Instances.LSquareCore.lNu 1)) :=
  markedCoreRealization_of_nuSupply B 1 hclear H

/-- The interface is exact modulo the binder: realization back to χ-free supply. -/
example (B : MarkedRecip R K)
    (M : MarkedCoreRealization (K := K) (B := B) (DSq 1) (Instances.LSquareCore.lNu 1)) :
    SqNuForwardSupply B 1 :=
  sqNuForwardSupply_of_realization M

end StressTests

/-! ## §5 Axiom pins

Committed prints: the bridge, the bypass, and the converse are **std-3**; the frame-chain
endpoint carries the `MarkedFrame` assembly's prints.  Census unchanged at **11**. -/

section AxiomPins

#print axioms ztwoIota_lNu
#print axioms sqNuForwardSupply_of_marked
#print axioms markedCoreRealization_of_nuSupply
#print axioms markedCoreRealization_of_supply
#print axioms sqNuForwardSupply_of_realization
#print axioms markedCoreRealization_of_certificate
#print axioms markedCoreRealization_of_supply_zero
#print axioms markedCoreRealization_of_supply_of_fixesCore
#print axioms markedCoreRealization_of_supply_of_seeds
#print axioms markedCoreRealization_of_cupOne_of_presentation

end AxiomPins

end GQ2.Dyadic.LSquare
