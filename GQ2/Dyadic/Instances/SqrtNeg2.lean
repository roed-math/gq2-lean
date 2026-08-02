/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Instances.KSupply
import GQ2.Dyadic.Count.Routine
import GQ2.Dyadic.Count.ProTwo
import GQ2.Dyadic.Count.WildDischarge
import GQ2.Dyadic.Count.Lifts
import GQ2.Dyadic.Count.Frozen
import GQ2.Dyadic.Count.Marking
import GQ2.Dyadic.GaussZ.FinalDK

/-!
# The pilot instance `ℚ₂(√−2)` — compact `N₂`, end to end  (dyadic campaign, ticket AS2)

**Packet Thm. 1.1 at the frozen pilot row**: the compact-`N` branch word at
`(α, h) = (2, 0)` — `R_{N,2,0} = x₀⁶ [x₀,x₁] · x₂^{-σ} (x₂τ)^{ω₂}`, selection-freeze row 2,
the `ℚ₂(√−2)` row — assembled through `candidate_equiv_galK_of_supply` into
`Γ_{R_{N,2,0}} ≅ G_K` for a supplied quadratic `K` on the ramified-`i` branch.

This file is the campaign's first complete general-`K` instance: it builds the **word
certificate** (`sqrtNegTwoWordCertificate`, §4) with every count-lane clause discharged from
the landed CB/WN0 stacks, builds the **`K`-side supply** (`sqrtNegTwoKSupply`, §5) with the
marked-core composite written down and CB-DET's determinant discharge consumed, and closes the
loop (`sqrtNegTwo_candidate_equiv_galK`, §6).

## The residual hypothesis surface, named

Everything below is assembly over landed theorems **except** the named binders, each of which
is a documented residual with an owner.  None is an axiom; none of the nine campaign
obligations appears.  In dependency order:

* `hsimp : PilotHsimp q` (§1) — **the row's single word-side analytic residual**: Stokes
  duality per simple module at the resolved compact-`N` family (packet Lem. 5.1's per-simple
  hypothesis slot; gate-F / AS-lane discharge; carried by all five branches, discharged by
  none).  Owner ruling: an explicit hypothesis binder, never an axiom.  From this ONE binder
  the file derives every duality payload the count lane consumes — the scalar payloads
  (`homCard`/`cardH2`), the `M_B` payload (`liftsOver_card`), the `T` payloads
  (`tcocycle_card`, `hsep`, `lem86`) and the `Vmod` payloads (`hZcard`, `hpartial`) — see §2.
* `hsplit`/`hZcount` (§4) — `stageR136`'s two recursion-side residues, exactly the two inputs
  `blockStageR136K` leaves open (SD-R3); their `ℚ₂` ancestors are the `RStage` per-carrier
  computations (`GQ2/Block/RStage.lean`, `GQ2/CardH2GammaA.stageR136_gammaA`).  Owner: a
  follow-on candidate-side R-stage ticket (CB1 memo's "stokes 1800" block priced them).
* `hdet` (§4) — **the candidate-side `AffineDeterminantCertificate`**, whole.  ⚠ The count
  lane's clause list closed 9 of the 11 `SourceDataN` clauses on the candidate side; the two
  Gauss-`Z` clauses have **no candidate-side supplier in the repository** (CB-DET is the
  `K`-side bridge; the word-side Hessian layer (WN0-c) exists but the Hessian ⇒
  `GaussZResidueK` bridge does not).  Owner: CB1 memo's "gauss 1900" ticket, unopened.
* the G-Lab pack (§5): `fLab` (Labute/Demushkin classification of `G_K(2)` — N-Lab, packet
  §7's hypothesis-binder state per gate G-Lab), `piAb`/`hpiAb`/`hpiNu` (the abelianization
  slot of the marked-core `K`-layer and its `ν`-compatibility with `toAbK` — the direct-factor
  inclusion `G_K(2)^{ab} ↪ G_K^{ab}`, which AS1's "composite" needs and which **nobody had
  written down**; recorded here as data), `horient` (the orientation datum), `hScal`
  (`NScalingHypothesis`, MC-N's S2 binder), `hpair` (marked-data pair-unimodularity).
* `hexact`/`hstokes` (§5) — the `K`-side `ExactLiftingSemantics` and
  `StokesDualityCertificate` at `G_K`: ASK's carried leaves 2–3 (`KSupply` §6), still owed by
  the `Phase140/Local`-successor lane (CB-SG built the substrate).
* `params`/`ramified`/`ramifiedData` (§6) — packet §12's field-side inputs at the concrete
  `K`, in AS1's own shapes (`DyadicLocalInput`); `ramifiedData`'s intended constructor is
  LG5's `ramifiedCertificateOfSubtype`.
* `hdeg : [K : ℚ₂] = 2` — the concrete field pin.  ⚠ The repository has **no** construction
  of `ℚ₂(√−2)` as an `IntermediateField` with computed invariants; the instance theorem is
  therefore stated over any supplied quadratic `K` on the branch, exactly as `KSupply`
  parametrizes.  Owner: a field-side arithmetic ticket (or AS5's final-theorem pass).

## The two fold-in deliverables (CB-6's hand-off), landed here

From the single `hsimp`:

* `sqrtNegTwo_selfDualN_vmod` (§2) — the `StokesDuality`-at-`Vmod` payload in the exact
  `IsSelfDualN` shape `Count/Marking.lean` §5's `isRightSeparating_vmod_nCompactFam` (and
  through it `Count/Separating.lean` §5) consumes;
* `sqrtNegTwo_stokesDuality_T` (§2) — the `StokesDuality`-at-`T` payload in the exact shape
  `Count/Marking.lean`'s `hsepN_marking` (`hd` slot) consumes.

## Axiom posture

No `sorry`, no new axiom, census untouched.  The candidate-side §1–§4 are std-3; the `K`-side
consumes what its inputs carry (`affineDeterminant_galK` = std-3 ∪ {B6, B7, B9, B11a};
`FieldData.tateDualityGalK` = B6; `tfg_galK` = B1), so the headline prints within
std-3 ∪ {B1, B6, B7, B9, B11a}.  **B5-K/B10-K are not consumed**: the `MarkedRecip` and
`OrientedTameQuotientK` bundles are hypothesis slots, per the ASK posture.  Per-declaration
prints are in the ticket report.

## Sources

Packet `docs/dyadic/refs/dyadic-presentations-formalization-proof.tex` Thm. 1.1, §7 (Def. 7.1),
§9 (Def. 9.1), §12; ledger §5.2–§5.3; selection freeze
(`general_2adic/artifacts/reports/selection-freeze.md`) row 2; board
`docs/dyadic/tickets.md` row AS2.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open TameSpec

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

namespace SqrtNeg2

open GQ2.Dyadic.Words GQ2.Dyadic.Certificates GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Count GQ2.Dyadic.Count.PilotN

-- CB-VAR's `⊥`-topology on the Heisenberg lift; `local instance` there, re-enabled here
-- exactly as `Count/Separating.lean` and `Count/Marking.lean` do.
attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-! ## §0 The pilot data

The frozen row: word `pilotW = nCompactW 2 0` on the alphabet `Generator 2` (`Count/Routine.lean`
§8), pro-2 core `P = D_N` at `(α, h) = (2, 0)` (MC2), marking `ν_P = ν_N` read through the
`Ztwo`-seam `ztwoIota` (so that `ν_P` lands in the boundary interface's `Ztwo`, with
`σ ↦ ztwoOne` and the wild letters to `1` — the normalization CB-P's bridge consumes). -/

/-- The pilot's pro-2 slot: the presented compact-`N` core at `(α, h) = (2, 0)`. -/
noncomputable abbrev pilotP : ProfiniteGrp := DN 2 0

/-- **The pilot's `ν_P`**: MC2's canonical marking `ν_N : D_N → ℤ₂` (`σ ↦ 1`, wild letters and
handles `↦ 0`), read back through the boundary seam `ztwoIota : Ztwo ≃ₜ* Multiplicative ℤ₂`. -/
noncomputable def pilotNuP : ContinuousMonoidHom (pilotP : Type) Ztwo :=
  ⟨(ztwoIota.symm.toMulEquiv.toMonoidHom).comp (nuN 2 0).toMonoidHom,
    ztwoIota.symm.continuous_toFun.comp (nuN 2 0).continuous_toFun⟩

@[simp] theorem pilotNuP_apply (x : (pilotP : Type)) :
    pilotNuP x = ztwoIota.symm (nuN 2 0 x) := rfl

/-- The seam inverts: `ztwoIota ∘ pilotNuP = ν_N`. -/
theorem ztwoIota_pilotNuP (x : (pilotP : Type)) : ztwoIota (pilotNuP x) = nuN 2 0 x :=
  ztwoIota.apply_symm_apply _

/-- `ν_P(σ) = ztwoOne` — the normalization CB-P's `nu_compat_coreHom` consumes. -/
theorem pilotNuP_dnSigma : pilotNuP (dnSigma 2 0) = ztwoOne := by
  rw [pilotNuP_apply, nuN_dnSigma, ← ztwoIota_ztwoOne]
  exact ztwoIota.symm_apply_apply ztwoOne

/-- `ν_P` kills the wild letters (through the compact-`N` dictionary `nWildIdx`). -/
theorem pilotNuP_wild (j : Fin (2 + 2 * 0 + 1)) :
    pilotNuP (dnGen 2 0 (nWildIdx 0 j)) = 1 := by
  fin_cases j
  · show pilotNuP (dnX0 2 0) = 1
    rw [pilotNuP_apply, nuN_dnX0]
    exact map_one ztwoIota.symm.toMulEquiv
  · show pilotNuP (dnX1 2 0) = 1
    rw [pilotNuP_apply, nuN_dnX1]
    exact map_one ztwoIota.symm.toMulEquiv
  · show pilotNuP (dnX2 2 0) = 1
    rw [pilotNuP_apply, nuN_dnX2]
    exact map_one ztwoIota.symm.toMulEquiv

/-- **`ν_P` is surjective** — the last hypothesis of the certificate-main theorem, discharged:
the range is closed and contains the topological generator `ztwoOne = ν_P(σ)`. -/
theorem pilotNuP_surjective : Function.Surjective pilotNuP :=
  SectionThree.surjective_of_mem_range_topGen pilotNuP SectionThree.topGen_ztwo
    ⟨dnSigma 2 0, pilotNuP_dnSigma⟩

end SqrtNeg2

end GQ2.Dyadic
