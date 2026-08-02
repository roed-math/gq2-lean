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

/-! ## §1 The row's single analytic residual: `hsimp`

Per-simple-module Stokes duality at the resolved compact-`N` family — packet Lem. 5.1's
hypothesis slot, exactly the `hsimp` argument of WN0-c's `nCompact_stokesDuality`, quantified
over the counting target `(C, t)` and the resolver `e` under the three honesty conditions the
consumers all hold (`e` odd; both resolved relators die at `t`).  Gate-F / AS-lane discharge;
owner ruling: an explicit hypothesis binder, never an axiom.

The binder is stated at `Type`-level modules, which is where every consumer below lives
(`Additive ↥D.T`, `DD.Vmod`, `Additive ↥RF.MB`, `ZMod 2`). -/

/-- **The `√−2` row's `hsimp`** (the single per-branch analytic residual, ledger §5.2 /
`CertificateMain.lean`'s named-residuals list): Stokes duality on every simple `𝔽₂[C]`-module
at the resolved compact-`N₂` family, for every finite counting target and every honest odd
resolver. -/
def PilotHsimp (q : ℕ) : Prop :=
  ∀ (C : Type) [Group C] [Finite C] (t : Marking 2 C) (e : ℕ), Odd e →
    PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW 2 q) = 1 →
    PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (nCompactW 2 0) = 1 →
    ∀ (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V →
      StokesDuality ⇑t (nCompactFam 2 0 q e) V

/-! ## §2 The duality payloads, all from the one `hsimp`

`sqrtNegTwo_stokesDuality` is the engine: for any marking obtained by pushing the tautological
`Γ_R`-marking along a continuous hom (so the relators die — CB-1's `lower_rel`), `hsimp` plus
WN0-c's `nCompact_stokesDuality` produce Stokes duality on **every** finite elementary module,
not only the simple ones.  The two named corollaries are CB-6's hand-off shapes. -/

section Payloads

variable {q : ℕ}

/-- The pilot candidate group at tame modulus `q`. -/
noncomputable abbrev pilotGamma (q : ℕ) : ProfiniteGrp := GammaR 2 q pilotW

/-- **The duality-payload engine.**  For a marking `ρ ∘ gammaGen` of a finite counting target
and an honest odd resolver, `hsimp` yields `StokesDuality` at every finite elementary
coefficient module.  The two relator conditions are not hypotheses: they are CB-1's
`lower_rel` at the scalar resolution, i.e. consequences of `Γ_R`'s own presentation. -/
theorem sqrtNegTwo_stokesDuality (hsimp : PilotHsimp q) (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    [DistribMulAction C (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
    (rho : ContinuousMonoidHom ((pilotGamma q : Type)) C) {e : ℕ} (he : Odd e)
    (hres : ResolvesAt (gammaFam 2 q pilotW) (nCompactFam 2 0 q e) (WordLift (ZMod 2) C))
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality (fun g => rho (gammaGen 2 q pilotW g)) (nCompactFam 2 0 q e) A := by
  set t : Marking 2 C := ⟨fun g => rho (gammaGen 2 q pilotW g)⟩ with ht
  have hr : ∀ k, FreeGroup.lift (⇑t) (nCompactFam 2 0 q e k) = 1 := fun k =>
    lower_rel (A := ZMod 2) rho (fun _ => rfl)
      (isAdmissibleMarkedPresentation_gammaR 2 q pilotW) hres k
  have hrt : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW 2 q) = 1 :=
    (lift_heisToFree_eq_one_iff ⇑t _ _ _).mp (hr 0)
  have hrw : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (nCompactW 2 0) = 1 :=
    (lift_heisToFree_eq_one_iff ⇑t _ _ _).mp (hr 1)
  exact nCompact_stokesDuality (α := 2) (h := 0) (q := q) (e := e) t one_le_two hqe he hrt hrw
    (hsimp C t e he hrt hrw) A hA₂

/-- **Fold-in deliverable A — the `Vmod` payload** (CB-6's hand-off, `Count/Marking.lean` §5 /
`Count/Separating.lean` §5): the `IsSelfDualN` package at `DD.Vmod`, in the exact shape
`isRightSeparating_vmod_nCompactFam`'s `hsd` slot consumes, from the one `hsimp`. -/
theorem sqrtNegTwo_selfDualN_vmod (hsimp : PilotHsimp q) (hqe : Even q)
    {Bg : Type} [Group Bg] [Finite Bg] {D : RadicalCoverData Bg} {DD : DescData D}
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0] [DistribMulAction DD.C0 (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) DD.C0)] [DiscreteTopology (WordLift (ZMod 2) DD.C0)]
    (rhoC : ContinuousMonoidHom ((pilotGamma q : Type)) DD.C0) :
    IsSelfDualN 2 (fun g => rhoC (gammaGen 2 q pilotW g))
      (nCompactFam 2 0 q (omega2Exp (vmodLevel DD))) DD.Vmod := by
  have hb := resolvesAt_and_endpoint_nCompactFam (Q := WordLift (ZMod 2) DD.C0)
    vmodLevel_ne_zero vmodLevel_even
    (orderOf_wordLiftScal_dvd_heisExponent (A := DD.Vmod)) (α := 2) (h := 0) (q := q)
    one_le_two hqe
  have hres : ResolvesAt (gammaFam 2 q pilotW) (nCompactFam 2 0 q (omega2Exp (vmodLevel DD)))
      (WordLift (ZMod 2) DD.C0) := hb.1
  exact isSelfDualN_of_stokesDuality (nCompact_degree 0)
    (sqrtNegTwo_stokesDuality hsimp hqe rhoC
      (odd_omega2Exp vmodLevel_ne_zero vmodLevel_even) hres DD.Vmod (Vmod_exp2 (DD := DD)))
    (fun k => lower_rel (A := ZMod 2) rhoC (fun _ => rfl)
      (isAdmissibleMarkedPresentation_gammaR 2 q pilotW) hres k)
    hb.2

/-- **Fold-in deliverable B — the `T` payload** (CB-6's hand-off): `StokesDuality` at
`Additive ↥D.T`, in the exact shape `hsepN_marking`'s `hd` slot consumes, from the one
`hsimp`.  Stated at the count lane's own level `heisLevel D` (CB-VAR §2), which also resolves
the split and dual targets `hsepN_marking` reads. -/
theorem sqrtNegTwo_stokesDuality_T (hsimp : PilotHsimp q) (hqe : Even q)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} [DistribMulAction (Bg ⧸ D.M) (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) (Bg ⧸ D.M))]
    [DiscreteTopology (WordLift (ZMod 2) (Bg ⧸ D.M))]
    (rho : ContinuousMonoidHom ((pilotGamma q : Type)) (Bg ⧸ D.M)) :
    StokesDuality (fun g => rho (gammaGen 2 q pilotW g))
      (nCompactFam 2 0 q (omega2Exp (heisLevel D))) (Additive ↥D.T) := by
  have hres : ResolvesAt (gammaFam 2 q pilotW) (nCompactFam 2 0 q (omega2Exp (heisLevel D)))
      (WordLift (ZMod 2) (Bg ⧸ D.M)) :=
    (resolvesAt_and_endpoint_nCompactFam (Q := WordLift (ZMod 2) (Bg ⧸ D.M))
      heisLevel_ne_zero heisLevel_even orderOf_dvd_heisLevel_scal (α := 2) (h := 0) (q := q)
      one_le_two hqe).1
  exact sqrtNegTwo_stokesDuality hsimp hqe rho
    (odd_omega2Exp heisLevel_ne_zero heisLevel_even) hres (Additive ↥D.T) (radT_add_self D)

end Payloads

/-! ## §3 The source-free radical-cover datum, reached from `Γ_R`

`cardH2` (and through it `lem86`'s nonemptiness route and `stageR136`'s `hcard`) needs one
concrete radical-cover datum with no descent **and** a surjection of the carrier onto its
`Bg ⧸ M`.  The datum is `GQ2.CardH2GammaA.datum` — source-free, reused verbatim, exactly as
CB-VAR §9 prescribes.  The surjection is rebuilt for the dyadic `Γ_R` (its `ℚ₂` sibling is
`CardH2GammaA.rho` at `Γ_A` and `HalfTorsorGammaR`'s at Roe's `Γ_R`, both `Fin 4`-pinned):
through the pro-2 core — `Γ_R ↠ D_N ↠ 𝔽₂²/⟨s̄⟩` — so relator death is `D_N`'s universal
property and no word is ever evaluated by hand. -/

section Datum

open GQ2.CardH2GammaA DihedralGroup

local instance : TopologicalSpace Base := ⊥
local instance : DiscreteTopology Base := ⟨rfl⟩

local instance : DiscreteTopology (Base ⧸ Mlayer) :=
  (CentralObstruction.discreteTopology_quotient datum : DiscreteTopology (Base ⧸ datum.M))

/-- `𝔽₂²/⟨s̄⟩` is elementary abelian of exponent `2`. -/
theorem datumQuot_sq (y : Base ⧸ Mlayer) : y * y = 1 := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, show b * b = 1 from by revert b; decide, QuotientGroup.mk_one]

/-- The datum's quotient is a `2`-group, hence pro-`2` as a finite discrete group. -/
theorem isProP_datumQuot : IsProP 2 (Base ⧸ Mlayer) :=
  isProP_of_isPGroup fun y => ⟨1, by rw [pow_one, pow_two]; exact datumQuot_sq y⟩

/-- **The core marking of the datum quotient**: `σ ↦ [r̄]`, everything else `↦ 1`.  The relator
dies because the `N`-relator at a marking with trivial `x`-slots is a bare commutator. -/
noncomputable def datumCoreHom : ContinuousMonoidHom ((DN 2 0) : Type) (Base ⧸ Mlayer) :=
  nLiftHom 2 0 isProP_datumQuot (coreMark 1 1 (QuotientGroup.mk (r 1)) 1)
    (by simp [nRelWord, nWord, commP])

@[simp] theorem datumCoreHom_dnGen (i : Fin (coreRank 0)) :
    datumCoreHom (dnGen 2 0 i) = coreMark (h := 0) 1 1 (QuotientGroup.mk (r 1)) 1 i :=
  nLiftHom_gen 2 0 _ _ _ i

variable {q : ℕ}

/-- **The surjection `Γ_R ↠ 𝔽₂²/⟨s̄⟩`**, through the pro-2 core. -/
noncomputable def datumRho (hq0 : q ≠ 0) (hqe : Even q) :
    ContinuousMonoidHom ((pilotGamma q : Type)) (Base ⧸ Mlayer) :=
  datumCoreHom.comp (CorePresentation.coreHom (nCorePresentation 2 0) hq0 hqe)

theorem datumRho_surjective (hq0 : q ≠ 0) (hqe : Even q) :
    Function.Surjective (datumRho hq0 hqe) := by
  intro y
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rcases quotient_cases b with h | h
  · exact ⟨1, by rw [map_one, h]⟩
  · obtain ⟨γ, hγ⟩ := CorePresentation.coreHom_surjective (nCorePresentation 2 0)
      (hq0 := hq0) (hqe := hqe) (dnSigma 2 0)
    refine ⟨γ, ?_⟩
    show datumCoreHom (CorePresentation.coreHom (nCorePresentation 2 0) hq0 hqe γ) = _
    rw [hγ, h, show dnSigma 2 0 = dnGen 2 0 2 from rfl, datumCoreHom_dnGen]
    simp

end Datum

end SqrtNeg2

end GQ2.Dyadic
