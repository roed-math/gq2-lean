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
certificate** (`sqrtNegTwoWordCertificate`, §5) with every count-lane clause discharged from
the landed CB/WN0 stacks, builds the **`K`-side supply** (`sqrtNegTwoKSupply`, §6) with the
marked-core composite written down and CB-DET's determinant discharge consumed, and closes the
loop (`sqrtNegTwo_candidate_equiv_galK`, §7).

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
* `hdet` (§5) — **the candidate-side `AffineDeterminantCertificate`**, whole.  ⚠ The count
  lane's clause list closed 9 of the 11 `SourceDataN` clauses on the candidate side; the two
  Gauss-`Z` clauses have **no candidate-side supplier in the repository** (CB-DET is the
  `K`-side bridge; the word-side Hessian layer (WN0-c) exists but the Hessian ⇒
  `GaussZResidueK` bridge does not).  Owner: CB1 memo's "gauss 1900" ticket, unopened.
* the G-Lab pack (§6): `fLab` (Labute/Demushkin classification of `G_K(2)` — N-Lab, packet
  §7's hypothesis-binder state per gate G-Lab), `piAb`/`hpiAb`/`hpiNu` (the abelianization
  slot of the marked-core `K`-layer and its `ν`-compatibility with `toAbK` — the direct-factor
  inclusion `G_K(2)^{ab} ↪ G_K^{ab}`, which AS1's "composite" needs and which **nobody had
  written down**; recorded here as data), `horient` (the orientation datum), `hScal`
  (`NScalingHypothesis`, MC-N's S2 binder), `hpair` (marked-data pair-unimodularity).
* `hexact`/`hstokes` (§6) — the `K`-side `ExactLiftingSemantics` and
  `StokesDualityCertificate` at `G_K`: ASK's carried leaves 2–3 (`KSupply` §6), still owed by
  the `Phase140/Local`-successor lane (CB-SG built the substrate).
* `params`/`ramified`/`ramifiedData` (§6–§7) — packet §12's field-side inputs at the concrete
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

local instance : DiscreteTopology (Base ⧸ datum.M) :=
  CentralObstruction.discreteTopology_quotient datum

/-- `𝔽₂²/⟨s̄⟩` is elementary abelian of exponent `2`.  (Stated at the `datum.M` spelling
throughout this section: the count lane's canonical instances — `cActT` and friends — are keyed
at `Bg ⧸ D.M`, and `Mlayer` does not match that key.) -/
theorem datumQuot_sq (y : Base ⧸ datum.M) : y * y = 1 := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_mul, show b * b = 1 from by revert b; decide, QuotientGroup.mk_one]

/-- The datum's quotient is a `2`-group, hence pro-`2` as a finite discrete group. -/
theorem isProP_datumQuot : IsProP 2 (Base ⧸ datum.M) :=
  isProP_of_isPGroup fun y => ⟨1, by rw [pow_one, pow_two]; exact datumQuot_sq y⟩

/-- **The core marking of the datum quotient**: `σ ↦ [r̄]`, everything else `↦ 1`.  The relator
dies because the `N`-relator at a marking with trivial `x`-slots is a bare commutator. -/
noncomputable def datumCoreHom : ContinuousMonoidHom ((DN 2 0) : Type) (Base ⧸ datum.M) :=
  nLiftHom 2 0 isProP_datumQuot (coreMark 1 1 (QuotientGroup.mk (r 1)) 1)
    (by simp [nRelWord, nWord, commP])

@[simp] theorem datumCoreHom_dnGen (i : Fin (coreRank 0)) :
    datumCoreHom (dnGen 2 0 i) = coreMark (h := 0) 1 1 (QuotientGroup.mk (r 1)) 1 i :=
  nLiftHom_gen 2 0 _ _ _ i

variable {q : ℕ}

/-- **The surjection `Γ_R ↠ 𝔽₂²/⟨s̄⟩`**, through the pro-2 core. -/
noncomputable def datumRho (hq0 : q ≠ 0) (hqe : Even q) :
    ContinuousMonoidHom ((pilotGamma q : Type)) (Base ⧸ datum.M) :=
  datumCoreHom.comp (CorePresentation.coreHom (nCorePresentation 2 0) hq0 hqe)

theorem datumRho_surjective (hq0 : q ≠ 0) (hqe : Even q) :
    Function.Surjective (datumRho hq0 hqe) := by
  intro y
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  have hcases : (QuotientGroup.mk b : Base ⧸ datum.M) = 1
      ∨ (QuotientGroup.mk b : Base ⧸ datum.M) = QuotientGroup.mk (r 1) := quotient_cases b
  rcases hcases with h | h
  · exact ⟨1, by rw [map_one, h]⟩
  · obtain ⟨γ, hγ⟩ := CorePresentation.coreHom_surjective (nCorePresentation 2 0)
      (hq0 := hq0) (hqe := hqe) (dnSigma 2 0)
    refine ⟨γ, ?_⟩
    show datumCoreHom (CorePresentation.coreHom (nCorePresentation 2 0) hq0 hqe γ) = _
    rw [hγ, h, show dnSigma 2 0 = dnGen 2 0 2 from rfl, datumCoreHom_dnGen]
    simp

end Datum

/-! ## §4 The count-lane clauses at the pilot

Each of the nine closed `SourceDataN` clauses, stated in the certificate's own vocabulary and
discharged from the CB lane plus the §2 payloads.  The scalar pair first (`homCard` outright,
`cardH2` through CB-VAR's variation class at the §3 datum). -/

section Clauses

open GQ2.CardH2GammaA

local instance : TopologicalSpace Base := ⊥
local instance : DiscreteTopology Base := ⟨rfl⟩

variable {q : ℕ}

/-- **`SourceDataN.cardH2` at the pilot** — `#H²(Γ_R, 𝔽₂) = 2`, from the one `hsimp` through
CB-VAR's `cardH2_of_variation` at the §3 datum. -/
theorem sqrtNegTwo_cardH2 (hsimp : PilotHsimp q) (hq0 : q ≠ 0) (hqe : Even q) :
    letI := scalarActionZmodTwo ((pilotGamma q : Type))
    Nat.card (H2 ((pilotGamma q : Type)) (ZMod 2)) = 2 := by
  letI := scalarActionZmodTwo ((pilotGamma q : Type))
  haveI : DiscreteTopology (Base ⧸ datum.M) := CentralObstruction.discreteTopology_quotient datum
  letI := scalarActionZmodTwo (Base ⧸ datum.M)
  set rho := datumRho hq0 hqe with hrho
  letI : TopologicalSpace (ElemDual (Additive ↥datum.T)) := ⊥
  haveI : DiscreteTopology (ElemDual (Additive ↥datum.T)) := ⟨rfl⟩
  letI : DistribMulAction ((pilotGamma q : Type)) (Additive ↥datum.T) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  letI : DistribMulAction ((pilotGamma q : Type)) (ElemDual (Additive ↥datum.T)) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  haveI : ContinuousSMul ((pilotGamma q : Type)) (ElemDual (Additive ↥datum.T)) := by
    constructor
    have hfac : (fun p : ((pilotGamma q : Type)) × ElemDual (Additive ↥datum.T) => p.1 • p.2)
        = (fun z : (Base ⧸ datum.M) × ElemDual (Additive ↥datum.T) => z.1 • z.2)
          ∘ (fun p : ((pilotGamma q : Type)) × ElemDual (Additive ↥datum.T) =>
              (rho p.1, p.2)) := by
      funext p; rfl
    rw [hfac]
    exact (continuous_of_discreteTopology
      (f := fun z : (Base ⧸ datum.M) × ElemDual (Additive ↥datum.T) => z.1 • z.2)).comp
      ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hb := resolvesAt_and_endpoint_nCompactFam (Q := WordLift (ZMod 2) (Base ⧸ datum.M))
    heisLevel_ne_zero heisLevel_even orderOf_dvd_heisLevel_scal (α := 2) (h := 0) (q := q)
    one_le_two hqe
  have hresS : ResolvesAt (gammaFam 2 q pilotW)
      (nCompactFam 2 0 q (omega2Exp (heisLevel datum))) (WordLift (ZMod 2) (Base ⧸ datum.M)) :=
    hb.1
  have hresP : ResolvesAt (gammaFam 2 q pilotW)
      (nCompactFam 2 0 q (omega2Exp (heisLevel datum)))
      (WordLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
    (resolvesAt_and_endpoint_nCompactFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_prim (α := 2) (h := 0) (q := q) one_le_two hqe).1
  have hresD : ResolvesAt (gammaFam 2 q pilotW)
      (nCompactFam 2 0 q (omega2Exp (heisLevel datum)))
      (WordLift (ElemDual (Additive ↥datum.T)) (Base ⧸ datum.M)) :=
    (resolvesAt_and_endpoint_nCompactFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_dual (α := 2) (h := 0) (q := q) one_le_two hqe).1
  have hresH : ResolvesAt (gammaFam 2 q pilotW)
      (nCompactFam 2 0 q (omega2Exp (heisLevel datum)))
      (HeisLift (Additive ↥datum.T) (Base ⧸ datum.M)) :=
    (resolvesAt_and_endpoint_nCompactFam heisLevel_ne_zero heisLevel_even
      orderOf_dvd_heisLevel_heis (α := 2) (h := 0) (q := q) one_le_two hqe).1
  exact cardH2_of_variation (tComplement_nonempty datum).some rho (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (isAdmissibleMarkedPresentation_gammaR 2 q pilotW)
    (fun V => hwildLevel_gammaR V) (isWildTwo_of_gammaGen rho (datumRho_surjective hq0 hqe)
      (fun _ => rfl))
    hresS hresP hresD hresH
    (sqrtNegTwo_stokesDuality_T hsimp hqe rho)
    (sqrtNegTwo_stokesDuality hsimp hqe rho
      (odd_omega2Exp heisLevel_ne_zero heisLevel_even) hresS (ZMod 2)
      (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2 datum_noDescent (datumRho_surjective hq0 hqe)

/-- **`SourceDataN.homCard` at the pilot** — `#Hom_c(Γ_R, 𝔽₂) = 2^{2+2}`, CB-2's field goal at
the same datum marking. -/
theorem sqrtNegTwo_homCard (hsimp : PilotHsimp q) (hq0 : q ≠ 0) (hqe : Even q) :
    Nat.card (ContinuousMonoidHom (pilotGamma q) (Multiplicative (ZMod 2)))
      = (standardNumerics 2).homScalar := by
  haveI : DiscreteTopology (Base ⧸ datum.M) := CentralObstruction.discreteTopology_quotient datum
  letI := scalarActionZmodTwo (Base ⧸ datum.M)
  set rho := datumRho hq0 hqe with hrho
  have hb := resolvesAt_and_endpoint_nCompactFam (Q := WordLift (ZMod 2) (Base ⧸ datum.M))
    heisLevel_ne_zero heisLevel_even orderOf_dvd_heisLevel_scal (α := 2) (h := 0) (q := q)
    one_le_two hqe
  have hresS : ResolvesAt (gammaFam 2 q pilotW)
      (nCompactFam 2 0 q (omega2Exp (heisLevel datum))) (WordLift (ZMod 2) (Base ⧸ datum.M)) :=
    hb.1
  exact homCard_field_goal rho (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR 2 q pilotW) hresS
    (isWildTwo_of_gammaGen rho (datumRho_surjective hq0 hqe) (fun _ => rfl))
    (nCompact_degree 0)
    (sqrtNegTwo_stokesDuality hsimp hqe rho
      (odd_omega2Exp heisLevel_ne_zero heisLevel_even) hresS (ZMod 2)
      (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2

/-- **Ledger field 5 at the pilot** — the scalar block, assembled. -/
theorem sqrtNegTwo_scalar (hsimp : PilotHsimp q) (hq0 : q ≠ 0) (hqe : Even q) :
    ScalarHilbertCertificate (pilotGamma q) 2 (standardNumerics 2)
      (scalarActionZmodTwo ((pilotGamma q : Type))) :=
  ⟨sqrtNegTwo_homCard hsimp hq0 hqe, sqrtNegTwo_cardH2 hsimp hq0 hqe⟩

/-! ### The `stageR136` residuals

The two per-frame recursion-side inputs SD-R3's `blockStageR136K` leaves open, at this
carrier — the exact shapes of its `hsep_hom` and `hZcount` binders, with the `htriv`/`hcard`
proofs quantified (proof irrelevance makes any pair usable).  Their `ℚ₂` ancestors are the
per-carrier `RStage` computations (`GQ2/Block/RStage.lean:372`,
`GQ2.CardH2GammaA.stageR136_gammaA`); no candidate-side general-`K` supplier exists.
**Owner:** a follow-on candidate-side R-stage ticket (CB1 memo's "stokes 1800" block). -/

/-- **`stageR136` residual 1** — the obstruction-vanishing homomorphism-lift clause
(`blockStageR136K`'s `hsep_hom`) at `Γ_R`, per frame. -/
def PilotStageSep (q : ℕ) : Prop :=
  letI := scalarActionZmodTwo ((pilotGamma q : Type))
  ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY) (hE2 : ∀ e : E, e ^ 2 = 1)
    (b : ContinuousMonoidHom ((pilotGamma q : Type)) ↥(boundarySubgroupQ q pilotNuP))
    (F : BoundaryFrameK q pilotP H E)
    (htriv : ∀ (γ : ((pilotGamma q : Type))) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 ((pilotGamma q : Type)) (ZMod 2)) = 2)
    (g : BoundaryLiftsK b F (blockFrameImpl T Blk hE2).TB),
    obs (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2) htriv hcard g.1.1 = 0 →
      ∃ φ : ContinuousMonoidHom ((pilotGamma q : Type)) Y,
        ∀ γ, (blockFrameImpl T Blk hE2).piB (φ γ) = g.1.1 γ

/-- **`stageR136` residual 2** — the `R`-cocycle torsor count (`blockStageR136K`'s `hZcount`)
at `Γ_R`, per frame. -/
def PilotStageZ (q : ℕ) : Prop :=
  ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY) (hE2 : ∀ e : E, e ^ 2 = 1)
    (b : ContinuousMonoidHom ((pilotGamma q : Type)) ↥(boundarySubgroupQ q pilotNuP))
    (F : BoundaryFrameK q pilotP H E) (f₀ : BoundaryLiftsK b F T),
    Nat.card (RCocycle (blockFrameImpl T Blk hE2) f₀.1.1) = (blockFrameImpl T Blk hE2).zR

/-- **Ledger field 3 at the pilot** — `ExactLiftingSemantics`, its three conjuncts closed by
CB-3 (`liftsOver_card`), CB-VAR (`lem86`) and SD-R3's `blockStageR136K` over the two named
residuals. -/
theorem sqrtNegTwo_exactLifting (hsimp : PilotHsimp q) (hq0 : q ≠ 0) (hqe : Even q)
    (hsplit : PilotStageSep q) (hZcount : PilotStageZ q) :
    ExactLiftingSemantics (pilotGamma q) 2 q pilotP pilotNuP (standardNumerics 2) := by
  refine ⟨?_, ?_, ?_⟩
  · -- `liftsOver_card` (CB-3, at the branch's own degree bookkeeping)
    intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk RF b F ρ
    letI := mbCommGroup RF
    letI := mbConjActC RF
    letI := scalarActionZmodTwo RF.YC
    have hb := resolvesAt_and_endpoint_nCompactFam
      (Q := WordLift (Additive ↥RF.MB) RF.YC)
      (N := Monoid.exponent (HeisLift (Additive ↥RF.MB) RF.YC))
      heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2
      orderOf_wordLift_dvd_heisExponent (α := 2) (h := 0) (q := q) one_le_two hqe
    have hres : ResolvesAt (gammaFam 2 q pilotW)
        (nCompactFam 2 0 q (omega2Exp (Monoid.exponent (HeisLift (Additive ↥RF.MB) RF.YC))))
        (WordLift (Additive ↥RF.MB) RF.YC) := hb.1
    have hresS : ResolvesAt (gammaFam 2 q pilotW)
        (nCompactFam 2 0 q (omega2Exp (Monoid.exponent (HeisLift (Additive ↥RF.MB) RF.YC))))
        (WordLift (ZMod 2) RF.YC) :=
      (resolvesAt_and_endpoint_nCompactFam heisLevel_ne_zero_and_even.1
        heisLevel_ne_zero_and_even.2 orderOf_wordLiftScal_dvd_heisExponent
        (α := 2) (h := 0) (q := q) one_le_two hqe).1
    exact nCompact_liftsOver_card (hN := 0) RF b F ρ
      (isAdmissibleMarkedPresentation_gammaR 2 q pilotW) (fun _ => rfl)
      (isWildTwo_of_gammaGen ρ.1.1 ρ.1.2 (fun _ => rfl)) hres
      (sqrtNegTwo_stokesDuality hsimp hqe ρ.1.1
        (odd_omega2Exp heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2) hresS
        (Additive ↥RF.MB) (mb_add_self RF))
      hb.2
  · -- `lem86` (CB-VAR, at the given radical-cover datum)
    intro Bg _ _ _ _ D hedge ρ hρ
    letI := scalarActionZmodTwo ((pilotGamma q : Type))
    letI := scalarActionZmodTwo (Bg ⧸ D.M)
    letI : TopologicalSpace (ElemDual (Additive ↥D.T)) := ⊥
    haveI : DiscreteTopology (ElemDual (Additive ↥D.T)) := ⟨rfl⟩
    letI : DistribMulAction ((pilotGamma q : Type)) (Additive ↥D.T) :=
      DistribMulAction.compHom _ ρ.toMonoidHom
    letI : DistribMulAction ((pilotGamma q : Type)) (ElemDual (Additive ↥D.T)) :=
      DistribMulAction.compHom _ ρ.toMonoidHom
    haveI : ContinuousSMul ((pilotGamma q : Type)) (ElemDual (Additive ↥D.T)) := by
      constructor
      have hfac : (fun p : ((pilotGamma q : Type)) × ElemDual (Additive ↥D.T) => p.1 • p.2)
          = (fun z : (Bg ⧸ D.M) × ElemDual (Additive ↥D.T) => z.1 • z.2)
            ∘ (fun p : ((pilotGamma q : Type)) × ElemDual (Additive ↥D.T) =>
                (ρ p.1, p.2)) := by
        funext p; rfl
      rw [hfac]
      exact (continuous_of_discreteTopology
        (f := fun z : (Bg ⧸ D.M) × ElemDual (Additive ↥D.T) => z.1 • z.2)).comp
        ((ρ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
    have hb := resolvesAt_and_endpoint_nCompactFam (Q := WordLift (ZMod 2) (Bg ⧸ D.M))
      heisLevel_ne_zero heisLevel_even orderOf_dvd_heisLevel_scal (α := 2) (h := 0) (q := q)
      one_le_two hqe
    have hresS : ResolvesAt (gammaFam 2 q pilotW)
        (nCompactFam 2 0 q (omega2Exp (heisLevel D))) (WordLift (ZMod 2) (Bg ⧸ D.M)) := hb.1
    have hresP : ResolvesAt (gammaFam 2 q pilotW)
        (nCompactFam 2 0 q (omega2Exp (heisLevel D)))
        (WordLift (Additive ↥D.T) (Bg ⧸ D.M)) :=
      (resolvesAt_and_endpoint_nCompactFam heisLevel_ne_zero heisLevel_even
        orderOf_dvd_heisLevel_prim (α := 2) (h := 0) (q := q) one_le_two hqe).1
    have hresD : ResolvesAt (gammaFam 2 q pilotW)
        (nCompactFam 2 0 q (omega2Exp (heisLevel D)))
        (WordLift (ElemDual (Additive ↥D.T)) (Bg ⧸ D.M)) :=
      (resolvesAt_and_endpoint_nCompactFam heisLevel_ne_zero heisLevel_even
        orderOf_dvd_heisLevel_dual (α := 2) (h := 0) (q := q) one_le_two hqe).1
    have hresH : ResolvesAt (gammaFam 2 q pilotW)
        (nCompactFam 2 0 q (omega2Exp (heisLevel D)))
        (HeisLift (Additive ↥D.T) (Bg ⧸ D.M)) :=
      (resolvesAt_and_endpoint_nCompactFam heisLevel_ne_zero heisLevel_even
        orderOf_dvd_heisLevel_heis (α := 2) (h := 0) (q := q) one_le_two hqe).1
    exact lem86_of_variation (tComplement_nonempty D).some ρ (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ => rfl) (isAdmissibleMarkedPresentation_gammaR 2 q pilotW)
      (fun V => hwildLevel_gammaR V)
      (isWildTwo_of_gammaGen ρ hρ (fun _ => rfl)) hresS hresP hresD hresH
      (sqrtNegTwo_stokesDuality_T hsimp hqe ρ)
      (sqrtNegTwo_stokesDuality hsimp hqe ρ
        (odd_omega2Exp heisLevel_ne_zero heisLevel_even) hresS (ZMod 2)
        (by decide : ∀ a : ZMod 2, a + a = 0))
      hb.2 hedge hρ
  · -- `stageR136` (SD-R3's `blockStageR136K` over the two named residuals)
    intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE2 hRK hR2 b F
    letI := scalarActionZmodTwo ((pilotGamma q : Type))
    haveI := scalarActionZmodTwo_continuousSMul ((pilotGamma q : Type))
    exact blockStageR136K T Blk hE2 (scalarActionZmodTwo_triv _)
      (sqrtNegTwo_cardH2 hsimp hq0 hqe)
      (GQ2.Dyadic.Count.gammaR_topologicallyFinitelyGenerated 2 q pilotW) b F
      (fun g hg => hsplit T Blk hE2 b F (scalarActionZmodTwo_triv _)
        (sqrtNegTwo_cardH2 hsimp hq0 hqe) g hg)
      (fun f₀ => hZcount T Blk hE2 b F f₀)

/-! ### The Stokes bundle

The four analytic conjuncts, standalone (one theorem each: the packed form re-elaborates the
recursion's `radData`/`descData` projections at four frames at once and diverges — see the
report's trap note; and ⚠ every `nCompact`-indexed call below pins `(α := 2) (h := 0)`
explicitly, because an unpinned `{h}` under `2 + 2 * h` sends the unifier through `GammaR`'s
admissible-limit definition, unfolding `FreeGroup`/arithmetic ~320k times). -/

/-- The `C₀`-valued lower map of a boundary lift, as a continuous hom. -/
noncomputable def rho0CMH {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    [Finite Bg] {D : RadicalCoverData Bg} (DD : DescData D)
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0] {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] (rho : ContinuousMonoidHom Γ (Bg ⧸ D.M)) :
    ContinuousMonoidHom Γ DD.C0 :=
  ⟨rho0 DD rho,
    (continuous_of_discreteTopology (f := fun x : Bg ⧸ D.M => liftC0 DD x)).comp
      rho.continuous_toFun⟩

theorem rho0CMH_surjective {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    [Finite Bg] {D : RadicalCoverData Bg} (DD : DescData D)
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0] {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] (rho : ContinuousMonoidHom Γ (Bg ⧸ D.M))
    (hrho : Function.Surjective rho) : Function.Surjective (rho0CMH DD rho) := by
  intro c0
  obtain ⟨bb, hb⟩ := DD.hpiC0 c0
  obtain ⟨γ, hγ⟩ := hrho (QuotientGroup.mk bb)
  exact ⟨γ, (rho0_apply_of_rep DD rho γ bb hγ.symm).trans hb⟩

set_option maxHeartbeats 800000 in
/-- **`SourceDataN.tcocycle_card` at the pilot** (stokes conjunct 1) — CB-1's comparison at
the `T`-module, `T` payload from the one `hsimp`. -/
theorem sqrtNegTwo_tcocycle (hsimp : PilotHsimp q) (hqe : Even q)
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((pilotGamma q : Type)) ↥(boundarySubgroupQ q pilotNuP))
    (F : BoundaryFrameK q pilotP H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (ρ : BoundaryLiftsK b F RF.TC) :
    Nat.card (TCocycle (En.radData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
      = (standardNumerics 2).tMult (Nat.card (Additive ↥(En.radData l h).T))
        * Nat.card (fixedPts (RF.YB ⧸ (En.radData l h).M)
            (ElemDual (Additive ↥(En.radData l h).T))) := by
  letI : TopologicalSpace (Additive ↥(En.radData l h).T) := ⊥
  haveI : DiscreteTopology (Additive ↥(En.radData l h).T) := ⟨rfl⟩
  letI : DistribMulAction ((pilotGamma q : Type)) (Additive ↥(En.radData l h).T) :=
    DistribMulAction.compHom _ (rhoPrimeK RF b F (En.radData l h) rfl ρ).toMonoidHom
  letI := scalarActionZmodTwo (RF.YB ⧸ (En.radData l h).M)
  have hsurj : Function.Surjective (rhoPrimeK RF b F (En.radData l h) rfl ρ) :=
    rhoPrimeK_surjective RF b F (En.radData l h) rfl ρ
  have hb := resolvesAt_and_endpoint_nCompactFam
    (Q := WordLift (Additive ↥(En.radData l h).T) (RF.YB ⧸ (En.radData l h).M))
    (heisLevel_ne_zero (D := En.radData l h)) (heisLevel_even (D := En.radData l h))
    (orderOf_dvd_heisLevel_prim (D := En.radData l h))
    (α := 2) (h := 0) (q := q) one_le_two hqe
  have hres : ResolvesAt (gammaFam 2 q pilotW)
      (nCompactFam 2 0 q (omega2Exp (heisLevel (En.radData l h))))
      (WordLift (Additive ↥(En.radData l h).T) (RF.YB ⧸ (En.radData l h).M)) := hb.1
  have hresS : ResolvesAt (gammaFam 2 q pilotW)
      (nCompactFam 2 0 q (omega2Exp (heisLevel (En.radData l h))))
      (WordLift (ZMod 2) (RF.YB ⧸ (En.radData l h).M)) :=
    (resolvesAt_and_endpoint_nCompactFam
      (heisLevel_ne_zero (D := En.radData l h)) (heisLevel_even (D := En.radData l h))
      (orderOf_dvd_heisLevel_scal (D := En.radData l h))
      (α := 2) (h := 0) (q := q) one_le_two hqe).1
  exact nCompact_tcocycle_card (α := 2) (h := 0) (q := q) (Bg := RF.YB)
    (D := En.radData l h) (e := omega2Exp (heisLevel (En.radData l h)))
    (t := ⟨fun i => rhoPrimeK RF b F (En.radData l h) rfl ρ (gammaGen 2 q pilotW i)⟩)
    (rhoPrimeK RF b F (En.radData l h) rfl ρ) (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR 2 q pilotW) hres
    (radT_add_self (En.radData l h))
    (isWildTwo_of_gammaGen (rhoPrimeK RF b F (En.radData l h) rfl ρ) hsurj (fun _ => rfl))
    hsurj
    (sqrtNegTwo_stokesDuality_T hsimp hqe (rhoPrimeK RF b F (En.radData l h) rfl ρ)) hb.2

set_option maxHeartbeats 800000 in
/-- **`SourceDataN.hsep` at the pilot** (stokes conjunct 2) — CB-6's marking route,
consuming the `T` payload (fold-in deliverable B's consumer shape). -/
theorem sqrtNegTwo_hsep (hsimp : PilotHsimp q) (hqe : Even q)
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((pilotGamma q : Type)) ↥(boundarySubgroupQ q pilotNuP))
    (F : BoundaryFrameK q pilotP H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (Dsc : Descent (En.radData l h)) (ρ : BoundaryLiftsK b F RF.TC)
    (c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
    (hvan : letI := scalarActionZmodTwo ((pilotGamma q : Type))
      ∀ χ : ↥(TCharC (En.radData l h)),
        betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c = 0) :
    TLiftable (descSigma_spec En l h Dsc) c := by
  letI := scalarActionZmodTwo ((pilotGamma q : Type))
  letI := scalarActionZmodTwo (RF.YB ⧸ (En.radData l h).M)
  have hres2 : ResolvesAt (gammaFam 2 q pilotW)
      (nCompactFam 2 0 q (omega2Exp (heisLevel (En.radData l h))))
      (WordLift (ZMod 2) (RF.YB ⧸ (En.radData l h).M)) :=
    (resolvesAt_and_endpoint_nCompactFam
      (heisLevel_ne_zero (D := En.radData l h)) (heisLevel_even (D := En.radData l h))
      (orderOf_dvd_heisLevel_scal (D := En.radData l h))
      (α := 2) (h := 0) (q := q) one_le_two hqe).1
  have hb := resolvesAt_and_endpoint_nCompactFam
    (Q := WordLift (Additive ↥(En.radData l h).T) (RF.YB ⧸ (En.radData l h).M))
    (heisLevel_ne_zero (D := En.radData l h)) (heisLevel_even (D := En.radData l h))
    (orderOf_dvd_heisLevel_prim (D := En.radData l h))
    (α := 2) (h := 0) (q := q) one_le_two hqe
  have hresT : ResolvesAt (gammaFam 2 q pilotW)
      (nCompactFam 2 0 q (omega2Exp (heisLevel (En.radData l h))))
      (WordLift (Additive ↥(En.radData l h).T) (RF.YB ⧸ (En.radData l h).M)) := hb.1
  exact hsep_field_goal_marking b F En l h Dsc ρ (scalarActionZmodTwo _)
    (scalarActionZmodTwo_triv _) (scalarActionZmodTwo _) (scalarActionZmodTwo_triv _)
    (isAdmissibleMarkedPresentation_gammaR 2 q pilotW) (fun _ => rfl)
    (isWildTwo_of_gammaGen (rhoPrimeK RF b F (En.radData l h) rfl ρ)
      (rhoPrimeK_surjective RF b F (En.radData l h) rfl ρ) (fun _ => rfl))
    hres2 hresT
    (sqrtNegTwo_stokesDuality_T hsimp hqe (rhoPrimeK RF b F (En.radData l h) rfl ρ))
    hb.2 c hvan

set_option maxHeartbeats 800000 in
/-- The `hpartial` fork's right-separation input, in the verbatim shape of
`hpartial_field_goal`'s `hrsep` binder. -/
theorem sqrtNegTwo_hrsep (hsimp : PilotHsimp q) (hqe : Even q)
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((pilotGamma q : Type)) ↥(boundarySubgroupQ q pilotNuP))
    (F : BoundaryFrameK q pilotP H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (ρ : BoundaryLiftsK b F RF.TC) :
    letI := scalarActionZmodTwo ((pilotGamma q : Type))
    letI : TopologicalSpace (En.descData l h).Vmod := ⊥
    haveI : DiscreteTopology (En.descData l h).Vmod := ⟨rfl⟩
    letI : DistribMulAction ((pilotGamma q : Type)) (En.descData l h).Vmod :=
      DistribMulAction.compHom (En.descData l h).Vmod
        (rho0 (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
    letI : TopologicalSpace (ElemDual (En.descData l h).Vmod) := ⊥
    haveI : DiscreteTopology (ElemDual (En.descData l h).Vmod) := ⟨rfl⟩
    IsRightSeparating ((pilotGamma q : Type)) (En.descData l h).Vmod := by
  letI := scalarActionZmodTwo ((pilotGamma q : Type))
  haveI := scalarActionZmodTwo_continuousSMul ((pilotGamma q : Type))
  letI : TopologicalSpace (En.descData l h).Vmod := ⊥
  haveI : DiscreteTopology (En.descData l h).Vmod := ⟨rfl⟩
  letI : DistribMulAction ((pilotGamma q : Type)) (En.descData l h).Vmod :=
    DistribMulAction.compHom (En.descData l h).Vmod
      (rho0 (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
  letI : TopologicalSpace (ElemDual (En.descData l h).Vmod) := ⊥
  haveI : DiscreteTopology (ElemDual (En.descData l h).Vmod) := ⟨rfl⟩
  letI : TopologicalSpace (En.descData l h).C0 := ⊥
  haveI : DiscreteTopology (En.descData l h).C0 := ⟨rfl⟩
  letI := scalarActionZmodTwo (En.descData l h).C0
  have hcompat : ∀ (γ : ((pilotGamma q : Type))) (a : (En.descData l h).Vmod),
      γ • a = rho0CMH (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ) γ • a :=
    fun _ _ => rfl
  haveI : ContinuousSMul ((pilotGamma q : Type)) (ElemDual (En.descData l h).Vmod) := by
    constructor
    have hfac : (fun p : ((pilotGamma q : Type)) × ElemDual (En.descData l h).Vmod =>
          p.1 • p.2)
        = (fun z : (En.descData l h).C0 × ElemDual (En.descData l h).Vmod => z.1 • z.2)
          ∘ (fun p : ((pilotGamma q : Type)) × ElemDual (En.descData l h).Vmod =>
              (rho0CMH (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ) p.1,
                p.2)) := by
      funext p
      exact elemDual_compat
        (rho0CMH (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ)) hcompat p.1 p.2
    rw [hfac]
    exact (continuous_of_discreteTopology
      (f := fun z : (En.descData l h).C0 × ElemDual (En.descData l h).Vmod =>
        z.1 • z.2)).comp
      (((rho0CMH (En.descData l h)
          (rhoPrimeK RF b F (En.radData l h) rfl ρ)).continuous_toFun.comp
        continuous_fst).prodMk continuous_snd)
  have step1 := sqrtNegTwo_selfDualN_vmod (DD := En.descData l h) hsimp hqe
    (rho0CMH (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
  have step2 := isRightSeparating_vmod_nCompactFam (DD := En.descData l h)
    (n := 2) (α := 2) (h := 0) (q := q)
    (rho0CMH (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ)) hcompat
    one_le_two hqe (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR 2 q pilotW)
    (isWildTwo_of_gammaGen
      (rho0CMH (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
      (rho0CMH_surjective (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ)
        (rhoPrimeK_surjective RF b F (En.radData l h) rfl ρ)) (fun _ => rfl))
    step1
  exact step2

set_option maxHeartbeats 800000 in
/-- **`SourceDataN.hpartial` at the pilot** (stokes conjunct 3) — CB-4's field goal over the
fork supplied by `sqrtNegTwo_hrsep`. -/
theorem sqrtNegTwo_hpartial (hsimp : PilotHsimp q) (hq0 : q ≠ 0) (hqe : Even q)
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((pilotGamma q : Type)) ↥(boundarySubgroupQ q pilotNuP))
    (F : BoundaryFrameK q pilotP H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (Dsc : Descent (En.radData l h)) (ρ : BoundaryLiftsK b F RF.TC)
    (χ : ↥(TCharC (En.radData l h))) (hχ : χ ≠ 0) :
    letI := scalarActionZmodTwo ((pilotGamma q : Type))
    ∃ cc : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ cc
        ≠ betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ
            (0 : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ)) :=
  hpartial_field_goal b F En l h Dsc ρ (scalarActionZmodTwo _)
    (scalarActionZmodTwo_triv _) (sqrtNegTwo_cardH2 hsimp hq0 hqe)
    (sqrtNegTwo_hrsep hsimp hqe b F En l h ρ) χ hχ

set_option maxHeartbeats 800000 in
/-- **`SourceDataN.hZcard` at the pilot** (stokes conjunct 4) — CB-1's `V`-side comparison,
`Vmod` payload from the one `hsimp`. -/
theorem sqrtNegTwo_hZcard (hsimp : PilotHsimp q) (hqe : Even q)
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((pilotGamma q : Type)) ↥(boundarySubgroupQ q pilotNuP))
    (F : BoundaryFrameK q pilotP H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (hsimple : ∀ W : AddSubgroup En.Vmod, (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (ρ : BoundaryLiftsK b F RF.TC) :
    Nat.card (VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
      = Nat.card En.Vmod * (standardNumerics 2).h1Mult (Nat.card En.Vmod) := by
  letI : TopologicalSpace (En.descData l h).Vmod := ⊥
  haveI : DiscreteTopology (En.descData l h).Vmod := ⟨rfl⟩
  letI : DistribMulAction RF.YC (En.descData l h).Vmod :=
    (inferInstance : DistribMulAction RF.YC En.Vmod)
  letI : DistribMulAction ((pilotGamma q : Type)) (En.descData l h).Vmod :=
    DistribMulAction.compHom _ ρ.1.1.toMonoidHom
  haveI : ContinuousSMul ((pilotGamma q : Type)) (En.descData l h).Vmod := by
    constructor
    have hfac : (fun p : ((pilotGamma q : Type)) × (En.descData l h).Vmod => p.1 • p.2)
        = (fun z : RF.YC × (En.descData l h).Vmod => z.1 • z.2)
          ∘ (fun p : ((pilotGamma q : Type)) × (En.descData l h).Vmod =>
              (ρ.1.1 p.1, p.2)) := by
      funext p; rfl
    rw [hfac]
    exact (continuous_of_discreteTopology
      (f := fun z : RF.YC × (En.descData l h).Vmod => z.1 • z.2)).comp
      ((ρ.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  letI := scalarActionZmodTwo RF.YC
  have hb := resolvesAt_and_endpoint_nCompactFam
    (Q := WordLift (En.descData l h).Vmod RF.YC)
    (N := Monoid.exponent (HeisLift (En.descData l h).Vmod RF.YC))
    heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2
    orderOf_wordLift_dvd_heisExponent (α := 2) (h := 0) (q := q) one_le_two hqe
  have hres : ResolvesAt (gammaFam 2 q pilotW)
      (nCompactFam 2 0 q
        (omega2Exp (Monoid.exponent (HeisLift (En.descData l h).Vmod RF.YC))))
      (WordLift (En.descData l h).Vmod RF.YC) := hb.1
  have hresS : ResolvesAt (gammaFam 2 q pilotW)
      (nCompactFam 2 0 q
        (omega2Exp (Monoid.exponent (HeisLift (En.descData l h).Vmod RF.YC))))
      (WordLift (ZMod 2) RF.YC) :=
    (resolvesAt_and_endpoint_nCompactFam
      (heisLevel_ne_zero_and_even (A := (En.descData l h).Vmod) (C := RF.YC)).1
      (heisLevel_ne_zero_and_even (A := (En.descData l h).Vmod) (C := RF.YC)).2
      (orderOf_wordLiftScal_dvd_heisExponent (A := (En.descData l h).Vmod))
      (α := 2) (h := 0) (q := q) one_le_two hqe).1
  have hsimple' : IsSimpleModTwo RF.YC (En.descData l h).Vmod := by
    obtain ⟨v, hv⟩ := hVne
    exact ⟨nontrivial_of_ne v 0 hv, hsimple⟩
  exact nCompact_hZcard (α := 2) (h := 0) (q := q) (Bg := RF.YB) (D := En.radData l h)
    (DD := En.descData l h) (E := RF.YC)
    (e := omega2Exp (Monoid.exponent (HeisLift (En.descData l h).Vmod RF.YC)))
    (t := ⟨fun i => ρ.1.1 (gammaGen 2 q pilotW i)⟩) ρ.1.1
    (fun γ v => congrArg (fun g : RF.YC => g • v) (rho0_descData_rhoPrimeK b F En l h ρ γ))
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR 2 q pilotW) hres
    (Vmod_exp2 (DD := En.descData l h))
    (isWildTwo_of_gammaGen ρ.1.1 ρ.1.2 (fun _ => rfl)) ρ.1.2
    (sqrtNegTwo_stokesDuality hsimp hqe ρ.1.1
      (odd_omega2Exp heisLevel_ne_zero_and_even.1 heisLevel_ne_zero_and_even.2) hresS
      ((En.descData l h).Vmod) (Vmod_exp2 (DD := En.descData l h)))
    hb.2 hsimple' hnt

set_option maxHeartbeats 800000 in
/-- **Ledger field 4 at the pilot** — `StokesDualityCertificate`, assembled. -/
theorem sqrtNegTwo_stokes (hsimp : PilotHsimp q) (hq0 : q ≠ 0) (hqe : Even q) :
    StokesDualityCertificate (pilotGamma q) 2 q pilotP pilotNuP (standardNumerics 2)
      (scalarActionZmodTwo ((pilotGamma q : Type))) :=
  ⟨fun b F En l h ρ => sqrtNegTwo_tcocycle hsimp hqe b F En l h ρ,
   fun b F En l h Dsc ρ c hvan => sqrtNegTwo_hsep hsimp hqe b F En l h Dsc ρ c hvan,
   fun b F En l h Dsc ρ χ hχ => sqrtNegTwo_hpartial hsimp hq0 hqe b F En l h Dsc ρ χ hχ,
   fun b F En l h hsimple hVne hnt ρ => sqrtNegTwo_hZcard hsimp hqe b F En l h hsimple hVne hnt ρ⟩

end Clauses

/-! ## §5 The pilot word certificate  (packet Def. 9.1 at the frozen `√−2` row) -/

section TheCertificate

variable {q : ℕ}

/-- **Ledger field 1** at the pilot (`q`-generic): the compact-`N` word tame-specializes. -/
theorem pilotTameSpec (hq0 : q ≠ 0) (hqe : Even q) : TameSpecializes 2 q pilotW :=
  tameSpecializes_nCompact hq0 hqe 2 0

/-- **The pro-2 leg**: CB-P's bridge `Γ_R ↠ Γ_R(2) ≅ D_N` at the pilot core presentation. -/
noncomputable def pilotPro2 (hq0 : q ≠ 0) (hqe : Even q) :
    ContinuousMonoidHom ((pilotGamma q : Type)) (pilotP : Type) :=
  CorePresentation.coreHom (nCorePresentation 2 0) hq0 hqe

/-- **ν-compatibility** of the tame and pro-2 legs, from `ν_N`'s normalization (§0). -/
theorem pilotCompat (hq0 : q ≠ 0) (hqe : Even q) (g : ((pilotGamma q : Type))) :
    nuTq q (tameOfSpec 2 q pilotW (pilotTameSpec hq0 hqe) g)
      = pilotNuP (pilotPro2 hq0 hqe g) :=
  CorePresentation.nu_compat_coreHom (nCorePresentation 2 0) hq0 hqe
    (pilotTameSpec hq0 hqe) pilotNuP
    (by rw [nCorePresentation_mark_sigma]; exact pilotNuP_dnSigma)
    (fun i => by rw [nCorePresentation_mark_wild]; exact pilotNuP_wild i) g

/-- **The candidate-side determinant residual, named** — the whole
`AffineDeterminantCertificate` at `Γ_R`.  ⚠ The count lane closed 9 of the 11 `SourceDataN`
clauses on the candidate side; the two Gauss-`Z` clauses have **no candidate-side supplier in
the repository** (CB-DET's `GaussZ/FinalDK.lean` is the `K`-side bridge; WN0-c's word-side
Hessian layer exists but the Hessian ⇒ `GaussZResidueK` bridge does not).  **Owner:** CB1
memo's "gauss 1900" candidate-side ticket, unopened. -/
def PilotDet (q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) : Prop :=
  AffineDeterminantCertificate (pilotGamma q) 2 q pilotP pilotNuP (standardNumerics 2)
    (tameOfSpec 2 q pilotW (pilotTameSpec hq0 hqe)) (pilotPro2 hq0 hqe)
    (pilotCompat hq0 hqe) (scalarActionZmodTwo ((pilotGamma q : Type)))

/-- **The pilot word certificate** — packet Def. 9.1 / ledger §5.2 at the frozen `√−2` row,
`q`-generic (instantiated at `q = q_K` by §7).  Every field is landed except the four named
residuals, threaded as binders: `hsimp` (the row's per-simple-module Stokes duality, feeding
every count-lane payload), `hsplit`/`hZcount` (`stageR136`'s recursion-side residues) and
`hdet` (the candidate-side Gauss clauses). -/
noncomputable def sqrtNegTwoWordCertificate (hq0 : q ≠ 0) (hqe : Even q)
    (hsimp : PilotHsimp q) (hsplit : PilotStageSep q) (hZcount : PilotStageZ q)
    (hdet : PilotDet q hq0 hqe) :
    WordCertificate 2 q pilotW pilotP (isProP_DN 2 0) pilotNuP (standardNumerics 2) where
  tameSpecialization := pilotTameSpec hq0 hqe
  coreRel := fun _ _ _ _ _ _ t =>
    MarkedCore.nRelWord (h := 0) 2 (MarkedCore.coreMark (t.x 0) (t.x 1) t.σ (t.x 2))
  proTwoWord := fun _ _ _ _ _ _ t => eval_pro2_nCompact_eq_nRelWord 2 t
  pro2 := pilotPro2 hq0 hqe
  ker_pro2 := CorePresentation.ker_coreHom (nCorePresentation 2 0) hq0 hqe
  hpro2 := CorePresentation.coreHom_surjective (nCorePresentation 2 0) hq0 hqe
  compat := pilotCompat hq0 hqe
  tfg := GQ2.Dyadic.Count.gammaR_topologicallyFinitelyGenerated 2 q pilotW
  smulZmod2 := scalarActionZmodTwo ((pilotGamma q : Type))
  contSMulZmod2 := scalarActionZmodTwo_continuousSMul ((pilotGamma q : Type))
  htriv := scalarActionZmodTwo_triv ((pilotGamma q : Type))
  exactLifting := sqrtNegTwo_exactLifting hsimp hq0 hqe hsplit hZcount
  stokes := sqrtNegTwo_stokes hsimp hq0 hqe
  scalar := sqrtNegTwo_scalar hsimp hq0 hqe
  determinant := hdet
  htame := htame_of_tameSpecializes (pilotTameSpec hq0 hqe)
  hwild := hwild_nCompact (q := q) (α := 2) (h := 0) (pilotTameSpec hq0 hqe)

end TheCertificate

/-! ## §6 The `K`-side supply: the marked-core composite, written down

ASK left four `KSupply` fields carried "per branch, via `marked_matching_certificate_KN` —
not new mathematics: AS1 identified the composite; nobody has written it down".  This section
writes it down, and the writing-down surfaces one datum the prose composite missed: the
**abelianization slot** `piAb : G_K(2) →* G_K^{ab}` with its `ν`-compatibility `hpiNu` against
`toAbK`.  The `K`-layer certificate reads both marked characters through `piAb`
(`MarkedCoreCertificateKN B α h π`), and the record's `nu_compat` is stated at `toAbK`; since
`toAbK` itself does **not** factor through the pro-2 quotient (the abelianization is not
pro-2), the composite needs the slot and the compatibility as data — mathematically, the
inclusion of the pro-2 direct factor of the abelianized local Galois group.  Recorded as two
binders of the G-Lab pack. -/

section KSide

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity} {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}
  {T : OrientedTameQuotientK B FF}

/-- **The `K`-side supply at the pilot** — `KSupply` with the pro-2 block built from the
marked-core certificate (MC-N's `marked_matching_certificate_KN`, its G-Lab binder state kept
as binders), the determinant discharged by CB-DET's `affineDeterminant_galK`, and ASK's two
remaining carried leaves (`hexact`/`hstokes`) threaded.

The G-Lab pack, with owners: `fLab` (the Labute/Demushkin classification of `G_K(2)` at the
compact-`N` core — N-Lab, gate G-Lab), `piAb`/`hpiAb`/`hpiNu` (the abelianization slot, see
the section docstring), `horient` (packet §7's orientation datum), `hScal` (MC-N's
`NScalingHypothesis`), `hpair` (marked-data pair-unimodularity). -/
noncomputable def sqrtNegTwoKSupply
    (hdeg : Module.finrank ℚ_[2] K = 2)
    (fLab : ContinuousMulEquiv ((DN 2 0) : Type) ((maxProPQuotient 2 (GalK K)) : Type))
    (piAb : ((maxProPQuotient 2 (GalK K)) : Type) →* GalKab K) (hpiAb : Continuous piAb)
    (hpiNu : ∀ g : GalK K, B.nu_ur (piAb (maxProPMk 2 (GalK K) g)) = B.nu_ur (toAbK K g))
    (horient : ∀ x, chiCycKAb K (piAb (fLab x)) = chiN 2 0 x)
    (hScal : NScalingHypothesis 2 0)
    (hpair : IsUnit (Multiplicative.toAdd (B.nu_ur (piAb (fLab (dnSigma 2 0)))))
      ∨ IsUnit (Multiplicative.toAdd (B.nu_ur (piAb (fLab (dnX2 2 0))))))
    (hexact : ExactLiftingSemantics (galKProfinite K) 2 (qOf K FF) pilotP pilotNuP
      (standardNumerics 2))
    (hstokes : StokesDualityCertificate (galKProfinite K) 2 (qOf K FF) pilotP pilotNuP
      (standardNumerics 2) (smulZmod2GalK K))
    (params : FieldParameters) (params_n : params.n = 2) (params_qK : params.qK = qOf K FF)
    (ramifiedData : ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
      (V : Type) [AddCommGroup V] [DistribMulAction D V]
      (c : ContinuousMonoidHom (Tq params.qK) D)
      (rho : ContinuousMonoidHom ↥(GalKsub K) D),
      (∃ v : V, c (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) V c rho)) :
    KSupply T 2 pilotP (isProP_DN 2 0) pilotNuP (standardNumerics 2) :=
  -- the marked-core certificate, and the ν-corrected identification `E : D_N ≅ G_K(2)`
  letI C := (marked_matching_certificate_KN B 2 0 piAb hpiAb fLab horient hScal hpair).some
  letI E : ContinuousMulEquiv ((DN 2 0) : Type) ((maxProPQuotient 2 (GalK K)) : Type) :=
    C.correction.trans C.abstractEquiv
  letI pro2K : ContinuousMonoidHom (GalK K) ((DN 2 0) : Type) :=
    ⟨E.symm.toMulEquiv.toMonoidHom.comp (maxProPMk 2 (GalK K)).toMonoidHom,
      E.symm.continuous_toFun.comp (maxProPMk 2 (GalK K)).continuous_toFun⟩
  have hnu : ∀ g : GalK K, ztwoIota (pilotNuP (pro2K g)) = B.nu_ur (toAbK K g) := by
    intro g
    have h2 := C.correction_nu (E.symm (maxProPMk 2 (GalK K) g))
    have h3 : E (E.symm (maxProPMk 2 (GalK K) g)) = maxProPMk 2 (GalK K) g :=
      E.apply_symm_apply _
    calc ztwoIota (pilotNuP (pro2K g))
        = nuN 2 0 (E.symm (maxProPMk 2 (GalK K) g)) := ztwoIota_pilotNuP _
      _ = B.nu_ur (piAb (E (E.symm (maxProPMk 2 (GalK K) g)))) := h2.symm
      _ = B.nu_ur (piAb (maxProPMk 2 (GalK K) g)) := by rw [h3]
      _ = B.nu_ur (toAbK K g) := hpiNu g
  { hdeg := hdeg
    hhom := rfl
    pro2 := pro2K
    hpro2 := fun y => by
      obtain ⟨g, hg⟩ := quotientMk_surjective _ (E y)
      exact ⟨g, by
        show E.symm (maxProPMk 2 (GalK K) g) = y
        rw [show maxProPMk 2 (GalK K) g = E y from hg]
        exact E.symm_apply_apply y⟩
    ker_pro2 := by
      ext g
      rw [MonoidHom.mem_ker]
      constructor
      · intro hg
        have hg' : E.symm (maxProPMk 2 (GalK K) g) = 1 := hg
        have h1 : maxProPMk 2 (GalK K) g = 1 := by
          have h0 := congrArg E hg'
          rwa [E.apply_symm_apply, map_one] at h0
        exact (ker_maxProPMk (GalK K)).le (MonoidHom.mem_ker.mpr h1)
      · intro hg
        show E.symm (maxProPMk 2 (GalK K) g) = 1
        have h1 : maxProPMk 2 (GalK K) g = 1 :=
          MonoidHom.mem_ker.mp ((ker_maxProPMk (GalK K)).ge hg)
        rw [h1, map_one]
    nu_compat := hnu
    exactLifting := hexact
    stokes := hstokes
    determinant := affineDeterminant_galK K params params_n params_qK hdeg
      (fun _ => rfl) (fun _ => rfl) T.tameFK T.tameFK_surjective pro2K
      (fun g => T.compatF_K pro2K pilotNuP hnu g) ramifiedData }

end KSide

/-! ## §7 The headline: packet Thm. 1.1 at the pilot -/

section Headline

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity} {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}

/-- **Packet Theorem 1.1 at the frozen pilot row** — the campaign's first complete general-`K`
instance:

`Γ_{R_{N,2,0}} = ⟨σ, τ, x₀, x₁, x₂ ∣ τ^σ = τ^{q_K}, x₀⁶[x₀,x₁]·x₂^{-σ}(x₂τ)^{ω₂} = 1⟩ ≅ G_K`

for a supplied quadratic `K` on the ramified-`i` branch (the intended `K` is `ℚ₂(√−2)`).

The hypothesis surface is exactly the file's named-residuals list (module docstring): the
arithmetic bundles `(B, FF, T)` per the ASK posture, the G-Lab pack, the two `K`-side carried
leaves, the four candidate-side residuals, and packet §12's field-side inputs.  Everything
else — the word certificate, the marked-core composite, the determinant bridge and the final
assembly — is landed mathematics, cited. -/
theorem sqrtNegTwo_candidate_equiv_galK (T : OrientedTameQuotientK B FF)
    (hdeg : Module.finrank ℚ_[2] K = 2)
    (fLab : ContinuousMulEquiv ((DN 2 0) : Type) ((maxProPQuotient 2 (GalK K)) : Type))
    (piAb : ((maxProPQuotient 2 (GalK K)) : Type) →* GalKab K) (hpiAb : Continuous piAb)
    (hpiNu : ∀ g : GalK K, B.nu_ur (piAb (maxProPMk 2 (GalK K) g)) = B.nu_ur (toAbK K g))
    (horient : ∀ x, chiCycKAb K (piAb (fLab x)) = chiN 2 0 x)
    (hScal : NScalingHypothesis 2 0)
    (hpair : IsUnit (Multiplicative.toAdd (B.nu_ur (piAb (fLab (dnSigma 2 0)))))
      ∨ IsUnit (Multiplicative.toAdd (B.nu_ur (piAb (fLab (dnX2 2 0))))))
    (hexact : ExactLiftingSemantics (galKProfinite K) 2 (qOf K FF) pilotP pilotNuP
      (standardNumerics 2))
    (hstokes : StokesDualityCertificate (galKProfinite K) 2 (qOf K FF) pilotP pilotNuP
      (standardNumerics 2) (smulZmod2GalK K))
    (hsimp : PilotHsimp (qOf K FF)) (hsplit : PilotStageSep (qOf K FF))
    (hZcount : PilotStageZ (qOf K FF))
    (hdet : PilotDet (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF))
    (params : FieldParameters) (params_n : params.n = 2) (params_qK : params.qK = qOf K FF)
    (ramified : ∀ δi : ℚ̄₂, δi ^ 2 = -1 → ¬ HasEqualNormValueGroups K δi)
    (ramifiedData : ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
      (V : Type) [AddCommGroup V] [DistribMulAction D V]
      (c : ContinuousMonoidHom (Tq params.qK) D)
      (rho : ContinuousMonoidHom ↥(GalKsub K) D),
      (∃ v : V, c (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) V c rho)) :
    Nonempty (ContinuousMulEquiv ((candidateGroup 2 (qOf K FF) pilotW : Type)) (GalK K)) :=
  candidate_equiv_galK_of_supply (T := T)
    (sqrtNegTwoWordCertificate (qOf_ne_zero K FF) (even_qOf K FF) hsimp hsplit hZcount hdet)
    (sqrtNegTwoKSupply hdeg fLab piAb hpiAb hpiNu horient hScal hpair hexact hstokes
      params params_n params_qK ramifiedData)
    params params_n params_qK ramified ramifiedData pilotNuP_surjective

end Headline

end SqrtNeg2

end GQ2.Dyadic
