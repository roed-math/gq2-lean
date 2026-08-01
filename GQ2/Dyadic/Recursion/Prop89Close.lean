/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Recursion.Phase140Assembly
import GQ2.Dyadic.Recursion.Numerics
import GQ2.Dyadic.Recursion.MStageCount
import GQ2.Prop89Close

/-!
# The Prop. 8.9 close at the `K`-boundary (dyadic campaign, ticket SD-R3)

Clone of the **generic half** of `GQ2/Prop89Close.lean` (424 ln), re-typed at the general
`K`-boundary and fully numerically parameterized — plus the predicted omega seam.  This is the
last file of the SD-R spine clone: everything above it exists so that this file can hand SD3 a
**one-sided, source-generic `ClosedRecursionK` producer** to apply twice.

## Finding: the model's file is a three-way split, and only the middle third is SD-R work

* **boundary-free (consumed by import)** — the whole `PhaseWitness` section (`:78-135`):
  `descentOf`, `trivialPhaseCover`, `phaseFamily`, `phaseFamily_pos`.  Only `muZero` (`:130`)
  needs a clone, and not for boundary reasons — for the memo §4.1(c) `tMult` parameterization.
* **`Γ_A`-typed (NOT spine)** — the `Half139GammaA` section (`:145-192`): `hlem86M_gammaA`,
  `hMcountM_gammaA`, `half139_gammaA` are the `Γ_A` **instantiation**, and
  `prop_8_9_of_source` (`:245`) / `prop_8_9` (`:377`) carry `B : BoundaryMaps` and the
  `AbsGalQ2` instance package.  None of these clone: under the two-sided restatement (memo §3.1)
  the B-side special-casing disappears and both sides go through the record.
* **`b`-typed generic (cloned below)** — `half139_of_leaves` (`:218`).

## What this file adds beyond cloning

Two declarations that have no single model theorem, both of which SD3 needs and neither of which
belongs to SD3's own file:

**1. `nPhaseK_eq_of_strata` — the predicted omega seam.**  The board predicted one omega seam at
`GQ2/ThmFourTwo.lean:285` (`rStage_phase`, `private`).  Confirmed exactly there, and it is the
memo §4.1(a) pattern: the model derives `8 * liftableCount(source) = 8 * liftableCount(local)`
from `lemma_8_3` on both sides and cancels the literal `8` by `omega`.  With the scalar an opaque
`cS` that `omega` cannot fire, so it becomes `Nat.eq_of_mul_eq_mul_left hcS` at a threaded
positivity hypothesis — the record field `SN.homScalar_pos` (`Numerics.lean:57`), which SD2
supplies and SD3 feeds.  This is the same fix SD-R2 applied at its own `hcS` seam.

The theorem is stated **two-sidedly and at two different `Γ`s** (`Γ₁`, `Γ₂`), because that is what
the two-sided assembly needs: at `n = 1` the sides are `S.Γ` and `AbsGalQ2`.  Only the phase-count
equality is packaged here; the strata hypothesis `hstr` stays SD3's, since deriving it is the
induction step.

**2. `closedRecursionK_of_source` — the one-sided generic Prop 8.9 producer.**  The model's
`prop_8_9_of_source` is a *hybrid*: source-side through hypotheses, `G_ℚ₂`-side through the
`_local` pack, with the shared `(μ, G⁰, D_T, phase)` packaged existentially in one theorem.  That
shape cannot be cloned two-sidedly.  The clone factors it: this file proves the **one-sided**
statement "these residues ⟹ `ClosedRecursionK` at this shared data", and SD3 applies it once per
source and packages the ∃.  The `_local` branch of the model's proof (`:348-360`) simply becomes a
second application — which is precisely memo §8's "the `_local` branch disappears".

It is also stated at a general `RF : RecursionFrame T Blk` rather than at `blockFrameImpl`: the
model specializes only because it discharges the (136) leaf internally from `lemma_7_2`, and here
(136) arrives as the hypothesis `hstage` (produced by `blockStageR136K_ofSplitCriterion`).  So the
`hRK`/`hR2` plumbing of `prop_8_9_of_source`'s `hstageS` is gone too.

## Parameterization delta versus the `ℚ₂` model

All three memo §4.1 shapes are live here simultaneously, as the opaque `cS` / `mM` / `vH` of
`ClosedRecursionK` plus `tMult` inside `muZeroN`.  `muZeroN_standard` is the `n = 1` bridge and is
`rfl` (`standardNumerics 1 |>.tMult T = T ^ 2` definitionally, `Numerics.lean:101`).

Plain-import (memo §5).

Axioms: none beyond std-3.  Print check performed for every declaration in this file: each
prints `[propext, Classical.choice, Quot.sound]`, equal to its model's print — hence a subset.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh LocalLiftingDuality FoxH

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}

/-! ## The shared `T`-cocycle count `μ₀`, at a parameterized multiplicity -/

/-- **The shared `T`-cocycle count `μ₀`** at a parameterized multiplicity.  Clone of
`GQ2.SectionEight.muZero` (`GQ2/Prop89Close.lean:130`); the model's `^ 2` on the `T`-factor
becomes the opaque `tMult` (memo §4.1(c) — `SN.tMult` at instantiation).  The `fixedPts` factor
is a separate literal factor of the field shape and does not move.

Boundary-free, like its model: this is a numeric parameterization, not a re-typing. -/
noncomputable def muZeroN {RF : RecursionFrame T Blk} (tMult : ℕ → ℕ) (En : RF.Enrichment)
    (l₀ : RF.DR) (h₀ : l₀ ≠ RF.zeroDR) : ℕ :=
  tMult (Nat.card (Additive ↥(En.radData l₀ h₀).T))
    * Nat.card (fixedPts (RF.YB ⧸ (En.radData l₀ h₀).M)
        (ElemDual (Additive ↥(En.radData l₀ h₀).T)))

/-- **The `n = 1` bridge for `μ₀`** — `rfl`: `(standardNumerics 1).tMult T = T ^ 2`
definitionally (`Numerics.lean:101`), so the parameterized `μ₀` **is** the model's. -/
theorem muZeroN_standard {RF : RecursionFrame T Blk} (En : RF.Enrichment)
    (l₀ : RF.DR) (h₀ : l₀ ≠ RF.zeroDR) :
    muZeroN (standardNumerics 1).tMult En l₀ h₀ = muZero En l₀ h₀ := rfl

/-! ## The (139) half count from the source leaves -/

section SourceGeneric

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ]

/-- **The (139) half count from the source leaves** at the `K`-boundary, at an opaque
multiplicity `mM`.  Clone of `GQ2.SectionEight.half139_of_leaves`
(`GQ2/Prop89Close.lean:218`); the model's `(Nat.card ↥RF.MB) ^ 2` becomes `mM` (memo §4.1(b)).

The exact `RecursionInputsK.half139` shape for an abstract source, from the source's Lemma 8.6
half-torsor obligation and its `M`-lift count obligation, assembled through
`half139_via_radDataK`. -/
theorem half139_of_leavesK
    (RF : RecursionFrame T Blk) (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (mM : ℕ)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (hlem86 : ∀ {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
      (D : RadicalCoverData Bg), D.NoDescent →
      ∀ (ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)), Function.Surjective ρ →
        2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ))
    (hMcount : ∀ ρ : BoundaryLiftsK b F RF.TC, Nat.card (LiftsOverK RF b F ρ) = mM)
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (hedge : ¬∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
      N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) :
    2 * zBCK RF b F l h = mM * exactImageCountK b F RF.TC :=
  half139_via_radDataK RF b F En l h mM hfg
    (fun ρ => hlem86 (En.radData l h) hedge (rhoPrimeK RF b F (En.radData l h) rfl ρ)
      (rhoPrimeK_surjective RF b F (En.radData l h) rfl ρ))
    (fun ρ => (Nat.card_congr (liftsOverK_equiv RF b F (En.radData l h) rfl ρ)).symm.trans
      (hMcount ρ))

end SourceGeneric

/-! ## The omega seam: phase counts agree, cancelled at a positivity hypothesis -/

/-- **The `R`-stage phase-cover counts agree**, at an opaque scalar — **the SD-R3 omega seam**.

Generic core of the `private` `GQ2.rStage_phase` (`GQ2/ThmFourTwo.lean:242-285`), stated
two-sidedly over two independent source groups `Γ₁`, `Γ₂` sharing one boundary frame.

The seam: the model finishes from `lemma_8_3` on both sides with

    `8 * liftableCount(b₁) = 8 * liftableCount(b₂)`  ⟹  `omega`  (`ThmFourTwo.lean:285`)

and `omega` cannot cancel a *variable* coefficient.  So the clone threads
`hcS : 0 < cS` and finishes with `Nat.eq_of_mul_eq_mul_left` — exactly the substitution memo
§4.1(a) predicted, and the same one SD-R2 made at its `hcS` seam.  SD3 supplies `hcS` from the
record field `SourceNumerics.homScalar_pos`.

`hstr` — agreement of the proper `C`-strata counts — is **not** discharged here: it is the
induction hypothesis applied at the `(145)/(148)/(153)` bounds, which is SD3's step. -/
theorem nPhaseK_eq_of_strata (RF : RecursionFrame T Blk) (F : BoundaryFrameK q P H E)
    {Γ₁ : Type} [Group Γ₁] [TopologicalSpace Γ₁] [IsTopologicalGroup Γ₁] [CompactSpace Γ₁]
    [TotallyDisconnectedSpace Γ₁]
    {Γ₂ : Type} [Group Γ₂] [TopologicalSpace Γ₂] [IsTopologicalGroup Γ₂] [CompactSpace Γ₂]
    [TotallyDisconnectedSpace Γ₂]
    (b₁ : ContinuousMonoidHom Γ₁ ↥(boundarySubgroupQ q nuP))
    (b₂ : ContinuousMonoidHom Γ₂ ↥(boundarySubgroupQ q nuP))
    (hfg₁ : ∃ s : Finset Γ₁, (Subgroup.closure (s : Set Γ₁)).topologicalClosure = ⊤)
    (hfg₂ : ∃ s : Finset Γ₂, (Subgroup.closure (s : Set Γ₂)).topologicalClosure = ⊤)
    (cS : ℕ) (hcS : 0 < cS)
    (hscalar₁ : Nat.card (ContinuousMonoidHom Γ₁ (Multiplicative (ZMod 2))) = cS)
    (hscalar₂ : Nat.card (ContinuousMonoidHom Γ₂ (Multiplicative (ZMod 2))) = cS)
    (Cζ : CentralCover RF.YC)
    (hstr : ∀ J' ∈ {J' : Subgroup Cζ.cover | J'.map Cζ.p = ⊤},
      exactImageCountOnK b₁ F (Cζ.pullTarget RF.TC) J'
        = exactImageCountOnK b₂ F (Cζ.pullTarget RF.TC) J') :
    nPhaseK RF b₁ F Cζ = nPhaseK RF b₂ F Cζ := by
  have h8₁ := lemma_8_3K hfg₁ b₁ F RF.TC Cζ cS hscalar₁ ⊤ RF.TC.top_head_surjective
  have h8₂ := lemma_8_3K hfg₂ b₂ F RF.TC Cζ cS hscalar₂ ⊤ RF.TC.top_head_surjective
  have heq : cS * liftableCountK b₁ F RF.TC Cζ ⊤ RF.TC.top_head_surjective
      = cS * liftableCountK b₂ F RF.TC Cζ ⊤ RF.TC.top_head_surjective := by
    rw [h8₁, h8₂]
    exact finsum_mem_congr rfl hstr
  rw [nPhaseK_eq_liftableCountK_top RF b₁ F Cζ, nPhaseK_eq_liftableCountK_top RF b₂ F Cζ]
  -- the seam: `omega` at the model's literal `8` becomes a positivity-cancel at the opaque `cS`
  exact Nat.eq_of_mul_eq_mul_left hcS heq

/-! ## The one-sided generic `ClosedRecursionK` producer -/

section Producer

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

open scoped Classical in
/-- **Proposition 8.9 over one abstract source**, at the `K`-boundary and fully numerically
parameterized: the source's residues produce the boxed system `ClosedRecursionK` at the shared
data `(μ, G⁰, D_T, phase)` read off a reference edge `(l₀, h₀)`.

Generic half of `GQ2.SectionEight.prop_8_9_of_source` (`GQ2/Prop89Close.lean:245`), refactored
one-sidedly per this file's header.  **SD3 applies this once per source** with the same
`(l₀, h₀)`, `Fintype` instance, `G0`, `tMult` and `En` — the two `ClosedRecursionK`s then share
`μ`, `G⁰`, `D_T` and `phase` syntactically, which is what the two-sided theorem requires.

The obligations are in the exact shapes of the model's `_gammaA`/`_local` supply lemmas, so the
`n = 1` instantiation is unchanged; the numeric slots are `cS` (memo §4.1a), `mM` (§4.1b),
`vH` and `tMult` (§4.1c). -/
theorem closedRecursionK_of_source (RF : RecursionFrame T Blk) (En : RF.Enrichment)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (l₀ : RF.DR) (h₀ : l₀ ≠ RF.zeroDR) [Fintype ↥(TCharC (En.radData l₀ h₀))]
    (cS mM vH : ℕ) (tMult : ℕ → ℕ) (G0 : ℤ)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (hscalar : Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) = cS)
    (hH2 : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hhead : Function.Surjective (fun γ : Γ => (F.frameMap (b γ)).1))
    (hstage : (Nat.card RF.DR : ℤ) * exactImageCountK b F T
      = RF.zR * ∑ᶠ l : RF.DR, (2 * (mBK RF b F l : ℤ) - exactImageCountK b F RF.TB))
    (hlem86 : ∀ {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
      (D : RadicalCoverData Bg), D.NoDescent →
      ∀ (ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)), Function.Surjective ρ →
        2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ))
    (hMcount : ∀ ρ : BoundaryLiftsK b F RF.TC, Nat.card (LiftsOverK RF b F ρ) = mM)
    (htcoc : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (ρ : BoundaryLiftsK b F RF.TC),
      Nat.card (TCocycle (En.radData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
        = tMult (Nat.card (Additive ↥(En.radData l h).T))
          * Nat.card (fixedPts (RF.YB ⧸ (En.radData l h).M)
              (ElemDual (Additive ↥(En.radData l h).T))))
    (hsep : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (Dsc : Descent (En.radData l h))
      (ρ : BoundaryLiftsK b F RF.TC)
      (c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ)),
      (∀ χ : ↥(TCharC (En.radData l h)),
        betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c = 0) →
        TLiftable (descSigma_spec En l h Dsc) c)
    (hpartial : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (Dsc : Descent (En.radData l h))
      (ρ : BoundaryLiftsK b F RF.TC)
      (χ : ↥(TCharC (En.radData l h))), χ ≠ 0 →
      ∃ c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ),
        betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
          ≠ betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ
              (0 : VCocycle (En.descData l h)
                (rhoPrimeK RF b F (En.radData l h) rfl ρ)))
    (hZcard : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (ρ : BoundaryLiftsK b F RF.TC),
      Nat.card (VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
        = Nat.card En.Vmod * vH)
    (hGaussZ : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR), GaussZResidueK b F En l h G0) :
    ClosedRecursionK RF b F (Nat.card En.Vmod * muZeroN tMult En l₀ h₀) G0
      ↥(TCharC (En.radData l₀ h₀)) (phaseFamily En l₀ h₀) cS mM vH := by
  classical
  refine prop_8_9_auxK RF hfg b F cS hscalar hhead _ _ _ _ _ _ ?_
  refine ⟨hstage, fun l h hedge => ?_, fun l h hN => ?_⟩
  · exact half139_of_leavesK RF b F En mM hfg hlem86 hMcount l h hedge
  · -- (140) for this source: the four residues through the source-generic assembly, at the
    -- unpacked descent + the `dif_pos`-reduction of the phase family
    have h140 := phase140_from_residuesK b F En l h (descentOf En l h hN)
      htriv hfg hH2 (muZeroN tMult En l₀ h₀) vH G0
      (fun ρ => (tcocycle_cardK_l_indep RF b F En l h l₀ h₀ ρ).trans (htcoc l₀ h₀ ρ))
      (fun ρ => hsep l h (descentOf En l h hN) ρ)
      (fun ρ => hpartial l h (descentOf En l h hN) ρ)
      (fun ρ => hZcard l h ρ)
      (hGaussZ l h)
    simp only [phaseFamily_pos En l₀ h₀ l h hN]
    exact h140

open scoped Classical in
/-- **The degenerate branch**: no nonzero scalar character exists, so (137)–(140) are vacuous and
only the (136) stage is live.  Generic half of the second branch of
`GQ2.SectionEight.prop_8_9_of_source` (`GQ2/Prop89Close.lean:361-367`), one-sided.

Stated at arbitrary shared data so SD3 can apply it to both sources at the *same*
`(μ, G⁰, D_T, phase)` — the model picks `⟨1, G0, PUnit, …⟩`. -/
theorem closedRecursionK_of_source_degenerate (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (cS mM vH μ : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT]
    (phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (hscalar : Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) = cS)
    (hhead : Function.Surjective (fun γ : Γ => (F.frameMap (b γ)).1))
    (hex : ¬∃ l : RF.DR, l ≠ RF.zeroDR)
    (hstage : (Nat.card RF.DR : ℤ) * exactImageCountK b F T
      = RF.zR * ∑ᶠ l : RF.DR, (2 * (mBK RF b F l : ℤ) - exactImageCountK b F RF.TB)) :
    ClosedRecursionK RF b F μ G0 DT phase cS mM vH :=
  prop_8_9_auxK RF hfg b F cS hscalar hhead _ _ _ _ _ _
    ⟨hstage, fun l h => absurd ⟨l, h⟩ hex, fun l h => absurd ⟨l, h⟩ hex⟩

end Producer

end GQ2.Dyadic
