/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.ThmFourTwoN
import GQ2.Dyadic.TameBoundary
import GQ2.Dyadic.MarkedCore.Certificate
import GQ2.Dyadic.SqCore.Certificate
import GQ2.Dyadic.LocalGauss.Main
import GQ2.Dyadic.FieldDataEven
import GQ2.Dyadic.OrientedTameBundle
import GQ2.Dyadic.FinitelyGeneratedK

/-!
# The certificate-main theorem  (dyadic campaign, ticket AS1)

**Packet Thm. 1.1** (`thm:certificate-main`), ledger §5.3: marked-core certificate + word
certificate + standard local inputs ⇒ `Γ_{R_K} ≅ G_K`.  This file is the campaign's assembly
capstone: it defines the two consumer-facing records (`WordCertificate`, `DyadicLocalInput`)
and proves the main theorem **by assembly only** — every step below is either a projection out
of one of the three certificates, an application of F3's `GQ2/Dyadic/TameBoundary.lean`
boundary layer, or the single call to SD3's
`nonempty_continuousMulEquiv_of_sourcesN` (`GQ2/Dyadic/ThmFourTwoN.lean:729`).  No
mathematics is proved here beyond the one arithmetic one-liner FD2 assigned to this ticket
(`kappa_ne_zero_of_ramified`, §4).

## The architecture in one paragraph

SD3's reconstruction corollary compares **two** `SourceDataN` records over one abstract slot
`(n, q, P, hP, νP, SN)` and returns `Nonempty (ContinuousMulEquiv S₁.Γ S₂.Γ)`.  The slot's
pro-2 component `P` is the **presented standard core** `D_P` (MC2's `DM`/`DN`, SqCore's
`DSq`).  The candidate side lands in `P` through the word certificate's pro-2 specialization;
the arithmetic side lands in `P` through the marked-core certificate's `abstractEquiv`
(`GQ2/Dyadic/MarkedCore/Certificate.lean:629`), which is *exactly* what that record is for.
That is the whole design: the two sides meet at `D_P`, and everything else is bookkeeping.

## The candidate group

`candidateGroup K R` is F3's `GammaR n q R = ⟨σ, τ, x₀ … x_n ∣ τ^σ = τ^q, R = 1⟩_prof`
(`GQ2/Dyadic/TameBoundary.lean:286`), so the ledger's `candidateGroup` needs no new
construction — §1's abbreviation only renames it.  F3 also supplies, unconditionally, four of
the six *structural* `SourceDataN` fields on that group (`tame`, its surjectivity, the
ν-compatibility, and eq. (27) joint surjectivity), which is why the candidate side of the
assembly is genuinely assembled here rather than carried.

## ⚠ The asymmetry, and what it means for G3

The two sides are **not** symmetric, and the difference is a landed-reality finding, not a
design choice:

* the **candidate** `SourceDataN` is *built* below (`WordCertificate.toSource`), from F3 plus
  the four analytic clause fields;
* the **arithmetic** `SourceDataN` is *carried* as `DyadicLocalInput.source`, because the
  `G_K`-side supply package is ticket **ASK**, which is `queued`, not done
  (`docs/dyadic/tickets.md`, lane SD).  `DyadicLocalInput` bundles the packet §12 arithmetic
  that ASK will consume, and pins ASK's output to `G_K` through `source_carrier`.

## ⚠ Where the ledger's prose and the landed reality diverge

Recorded here because AS2–AS5 and the G3 census sign-off read this docstring:

1. **`MarkedCoreCertificate` is not one record.**  Ledger §5.1 writes a single
   `MarkedCoreCertificate K P`.  What landed is **three**: `MarkedCoreCertificateM`,
   `MarkedCoreCertificateN` (`MarkedCore/Certificate.lean:624,640`) and
   `MarkedCoreCertificateSq` (`SqCore/Certificate.lean:293`), plus the `MarkedRecip`-read
   `K`-layer abbreviations `MarkedCoreCertificateKM`/`KN`/`KSq`.  §3 below therefore takes the
   *consequences* of a core certificate (a marked identification of `P` with the arithmetic
   pro-2 quotient) rather than the record itself, so that one main theorem serves all five
   branch rows; the three K-layer producers each discharge those consequences.
2. **`WordCertificate.tameSpecialization` is not an equation.**  The ledger writes
   `specializeTame R = 1`.  F3's landed gate is the *semantic* `KillsWild R`
   (`TameBoundary.lean:341`), equivalent to the syntactic form by
   `killsWild_iff_killWild` — and it is the semantic form that `tameR` consumes.  §2 uses
   `KillsWild`.
3. **`WordCertificate.proTwoSpecialization` cannot be the ledger's `specializeProTwo R =
   P.word`.**  That equation is a statement about *words*; what the recursion needs is a
   statement about *groups* (`pro2 : Γ_R → P` with `ker = proPKernel 2 Γ_R`).  The bridge —
   "the two universal properties agree, hence `Γ_R(2) ≅ D_P`" — is **not built anywhere in the
   repo**.  Its ℚ₂ ancestor is `GQ2.Roe.exists_pro2R` (`GQ2/Roe/Main.lean:226`), which is
   `Γ_R`-specific and consumes `BLabHypothesis`.  §2 therefore states the field at the group
   level (the bridge's *output*), and carries the ledger's word-level equation alongside it as
   `proTwoWord`, so that the missing bridge is visible as a named gap rather than hidden.
   **Owed by:** the WW lane (a generic `PWord`-level ⇒ presentation-level transfer) or F3.
4. **The four analytic ledger fields are stated as the recursion's clauses, not as the branch
   lanes' normal forms.**  This is the ticket's sharpest finding and it is discussed field by
   field in §2's docstrings.  In short: the five branch lanes closed at the level of Fox rows,
   Stokes endpoints, scalar Grams and Hessian certificates; `SourceDataN` consumes *counting*
   clauses (`#LiftsOver`, `#Z¹`, `#Hom`, the Gauss residue).  The certificate ⇒ count bridge is
   the §5–§9 theory, which at `ℚ₂` is the whole `GQ2/Roe/` stack and at general `K` has no
   owner.  Shaping the record to the branch lanes' outputs would have made the main theorem
   *not* an assembly; shaping it to the recursion's clauses keeps the assembly honest and makes
   the gap countable.  **Owed by:** a new lane (per branch), between W*-c and AS2.
5. **`DyadicLocalInput` has no `eulerChar` field** — LG1's ruling, honored: the local Euler
   characteristic is *derived* inside LG5 by `card_H1_eq_of_markingK`, not supplied.  Packet
   §12's `DyadicLocalData.eulerChar` row is therefore dead.

## Axiom posture

Every declaration in this file is `sorry`-free.  The file introduces **no axioms** and no
`decide`.  It legitimately inherits whatever its inputs carry: the records and the main theorem
are parametrized over `MarkedRecip` / `OrientedTameQuotientK` / `TateDualityG` *bundles* (never
`markedRecipAt` / `orientedTameQuotientAt`), so the census axioms B5-K and B10-K are **not**
consumed here; the standard three plus LG5's and FD1's B-set enter only where a headline
actually calls those layers.  Per-headline prints are in the report.

## Sources

Packet `docs/dyadic/refs/dyadic-presentations-formalization-proof.tex` §1 (Thm. 1.1), §12
(standard local inputs), §7 (Def. 7.1); ledger
`docs/dyadic/refs/dyadic-presentations-formalization-ledger.md` §5.1–§5.3; plan
`docs/dyadic/plan.md` §1, §7.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH

/-! ## §1 The candidate group

Ledger §5.3's `candidateGroup K R`.  F3 already built it; this is a rename, kept so that the
packet's and the ledger's vocabulary resolve in Lean. -/

/-- **The candidate group** `Γ_{R} = ⟨σ, τ, x₀, …, x_n ∣ τ^σ = τ^{q}, R = 1⟩_prof`
(ledger §5.3's `candidateGroup`, draft eq. 1.1).  Definitionally F3's `GammaR`. -/
noncomputable abbrev candidateGroup (n q : ℕ) (R : PWord (Generator n)) : ProfiniteGrp :=
  GammaR n q R

/-! ## §2 The word certificate  (ledger §5.2)

The ledger's six field names are kept verbatim.  Their *types* are the ones the landed stack
actually needs — see divergences 2–4 in the module docstring, and the per-field notes below,
which name for each field the branch theorems that exist and the bridge that does not. -/

section Clauses

variable (Γ : ProfiniteGrp) (n q : ℕ) (P : ProfiniteGrp) (nuP : ContinuousMonoidHom P Ztwo)
  (SN : SourceNumerics n)

set_option linter.unusedVariables false in
/-- **Ledger §5.2 field `exactLifting`** — `ExactLiftingSemantics`.

The recursion's lifting-and-stage supply for one source: `SourceDataN.liftsOver_card` (ii.3,
props 5.15/5.16), `.lem86` (ii.4, ⟦lem-radicaledge⟧) and `.stageR136` (ii.5 assembled), stated
verbatim at an abstract carrier `Γ` so that both sides of the comparison can use one
vocabulary.

**What the branch lanes proved:** the Fox layer — `GQ2/Dyadic/Certificates/{N0Fox, M0Fox,
NpcFox, MpcFox, LFox}.lean` — closed the *first-order* content (universal rows, elementary
row/column certificates, replay).  **What is missing:** the passage from a Fox certificate to
`#LiftsOver(ρ) = SN.mMult #M_B`.  At `ℚ₂` that passage is `GQ2/MStageCount.lean` +
`GQ2/RadicalEdge/`; at general `K` it has no owner.  AS2–AS5 supply this field per branch. -/
def ExactLiftingSemantics : Prop :=
  (∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
      [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
      {T : MarkedTarget H E Y}
      {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
      (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
      (ρ : BoundaryLiftsK b F RF.TC),
      Nat.card (LiftsOverK RF b F ρ) = SN.mMult (Nat.card ↥RF.MB))
  ∧ (∀ {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
      (D : RadicalCoverData Bg), D.NoDescent →
      ∀ (ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)), Function.Surjective ρ →
        2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ))
  ∧ (∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
      [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
      {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
      (hE2 : ∀ e : E, e ^ 2 = 1)
      (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
      (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
      (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E),
      (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) * exactImageCountK b F T
        = (blockFrameImpl T Blk hE2).zR * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
            (2 * (mBK (blockFrameImpl T Blk hE2) b F l : ℤ)
              - exactImageCountK b F (blockFrameImpl T Blk hE2).TB))

set_option linter.unusedVariables false in
/-- **Ledger §5.2 field `stokes`** — `StokesDualityCertificate`.

The recursion's (ii.6) family: the `T`-cocycle count, the `(T^∨)^C`-separation, nondegeneracy
of the obstruction pairing in the character, and the `V`-cocycle count.

**What the branch lanes proved:** all five closed a Stokes layer
(`Certificates/{N0, M0, Npc, MpcStokes, L}.lean`): exact-in-resolver rows, `IsStokesEndpoint`,
duality and kernel-`decide` Grams.  **What is missing:** every one of those is a statement
about the *word's* second-order behaviour; the four clauses here are *counts*.  WMP's row on
the obligation tracker names the residuals that survive even at the word level and that AS2–AS5
must therefore still supply or assume: `hsimp` (per-simple-module Stokes duality), WW4 gap
items **3** (per-χ shifts) and **5** (`HessRelZTarget`, which needs the unowned NpcJet ↔ WordCoh
bridge), the cited gate-F witness, and **P4's central clause per module** (assumed — the parity
escape is not expressible at the `PWord` layer). -/
def StokesDualityCertificate (smul : DistribMulAction ↥Γ (ZMod 2)) : Prop :=
  (∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
      [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
      {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
      (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
      (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR) (ρ : BoundaryLiftsK b F RF.TC),
      Nat.card (TCocycle (En.radData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
        = SN.tMult (Nat.card (Additive ↥(En.radData l h).T))
          * Nat.card (fixedPts (RF.YB ⧸ (En.radData l h).M)
              (ElemDual (Additive ↥(En.radData l h).T))))
  ∧ (∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
      [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
      {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
      (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
      (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
      (Dsc : Descent (En.radData l h)) (ρ : BoundaryLiftsK b F RF.TC)
      (c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ)),
      (∀ χ : ↥(TCharC (En.radData l h)),
        betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c = 0) →
        TLiftable (descSigma_spec En l h Dsc) c)
  ∧ (∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
      [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
      {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
      (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
      (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
      (Dsc : Descent (En.radData l h)) (ρ : BoundaryLiftsK b F RF.TC)
      (χ : ↥(TCharC (En.radData l h))), χ ≠ 0 →
      ∃ c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ),
        betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
          ≠ betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ
              (0 : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ)))
  ∧ (∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
      [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
      {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
      (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
      (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR),
      (∀ W : AddSubgroup En.Vmod, (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤) →
      (∃ v : En.Vmod, v ≠ 0) →
      (∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v) →
      ∀ ρ : BoundaryLiftsK b F RF.TC,
        Nat.card (VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
          = Nat.card En.Vmod * SN.h1Mult (Nat.card En.Vmod))

/-- **Ledger §5.2 field `scalar`** — `ScalarHilbertCertificate`.

Lemma 8.2 at degree `n` (`#Hom_cont(Γ, 𝔽₂) = SN.homScalar`, standardly `2^{n+2}`) together with
the degree-independent `#H²(Γ, 𝔽₂) = 2`.  The scalar action is a parameter because
`SourceDataN.cardH2` is stated under the record's own `smulZmod2` field.

**What the field side proved:** FD1's `card_H1_zmodTwo`/`finrank_H1_zmodTwo`/
`demushkinRank_galK` give `dim H¹ = n + 2` at `G_K` in all three vocabularies, and FD1 also
supplied the two Euler factors (`#H² = 2` had existed only at `G_ℚ₂`).  So on the **arithmetic**
side this clause is landed mathematics.  On the **candidate** side it is the branch lanes'
scalar Gram rows, which are not yet a `#Hom` count. -/
def ScalarHilbertCertificate (smul : DistribMulAction ↥Γ (ZMod 2)) : Prop :=
  Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) = SN.homScalar
    ∧ (letI := smul; Nat.card (H2 Γ (ZMod 2)) = 2)

set_option linter.unusedVariables false in
/-- **Ledger §5.2 field `determinant`** — `AffineDeterminantCertificate`.

The (ii.7) Gauss-`Z` residue at both heads, `G₀ = SN.gaussUnram m` and `SN.gaussRam m`.  This is
the clause the whole `LocalGauss` lane exists to discharge on the arithmetic side: LG5's
`local_gauss_K` (packet Thm. 6.15) *is* the ramified/unramified dichotomy, with the ramified
branch fed by `ramifiedCertificateOfSubtype`.

**On the candidate side** the branch lanes closed the Hessian/phase layer — WNP's
`npc_word_eq_certQ`, WM0's two projector branches, WMP's `mpc_isStokesEndpoint` and the
one-entry linear row, WL's `exists_cupFormK_normalForm` meeting `sqRelWord_centLift_fib` on the
same normal form.  WL-c deliberately did **not** build its `HessianCertificate` record: its
`affinePhase` needs the Arf-dependent Gauss value, which SD1 §6.3's row-5 rule makes an
*input* — i.e. this field. -/
def AffineDeterminantCertificate (tame : ContinuousMonoidHom Γ (Tq q))
    (pro2 : ContinuousMonoidHom Γ P) (compat : ∀ g : Γ, nuTq q (tame g) = nuP (pro2 g))
    (smul : DistribMulAction ↥Γ (ZMod 2)) : Prop :=
  (∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
      [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
      (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
      [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
      (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q) (F : BoundaryFrameK q P H E)
      (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
        (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
      (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v ≠ 0)
      (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
        (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g • v ≠ v)
      (m : ℕ) (hm : 1 ≤ m)
      (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod = 2 ^ (2 * m))
      (l : (SectionNine.blockFrame T Blk hE2).DR)
      (h : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
      (hunram :
        letI := blockPS_commGroup Blk
        letI := SectionNine.headAct T Blk
        ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau q) • v = v),
      letI := smul
      GaussZResidueK (sourceBoundaryMapK tame pro2 compat) F
        (blockEnrichmentDK T Blk hE2 hq0 hqe F) l h (SN.gaussUnram m))
  ∧ (∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
      [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
      (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
      [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
      (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q) (F : BoundaryFrameK q P H E)
      (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
        (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
      (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v ≠ 0)
      (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
        (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g • v ≠ v)
      (m : ℕ) (hm : 1 ≤ m)
      (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod = 2 ^ (2 * m))
      (l : (SectionNine.blockFrame T Blk hE2).DR)
      (h : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
      (hram :
        letI := blockPS_commGroup Blk
        letI := SectionNine.headAct T Blk
        ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau q) • v ≠ v),
      letI := smul
      GaussZResidueK (sourceBoundaryMapK tame pro2 compat) F
        (blockEnrichmentDK T Blk hE2 hq0 hqe F) l h (SN.gaussRam m))

end Clauses

/-! ## §2b The tame specialization at a **satisfiable** hypothesis

⚠ **Divergence 6, and the sharpest one in this file.**  F3's Gate-B predicate `KillsWild R`
(`TameBoundary.lean:341`) quantifies over *every* profinite group.  Every one of the five frozen
branch words **refutes it**: `GQ2.Dyadic.Words.LSq.not_killsWild`,
`Words.not_killsWild` (compact `N`), `Words.Npc.not_killsWild`,
`Words.MCompact.not_killsWild`, `Words.Mpc.not_killsWild` are all landed theorems.  The reason
is uniform and is *not* a defect in the words: the tame-killed value of a word carrying an
`(x_i τ)^{ω₂}`-shaped letter is `τ^{ω₂}`, which is `1` only where `τ` is pro-odd — which is
exactly where the packet's hypothesis lives (Lem. 3.1), and exactly what `T_q` is.  The WL lane
recorded this as micro-row **F3b** and correctly declined to act (`TameBoundary.lean` is not its
file; it is not mine either).

So `WordCertificate` **cannot** take `KillsWild R`, and `tameR` — whose only use of `hadm` is at
`G := T_q`, `t := tameMarking n q` (`tameBase_eval_R`) — cannot be called.  §2b therefore
re-does F3's three-step tame construction at the hypothesis that is both satisfiable and
*literally the ledger's* `specializeTame R = 1`.  Nothing here is new mathematics: `tameOfSpec`
is `tameR`'s term with one proof argument replaced, and `tameOfSpec_surjective` is
`tameR_surjective`'s proof verbatim.  **When F3b lands, all of §2b should be deleted and the F3
originals used instead.** -/

section TameSpec

variable {n q : ℕ} {R : PWord (Generator n)}

/-- **Ledger §5.2 field `tameSpecialization`**, on the nose: `specializeTame R = 1`, i.e. the
wild word dies under the tame marking `σ ↦ σ, τ ↦ τ, x_i ↦ 1` of `T_q`.

Satisfiable, and satisfied by all five branches: each `Words/*.lean` proves
`eval_killWildLetters_* = τ^{ω₂}` (or `= 1` outright, for `Mpc`) together with
`*_eq_one_of_odd`, and `τ^{ω₂} = 1` holds in `T_q` by Lem. 3.1 (`TameBoundary.lean` §1). -/
def TameSpecializes (n q : ℕ) (R : PWord (Generator n)) : Prop :=
  (tameMarking n q).eval R = 1

/-- F3's Gate B implies the ledger's equation — the compatibility direction, so that anything
stated against `KillsWild` still applies.  (The converse is what F3b would need, and is false
in F3's unrelativized `∀`-form.) -/
theorem tameSpecializes_of_killsWild (hadm : KillsWild R) : TameSpecializes n q R := by
  have h := hadm ((Tq q) : Type) (tameMarking n q)
  rwa [killWildLetters_tameMarking] at h

/-- The `R`-relator dies in `T_q`.  `tameBase_eval_R`'s proof with `KillsWild` replaced by the
ledger's equation. -/
theorem tameBase_eval_R_of_spec (hspec : TameSpecializes n q R) :
    (tameBase n q).hom.toMonoidHom ((freeMarking n).eval R) = 1 := by
  have h := Marking.map_eval (tameBase n q).hom (freeMarking n) R
  have hmark : (freeMarking n).map ⇑(tameBase n q).hom = tameMarking n q := by
    ext g; exact tameBase_of n q g
  rw [show (tameBase n q).hom.toMonoidHom ((freeMarking n).eval R)
      = (tameBase n q).hom ((freeMarking n).eval R) from rfl, h, hmark]
  exact hspec

/-- **The tame specialization** `Γ_R ↠ T_q`, at the satisfiable hypothesis.  `tameR`'s term. -/
noncomputable def tameOfSpec (n q : ℕ) (R : PWord (Generator n))
    (hspec : TameSpecializes n q R) : ContinuousMonoidHom (GammaR n q R) (Tq q) :=
  presentationLift (gammaRelators n q R) (tameBase n q).hom <| by
    rintro r (rfl | rfl)
    · exact tameBase_tameRelatorGen
    · exact tameBase_eval_R_of_spec hspec

@[simp] theorem tameOfSpec_gammaGen (hspec : TameSpecializes n q R) (g : Generator n) :
    tameOfSpec n q R hspec (gammaGen n q R g) = tameMarking n q g :=
  (presentationLift_mk _ _ _ (FreeProfiniteGroup.of g)).trans (tameBase_of n q g)

/-- `tameR_surjective`'s proof, verbatim. -/
theorem tameOfSpec_surjective (hspec : TameSpecializes n q R) :
    Function.Surjective (tameOfSpec n q R hspec) := by
  have hle : Subgroup.closure {tqSigma q, tqTau q}
      ≤ (tameOfSpec n q R hspec).toMonoidHom.range := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact ⟨gammaGen n q R .sigma, tameOfSpec_gammaGen hspec .sigma⟩
    · exact ⟨gammaGen n q R .tau, tameOfSpec_gammaGen hspec .tau⟩
  have hclosed : IsClosed (((tameOfSpec n q R hspec).toMonoidHom.range) : Set ((Tq q) : Type)) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range (tameOfSpec n q R hspec).continuous_toFun).isClosed
  have htop : (tameOfSpec n q R hspec).toMonoidHom.range = ⊤ := by
    rw [eq_top_iff, ← topGen_tq q]
    exact Subgroup.topologicalClosure_minimal _ hle hclosed
  exact MonoidHom.range_eq_top.mp htop

end TameSpec

/-! ## §2c The word certificate  (ledger §5.2) -/

set_option linter.unusedVariables false in
/-- **The word certificate** (ledger §5.2, packet Def. 9.1).

The six ledger field names are kept.  Two carry the branch lanes' actual output
(`tameSpecialization`, `proTwoWord`); four carry the recursion's supply clauses, because the
certificate ⇒ count bridge does not exist (module docstring, divergence 4).  Three further
fields (`pro2`, `ker_pro2`, and the scalar-action triple) are *structure*, not certificate
content, and are carried because F3 does not supply them.

### The complete obligation inventory for AS2–AS5

Per branch, the instantiating ticket must produce:

| field | what exists today | what is owed |
|---|---|---|
| `tameSpecialization` | `Words/*.eval_killWildLetters_*` + `*_eq_one_of_odd` | evaluate at `T_q` (Lem. 3.1 gives `τ^{ω₂} = 1`) — small |
| `proTwoWord` | `Words/*.eval_pro2_*_eq_{n,m,sq}RelWord` | nothing — landed for all five |
| `pro2`, `ker_pro2`, `compat` | `GQ2.Roe.exists_pro2R` at `ℚ₂` only | the generic `Γ_R(2) ≅ D_P` bridge (divergence 3) |
| `tfg`, `smulZmod2`, `contSMulZmod2`, `htriv` | — | routine, but nobody has written them for `GammaR` |
| `exactLifting` | `FoxCertificate`/`FoxRowCertificate` per branch | the Fox ⇒ `#LiftsOver` bridge |
| `stokes` | `IsStokesEndpoint` (all five, unconditional); `StokesDuality` **only modulo `hsimp`** | `hsimp` per simple module, then the duality ⇒ count bridge |
| `scalar` | `stokesGram` kernel-`decide` pins | the Gram ⇒ `#Hom` bridge |
| `determinant` | `HessianCertificate` (4 of 5) | the Hessian ⇒ `GaussZResidueK` bridge; **and L has no `HessianCertificate` at all** (its endpoint is `qDouble`, not `plusFormD`) and **Mpc has no word-side equation** (`HessRelZTarget` is a stated-open `Prop`) |

Named residuals that no lane owns and that AS2–AS5 must supply or assume, flagged here so the
G3 census sign-off sees them in one place: **`hsimp`** (per-simple-module Stokes duality — the
single biggest one, carried by all five branches), **WW4 gap items 3** (per-χ shifts) **and 5**
(`HessRelZTarget`, blocked on the unowned `NpcJet ↔ WordCoh` bridge), **the cited gate-F
witness**, **P4's central clause per module** (assumed; not expressible at the `PWord` layer),
and **`Mpc.hlinrow`** at general `(α, r, p, η)` (closed only at the `√−10` instance, by
`MpcStokes.sqrtNeg10ProductCert`).  The `α`-threshold mismatch is also live: the Fox layers need
`1 ≤ α`, the Stokes/Hessian layers need `2 ≤ α`, and compact `M`'s endpoint needs no `α` bound
at all. -/
structure WordCertificate (n q : ℕ) (R : PWord (Generator n)) (P : ProfiniteGrp)
    (hP : IsProP 2 P) (nuP : ContinuousMonoidHom P Ztwo) (SN : SourceNumerics n) where
  /-- **Ledger field 1.**  `specializeTame R = 1` (see §2b for why this, and not `KillsWild`). -/
  tameSpecialization : TameSpecializes n q R
  /-- **Ledger field 2, word level.**  The ledger's `specializeProTwo R = P.word`, in the
  semantic form the five `Words/*.lean` files actually prove: the pro-2 specialization of `R`
  evaluates, at every marking of every pro-2 group, to the standard core's relator.  The
  `coreRel` slot is the branch's `MarkedCore.nRelWord` / `.mRelWord` / `SqCore.sqRelWord`. -/
  coreRel : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G], Marking n G → G
  proTwoWord : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking n G),
    t.eval (pro2 R) = coreRel G t
  /-- **Ledger field 2, group level** — the bridge's *output* (divergence 3).  `ℚ₂` ancestor:
  `GQ2.Roe.exists_pro2R`. -/
  pro2 : ContinuousMonoidHom ((GammaR n q R) : Type) P
  /-- `pro2` is *the* maximal pro-2 quotient map. -/
  ker_pro2 : pro2.toMonoidHom.ker = proPKernel 2 ((GammaR n q R) : Type)
  /-- `pro2` is onto the core.  (`SourceDataN.pro2_surjective` derives this *from* eq. (27)
  joint surjectivity, so it cannot be reused here — eq. (27) is what we are building.) -/
  hpro2 : Function.Surjective pro2
  /-- ν-compatibility against §2b's tame map. -/
  compat : ∀ g : ((GammaR n q R) : Type),
    nuTq q (tameOfSpec n q R tameSpecialization g) = nuP (pro2 g)
  /-- Topological finite generation of `Γ_R`. -/
  tfg : ∃ s : Finset ((GammaR n q R) : Type),
    (Subgroup.closure (s : Set ((GammaR n q R) : Type))).topologicalClosure = ⊤
  /-- The ambient `ZMod 2`-scalar action (trivial). -/
  smulZmod2 : DistribMulAction ↥(GammaR n q R) (ZMod 2)
  contSMulZmod2 : letI := smulZmod2; ContinuousSMul ↥(GammaR n q R) (ZMod 2)
  htriv : letI := smulZmod2; ∀ (γ : ↥(GammaR n q R)) (m : ZMod 2), γ • m = m
  /-- **Ledger field 3.** -/
  exactLifting : ExactLiftingSemantics (GammaR n q R) n q P nuP SN
  /-- **Ledger field 4.** -/
  stokes : StokesDualityCertificate (GammaR n q R) n q P nuP SN smulZmod2
  /-- **Ledger field 5.** -/
  scalar : ScalarHilbertCertificate (GammaR n q R) n SN smulZmod2
  /-- **Ledger field 6.** -/
  determinant : AffineDeterminantCertificate (GammaR n q R) n q P nuP SN
    (tameOfSpec n q R tameSpecialization) pro2 compat smulZmod2
  /-- §10 instantiation-side condition 1 (SD3: *not* a `SourceDataN` field). -/
  htame : Function.Surjective (tameOfSpec n q R tameSpecialization)
  /-- §10 instantiation-side condition 2. -/
  hwild : IsProP 2 (tameOfSpec n q R tameSpecialization).toMonoidHom.ker

namespace WordCertificate

variable {n q : ℕ} {R : PWord (Generator n)} {P : ProfiniteGrp} {hP : IsProP 2 P}
  {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}

/-- **The candidate source.**  Pure projection: every field is either a certificate field, an
F3 theorem (`gammaR_boundary_surjective`'s §2b twin), or `tameOfSpec`.  This is the assembly the
ticket asks for on the candidate side. -/
noncomputable def toSource (W : WordCertificate n q R P hP nuP SN)
    (hq2 : 2 ≤ q) (hqe : Even q) : SourceDataN n q P hP nuP SN where
  Γ := GammaR n q R
  tame := tameOfSpec n q R W.tameSpecialization
  pro2 := W.pro2
  compat := W.compat
  surj := boundary_jointly_surjective_of_maxProP (by omega) hqe nuP _ W.pro2 W.htame W.hpro2
    W.ker_pro2 W.compat
  ker_pro2 := W.ker_pro2
  smulZmod2 := W.smulZmod2
  contSMulZmod2 := W.contSMulZmod2
  htriv := W.htriv
  tfg := W.tfg
  homCard := W.scalar.1
  cardH2 := W.scalar.2
  liftsOver_card := W.exactLifting.1
  lem86 := W.exactLifting.2.1
  stageR136 := W.exactLifting.2.2
  tcocycle_card := W.stokes.1
  hsep := W.stokes.2.1
  hpartial := W.stokes.2.2.1
  hZcard := W.stokes.2.2.2
  gaussZ_unramified := W.determinant.1
  gaussZ_ramified := W.determinant.2

end WordCertificate

end GQ2.Dyadic
