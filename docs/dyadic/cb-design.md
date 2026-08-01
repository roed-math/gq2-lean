# CB1 — the certificate ⇒ count bridge (design memo)

**Ticket** CB1 (lane CB, worktree `gq2-dyadic-ww`, branch `dyadic-cb1`).
**Owns** this file only. Read-only with respect to Lean source.
**Status** draft 1, 2026-08-01.

**The gap this memo scopes** is AS1's finding 4, recorded verbatim in
`GQ2/Dyadic/CertificateMain.lean`'s module docstring (divergence 4):

> The five branch lanes closed at the level of Fox rows, Stokes endpoints, scalar Grams and
> Hessian certificates; `SourceDataN` consumes *counting* clauses (`#LiftsOver`, `#Z¹`,
> `#Hom`, the Gauss residue). The certificate ⇒ count bridge is the §5–§9 theory, which at
> `ℚ₂` is the whole `GQ2/Roe/` stack and at general `K` has no owner. **Owed by:** a new lane
> (per branch), between W\*-c and AS2.

and AS1's finding 3 (divergence 3), the `proTwoSpecialization` gap, scoped in §4.

Both are sized here. This memo is the analogue of SD1 for the SD lane and MC1/NC1 before it:
it decides *how* the campaign closes the gap, and it is the fourth restructuring the campaign
has taken on measured evidence.

---

## 0. Executive summary — the verdict and the number

**The verdict on (3) is (c) MIXED, decisively weighted toward generic** — but the lane is
large either way, and the memo says so plainly.

Four headline measurements, all first-hand (method stated at each):

1. **The ℚ₂ ancestor is one word's worth of bridge, and it is 15,064 lines across 44 files** —
   and it exists **three times over**, once per source. *Counted:* the transitive supplier set
   of `SourceDataN`'s eleven count-shaped fields at each of the three `n = 1` instantiations
   (`sourceA_N` / `sourceR_N` / `sourceF_N`, `GQ2/Dyadic/SourceDataN.lean:371,421,476`), traced
   field-by-field (table in §1.3). The Γ_R stack decomposes into six layers (§1.4); **two of
   them, 5,306 lines, the dyadic campaign has already rebuilt generically**, and what remains
   unbuilt is **7,189 lines per word**.

2. **The three stacks are ~55% the same text.** Normalizing away source names
   (`gammaR`/`gammaA`/`_local`/`GammaR`/`GammaA`/`AbsGalQ2`), stripping comments and blanks,
   and comparing line multisets: **2,775 of the Γ_R stack's 5,060 code lines also occur in the
   Γ_A stack (54.8%)**. Per-file the split is not uniform and *not random* — it separates
   exactly along the seam the ℚ₂ files' own docstrings name (§3.1).

3. **The dyadic campaign is already most of the way to the generic version, and does not know
   it.** `GQ2/Dyadic/Word/` is **10,255** lines of alphabet-generic, word-generic,
   rank-generic evaluator machinery, and it already contains count-shaped generic theorems
   that the ℚ₂ campaign had only per-word: `WordCoh.card_H2_le_two`
   (`Word/WordCoh.lean:1210`), `StokesDual.card_wordH0/H1/H2` (`:561,570,580`),
   `Hessian.endpoint_card` (`:581`), the Gauss-sum evaluation `Phase.lean:428`. Crucially,
   `SourceDataN` is **already source-abstract** (an abstract carrier `Γ` and an abstract pro-2
   slot `P`), which `GQ2.SourceData` was not. **The ℚ₂ triplication was forced by a concrete
   record, not by the mathematics** — this is the memo's central structural claim, and §3.3
   proposes a cheap spike to falsify it before the lane is committed.

4. **The pro-2 gap is smaller than AS1 feared and does *not* reach the G-Lab docket.**
   `Roe.exists_pro2R` is the composite `eA ∘ e⁻¹ ∘ maxPro2Bridge ∘ maxProPMk`
   (`GQ2/Roe/Main.lean:248-251`). `BLabHypothesis` enters **only** through `e`
   (`markedPro2_R`, `GQ2/Roe/MarkedPro2.lean:163`), the *arithmetic* leg. The candidate leg is
   `GQ2/Roe/MaxPro2Bridge.lean` — 504 lines, `module`-style, **zero occurrences of `BLab`**
   (`grep -c BLab` = 0; `Roe/Main.lean` = 77). See §4: **no G-Lab consequence**.

**The size.** Naively cloning the ℚ₂ pattern five times is `5 × 7,189 ≈ 36,000` lines. The
generic route costs an estimated **10,000–13,000 lines across 9 tickets** (§5), i.e. it saves
roughly two-thirds — but it is still a lane the size of the entire Wave-2 branch-word effort.
**This is a large new lane. The campaign should hear that number before committing.**

**What AS2 needs is much less than the whole lane** (§6): the √−2 pilot needs one branch (N0)
through one head, and the shortest honest path is **4 tickets, ~3,500–4,500 lines**.

---

## 1. What the count bridge must produce, field by field

### 1.1 The consumer's actual signature

`SourceDataN` (`GQ2/Dyadic/SourceDataN.lean:153-327`) has **21 fields**. The bridge is
responsible for a proper subset. Classified against the landed signature (not against the
ledger's prose):

| # | field | kind | bridge's business? |
|---|---|---|---|
| 1 | `Γ : ProfiniteGrp` | carrier | no — `GammaR n q R`, F3's |
| 2 | `tame` | data | no — AS1 §2b's `tameOfSpec` |
| 3 | `pro2 : ContinuousMonoidHom Γ P` | data | **YES — §4** |
| 4 | `compat` | Prop | **YES — §4** (falls out of the pro-2 bridge) |
| 5 | `surj` (eq. 27) | Prop | no — F3's `boundary_jointly_surjective_of_maxProP` |
| 6 | `ker_pro2` | Prop | **YES — §4** |
| 7–9 | `smulZmod2`, `contSMulZmod2`, `htriv` | data+Prop | **YES, routine** (§5, CB-0) |
| 10 | `tfg` | Prop | **YES, routine** (§5, CB-0) |
| 11 | `homCard : #Hom_c(Γ, 𝔽₂) = SN.homScalar` | **count** | **YES** |
| 12 | `cardH2 : #H²(Γ, 𝔽₂) = 2` | **count** | **YES** |
| 13 | `liftsOver_card : #LiftsOverK = SN.mMult #M_B` | **count** | **YES** |
| 14 | `lem86` (half-torsor) | **count** | **YES** |
| 15 | `stageR136` (the (136) ℤ-identity) | **count** | **YES** |
| 16 | `tcocycle_card : #TCocycle = SN.tMult #T · #fixedPts` | **count** | **YES** |
| 17 | `hsep` ((T^∨)^C-separation) | qualitative | **YES** |
| 18 | `hpartial` (nondegeneracy in χ) | qualitative | **YES** |
| 19 | `hZcard : #VCocycle = #V · SN.h1Mult #V` | **count** | **YES** |
| 20 | `gaussZ_unramified : GaussZResidueK … (SN.gaussUnram m)` | residue | **YES** |
| 21 | `gaussZ_ramified : … (SN.gaussRam m)` | residue | **YES** |

So the bridge owes **11 clause fields** (11–21) plus the **4-field pro-2 block** (3, 4, 6, and
`hpro2` which `WordCertificate` carries separately) plus **4 routine fields** (7–10).

AS1 already bundled the 11 into four `Prop`s over an abstract carrier
(`CertificateMain.lean:165,206,264,282`), and `WordCertificate.toSource` (`:503`) is pure
projection. **The bundling is right and this memo does not reopen it.** The four bundles map
onto the record as:

| `WordCertificate` bundle | `SourceDataN` fields |
|---|---|
| `exactLifting` | `liftsOver_card`, `lem86`, `stageR136` |
| `stokes` | `tcocycle_card`, `hsep`, `hpartial`, `hZcard` |
| `scalar` | `homCard`, `cardH2` |
| `determinant` | `gaussZ_unramified`, `gaussZ_ramified` |

### 1.2 The vocabulary mismatch, stated precisely

This is the whole gap in one sentence:

> The eleven clauses are stated in the **recursion's** vocabulary — `LiftsOverK`, `MLifts`,
> `TCocycle`, `VCocycle`, `GaussZResidueK`, `blockEnrichmentDK`, `RecursionFrame` — and the
> five branch lanes produce theorems in the **word complex's** vocabulary — `WordH1`,
> `StokesH1`, `heisD0`, `FoxCertificate`, `relZ`, `HessianCertificate`, `plusFormD`.

Neither vocabulary is wrong; they are the two ends of a comparison isomorphism that is not
built. At ℚ₂ the comparison **is** built, twice, and it is exactly
`WordCohBridge.z1Equiv` / `WordCohBridgeR.z1EquivR`:

```
z1EquivR (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0) :
    Z1 GR A ≃+ Z1w (A := A) (markC_R q)          -- GQ2/WordCohBridgeR.lean:420
```

with `h1EquivR` (`:460`) descending it to `H¹`. **That is the bridge's spine.** Everything
downstream (the counts) is transport along it plus arithmetic.

### 1.3 The ℚ₂ supplier map — where each clause is actually discharged

*Method:* for each field of `sourceA_N` / `sourceR_N` / `sourceF_N`, read the supplied term
and `grep` its declaration site.

| clause | `Γ_A` supplier | `Γ_R` supplier | `G_ℚ₂` supplier |
|---|---|---|---|
| `homCard` | `SectionEight/ScalarCount.lean:245` | `Roe/Supply.lean:202` | `ScalarCount.lean:337` |
| `cardH2` | `CardH2GammaA.lean:215` | `HalfTorsorGammaR.lean:260` | `LocalLiftingDuality` |
| `liftsOver_card` | `MStageCountGammaA.lean:488` | `MStageCountGammaR.lean:510,626` | `MStageCount.lean` |
| `lem86` | `SectionEight/Partition.lean:291` | `HalfTorsorGammaR.lean:188` | `Partition.lean:304` |
| `stageR136` | `CardH2GammaA.lean:225` | `RStage/GammaR.lean:640` | `RStage/Local.lean:643` |
| `tcocycle_card` | `Phase140/GammaA/Foundation.lean:113` | `Phase140/GammaR/Foundation.lean:124` | `Phase140/Local.lean:258` |
| `hsep` | `Phase140/GammaA/Hsep.lean:469` | `Phase140/GammaR/Hsep.lean:480` | `Phase140/Local.lean:537` |
| `hpartial` | `Phase140/GammaA/Hsep.lean:789` | `Phase140/GammaR/Hsep.lean:805` | `Phase140/Local.lean:864` |
| `hZcard` | `Phase140/GammaA/Foundation.lean:48` | `Phase140/GammaR/Foundation.lean:60` | `Phase140/Local.lean:325` |
| `gaussZ_*` | `GaussZ/GammaAD.lean:300` | `GaussZ/GammaRD.lean:287` | `GaussZ/FinalD.lean:107` |

**Eleven clauses × three sources = thirty-three separate theorems.** Not one is shared.

### 1.4 The Γ_R bridge in six layers — and which two are already done

*Method:* transitive `GQ2.*` import closure of `GQ2/Roe/Main.lean` (304 files, 124,867 lines),
partitioned into the Γ_R-specific part (69 files, 28,324 lines) and shared infrastructure
(235 files, 96,543 lines); the Γ_R-specific part then split by role.

| layer | what it is | files | ln | dyadic status |
|---|---|---|---|---|
| **A1** | certificate layer — Fox rows, Stokes endpoints, normal forms, Hessian, Gauss signs | 8 | 2,471 | **DONE generically** (`Word/{Fox,FoxCert,Stokes,Hessian,Phase}`) and **instantiated** by all five branches (16,545 ln of `Certificates/`) |
| **A2** | dévissage — `Devissage/*`, `DevissageInduction`, `DualityAssembly` | 12 | 2,835 | **DONE generically** — WW3's `stokesDuality_of_simple` (packet Lem 5.1) as a once-only engine |
| **A3** | **transport** — `WordCohBridgeR`, `WordCoh2R`, `MixedBObsR`, `IotaGammaR`, `LedgerGammaR`, `CorrectionR`, `CoverLiftR` | 7 | 2,507 | **PARTLY** — degree 2 done (`Word/WordCoh.lean`); **degree ≤ 1 NOT built** (§3.4) |
| **A4** | **count layer** — `HalfTorsorGammaR`, `MStageCountGammaR`, `RStage/GammaR`, `Phase140/GammaR/*`, `GaussZ/{KappaR,RelatorGammaR,CoordGammaR,GammaRD}` | 10 | 4,682 | **NOT BUILT** |
| A5 | carrier/semantics/supply — `Roe/{GammaR,AdmissibleLimit,Tame,Prop23,Supply}` | 5 | 1,476 | mostly F3's + CB-0 |
| A6 | assembly — `SourceData.lean`, `Roe/Main.lean` | 2 | 1,093 | **DONE** — AS1's `CertificateMain.lean` |
| | **total** | **44** | **15,064** | |

**A3 + A4 = 7,189 lines is the unbuilt per-word bridge.** That is the number that multiplies by
five, and it is the number §5's board is sized against. (Separately: the pro-2 identification
buckets B1 `D_R`-side 5,278 ln and B2 Labute 7,982 ln do **not** multiply — §4.)

### 1.5 The seam, named: everything factors through one theorem

The single sharpest structural fact about the ℚ₂ bridge, and the one that most constrains the
design: **every one of the eleven clauses routes through `GQ2.FoxH.prop_5_15_R`**
(`GQ2/Roe/DualityAssembly.lean:485`), whose conclusion is `IsSelfDual_R`
(`GQ2/Roe/TrivialSelfDual.lean:463`):

```lean
def IsSelfDual_R (t : Marking C) (A) : Prop :=
  (Nat.card (H2wR t) = Nat.card (fixedPts C (ElemDual A)))                        -- clause 1
  ∧ (Nat.card (Z1wR t) = Nat.card A ^ 2 * Nat.card (fixedPts C (ElemDual A)))     -- clause 2: THE COUNT
  ∧ ∃ P : H1wR t → H1wR (ElemDual A) t → ZMod 2,                                  -- clause 3: THE HESSIAN
      (∀ x y, P (h1wMkR t x) (h1wMkR t y) = mixedB_R t x.val y.val)
      ∧ (∀ h, h ≠ 0 → ∃ h', P h h' ≠ 0) ∧ (∀ h', h' ≠ 0 → ∃ h, P h h' ≠ 0)
```

**Clause 2 is a cardinality; clause 3 is the Hessian nondegeneracy. That conjunction *is* the
certificate ⇒ count seam**, and `z1EquivR` (§1.2) is what carries it from the word complex into
continuous cohomology. Per-clause routing, verified: `liftsOver_card`, `tcocycle_card`,
`hZcard` and `stageR136` all consume clause 2 through `z1EquivR`; `cardH2`, `lem86` and
`hpartial` consume clause 3 (via `obs_varCoc_eq_mixedB_R` / `mixedB_eq_relZPairR`); `hsep`
consumes the whole thing through `sep_word_R`; `gaussZ_*` lands in
`QZeroR_finsum_sign_{un,}ramified` (`Roe/Gauss.lean:208,221`), the Gauss-sign count.

**Design consequence — this is what CB-1 must actually deliver.** The dyadic bridge should be
built around *one* `IsSelfDual`-shaped theorem over the abstract carrier, not eleven
independent transports. The WW lane has already built **clause 1 and clause 3 generically**
(`StokesDual.card_wordH0/H2`, and `stokesChi1_bijective` + `stokesChi1_separating` — WW3b's
docstring calls the latter "the `∃ P`-clause of `IsSelfDual` in the degree-generic form").
**Clause 2 — the count — is the one that is not yet generic, and WW3b flagged exactly that**
(see §3.2's caution). The lane's centre of gravity is therefore clause 2, and §3.3's spike is
aimed at it.

---

## 2. What the five lanes already give — the delta table

### 2.1 The finding, confirmed by count

*Method:* `grep -cE "Nat\.card|Fintype\.card|Finset\.card|\.ncard"` over
`GQ2/Dyadic/Certificates/*.lean`.

| file | count-shaped hits | file | hits |
|---|---|---|---|
| `L.lean` | 11 | `MpcStokes.lean` | 1 |
| `Npc.lean` | 4 | `M0.lean` | 1 |
| `Mpc.lean` | 4 | `NpcFox.lean` | **0** |
| `M0Assembly.lean` | 4 | `N0Fox.lean` | **0** |
| `N0.lean` | 2 | `MpcFox.lean` | **0** |
| | | `M0Fox.lean` | **0** |
| | | `LFox.lean` | **0** |

**All five Fox files contain zero cardinality statements.** Across 16,545 lines of branch
certificates there are 27 `card` occurrences total, and inspection shows them to be incidental
(module dimensions, `Fintype` side conditions) rather than clause-shaped. **AS1's finding is
confirmed: no branch produces a count.**

### 2.2 The per-field × per-branch delta

Legend for the "delta" column — what the branch still owes to hit the clause:
**T** = transport only (the mathematics exists; it must be moved across the comparison
isomorphism); **T+w** = transport plus a word-specific input the branch has;
**M** = missing mathematics, named.

| clause | what the five lanes give | N0 | M0 | Npc | Mpc | L |
|---|---|---|---|---|---|---|
| `homCard` | scalar Gram rows; kernel-`decide` pins | T | T | T | T | T |
| `cardH2` | `WordCoh.card_H2_le_two` (generic, ≤ half) + `relZ` Grams | T+w | T+w | T+w | T+w | T+w |
| `liftsOver_card` | `FoxCertificate` / `FoxRowCertificate`, universal rows, replay | T+w | T+w | T+w | T+w | T+w |
| `lem86` | — (source-free at ℚ₂: the `D₈` datum is reused verbatim) | T | T | T | T | T |
| `stageR136` | — (assembled from `cardH2` + frame) | T | T | T | T | T |
| `tcocycle_card` | `IsStokesEndpoint` (all five, unconditional) | T+w | T+w | T+w | T+w | T+w |
| `hsep` | `StokesDuality` **only modulo `hsimp`** | **M** | **M** | **M** | **M** | **M** |
| `hpartial` | duality Grams, kernel-`decide` | T+w | T+w | T+w | T+w | T+w |
| `hZcard` | `StokesDual.card_wordH1` (generic) | T | T | T | T | T |
| `gaussZ_*` | `HessianCertificate` | T+w | T+w | T+w | **M** | **M** |

**The two genuine mathematical gaps, named:**

* **`hsimp` — per-simple-module Stokes duality.** Carried by all five branches; AS1 calls it
  "the single biggest one". It is a hypothesis on the *module*, not on the word, which is why
  no branch could discharge it. **This is the one item in the table that is not transport.**
  See owner question Q3.
* **The `determinant` row has two branch-specific holes**, both recorded by AS1 and both
  confirmed against the landed files: **L has no `HessianCertificate` at all** (its endpoint is
  `qDouble`, not `plusFormD` — WL-c declined to build the record because `affinePhase` needs
  the Arf-dependent Gauss value, which SD1 §6.3 row 5 makes an *input*, i.e. this very field);
  and **Mpc has no word-side equation** (`HessRelZTarget` is a stated-open `Prop` at
  `Certificates/Mpc.lean:1038`, blocked on the unowned `NpcJet ↔ WordCoh` bridge — WW4 gap
  item 5).

**⚠ New this memo: L is short in a second way.** `LFox.lean` builds **no `FoxCertificate`
(Jacobian) at all** — only four `FoxRowCertificate`s plus three ℚ₂-base reuses. It is a
single-relator lane, so the Jacobian record has no content there. Every other branch has both
(`N0Fox` 7+4, `M0Fox` 4+8, `NpcFox` 5+5, `MpcFox`/`Mpc`/`MpcStokes` 1+1+3+1). Since
`exactLifting`'s `liftsOver_card` is the **Fox ⇒ `#LiftsOver`** bridge, CB-3 must not assume a
Jacobian certificate exists per branch. *This was not in AS1's inventory.*

**Two structural confirmations that make the generic route more plausible**, both measured
across all twelve files: the five lanes share **one** evaluator stack (one `PWord`/`Marking`
syntax, one `foxD`/`foxDHom`/`foxJacobian`, one `heisEvalZ`/`heisD0`/`heisD1`/`stokesGram`, one
`hessRelZ`/`HessianCertificate`) — there is no competing `Evaluator` abstraction and no lane
rolls its own; and the three lane-local additions (`NpcSym`'s η̂-coefficient extension,
`MpcFox`'s `MLetter`/`shM` display alphabet, `MpcStokes`'s `epsZ`) are coefficient-alphabet
extensions and wrappers, **three of the four flagged as hoist candidates by their own authors**.
Density across the twelve files: 1,049 declarations in 16,545 lines, 834 `theorem` to 2 `lemma`,
**zero `sorry` and zero `TODO`**.

**Headline of the table:** *nine of the eleven clauses are transport, not mathematics.* The
lane is large because transport across an unbuilt comparison isomorphism is expensive, not
because nine new theorems are needed.

### 2.3 The other named residuals (inherited, not created here)

Carried forward from AS1's inventory so that the G3 census sign-off sees them in one place:
WW4 gap item **3** (per-χ shifts); the cited **gate-F witness**; **P4's central clause per
module** (assumed — the parity escape is not expressible at the `PWord` layer);
**`Mpc.hlinrow`** at general `(α, r, p, η)` (closed only at the `√−10` instance, by
`MpcStokes.sqrtNeg10ProductCert`). Also live: the **α-threshold mismatch** — Fox layers need
`1 ≤ α`, Stokes/Hessian layers need `2 ≤ α`, compact `M`'s endpoint needs no bound.

---

## 3. Generic vs per-branch — the decision that sizes the campaign

### 3.1 The evidence: where the ℚ₂ copies agree and where they differ

*Method:* per file pair (Γ_R vs Γ_A), normalize source names, strip comments/blanks, compare
sorted line multisets. `shared/R` = fraction of the Γ_R file's code lines that also occur in
its Γ_A twin.

| layer | file pair | Γ_R code ln | shared/R |
|---|---|---|---|
| recursion counts | `MStageCountGammaR` ↔ `MStageCountGammaA` | 589 | **75%** |
| recursion counts | `Phase140/GammaR/Hsep` ↔ `GammaA/Hsep` | 913 | **74%** |
| recursion counts | `Phase140/GammaR/Foundation` ↔ `GammaA/Foundation` | 345 | **60%** |
| recursion counts | `RStage/GammaR` ↔ `RStage/GammaA` | 593 | **56%** |
| ledger | `LedgerGammaR` ↔ `LedgerGammaA` | 276 | **59%** |
| degree-2 comparison | `WordCoh2R` ↔ `WordCoh2` | 707 | 45% |
| Gauss residue | `GaussZ/GammaRD` ↔ `GammaAD` | 834 | 42% |
| degree-2 comparison | `MixedBObsR` ↔ `MixedBObs` | 99 | 41% |
| H² leaves | `HalfTorsorGammaR` ↔ `HalfTorsorGammaA` | 232 | 36% |
| degree-2 comparison | `IotaGammaR` ↔ `IotaGammaA` | 66 | 34% |
| degree-≤1 comparison | `WordCohBridgeR` ↔ `WordCohBridge` | 406 | 29% |
| | **weighted total** | **5,060** | **54.8%** |

**The split is structural.** The high-overlap band (56–75%) is the *recursion counting
machinery*; the low band (29–45%) is the *presentation comparison* and the *Gauss residue* —
precisely where a relator is read off a marking.

And the ℚ₂ files say so themselves, in their own docstrings, without ambiguity:

* `WordCohBridgeR.lean`: "The entire argument is relator-agnostic *except* one step … Everything
  genuinely word-independent is **imported from the `Γ_A` file and reused verbatim**, never
  re-defined".
* `WordCoh2R.lean`: "All of that is **imported and reused verbatim** — it never mentions a
  relator. What is re-derived here is exactly the part that reads the *wild* relator off a
  marking".
* `MixedBObsR.lean`: "are **word-independent** and reused verbatim from the `Γ_A` file; only the
  two statements that read a *relator* off a marking are re-derived".
* `IotaGammaR.lean`: "are **generic in `Γ`** and reused verbatim; the only `Γ_R`-specific inputs
  are `WordCoh2R.obs_ker_eq_B2_R` and `WordCoh2R.obsFun_eq_R`".
* `MStageCountGammaR.lean:507`: "the `Z¹`-torsor bridge … **is source-generic once a base lift
  exists**".

**⚠ Landed-code finding (the code wins over the prose).** The ℚ₂ campaign's *stated* design was
"reuse verbatim, re-derive only the relator layer". What landed is **55% textual duplication**
with mechanical `_R` renaming. The abstraction the docstrings describe was **described but never
built**. This is not a criticism of the ℚ₂ campaign — with a *concrete* `SourceData` record
(fixed `Γ_A` / `Γ_R` / `AbsGalQ2` carriers) there was nowhere to put the generic statement. It is
a warning: the dyadic campaign will reproduce the duplication by default unless the generic
statement is given a home first.

### 3.2 What the dyadic campaign already has that ℚ₂ did not

Two assets change the arithmetic, and both are landed:

**(i) `SourceDataN` is source-abstract.** Its `Γ` is a field, its pro-2 target `P` is an
abstract slot, its numerics are an abstract `SN`. The eleven clauses are already stated as
`∀`-shapes over that abstract carrier (`SourceDataN.lean:191-327`), and AS1 already restated
them at an abstract `Γ` in `CertificateMain.lean`'s four bundles. **There is now a place to put
the generic theorem.** At ℚ₂ there was not.

**(ii) `GQ2/Dyadic/Word/` is 10,255 lines of already-generic evaluator machinery.** Sizes and
what each gives:

| file | ln | already-generic assets relevant to the bridge |
|---|---|---|
| `Stokes.lean` | 1,789 | `stokesDuality_of_simple` — packet Lem 5.1 as a **once-only dévissage engine**, extends quasi-iso to *all* finite elementary modules incl. nonsplit |
| `WordCoh.lean` | 1,504 | `relZ`, `relZFam`, `obsH2`, `obsH2_injective`, **`card_H2_le_two`**, `obsH2_eq_of_factor`, `MarkedRelator`/`PresentedBy` bundles — generic in alphabet, word, marking, relator family |
| `Fox.lean` | 1,395 | Fox rows, generic |
| `FoxCert.lean` | 1,026 | `FoxCertificate`/`FoxRowCertificate` grammars, `card_ker` |
| `Hessian.lean` | 829 | `endpoint_card : #W = 2^(2·baseDim)`, `plusFormD` covers |
| `Export.lean` | 805 | one-tree export + hashes |
| `Eval.lean` | 772 | the F2 denotations + the four per-word lemmas proved **once** |
| `Syntax.lean` | 684 | `PWord` reflected syntax |
| `StokesDual.lean` | 603 | **`card_wordH0/H1/H2`**, `stokesChi1_bijective`, universal coefficients |
| `Phase.lean` | 599 | Gauss sums; `gaussSum (plusFormD d₀ q) = #V` |
| `Blocks.lean` | 249 | |

The campaign already banked this pattern once and *measured the saving*: the WW3 log records
that the once-only dévissage engine saved "**5 branch words ≈ 11k avoidable lines**", and the
orchestrator log line 999 records the same principle from the `Roe/Devissage` clone experiment.
**The precedent for "build once, instantiate five times" is the campaign's own, and it is
quantified.** Cross-check: the ℚ₂ layers A1 + A2 (§1.4) total 5,306 lines per word; five words
is 26,530, and WW3's "≈ 11k avoidable" plus the branch lanes' own 16,545 lines of
`Certificates/` accounts for it. **The campaign has already spent this lane's analogue once and
came out ahead.**

**⚠ The one recorded caution, and it lands squarely on this lane.** WW3b's closing report (board
row, `tickets.md:1454`) left "TWO record-design cautions for the `StokesDualityCertificate`
author", the first of which is:

> `IsSelfDual`'s second numeric clause (`#Z¹w = #A²·…`) is **NOT** degree-generic (do not expect
> it)

That clause is **exactly** clause 2 of §1.5 — the count — and it is the source of
`liftsOver_card`, `tcocycle_card` and `hZcard`. *Reading:* the literal exponent `²` is what
fails to be degree-generic, not the existence of a generic statement; at degree `n` the shape
moves, which is precisely what `SourceNumerics`' moving leaves (`SN.mMult`, `SN.tMult`,
`SN.h1Mult`) were introduced to carry (SD1 §1.3's shape rule, and `SourceDataN.lean:260-263`'s
load-bearing note that the **outer** `#V` stays literal while the **inner** factor moves). So
the caution is survivable — **but it is survivable only if `SN` is threaded through the generic
statement from the start**, and it is the single most likely place for the generic route to
fail. The second caution (`card_wordH0/H2` are phrased against `(heisD0 c).ker`, so a
`fixedPts` shape needs a generation hypothesis) also lands on CB-4.

### 3.3 The verdict, and the one claim that must be spiked first

**Verdict: (c) mixed.** Field by field:

| clause | generic over the abstract `Γ` + `SN`? | per-branch residue |
|---|---|---|
| `homCard` | **generic** (Euler-characteristic route) | the scalar Gram value |
| `cardH2` | **generic** — `WordCoh.card_H2_le_two` already is | a nonzero `relZ` Gram value (branch has it) |
| `liftsOver_card` | **generic** ("source-generic once a base lift exists") | the base lift's existence |
| `lem86` | **fully generic** — source-free even at ℚ₂ | none |
| `stageR136` | **fully generic** — assembled from `cardH2` | none |
| `tcocycle_card` | **generic** via `StokesDual` + the comparison | `IsStokesEndpoint` (branch has it) |
| `hsep` | **generic given `hsimp`** | `hsimp` — see Q3 |
| `hpartial` | **generic** | the duality Gram (branch has it) |
| `hZcard` | **generic** — `card_wordH1` already is | none |
| `gaussZ_*` | **per-branch** — the Hessian/phase reading is word-specific | the whole `HessianCertificate` ⇒ residue step |

**So: ten of eleven clauses are generic; `gaussZ_*` is genuinely per-branch.** Plus the
degree-≤1 comparison isomorphism, which is generic in shape but needs a per-word "the relator
dies" input that all five branches already have.

**⚠ The central claim, stated so it can be falsified.** The claim that carries the whole sizing
is:

> The nine transport clauses follow, over an abstract carrier, from `(homCard, cardH2)` plus the
> boundary structure plus the comparison isomorphism — i.e. by the Euler-characteristic route —
> and therefore admit **one** proof rather than five.

Evidence for it: SD1 §3.3 already names exactly this route for the *arithmetic* side
("K-clones of the `MStageCount`/`Phase140/Local` count lemmas (**Euler-char based**)"); the
56–75% textual overlap in the counting band; and `MStageCountGammaR`'s own "source-generic once
a base lift exists". Evidence against it: nobody has written it, and the ℚ₂ campaign — which
had every incentive — did not.

**Recommendation: do not commit the lane on this memo alone. Spike it (ticket CB-S, §5).**

*Spike design, aimed at the actual risk.* Target **`hZcard`** — not because it is cheapest, but
because it is the direct consumer of `IsSelfDual` clause 2, the one thing WW3b explicitly warned
is not degree-generic. Budget ~300 lines. The spike must:

1. state clause 2 over an **abstract carrier** with the count valued in `SN.h1Mult`, not `²`;
2. derive `hZcard`'s exact `SourceDataN` shape from it (`#VCocycle = #V * SN.h1Mult #V`);
3. instantiate at **N0** and check the `standardNumerics` value bridge closes.

If step 1 forces a per-word hypothesis that `SN` cannot absorb, the generic route is refuted and
the campaign should re-scope to clone-per-branch (~36k lines) rather than force it. If the spike
is green the lane is ~10–13k lines. This is the same discipline MC1's HandleMix spike and SD1's
probe pack used, and both paid for themselves.

### 3.4 The measured gap in the WW lane

One precise structural hole, worth its own ticket:

**`Word/` has the degree-2 comparison but not the degree-≤1 comparison.**
*Method:* `grep -cE "ContCoh|\bZ1\b|\bH1 \b|\bH2 \b"` over `GQ2/Dyadic/Word/*.lean` — every
file returns 0 except `WordCoh.lean` (8 hits, all degree 2: `Z2`, `B2`, `H2 G (ZMod 2)`).
There is no `Z1 Γ A ≃+ Z1w(marking)` anywhere under `GQ2/Dyadic/`.

At ℚ₂ that isomorphism is `WordCohBridge.z1Equiv` (492 ln file) and `WordCohBridgeR.z1EquivR`
(497 ln). It is the substrate the entire `Γ_R` supply lane is stated against
(`WordCohBridgeR.lean` docstring: "This is the substrate the whole `Γ_R` supply lane (tickets
R31c–R31g) is stated against"). **It is the single most load-bearing missing piece**, and it is
the first ticket of the lane.

---

## 4. The `proTwoSpecialization` gap (AS1 finding 3)

### 4.1 The finding, restated against the landed code

AS1: word-level `pro2 R = coreRel` (all five lanes have it) does not give group-level
`Γ_R(2) ≅ D_P`; the generic bridge is unbuilt; the ℚ₂ ancestor `Roe.exists_pro2R` is
Γ_R-specific and consumes `BLabHypothesis`. **Confirmed on all three points.** But the
disposition is better than feared.

### 4.2 `exists_pro2R` decomposes, and the Labute leg is the *arithmetic* one

`GQ2/Roe/Main.lean:226-251`. The statement:

```
theorem exists_pro2R (hBLab : BLabHypothesis) :
    ∃ pro2R : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NR) PiBd,
      (∀ g, nuT (phiR g) = nuTwo (pro2R g)) ∧ Function.Surjective pro2R ∧
      pro2R.toMonoidHom.ker = proPKernel 2 (FreeProfiniteGroup (Fin 4) ⧸ NR) ∧
      pro2R gammaTauR = 1
```

and the witness is the four-fold composite

```
eA ∘ e⁻¹ ∘ maxPro2Bridge ∘ maxProPMk
```

| leg | what it is | where | Labute? |
|---|---|---|---|
| `maxProPMk 2 (F₄/N_R)` | `Γ_R ↠ Γ_R(2)` | generic | no |
| `maxPro2Bridge` | **`Γ_R(2) ≅ D_R`** | `Roe/MaxPro2Bridge.lean:426` | **no** |
| `e⁻¹` | `D_R ≅ G_ℚ₂(2)` | `markedPro2_R`, `Roe/MarkedPro2.lean:163` | **YES — `hBLab`** |
| `eA` | `G_ℚ₂(2) ≅ Π` | `prop_3_10_local_marked` | no |

*Method:* `grep -c BLab` — `MaxPro2Bridge.lean` = **0**, `Roe/Main.lean` = **77**.

**Why the arithmetic legs are there at all:** `PiBd` is *not* a presented core. It is
`maxProPQuotient 2 (profinitePresentation {piRelator})` (`GQ2/BoundaryFrame.lean:142`), the
pro-2 boundary object of the **one-sided** ℚ₂ record — so `pro2R` was forced to land on the
arithmetic side, and the chain had to pass through `G_ℚ₂(2)`, which is where Labute lives.

**The dyadic setting removed that.** SD-n went two-sided (architecture decision A2). In
`SourceDataN` the pro-2 slot `P` is the **presented standard core** `D_P` (MC2's `DM`/`DN`,
SqCore's `DSq`) — AS1's own docstring: "the two sides meet at `D_P`". The candidate side
therefore needs only the `maxPro2Bridge` leg. The Labute-type content sits on the *arithmetic*
side, where it already is: `MarkedCoreCertificateM/N.abstractEquiv :
ContinuousMulEquiv (DM α h) G` (`MarkedCore/Certificate.lean:629,645`), fed by
`MLabHypothesis`/`NLabHypothesis` and consumed by ticket **ASK**.

### 4.3 Disposition

> **The candidate-side pro-2 bridge is Labute-free. It does NOT land on the G-Lab docket.**
> `Roe.exists_pro2R` does **not** generalize — it is the wrong composite, three-quarters
> arithmetic — but its candidate leg `maxPro2Bridge` does, and that is the only leg the
> two-sided architecture needs.

### 4.4 What the generic bridge needs, and what already exists

`MaxPro2Bridge.lean`'s architecture, from its own docstring: "forward via the maximal-pro-2
universal property fed by `R`-admissibility at every finite 2-group level of `D_R`, backward via
`D_R`'s own universal property `drLiftHom`, mutual inverse by density." Its analytical keystone
is `wildValueR_eq_drWord_of_powOmega2_id` (`:114`): in a 2-group, where `ω₂` acts as the
identity, the wild value of the marking **is** the core relator.

**That keystone is exactly `WordCertificate.proTwoWord`**, and all five branches have landed it:
`Words/L.lean:680`, `Words/Npc.lean:717`, `Words/M0.lean:684`, `Words/N0.lean:378` (+ `Mpc`).

The generic bridge therefore needs:

| input | status |
|---|---|
| word-level `t.eval (pro2 R) = coreRel G t` | **landed, all five** (`eval_pro2_*_eq_*RelWord`) |
| `PresentedBy` for the core `D_P` | **landed generically** — `Word/WordCoh.lean`, and `presentedBy_DM`/`_DN` at `MarkedCore/Certificate.lean:278,285` |
| `MarkedRelator` (Frattini + holds) | **landed generically** — same file, `markedRelator_DM`/`_DN` at `:255,266` |
| `R`-admissibility at finite 2-group levels | per branch, small |
| `τ` dies pro-2 | generic (tame relation ⇒ odd order ⇒ trivial in a 2-group) |

**Sizing:** the two ℚ₂ instances are `MaxPro2Bridge.lean` (504 ln) and `maxAEquiv` in
`BoundaryConstruction.lean` (499 ln file). A generic version over `PWord`/`Marking`/
`PresentedBy` should be **one theorem of ~500–700 lines**, with per-branch instantiation
**~80–150 lines** (the admissibility argument plus a landed `proTwoWord`). It is `module`-style
already at ℚ₂, so it can live under `GQ2/Dyadic/Word/`.

This is the **cheapest high-value ticket in the lane** and it unblocks four `SourceDataN`
fields at once (`pro2`, `ker_pro2`, `hpro2`, `compat`).

---

## 5. The ticket board

Lane **CB** (certificate ⇒ count bridge), between W\*-c and AS2. Proposed worktree
`gq2-dyadic-cb`, branch `dyadic-cb`.

Size estimates are in the campaign's measured units. Calibration used: the SD-R spine clone
came in at **54–69% of budget** (SD-R1 1,751/3,050 = 57%; SD-R2 1,654/2,200 = 54% spine-alone;
SD-R3 1,968 = 69%); the Wave-2 `-a`/`-b`/`-c` tickets landed at **641–1,963 lines**, median
~1,460 (measured across all 15 rows). Budgets below are *budgets*, so apply the same 55–70%
expectation.

| id | title | model | files owned | depends on | budget |
|---|---|---|---|---|---|
| **CB-S** | **spike**: one clause (`hZcard`) proved once over the abstract `SourceDataN` carrier + instantiated at N0 — **gates the whole lane** | fable | `GQ2/Dyadic/Bridge/Spike.lean` (throwaway) | AS1 ✓ | **300** |
| CB-P | generic pro-2 bridge `Γ_R(2) ≅ D_P` (§4) + the four `SourceDataN` pro-2 fields | fable | `GQ2/Dyadic/Word/MaxProTwo.lean` | AS1 ✓, WW1 ✓ | 700 |
| CB-0 | the four routine fields (`tfg`, `smulZmod2`, `contSMulZmod2`, `htriv`) for `GammaR n q R` | opus | `GQ2/Dyadic/Bridge/Routine.lean` | AS1 ✓ | 350 |
| CB-1 | **the degree-≤1 comparison** `Z1 Γ A ≃+ Z1w(marking)` + `h1Equiv`, generic in alphabet/word/marking (§3.4) | fable | `GQ2/Dyadic/Word/CohBridge.lean` | CB-S | 1,400 |
| CB-2 | `scalar` bundle: `homCard` + `cardH2` over the abstract carrier (uses `card_H2_le_two`) | opus | `GQ2/Dyadic/Bridge/Scalar.lean` | CB-1 | 900 |
| CB-3 | `exactLifting` bundle: `liftsOver_card`, `lem86`, `stageR136` | opus | `GQ2/Dyadic/Bridge/Lifting.lean` | CB-1, CB-2 | 1,600 |
| CB-4 | `stokes` bundle: `tcocycle_card`, `hsep`, `hpartial`, `hZcard` — **carries the `hsimp` decision (Q3)** | fable | `GQ2/Dyadic/Bridge/Stokes.lean` | CB-1, CB-2 | 1,800 |
| CB-5 | `determinant` bundle: the **per-branch** Hessian ⇒ `GaussZResidueK` step, generic skeleton + N0/M0/Npc instantiations | fable | `GQ2/Dyadic/Bridge/Gauss.lean` | CB-1, CB-4 | 1,900 |
| CB-5L | `determinant` for **L** — needs the `qDouble` endpoint and the Arf-dependent Gauss value (no `HessianCertificate` exists) | fable | `GQ2/Dyadic/Bridge/GaussL.lean` | CB-5 | 1,100 |
| CB-5M | `determinant` for **Mpc** — blocked on the `NpcJet ↔ WordCoh` bridge (WW4 item 5) | fable | `GQ2/Dyadic/Bridge/GaussMpc.lean` | CB-5, **WW4-5** | 1,300 |
| CB-6 | the five per-branch instantiations: `WordCertificate` field witnesses per branch | opus ×5 | `GQ2/Dyadic/Bridge/Inst/{N0,M0,Npc,Mpc,L}.lean` | CB-2…CB-5M | 5 × 500 |

**Totals.** Budget **13,850** lines across 11 tickets; at the campaign's measured 55–70%
realization that is **≈ 7,600–9,700 landed lines**. Add the pro-2 and routine tickets already
counted. **Call it 9 dispatchable tickets plus the spike plus five thin instantiations, and
10,000–13,000 lines of budget.**

**Dependency shape.** CB-S gates everything. CB-P and CB-0 are independent of CB-S and can run
immediately in parallel (they touch no count clause). CB-1 is the spine; CB-2…CB-5 fan out from
it; CB-6 is five parallel thin tickets at the end.

**Two tickets are not startable today:** CB-5M needs WW4 gap item 5 (the unowned
`NpcJet ↔ WordCoh` bridge — **this bridge has no ticket anywhere on the board and should get
one**), and CB-4 needs the `hsimp` decision (Q3).

---

## 6. The shortest path to AS2 (√−2)

AS2 is the pilot instance: `ℚ₂(√−2)`, compact `N₂`, i.e. **branch N0 only**. It does not need
the lane; it needs one branch through one head. Concretely, AS2 needs a
`WordCertificate 2 q_K R_{N0} P hP nuP SN` — and `WordCertificate` has 17 fields.

**Fields already discharged for N0 today:** `tameSpecialization` (evaluate
`Words/N0.lean`'s `eval_killWildLetters` at `T_q`; Lem 3.1 gives `τ^{ω₂} = 1` — small),
`coreRel` + `proTwoWord` (`Words/N0.lean:378`, landed), `htame`/`hwild` (F3's, §2b's twins).

**The critical path is therefore exactly four tickets:**

| step | ticket | why it is on the path | budget |
|---|---|---|---|
| 1 | **CB-P** | supplies `pro2`, `ker_pro2`, `hpro2`, `compat` — nothing else can | 700 |
| 2 | **CB-0** | supplies `tfg` + the scalar-action triple; trivially parallel with CB-P | 350 |
| 3 | **CB-1** | the comparison isomorphism — every count clause transports along it | 1,400 |
| 4 | **CB-2/3/4/5 restricted to N0 only** | the eleven clauses at one branch, one head | ~1,500 |

**≈ 3,950 budget lines, ≈ 2,200–2,800 landed, 4 tickets, and steps 1–2 are parallel.**

**Three shortening opportunities, in order of value:**

1. **Do CB-P and CB-0 now, before the spike.** Neither depends on the count bridge, both are
   independently useful, and together they close 8 of `WordCertificate`'s 17 fields. If the
   owner wants motion this week, this is the motion.
2. **Restrict CB-5 to the unramified head for the pilot.** `SourceDataN` needs both
   `gaussZ_unramified` and `gaussZ_ramified`, but N0's pilot instance selects a head; if the
   √−2 slot only exercises one, the other can be deferred to CB-5 proper. *This needs
   checking against `Words/N0.lean`'s √−2 instance — flagged, not asserted.*
3. **`hsimp` at N0 may be dischargeable concretely** even though the general statement is
   open: at a fixed branch and a fixed small module the simplicity hypothesis may fall to
   `decide`. Worth 30 minutes before Q3 is escalated.

**AS2 is not blocked behind the whole lane. It is blocked behind CB-P + CB-1.**

---

## 7. Owner questions

**Q1. Do we spike before committing the lane?**
*Recommendation: **yes**.* CB-S, ~300 lines, one clause, gates a 10–13k-line lane. The central
claim of §3.3 (nine clauses are one theorem, not five) is well-evidenced but unproven, and the
ℚ₂ campaign's own docstrings assert an abstraction it then did not build — which is exactly the
failure mode a spike catches. The campaign has taken three restructurings on measured evidence;
this is the cheapest measurement available before the fourth.

**Q2. Generic-first, or clone-per-branch?**
*Recommendation: **generic-first**, contingent on Q1.* Measured basis: 55% textual overlap in
the ℚ₂ triplication; the campaign's own quantified precedent (WW3's dévissage engine saved
"5 branch words ≈ 11k avoidable lines"); and `SourceDataN`'s abstract carrier, which is the
home ℚ₂ lacked. Clone-per-branch costs ~34k lines and reproduces a duplication the campaign has
already twice decided against. **But if the spike is red, clone-per-branch is the honest
fallback and the campaign should re-scope rather than force the abstraction.**

**Q3. `hsimp` — hypothesis, or obligation?**
This is the one non-transport item in the delta table, and all five branches carry it. Three
options, priced:
  (a) **thread it as a hypothesis** on `StokesDualityCertificate` (cost ~0 now; it becomes a
      visible residual on the G3 census, alongside P4's central clause — precedent exists);
  (b) **prove it per branch** at the concrete modules (cost: unknown, possibly `decide`-able at
      small modules — see §6 item 3);
  (c) **prove it generically** as a tenth obligation (cost: a new lane; not recommended).
*Recommendation: **(a) now, (b) opportunistically at N0**.* It matches how the campaign handled
`BLabHypothesis`, `MMixHypothesis`, `NScalingHypothesis` — thread, make visible, discharge
later. It must **never** become an axiom (board rule: the nine obligations are proof
obligations; `hsimp` is a tenth of the same character).

**Q4. Who owns the `NpcJet ↔ WordCoh` bridge?**
WW4 gap item 5 (`HessRelZTarget`) is blocked on it, CB-5M is blocked on item 5, and Mpc's
`determinant` field is blocked on CB-5M. **It has no ticket on the board anywhere.** It is a
silent critical-path item. *Recommendation: open it as **WW6** in the WW lane (which owns both
sides) before the CB lane starts, so CB-5M is not dispatched into a wall.*

**Q5. Does `L`'s missing `HessianCertificate` get built, or does the record change?**
WL-c deliberately did not build it: L's endpoint is `qDouble`, not `plusFormD`, and its
`affinePhase` needs the Arf-dependent Gauss value that SD1 §6.3's row-5 rule makes an *input*.
So there is a genuine circularity to break. Options: (a) build an L-shaped `HessianCertificate`
variant (CB-5L as boarded, 1,100); (b) restate `determinant` for L directly against `qDouble`,
skipping the record. *Recommendation: **(b)**, and let CB-5L be the ticket that decides it after
reading `Certificates/L.lean` — this memo did not read L deeply enough to rule.*

**Q6. Lane assignment and worktree.**
CB touches `GQ2/Dyadic/Word/` (WW's tree) for CB-P and CB-1, and a new `GQ2/Dyadic/Bridge/` for
the rest. *Recommendation:* CB-P and CB-1 land **in the WW lane** (its files, its module
discipline, its conventions); CB-2…CB-6 form a new CB lane on `GQ2/Dyadic/Bridge/`. This
respects the board's exclusive-file-ownership rule without a cross-lane handoff mid-ticket.

**Q7. Is ASK the same animal as this lane?**
*Answer: **adjacent, not the same**, and the memo recommends keeping them separate.* ASK
(SD1 §3.3) supplies the **arithmetic** side's eleven clauses at `G_K` — by Euler-characteristic
clones of the `*_local` pack plus LG5's `local_gauss_K`. CB supplies the **candidate** side's
eleven at `Γ_R` — by transport across the presentation comparison. Same record, same eleven
field shapes, **completely different suppliers**. They should share the generic statement of any
clause that is genuinely source-abstract (which is the §3.3 claim's real payoff: *if* the spike
is green, CB-2…CB-4's generic theorems serve **both** sides and ASK shrinks too). *That is a
second reason to run the spike.*

---

## 8. What this changes on the campaign's critical path

1. **A new lane exists between W\*-c and AS2, and it is large.** 9–11 tickets,
   ~10,000–13,000 budget lines. The board currently shows AS2 as depending only on
   "AS1, WN0-c" — **that dependency is wrong** and should read "AS1, WN0-c, CB-P, CB-1,
   CB-{2,3,4,5}|N0".
2. **AS2 is not blocked behind the whole lane** — 4 tickets, ~2,200–2,800 landed lines (§6).
   Two of them (CB-P, CB-0) are startable today and are parallel.
3. **The pro-2 gap does not reach G-Lab.** No new Labute-type obligation at rank four. The
   G-Lab docket is unchanged by this memo.
4. **A silent blocker surfaced:** the `NpcJet ↔ WordCoh` bridge has no ticket and gates Mpc's
   `determinant` through two levels of dependency (Q4).
5. **`hsimp` becomes a visible tenth residual** carried by all five branches, and needs an
   owner ruling before CB-4 (Q3).
6. **If the §3.3 spike is green, ASK shrinks too** (Q7) — the generic clause theorems would
   serve both sides of the two-sided comparison. This is upside the board does not currently
   price.

---

## Appendix A — measurement methods

Every number in this memo is reproducible from the worktree at `dyadic-cb1` (a103283).

* **Stack sizes (§0.1, §1.3).** For each of `sourceA_N`/`sourceR_N`/`sourceF_N`
  (`SourceDataN.lean:371,421,476`), each field's supplied term was read and its declaration
  located by `grep -rn --include='*.lean' -E "(theorem|lemma|def|abbrev)[[:space:]]+<name>\b"`.
  The file set per source was then summed with `wc -l`.
* **Textual overlap (§3.1).** Per file pair: `sed -E 's/[Gg]amma[RA]//g; s/gammaR|gammaA//g;
  s/_local//g; s/GammaR|GammaA//g; s/AbsGalQ2//g; s/[[:space:]]+/ /g'`, then drop comment and
  blank lines, then `comm -12` on the sorted line multisets. `shared/R` is
  `|shared| / |R code lines|`. This over-counts trivial lines (`by`, `exact ?_`) and
  under-counts semantically-identical-but-reformatted proofs; it is a proxy, and it is
  corroborated by the files' own docstrings (quoted in §3.1).
* **Count-shaped hits (§2.1).** `grep -cE "Nat\.card|Fintype\.card|Finset\.card|\.ncard"`.
* **Labute dependence (§4.2).** `grep -c BLab`.
* **Degree-≤1 gap (§3.4).** `grep -cE "ContCoh|\bZ1\b|\bH1 \b|\bH2 \b"` over
  `GQ2/Dyadic/Word/*.lean`.
* **Size calibration (§5).** All 15 Wave-2 `-a`/`-b`/`-c`/`-d` rows and the three SD-R rows of
  `docs/dyadic/tickets.md`, read for their landed `N ln` figures and budget percentages.

## Appendix B — divergences found while writing this memo

Recorded per board protocol; the landed code wins over earlier prose in every case.

1. **§3.1 — the ℚ₂ "reuse verbatim" claim is aspirational.** Five files' docstrings state that
   word-independent content is imported and reused verbatim. Measured duplication between the
   `Γ_R` and `Γ_A` stacks is 55%. The abstraction was described, not built. *Cause identified:*
   `GQ2.SourceData` has concrete carriers, so there was no home for the generic statement.
2. **§1.3 — thirty-three theorems, not eleven.** The ledger and SD1 both speak of the eleven
   clause fields as if each had one supplier. At `n = 1` each has three, one per source, sharing
   no proof.
3. **§4 — `exists_pro2R` is three-quarters arithmetic.** AS1 recorded it as "Γ_R-specific and
   consumes `BLabHypothesis`", which is true of the composite but obscures that the candidate
   leg (`maxPro2Bridge`) is Labute-free and is the only leg the two-sided architecture needs.
   This materially reduces the gap.
4. **§5 — the `NpcJet ↔ WordCoh` bridge has no ticket.** Referenced as "unowned" in AS1's
   docstring and in WMP's residual list, but never boarded. It gates Mpc's `determinant`.
5. **§0.3 — `Word/WordCoh.lean` already provides `card_H2_le_two` generically.** AS1's
   obligation table lists `scalar`'s `cardH2` as owing "the Gram ⇒ `#Hom` bridge" without noting
   that the `#H² ≤ 2` half is landed and rank-generic. The remaining half is a nonzero Gram
   value, which every branch has.
