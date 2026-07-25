# roe R30a: SourceData recon memo

**Ticket:** R30a (read-only recon for R30 SourceData refactor) · branch `roe`.
**Scope:** map the two-source (Γ_A / G_ℚ₂) assembly so R30 can extract a `SourceData`
structure letting Γ_R plug in beside Γ_A, with Γ_A capstones byte-identical.
(Produced by the R30a agent; committed verbatim by the orchestrator — the recon agent ran
read-only.)

**Headline:** the recursion/induction core is *already* source-generic. Every solver —
`prop_8_9_aux` + `RecursionInputs` (GQ2/SectionEight/Recursion.lean:706,738),
`mStage_partition`, `count_eq_of_closedRecursion` (GQ2/SectionNine/Induction.lean:503), and
the terminal bridge `qlifts_equiv_commonLifts` (GQ2/SectionNine/Terminal.lean) — is
quantified over an abstract `Γ` + `b : ContinuousMonoidHom Γ ↥boundarySubgroup`. The
two-source hard-coding lives *only* in the outer assembly (`thm_4_2`, `prop_8_9`,
`prop_8_9_of`, their lanes) where the `_gammaA` supply lemmas and `GammaA` instances are
plugged into the A-slot. R30 is a re-plumbing of the outer layer, not a rewrite.

## Task 1 — FIELD LIST

### (i) A-side boundary fields (`BoundaryMaps`, GQ2/BoundaryFrame.lean:368-388) — 12 + 1 derived

| # | Field | Type | Consumed by |
|---|-------|------|-------------|
| 1 | `tameA` | `ContinuousMonoidHom GammaA Ttame` | `bA`; Gauss head-id (GaussZ/GammaAD.lean:222); `tameCoord_bA` (SectionTenSources.lean:53) |
| 2 | `pro2A` | `ContinuousMonoidHom GammaA PiBd` | `bA`; terminal lane (Induction.lean:64 via `hbpro2A`, `hpro2A_surj`) |
| 3 | `compatA` | `∀ g, nuT (tameA g) = nuTwo (pro2A g)` | `bA` codRestrict witness (BoundaryFrame.lean:415) |
| 4-7 | `tameA_sigma/tau/x0/x1` | `↦ tameSigma / tameTau / 1 / 1` | Gauss head-id (GaussZ/GammaAD.lean:233-260) |
| 8-11 | `pro2A_sigma/tau/x0/x1` | `↦ piSigma / 1 / piX0 / piX1` | `ker_pro2A` proof (Terminal.lean:861-864) |
| 12 | `surjA` | joint surjectivity of `g ↦ ⟨(tameA g, pro2A g), compatA g⟩` | `bA_surjective` → `hheadA`; terminal `hbA`/`hpro2A_surj` |
| — | `ker_pro2A` (derived thm, Terminal.lean:852) | `pro2A.ker = proPKernel 2 GammaA` | terminal `hker` arg (Induction.lean:64) |

Derived: `bA` (:379), `bA_apply_coe` (:390), `bA_surjective` (:398). Asymmetry: F-side has
`ker_pro2F` as a FIELD (:406); A-side derives it from generator values + `prop_3_10_gammaA`
+ `topGen_gammaA`. **Promote `ker_pro2` to a SourceData field** (both sources supply it
from their max-pro-2 iso).

### (ii) Per-source obligations (the `_gammaA` supply lemmas) — 7 families

| # | Γ_A form (file:line) | Fed into | Shape |
|---|---|---|---|
| 1 | `gammaA_topologicallyFinitelyGenerated` (FinitelyGenerated.lean:91) | `prop_8_9_aux` `hfg`; lanes `hfgA` | `∃ s : Finset Γ, (closure s).topologicalClosure = ⊤` |
| 2 | `lemma_8_2_gammaA` (SectionEight/ScalarCount.lean:245) | `prop_8_9_aux` `hscalar`; `prop_8_9_of`; `rStage_phase` (ThmFourTwo.lean:269) | `Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) = 8` |
| 3 | `liftsOver_card_gammaA` (MStageCountGammaA.lean:603) | `mStage_lane` `hmultA` (ThmFourTwo.lean:132) | `Nat.card (RF.LiftsOver b F ρ) = (Nat.card MB)^2` |
| 4 | `lemma_8_6_gammaA` (SectionEight/Partition.lean:291) | `half139_gammaA` → `RecursionInputs.half139` | half-torsor `2·#central = #M-lifts` |
| 5 | `card_H2_gammaA` (CardH2GammaA.lean:215) → `stageR136_gammaA` | `RecursionInputs.stageR136` (Prop89Close.lean:~248) | `Nat.card (H2 Γ (ZMod 2)) = 2` |
| 6 | `Phase140GammaA.{tcocycle_card,hsep,hpartial,hZcard}` + `RStageGammaA.htriv_gammaA` | `phase140_from_residues` → `RecursionInputs.phase140` (:~232) | per-λ residues |
| 7 | GaussZ package: `gaussZResidue_gammaA_*`/`boundaryLift_head_gammaA`/`h1CoordGammaA` (GaussZ/GammaAD.lean, GaussZ/FinalGammaA*) | `gaussZ_obtain_blockD` → `hGaussZA` (ThmFourTwo.lean:341) | `GaussZResidue b F En l h G0` |

`stageR136_gammaA`/`half139_gammaA` are generic builders (`stageR136_ofRSepData`,
`half139_via_radData`) fed by leaves 4/5/6 — the true Γ_R leaves are rows 1-7 = R31's list.

### (iii) Asymmetry / interface confinement

A-side pinned by presentation (generator-value fields); F-side by intrinsic characterization
(`wild_isProP`/`wild_isMax`/`ker_pro2F`). Both Γ_A and Γ_R are presented, so the
generator-value interface is right for the pluggable A-slot; F-side stays `AbsGalQ2`.
**No lane inspects Γ_A beyond the (i)/(ii) interface** — `thm_4_2` (ThmFourTwo.lean:400)
touches only `B.bA`/`B.bF` and delegates; the GaussZ head-id's reach into Γ_A word
structure (`h1CoordGammaA`, `x0Supported`) IS obligation (ii.7).

## Task 2 — REFACTOR SHAPE

Classification: `thm_4_2` statement = (b) only via `B.bA` (+`B.tameF` in `horient`); proof
(c). `prop_8_9` = (a) `GammaA` in `hheadA`/`[CompactSpace GammaA]` binders; proof (c).
`prop_8_9_of` = (a) binders; proof (c). `eq_154` = (a) inherent (`ContSurj GammaA G`).

**Minimal-diff shape (b9a T5 same-name flip):** new `GQ2/SourceData.lean` bundling: source
group Γ (+ profinite instances), the (i) fields incl. `ker_pro2`, and the (ii) obligations.
Restate `thm_4_2`/`prop_8_9`/`prop_8_9_of` generically over two `SourceData` (F-slot fixed
to `AbsGalQ2` data). `sourceA : SourceData` = existing `BoundaryMaps` A-fields + untouched
`_gammaA` lemmas; recover old-named theorems as defeq-preserving abbreviations so all
downstream statements stay byte-identical.

MUST touch: `BoundaryFrame.lean` (split A-side into `SourceBoundary`, keep `BoundaryMaps`
as the (Γ_A,F) pairing via abbreviation), new `SourceData.lean`, `Prop89Close.lean`,
`RecursionSplice.lean`, `ThmFourTwo.lean` (+lanes), `SectionNine/Induction.lean`
(`terminal_count_eq` routing; `ker_pro2A` becomes `sourceA`'s field value).
MUST NOT touch: `SectionEight/Recursion.lean`, `SectionNine/Terminal.lean`'s generic
bridge, `MStageCount.lean` local side, `count_eq_of_closedRecursion`, all Γ_A producer
files (they become `sourceA` field values, unchanged), all F-side/`_local` files, `eq_154`
(Γ_R sibling `eq_154_R` is a NEW theorem in R32, not an edit).

## Task 3 — Γ_R READINESS

| SourceData slot | Γ_A decl | Γ_R status | cite |
|---|---|---|---|
| source group Γ | `GammaA` | **DONE** | R3 `GammaR` (Roe/GammaR.lean:196), `NR`:182 |
| tame map + surj | `tameA` | **DONE** | R6 `phiR`:181, `phiR_surjective`:359 |
| tame generator values | `tameA_*` | **DONE** | R6 `phiR_gammaSigma/Tau/X0/X1`:185-202 |
| ν / compat-LHS | (compatA) | **DONE** | R6 `nuR`:407, `nuR_surjective`:428 |
| `ker tame = W` + wild pro-2 + max | `ker_phiA` | **DONE** | R6 `ker_phiR`:368, `wildCoreR_isMax`:382; R3 `isProP_wildCoreR` (Roe/AdmissibleLimit.lean:231) |
| pro2 coordinate (map/surj/gen values) | `pro2A_*` | **IN-FLIGHT** | R15a `MaxPro2Bridge` |
| compat + joint surj | `compatA`/`surjA` | **IN-FLIGHT** (needs pro2R) | R15a→R31 |
| `ker_pro2 = proPKernel 2 Γ` | `ker_pro2A` | **IN-FLIGHT** | R15a |
| (ii.1) t.f.g. | FinitelyGenerated.lean:91 | **MISSING** (trivial clone) | R31 |
| (ii.2) #Hom=8 | `lemma_8_2_gammaA` | **MISSING** | R31 |
| (ii.3) multiplicity | `liftsOver_card_gammaA` | **MISSING** | R31 |
| (ii.4) half-torsor | `lemma_8_6_gammaA` | **MISSING** (needs prop_5_15_R) | R31 ← R26b |
| (ii.5) #H²(Γ_R)=2 | `card_H2_gammaA` | **MISSING** (Roe dévissage) | R31 ← R22-R26 |
| (ii.6) phase-140 residues | Phase140GammaA.* | **MISSING** | R31 |
| (ii.7) GaussZ package | gaussZResidue_gammaA_* | **MISSING** (word layer DONE: R27 `QZeroR*`, ∓2^m signs) | R31 |
| epi-semantics (eq_154_R) | `prop_2_3` | **DONE** | R4 `prop_2_3_R` (Roe/Prop23.lean:186), `markC_admissible_R`:209 |

**Carrier-spelling mismatch flagged:** R6's `phiR`/`nuR` live on raw `F₄ ⧸ NR`;
`BoundaryMaps` expects bundled `ProfiniteGrp` carriers. Defeq-bridgeable
(`profiniteQuotient N = ProfiniteGrp.of (F₄ ⧸ N)`, ProfiniteQuotient.lean:83) but instance
diamonds are real — `sourceR` likely needs `GammaR`-spelled wrappers. **Decide the
SourceData carrier spelling BEFORE freezing the structure.**

## Task 4 — TOP 3 RISKS

1. **Shared-`G0` Gauss coupling (highest).** `gaussZ_obtain_blockD` returns ONE `G0` valid
   for both sources; `prop_8_9`/`count_eq_of_closedRecursion` need both at the SAME `G0`
   (fixed ∓2^m by the F-side orientation). Γ_R's residue must land on the identical sign —
   exactly what R27 set up. Cleaner seam: have `SourceData` supply per-source
   `GaussZResidue … G0` at an EXTERNALLY GIVEN `G0` (as `prop_8_9`'s `hGaussZA`/`hGaussZF`
   args already are) so R30 need not re-open the obtain.
2. **pro2/`ker_pro2` critical path.** Terminal lane hard-requires
   `hker : pro2.ker = proPKernel 2 Γ`; the whole Γ_R pro2 coordinate is gated on R15a.
   → R30 ships `sourceA`-only; `sourceR` lands in R32.
3. **Binder/carrier fragility.** `prop_8_9`/`prop_8_9_of` name `GammaA` in
   `[CompactSpace GammaA]`/`hheadA`/`hfgA` binders; the rewrite plus raw-vs-bundled carrier
   is where Γ_A byte-identity most likely breaks. Regression-gate each recovered capstone
   (`thm_4_2`, `prop_8_9`, `prop_8_9_of`, `eq_154`, `main_surjection_count'`) on statement
   defeq. `hE2`/enrichment facts are target-side, source-independent — no risk.
