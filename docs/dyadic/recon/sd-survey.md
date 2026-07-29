# SD-n recon survey — SourceData degree-parameterization (2026-07-28)

Read-only survey of the repo at master `d0714a7`, taken at campaign setup. Seed material for
ticket SD1 (design memo). File:line anchors verified at survey time.

## 1. The source record

**`GQ2.SourceData`** — `GQ2/SourceData.lean:75` (structure body to line 268; preceded by
`set_option linter.unusedVariables false in` at :67). Single flat structure, **33 fields**, no
type parameters (hence nothing to hang `n` on today).

| group | fields (line) |
|---|---|
| carrier + 4 marked generators | `Γ` (78), `sigma` (80), `tau` (82), `x0` (84), `x1` (86) |
| eq. (27) boundary maps | `tame` (88), `pro2` (90), `compat` (92) |
| generator pinning (8) | `tame_sigma` (94), `tame_tau` (96), `tame_x0` (98), `tame_x1` (100), `pro2_sigma` (102), `pro2_tau` (104), `pro2_x0` (106), `pro2_x1` (108) |
| surjectivity + promoted kernel | `surj` (110), `ker_pro2` (115) |
| ZMod-2 action layer | `smulZmod2` (119), `contSMulZmod2` (121), `htriv` (123) |
| **seven supply families** (12 fields) | (ii.1) `tfg` (127); (ii.2) `hom8` (131); (ii.3) `liftsOver_card` (137); (ii.4) `lem86` (147); (ii.5) `cardH2` (134) + `stageR136` (154); (ii.6) `tcocycle_card` (168), `hsep` (180), `hpartial` (193), `hZcard` (207); (ii.7) `gaussZ_unramified` (223), `gaussZ_ramified` (247) |

Derived API: `SourceData.b` (:276), `b_apply_coe` (:279), `b_surjective` (:282),
`pro2_surjective` (:286).

**Consumption census**: the 8 pinning fields are consumed **nowhere** — confirmed by the design
note at `GQ2/Roe/Main.lean:68-81` ("`thm_4_2_of_sources` and all its lanes touch only
`b`/`tame`/`pro2`/`compat`/`surj`/`ker_pro2`/the action layer/the obligations"). For SD-n they
are documentation only, but their *types* still name degree-one constants.

## 2. Degree-one hard-coding

**Inside the record (values):**
- `SourceData.lean:131` — `hom8 : Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) = 8`.
  This is `2^(1+2)`; general `n` ⇒ `2^(n+2)`. Source lemma `lemma_8_2_gammaA`
  (`GQ2/SectionEight/ScalarCount.lean:245`) derives it from "the free `𝔽₂³` of `σ, x₀, x₁`-values".
- `SourceData.lean:143` — `Nat.card (RF.LiftsOver b F ρ) = (Nat.card ↥RF.MB) ^ 2`. Exponent 2
  comes from `prop_5_15` clause 2 (`#Z¹ = #V²·#fixedPts`, `GQ2/DualityAssembly.lean:574`, used at
  `GQ2/MStageCountGammaA.lean:484-488`); for degree `n` this is `|M|^(n+1)`.
- `SourceData.lean:174-177` — `tcocycle_card … = Nat.card (Additive ↥T) ^ 2 * Nat.card (fixedPts …)`.
  Same exponent-2 origin.
- `SourceData.lean:217-218` — `hZcard … = Nat.card En.Vmod * Nat.card En.Vmod` (i.e. `|V|²`);
  docstring: "`#Z¹_{Γ,ρ'}(V) = #V²`". Derivation at `GQ2/Phase140/GammaA/Foundation.lean:39-43`.
- `SourceData.lean:235` and `:259` — `hcard : Nat.card (…).Vmod = 2 ^ (2 * m)`, conclusions
  `GaussZResidue … (-(2 ^ m : ℤ))` (:244) and `… (2 ^ m : ℤ)` (:268). The `2^m = |V|^{1/2}`
  magnitude and the ∓ sign convention are the degree-one (83)-evaluation. `GaussZResidue`
  normalizes by `(Nat.card En.Vmod : ℤ) * G0` (`GQ2/Phase140/Assembly.lean:145-149`) — the
  `|V|¹` factor is `#Z¹/|V|` at n = 1 and moves with the exponent above.
- `SourceData.lean:150` — `lem86 : 2 * Nat.card {f // f.Central} = Nat.card (MLifts D ρ)` and
  `:162-165` `stageR136` (`2 * mB - e`, `zR`): these `2`s look degree-independent (half-torsor
  index / ± scalar classes) but must be re-derived, not assumed.
- `SourceData.lean:134` — `cardH2 : Nat.card (H2 Γ (ZMod 2)) = 2` is degree-**independent**
  (dim H² = 1 for every local field) and survives unchanged.

**Inside the record (types) — the bigger structural cost:**
- `tame : ContinuousMonoidHom Γ Ttame` (:88). `Ttame = ⟨σ,τ | τ^σ = τ²⟩`
  (`GQ2/BoundaryFrame.lean:120-124`, `tameWord` uses `τ^2`) — residue cardinality `q = 2` is
  hard-coded; for `K` with residue degree `f` it must be `τ^σ = τ^{q_K}`.
- `pro2 : ContinuousMonoidHom Γ PiBd` (:90), plus `pro2_sigma/x0/x1`. `PiBd`
  (`GQ2/BoundaryFrame.lean:136-143`) is the **rank-3** Demushkin group
  `⟨σ,x₀,x₁ | x₀^{σ²}x₀[x₁,σ]⟩_{pro-2}`; degree `n` needs rank `n+2` and the branch core.
  Consequently `x0`/`x1` become an `n+1`-indexed family, and `boundarySubgroup`/`nuTwo`
  (`BoundaryFrame.lean:228,248`) move with it.
- `ker_pro2` (:115), `surj` (:110), `compat` (:92), `tfg` (:127), the action layer (:119-123)
  are degree-generic as written.

## 3. The source-generic induction theorem

**`GQ2.thm_4_2_of_sources`** — `GQ2/ThmFourTwo.lean:386-414`.
Hypotheses: `(S : SourceData) (B : BoundaryMaps) (F : BoundaryFrame H E) (R : LocalReciprocity)
(horient : TameUnitOrientation R B.tameF)`, instances `[CompactSpace AbsGalQ2]
[TotallyDisconnectedSpace AbsGalQ2]`, a finite discrete marked target `(T : MarkedTarget H E Y)`,
and `(hE2 : ∀ e : E, e ^ 2 = 1)`. Conclusion:
`exactImageCount S.b F T = exactImageCount B.bF F T`. Proof = strong induction on
`n = Nat.card ↥T.LY` with three lanes: `terminal_count_eq_of_sources` (`SourceData.lean:349`),
`mStage_lane` (`ThmFourTwo.lean:104`), `rStage_lane` (`ThmFourTwo.lean:290`). Capstone
`thm_4_2` (:443) is literally `thm_4_2_of_sources B.sourceA B F R horient T hE2` (:453).

**Does the recursion use degree-one facts outside the record? Yes — three classes:**
1. **Literal `8` in the shared shape.** `ThmFourTwo.lean:271-285` (`rStage_phase`):
   `SectionEight.lemma_8_3` (`GQ2/SectionEight/Partition.lean:209-218`, hypothesis
   `hscalar … = 8`, conclusion `8 * liftableCount … = ∑ᶠ …`) is applied to *both* sides —
   source via `S.hom8`, target via `SectionEight.lemma_8_2_local B`; the final `omega` cancels
   the literal `8`. Same literal in `ClosedRecursion.eq138` (`GQ2/SectionEight/Recursion.lean:407`).
2. **Exponent-2 counts baked into `ClosedRecursion`** (`GQ2/SectionEight/Recursion.lean:383-431`):
   `eq139` (:417) `2 * zBC = |M_B|^2 * e_Γ(C)`; `eq140` (:428-431) with `2^{r+1} = 2|D_T|`,
   `2^d = |M|/|T| = |V|`; and `μ := Nat.card En.Vmod * muZero …` where
   `muZero = |T|² * fixedPts` (`GQ2/Prop89Close.lean:130-133`, :331).
3. **The `G_ℚ₂` slot is pinned, not abstracted.** `mStage_lane` uses `liftsOver_card_local` for
   `|M_B|²` on the B-side (`ThmFourTwo.lean:128-131`) and
   `Foundations.absGalQ2_isTopologicallyFinitelyGenerated` (:122); `prop_8_9_of_source`
   (`GQ2/Prop89Close.lean:245-367`, hypotheses `hscalarS … = 8` :256, `hH2S … = 2` :257,
   `hMcountS … ^ 2` :268-270, `htcocS … ^ 2` :276, `hZcardS … |V|*|V|` :302) discharges the
   target side with `lemma_8_2_local`/`stageR136_local`/`half139_local`/`phase140_local`/
   `tcocycle_card_local` (:349-357); `gaussZ_obtain_blockD_of_sources`
   (`SourceData.lean:387-434`) pairs each source leaf with
   `SectionNine.gaussZResidueD_local_{un}ramified` (:426,:431); `terminal_count_eq_of_sources`
   (`SourceData.lean:349-379`) runs through `B.ker_pro2F`/`B.pro2F_surjective`, i.e.
   `G_ℚ₂(2) ≅ Π` (rank 3).

The induction *skeleton* (strong recursion on `|L_Y|`, stratum bookkeeping,
`count_eq_of_closedRecursion` at `GQ2/SectionNine/Induction.lean:503`) is degree-free — degree
enters only via (a) record field values, (b) the pinned `G_ℚ₂` twins, (c) the two literal shapes
`8` and `^2` in `lemma_8_3`/`ClosedRecursion`. **SD-n therefore needs the record parameterized
AND a matching `n`-parameterized target slot (a `BoundaryMaps`-analogue for `G_K`), or the second
source will still be `G_{ℚ₂}`** — i.e., the parameterized theorem should be the packet's
two-sided Theorem 11.1 (`S₁, S₂` both records).

## 4. Instantiations of the record

- **`GammaA`**: `GQ2.BoundaryMaps.sourceA` — `GQ2/SourceData.lean:297-334`, with the
  load-bearing `@[simp] BoundaryMaps.sourceA_b : B.sourceA.b = B.bA := rfl` at :339.
- **`GammaR`**: `GQ2.Roe.sourceR` — `GQ2/Roe/Main.lean:388-430` (binder
  `hBLab : BLabHypothesis`, `variable` at :294); helpers `sourceR_tame` (:434), `sourceR_Γ`
  (:437); consumed by `eq_154_R` (:476-494) via `thm_4_2_of_sources`.
- Supply-side "shape lock" files needing parallel edits: `GQ2/MStageCountGammaR.lean:636`,
  `GQ2/HalfTorsorGammaR.lean:36,271-277`, `GQ2/RStage/GammaR.lean:23-24,107-110`,
  `GQ2/Phase140/GammaR/Foundation.lean:369-370`, `GQ2/GaussZ/GammaRD.lean:865-868` — each
  documents that it mirrors a `SourceData` field type exactly.
- No other `SourceData` instances exist. (`*SourceData` hits under `GPT_Fable_formalization/`
  are an unrelated legacy tree.)

## 5. `module` keyword status

All files central to SD-n are **plain-import (non-`module`)**:
- `GQ2/SourceData.lean:1-7` — plain imports of `GQ2.Prop89Close` / `GQ2.GaussZ.GammaAD`. Its
  docstring at :37-44 makes this a hard constraint: "This file must stay **plain-import**
  (non-`module`): it imports the §8 stack … and `module`-style files cannot import plain files
  (the R31a pitfall)."
- `GQ2/ThmFourTwo.lean:1-8`, `GQ2/SectionTenSources.lean:1-8`, `GQ2/Roe/Main.lean:1-8`
  (import-discipline note at :82-90), `GQ2/Prop89Close.lean`, `GQ2/SectionNine.lean` — plain.
- **Module-style** (unusable as a home for a plain-importing adapter): `GQ2/GammaA.lean:6`,
  `GQ2/Demushkin.lean:6`, and 159 others — 161 of 304 `GQ2/*.lean` files begin with `module`.

**Practical upshot:** any degree-n adapter touching `SourceData` must itself be plain-import and
sit as a new leaf above both `GQ2/SourceData.lean` and the `_gammaR` suppliers (the position
`GQ2/Roe/Main.lean` occupies).
