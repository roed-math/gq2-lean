# R31 survey: ii.5/ii.6 Phase140/word-coh surface for Γ_R (2026-07-25)

Produced by R31's survey subagent (read-only pass over the Γ_A twins). Consumed by R31b
(bridge prerequisites) and R31c (residue clones). File:line cites verified at survey time
(tip ≈ c054ae5).

## 0. Headline — the generic layer already exists, twice; NO refactoring anywhere

- **Seam A**: `GQ2/Phase140/Assembly.lean` `phase140_from_residues` (:~120) + inner
  `hMobst_of_residues` (:158) are abstract in `Γ` (context binders Assembly.lean:132–138).
  They take the four residues as hypotheses (`hμ`/`hsep`/`hpartial`/`hZcard` + `hGaussZ`,
  `htriv`, `hfg`, `hH2 : Nat.card (H2 Γ (ZMod 2)) = 2`).
- **Seam B**: `GQ2/SourceData.lean:75` `structure SourceData` carries the four residues as
  fields in exactly the `_gammaA` ∀-shape (`tcocycle_card` :~100, `hsep` :180, `hpartial`
  :193, `hZcard` :207). `BoundaryMaps.sourceA` (:325–330) populates them with
  `Phase140GammaA.{tcocycle_card,hsep,hpartial,hZcard}_gammaA` via plain lambdas.
- Downstream source-abstract entry points, all landed: `prop_8_9_of_source`
  (Prop89Close.lean:245), `prop_8_9_of_sources` (SourceData.lean:441),
  `terminal_count_eq_of_sources` (:349), `gaussZ_obtain_blockD_of_sources` (:387),
  `thm_4_2_of_sources` (ThmFourTwo.lean:386).
- **Therefore Γ_R needs exactly four new theorems `*_gammaR` in the SourceData field
  shapes** (+ their prerequisites below), then `sourceR : SourceData` (R32) and
  `thm_4_2_of_sources sourceR …`. Γ_A deliberately has NO `phase140_gammaA` wrapper —
  follow the Γ_A pattern (SourceData fields), not the `phase140_local` pattern.

## 1. The four targets (Γ_A originals, with per-target skeletons)

### 1.1 `hZcard_gammaA` — Phase140/GammaA/Foundation.lean:38–103 (66 ln)
Skeleton: θ := ρ.1.1; roundtrip via `rho0_descData_rhoPrime` (Assembly.lean:117, GENERIC);
module pack (⊥ topology, `DistribMulAction.compHom`, continuity by composition,
`Vmod_exp2` AffineTLift.lean:459); hand-built `VCocycle ≃ ↥(Z1 GA En.Vmod)`
(`mem_Z1_iff`, `IsLocallyConstant.desc`, `iV`, `iV_ofAdd_inj` VCocycle.lean:196);
`adm := markC_admissible θ hθs`; then
`rw [Nat.card_congr hequiv, Nat.card_congr (z1Equiv θ …).toEquiv, (prop_5_15 (markC θ) …).2.1]`;
close with `IsSimpleModTwo` + `card_fixedPts_elemDual_eq_one_of_nontrivial`
(DualityAssembly.lean:112), `mul_one`, `pow_two`.
Γ_A-specific: `GammaA` binder, `GA := FreeProfiniteGroup (Fin 4) ⧸ NA` (WordCohBridge.lean:47),
`markC` (:89), `markC_admissible` (:91), `z1Equiv` (:438).
Generic: `prop_5_15` (DualityAssembly.lean:574, any `Marking C` — Γ_R uses `prop_5_15_R`,
Roe/DualityAssembly.lean:485, hypothesis surface per R26b report), `IsSimpleModTwo`
(FoxHeisenberg/Traced.lean:562), `Enrichment.descData`/`descSigma_spec` (Assembly.lean:47/:76).

### 1.2 `tcocycle_card_gammaA` — Foundation.lean:105–180 (77 ln)
Skeleton: `(En.radData l h).M.Normal` instance; `DiscreteTopology (RF.YB ⧸ M)` by
`discreteTopology_quotient` (CentralObstruction.lean:809, GENERIC); θ := rhoPrime retyped
over GA; `rhoPrime_surjective` (Half139Local.lean:47, GENERIC); module pack on
`Additive ↥T` with representative law from `cactFun_eq` (RadicalEdge/GammaA.lean:63,
Γ-free over `RadicalCoverData Bg`) + `cActT_toMul` (:108); hand `TCocycle ≃ ↥(Z1 GA (Additive ↥T))`
(`QuotientGroup.out_eq'`, `u.crossed`); same `z1Equiv` + `prop_5_15` clause-2 close.
The `#fixedPts` factor is deliberately NOT reduced (it is the shared `μ₀`).

### 1.3 `hsep_gammaA` — Phase140/GammaA/Hsep.lean:459–525 (68 ln + support)
§-numbered skeleton: §1 `exists_marking_map_eq` (Hsep.lean:137, GENERIC) → set-lift marking
tB; §2 `relatorValues_mem_of_map_eq_push` (Hsep.lean:186, GA-typed retype-only); §3–4
`markC_admissible` + `hsd := prop_5_15 …` + `hv := invariant_dual_relatorSum_eq_zero`
(chains `tCharC_relatorSum_eq_zero` → `exists_lift_charCover` (Foundation.lean:365,
GENERIC abstract-Γ + htriv) → `redValues_eq_of_coverLift` (RStage/GammaA.lean:740,
Γ_A-specific) → `charKer_normal`/`mem_charKer_iff`; `H0w_eq_fixedPts`
Devissage/GeneratesBridge.lean:36); §5 `sep_word` (RStage/GammaA.lean:334 — takes
`IsSelfDual`, needs `sep_word_R` at `IsSelfDual_R`) → word correction; §6
`mk_eq_of_mkT_eq` (Hsep.lean:203, GENERIC), `marking_ext` at the 4 `gammaGen` generators,
`exists_relatorFree_marking` (Hsep.lean:385 — Γ_A-typed, body never touches GA); §7
`mlift_of_relatorFree_marking` (Foundation.lean:461, 221 ln, Γ_A-SPECIFIC descent via
`Marking.descend` Prop23.lean:141, `univMarking`) → f₀; close `redTLift_apply`.
Generic support: charKer/charCover section (Foundation.lean:181–441, 261 ln, abstract Γ);
`corrected_tameValue`/`corrected_wildValue`/`d1Fun_base_change`/`marking_ext`
(RStage/GammaA.lean:678/690/712/596); `Marking.push_admissible`,
`Marking.toHom_hom_univMarking_map` (Prop23.lean:121/:58).

### 1.4 `hpartial_gammaA` — Hsep.lean:781–987 (209 ln; synthInstance.maxHeartbeats 800000)
10-stage skeleton: by_contra; Stage 0 module instances over raw GA (`htriv := rfl`,
`continuousSMul_of_smul_factor` Hsep.lean:147, `elemDual_smul_eq_of_smul_eq` :161 —
GA-typed retype-only); Stage 1 `exists_splitting_of_symm_zero_diag`
(KeystoneDelta/ThetaExtraction.lean:62, GENERIC) on χ∘mDef using
`isEquivariantFactorSet_datChi` (AtomCalculus.lean:380); Stage 2 `cupChi_iotaB_eq_zero`
(Hsep.lean:730, 55 ln — uses **`CardH2GammaA.card_H2_gammaA`** CardH2GammaA.lean:215,
`chiDef_decomp`/`cupChi_zero`/`gPart_mem_B2` AffineAssembly.lean:74/128/139,
`chiDef_mem_Z2` VLiftCount.lean:228, `iotaB*` Phase140/Obstruction.lean:56/61/80 abstract);
Stages 3–5 build ξfun ∈ Z1 GA (ElemDual Vmod), pair-cochain ∈ B2; Stages 6–7
**`b1_of_pair_cochain_B2`** (Hsep.lean:55, 101 ln, private, over GA — the engine:
`markC_admissible` → `prop_5_15` clause 3 right slot → `wordHom` → `WordCoh2.obs`
(WordCoh2.lean:1362) → `obs_B2_eq_zero` (:1392) → `MixedBObs.obs_inflation`
(MixedBObs.lean:110, typed at F₄⧸NA) → `markC_map` → `mixedB_eq_relZPair`
(MixedBObs.lean:79, generic) → `h1wMk`/`B1w` extraction → `eval_dZero` +
z1Equiv-injectivity); Stage 8 `mchar_conj_invariant_eq_zero` (Half139Local.lean:138,
Γ-free) + `psiVCoord*` (Hsep.lean:593–643, GENERIC); Stage 9 close.

## 2. Comparison with the G_ℚ₂ twin (Phase140/Local.lean, 1359 ln)
`tcocycle_card`/`hZcard`: structurally parallel (only final counting lemma swaps).
`hsep`: NOT parallel — local uses the cup20 route with no Γ_A analog; Γ_A route is the
marking-descent one above. `hpartial`: parallel except stage 6 (local:
`cup11_dualEval_right_separating` B6; Γ_A: `b1_of_pair_cochain_B2` through obs/mixedB).

## 3. Line accounting (Phase140/GammaA/*, 1695 ln total)
- GENERIC reusable as-is: 567 ln (33%) — CharCover section 261 (Foundation.lean:181–441);
  Hsep generic helpers 306 (`exists_marking_map_eq` 13, `mk_eq_of_mkT_eq` 25,
  CharKernelPrivate 22, `fixed_elemDual_conj_apply` 33, `coe_toMul_mkM_smul` 14,
  `descend_tPart_*` 63, `psiVCoord*` 136).
- Γ_A-tied: 1128 ln (67%) = ~880 real re-proof (`hZcard` 66, `tcocycle_card` 77,
  `b1_of_pair_cochain_B2` 101, `mlift_of_relatorFree_marking` 221,
  `tCharC_relatorSum_eq_zero` 36, `invariant_dual_relatorSum_eq_zero` 47, `hsep` 68,
  `cupChi_iotaB_eq_zero` 55, `hpartial` 209) + ~248 retype-only (headers 73; 4 micro-helpers
  52; `exists_relatorFree_marking` 79 — body never touches GA; end matter 44).

## 4. Γ_R readiness
Present: `NR`/`GammaR` (Roe/GammaR.lean:182/:196); `instDistribMulActionGammaR`/
`htriv_gammaR`/`gammaR_eq_quotient` (RStage/GammaR.lean:49/:61/:43); `markC_R`/
`markC_admissible_R` (Roe/Prop23.lean:203/:209); `prop_5_15_R`/`cor_5_17_card_R`
(Roe/DualityAssembly.lean:485/:509); `Z1wR`/`B1wR`/`H2wR` (Roe/FoxBasic.lean:152/156/190);
`IsSelfDual_R` (Roe/TrivialSelfDual.lean:463); `gammaR_topologicallyFinitelyGenerated`/
`lemma_8_2_R` (Roe/Supply.lean:75/:202).

**Missing prerequisites (searched, no hits) — the R31b package:**
1. `z1Equiv_R : Z1 (F₄⧸NR) A ≃+ Z1wR (markC_R q)` — WordCohBridge.z1Equiv (:438) twin.
   Needed by ALL FOUR residues. (Bring the small companion family: `markC_map`, `eval`,
   `toZ1wHom`, `eval_dZero`, `wordHom` — WordCohBridge.lean:96/~104/165/451/~62.)
2. `obs`/`obs_B2_eq_zero`/`obs_inflation` for `NR` — WordCoh2.lean (126 NA occurrences)
   and MixedBObs.lean are hard-wired to F₄⧸NA. Needed by `b1_of_pair_cochain_B2` ⇒ hpartial.
3. `card_H2_gammaR : Nat.card (H2 GammaR (ZMod 2)) = 2` — CardH2GammaA.lean:215 twin;
   ALSO the `SourceData.cardH2` field (ii.5 leaf).
4. `sep_word_R` — RStage/GammaA.lean:334 twin at `IsSelfDual_R`.
5. `redValues_eq_of_coverLift_R` + `mlift_of_relatorFree_marking_R` — both typed at
   GA/`gammaGen`/NA/`Marking.descend`; the latter additionally needs `WildRelR` for `WildRel`.

Spine swaps throughout: `WildRel → WildRelR`, `markC → markC_R`, `prop_5_15 → prop_5_15_R`
(clause numbering unchanged; hypothesis surface per R26b report — split shapes hU-free,
x₀↔x₁ slot swap per R22), `bridge_wildR` IMPORTED never re-defined.
