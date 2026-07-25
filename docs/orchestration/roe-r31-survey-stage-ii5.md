# R31 survey: ii.5 stageR136 chain (RStage) for Γ_R (2026-07-25)

Consumed by R31e. Tip ≈ c054ae5. Companion surveys: roe-r31-survey-ii6.md (Phase140),
roe-r31-survey-ii34.md, roe-r31-survey-gaussz.md.

## Architecture
- The generic builder is `blockStageR136` (GQ2/Block/RStage.lean:341–358; NOT RStage/GammaA),
  abstract Γ, taking `htriv`, `hcard : #H²(Γ,𝔽₂)=2` (THREAD HYPOTHESIS-SIDE, as
  `stageR136_gammaA_of_hcard` does — do not prove card_H2 here), `hfg`, `hsep_hom`, `hZcount`.
  Do NOT use `blockStageR136_ofSplitCriterion` (:415) — Γ_A doesn't (its hsplit quantifies
  over non-surjective g; BoundaryLifts bundles surjectivity; see RStage/Local.lean:28–31).
- Γ_R already banked: htriv_gammaR (RStage/GammaR.lean:61), gammaR_topologicallyFinitelyGenerated
  (Roe/Supply.lean:75), markC_R/markC_admissible_R(+_clauses) (Roe/Prop23.lean:203/209/216
  — clause order matches adm.1/.2.1/.2.2.1/.2.2.2 = Generates/TameRel/WildRel/Pro2Core),
  prop_5_15_R (Roe/DualityAssembly.lean:485, same .2.1 clause shape), prop_5_8_right_R
  (Roe/TrivialSelfDual.lean:176), H2w_two_torsion_R (Roe/Devissage/EvalPairings.lean:54),
  H0w_eq_fixedPts reuse verbatim (H0wR_eq_H0w is rfl, Roe/FoxBasic.lean:159),
  tameRelator_mem_NR / wildRelatorR_mem_NR (Roe/AdmissibleLimit.lean:70/75),
  Marking.descendR/AdmissibleR/pushR_admissible (Roe/Prop23.lean:127/108/110),
  Marking.map_wildValueR (Roe/Words.lean:146), gammaR_eq_quotient (RStage/GammaR.lean:43).

## hZcount_gammaA (RStage/GammaA.lean:71–251, 181 ln)
Body ~3 lines of source-specific math (:224–226): `markC_admissible` + `z1Equiv` +
`prop_5_15` clause 2. Everything else source-free plumbing: private helpers
`frattiniK_add_self` (:75, clone of Local.lean:148), `elemDual_fixed_apply_conj` (:89 ←
Local.lean:162), `card_fixedPts_eq_card_rCharSub` (:122 ← Local.lean:195),
`card_rCocycle_eq_sq_mul_card_fixedPts` (:150, 77 ln, ~74 source-free). `blockRChar_card`
(Block/RStage.lean:303) frame-generic reuse. Γ_R BLOCKER: z1EquivR (see bridge survey).

## hsep_hom_gammaA (RStage/GammaA.lean:253–1174, 922 ln)
7-step proof (:1036–1174, 139 ln body). Reusable verbatim (~215 ln): RelatorCorrection
section :360–438 (`powOmega2_central_involution`, `tameValue_correction` — tame relator
SHARED, `conjP_central_correction`, `commP_central_correction`), `conjP_central_left`,
`corrMark` def + `corrMark_sigma2` (sigma2 shared), `marking_ext` (:596), `projW`/`mulW`/
`baseW`/`liftMarking_map_projW`/`liftMarking_tameValue_g`/`corrected_tameValue` (:635–690).

Must re-prove (~700 ln, of which mechanical ~450):
1. `push_tameRelR`/`push_wildRelR` (:606/:612 — 5–6 ln each via *_mem_NR).
2. **`wildValueR_correction`** + corrMark chain (:440–589): Γ_A's NINE aux-word lemmas
   (u0,u1,g0,z0,d0,c0,dg,hc,h0) are ALL DEAD for Γ_R. Replacement is SHORTER (~60 ln vs
   ~110): `corrMark_aR` (from ((r₂x₀)³)⁻¹(r₁τ) = (r₂r₁)·(x₀⁻³τ) + powOmega2_central_involution),
   `corrMark_y1R` (conjP_central_correction), `corrMark_cR` (correction-free by
   commP_central_correction), plus (r₃x₁)² = x₁². Ledger cancels the same way (r₂ from
   (conjP x₀ σ)⁻¹, r₂r₁ from aR, r₂²=1) → **conclusion has the IDENTICAL shape
   `= r₁ · t.wildValueR`**, so everything downstream keeps its exact statement shape.
3. `liftMarking_wildValue_g` (:652, ~8 ln), `corrected_wildValueR` (:690, ~13 ln at d1FunR),
   `d1FunR_base_change` (:712, ~13 ln; tame slot free by d1FunR_fst = d1Fun_fst
   Roe/FoxBasic.lean:69; wild slot cf. Roe/WildRow.lean:219).
4. `wTrace_R` package + `sep_word_R` (:275–345, ~85 ln): statement-for-statement port on
   `H2wR = (A×A) ⧸ (d1R t).range` driven by prop_5_8_right_R + IsSelfDual_R clause 1 +
   H0w_eq_fixedPts + card_addHom_zmod2.
5. **`redValues_eq_of_coverLift_R`** (:740, 74 ln full re-proof; uses push_*RelR,
   gammaGenR — bundled marking MISSING, only the four scalars gammaSigmaR/TauR/X0R/X1R at
   Roe/Tame.lean:118–127; ~5 ln to bundle) and **`lift_of_relatorFree_markingR`**
   (:829, 125 ln, ~10 swap sites: Admissible→AdmissibleR, descend→descendR,
   push_admissible→pushR_admissible, NA→NR).
   ⚠ Phase140/GammaA reuses this L4/L5 kernel at the T-stage (Hsep.lean:302,
   Foundation.lean:444) — FACTOR the R version into a shared file (e.g.
   GQ2/Roe/CoverLiftR.lean) so ii.6 (R31f) imports it rather than re-cloning.
6. `hsep_invariantChar_killsRelatorSumR` (:961, 73 ln), `hsep_hom_gammaR` (139 ln port),
   `hZcount_gammaR` (~181 ln incl. 3rd copy of the private M_B/RStageLocal pack),
   `stageR136_gammaR_of_hcard` (21 ln mechanical).

Grep facts: prop_3_8/x0Supported/x1Supported/IsAdmissibleU never used in RStage/GammaA;
NA only at :607–614/:922/:929; Marking.descend at :920. Generic frame/obstruction API all
reusable: obs_zero_iff_lifts, pair_coverMap, coverMap_lifts, scalarCover, trivialRCD,
zsign, homLift_of_split, RStageLocal.{rCommGroup, conjC, conj_mem_R, conjC_smul_of_mk}.
