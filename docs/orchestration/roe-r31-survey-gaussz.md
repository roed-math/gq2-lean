# R31 survey: ii.7 GaussZ dichotomy twins + the WordCohBridge gap for Γ_R (2026-07-25)

Consumed by R31b (bridge section) and R31g (GaussZ layer). Tip ≈ c054ae5.

## The Γ_A twins
`gaussZResidueD_gammaA_unramified` (GaussZ/GammaAD.lean:296–314, proof to :587) and
`_ramified` (:589–606, proof to :899). Signatures byte-identical except
`hunram : ∀ v, F.alpha tameTau • v = v` vs `hram : ∃ v, F.alpha tameTau • v ≠ v` and
conclusion `-(2^m)` vs `(2^m)`. Section variables GammaAD.lean:199–203 (T, Blk + 3 Normal
instance binders). Consumer shape = SourceData.gaussZ_unramified/_ramified fields
(SourceData.lean:223–268) with B.bA → `sourceBoundaryMap tame pro2 compat` + letI smulZmod2
prefix; sourceR must bind Γ_R clones.

8-stage proofs (292/311 ln), sharing stages 0/1/HV/2/7; diverging in 3 (split vs ramified
pack), 4-membership, 6 (value). NOT parallel to the local twins (GaussZ/FinalD.lean —
Tate-duality route, no word gauge); no single generic engine exists. Shared substrate
(GEN, reuse): gaussZ_reduction (GaussZ/Reduction.lean:234), hfix_of_simple_nt
(GaussZ/CoordGammaA.lean:64), and crucially the count seams
`finsum_sign_{un,}ramified_of_action` (GaussZ/FinalGammaA/Action.lean:109/:351, abstract
q/C/V, zero Γ_A content) — **Roe/Gauss.lean already wraps these as
QZeroR_finsum_sign_{un,}ramified**, which slot into stage 7 at C := HVq T Blk,
V := Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), q := blockQbar, c := cF; hq/hns/hinv/h2
inputs = blockHquad/blockHns/hv_inv/blockPS_exp2 (all GEN, available).

## Banked (R27, Roe/Gauss.lean, 252 ln std-3)
QZeroR(_apply/_split/_eq_qDouble), polar_QZeroR, QZeroR_nonsingular_ramified,
QZeroR_symplectic_split_cancels, toAddEquiv_smul(_symm), QZeroR_zeroCount_{un,}ramified,
QZeroR_finsum_sign_{un,}ramified. I.e. stage 7 is DONE abstractly.

## MISSING — stages 3–6 (everything between the word and the number)
1. κ⁰ evaluation of wildValueR: liftMark_kappa0_wildValueR_fib_{split,ramified} — twins of
   GaussZ/FinalGammaA/Kappa.lean:374 (140 ln) and :640 (137 ln + helpers 482–639). Split
   target: wildValueR.fib = q(d); ramified target: Wall double q d + polar q d (σ₂⁻¹•d)
   (= R27's QZeroR shape). Hardest part, ~435 ln analog. Kappa.lean toolkit :174–341
   (sdSec, liftMark_kappa0_tameValue_fib, relZPair_kappa0_fst_eq_zero — tame shared,
   sdToWL, sdBaseMarking, sdOffsets, m-calculus) is GENERIC (~168 ln) — reuse.
2. relZPairR + relZPairR_comap (WordCoh2.lean:173/:586 twins) — shared with ii.4 (R31c).
3. The degree-1 word bridge (see below) incl. h1CoordGammaR (CoordGammaA.lean:157 twin).
4. obsR / QZero_eq_relZPair_kappa0_R (RelatorGammaA.lean:223 twin; Γ_A section :186–291
   ~106 ln; the Sd carrier/kappa0Cocycle/graphSdHom :45–182 are GENERIC — reuse) + 
   IotaGammaR (IotaGammaA.lean twins :74/:86) + card_H2_gammaR (from R31c).
5. x₁-section bijections x1Section_bijective_{split,ramified}_R (Kappa.lean:62/:107 twins,
   ~130 ln; inputs BANKED: lemma_5_13_split_R Roe/NormalForms.lean:95 — shape
   `x 1 = 0 ∧ x 2 = 0`, lemma_5_13_ramified_R :130, x1Supported_mem_Z1wR_ramified
   Roe/DualityAssembly.lean:367, normalForm_of_shapes_R :256, split_shapes_of_wild_R :228,
   x1mem_of_Z1wRShape :249).
6. The two twins themselves (GammaRD.lean ~292+311 ln) + X1Sections ψ-glue (~85) +
   HeadSlots clones blockProjF_thetaGR_*/blockProjF_markC_R_* (~96; use S.tame_* fields
   in place of B.tameA_*) + relZPairR_kappa0_reindexHom (~15; rest of SdReindex generic) +
   CoordGammaR (~95: rhoPrimeGR/finite_vcocycle_gammaR — needs Phase140 hZcard (R31f)!/
   thetaGR/roundtripGR/h1CoordGammaR) + boundaryLift_head_gammaR (HeadDat.lean:342 twin,
   one-liner) + SourceData wiring (~5).

⚠ GAUGE SWAP everywhere: Γ_A normal form is x₀-supported ![0,0,c,0] (slot 2, Z¹w shape
`x 1 = x 3 = 0`); Γ_R is x₁-supported ![0,0,0,d] (slot 3, Z¹wR shape `x 1 = 0 ∧ x 2 = 0`).
Stage-6 slot facts use congrFun (hevalx v) 3 instead of 2; zero-slot facts permute.

## Clone budget (ii.7): core GaussZ Γ_R layer ≈ 1565 ln; +WordCohBridgeR +IotaGammaR/obsR
≈ 2190 ln total. Reused verbatim ≈ 1156 ln (Action 370, Counts 270, Assembly split-pack
254, Kappa toolkit 168, RelatorGammaA generic 138, + Reduction/Block head layer).

## THE BRIDGE (R31b's spec — needed by ii.3, ii.4, ii.5, ii.6, ii.7)
New file cloning GQ2/WordCohBridge.lean (492 ln) at GR := F₄ ⧸ NR (~400 ln; markC_R/
markC_admissible_R already banked in Roe/Prop23):
- gammaGenR := univMarking.map (quotientMk NR) (bundled marking — only the four scalars
  gammaSigmaR/TauR/X0R/X1R exist at Roe/Tame.lean:118–127);
- wordHom/liftHom at GR (:64/:330 twins), evalR (:102), eval_mem_Z1wR (:147 — the wild
  clause swaps wildRelator_mem_NA → wildRelatorR_mem_NR, Roe/AdmissibleLimit.lean:75 —
  the ONLY genuinely new ingredient), NR_le_ker_classify_R (:265), toZ1wRHom (:165),
  ofZ1wR (:365), round-trips toZ1wHom_ofZ1w/ofZ1w_toZ1wHom (:394/:417),
  z1EquivR : Z1 GR A ≃+ Z1wR (markC_R q) (:438 twin),
  h1EquivR (:467 twin), eval_dZeroR (:~484).
- liftMarking_eval_wildRel (:137) and liftMarking_Z1w_wildRel (:247) are wild-relator-
  specific: re-derive for wildValueR (cf. Roe/WildRow.lean:219, bridge_wildR in FoxBasic).
Also in R31b scope (CorrectionR): push_tameRelR/push_wildRelR, corrMark_{aR,y1R,cR} +
wildValueR_correction (see roe-r31-survey-stage-ii5.md §5.2 — conclusion shape
`= r₁ · t.wildValueR` identical to Γ_A's), liftMarking_wildValueR_g, corrected_wildValueR,
d1FunR_base_change, bundled gammaGenR if placed here.
