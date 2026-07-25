# R31 survey: ii.3 multiplicity + ii.4 half-torsor for Γ_R (2026-07-25)

Consumed by R31c (ii.4 + obs layer) and R31d (ii.3). Tip ≈ c054ae5.
Grades: SPEC-word = uses Γ_A relator words (real R work) · SPEC-type = only GA/GammaA as
type, proof source-agnostic (mechanical retype) · GEN = reuse verbatim.
Key: `GA := FreeProfiniteGroup (Fin 4) ⧸ NA` (WordCohBridge.lean:47) — anything typed at GA
is Γ_A-specific BY TYPE even when the proof is source-free.

## TARGET ii.3 — liftsOver_card_gammaA (MStageCountGammaA.lean:601–607)
One-liner over `liftsOver_card_gammaA_of_nonempty` (:488–599) + `liftsOver_nonempty_gammaA`
(:371–481). The :483 docstring's "source-generic" applies ONLY to Step 2 (the Z¹-torsor
translation against a base lift f₀, :530–597, pure group theory).

prop_5_16 is NOT used anywhere in this chain (it's the local twin's). prop_5_15 enters at
exactly two points, both right after `markC_admissible θ hθs`:
- :518–523 clause .2.1 (#Z1w count) after transporting along z1Equiv — the card twin;
- :392–393 clause .1 (#H2w = #fixedPts → = 1 at :439 via `card_fixedPts_MB_dual`) — puts the
  relator pair (v₁,v₂) in range (d1 (markC θ)) — the nonempty twin.
Other source entries: push_tameRel/push_wildRel (:430/:434, relator death, NO surjectivity
needed), the set-lift marking tB over `Marking.push θ` (:422–427), corrected_tame/wildValue +
d1Fun_base_change (:451–466), and `descend_piBC` (:56, private — rebuilds Admissible and
calls Marking.descend/classify/quotientMk NA/univMarking_map_toHom).

GEN reuse: `card_fixedPts_MB_dual` (:261, private, source-free, already duplicated at
MStageCount.lean:351), lemma_7_1_dual (SectionSeven/Basic.lean:434), MB_normal/MB_elem/
ker_piBC/piBC_surj (SectionEight/Recursion.lean:201–262), the private M_B module pack
(:175–361, source-free but private → third copy or de-privatize), LiftsOver
(RadicalEdge/Bridge.lean:71, abstract Γ), Marking.classify + univMarking_map_toHom.

Γ_R must supply: z1EquivR (bridge — see gaussz survey §bridge), push_tameRelR/push_wildRelR,
corrected_wildValueR, d1FunR_base_change (all four in R31b's CorrectionR scope),
descend_piBC_R (clone :56 with descendR/AdmissibleR/quotientMk NR/pushR_admissible),
M_B pack third copy. Banked: markC_R(+admissible+clauses), prop_5_15_R, pushR/descendR,
d1FunR family, map_wildValueR, wildRelatorR_mem_NR, gammaR_eq_quotient.

## TARGET ii.4 — lemma_8_6_gammaA (SectionEight/Partition.lean:286–296)
= `half_torsor_gammaA` (HalfTorsorGammaA.lean:130–161): retype ρ at F₄⧸NA, Γ_A tfg →
Finite (MLifts), then `exists_nonzero_varCoc_gammaA` (:28–108) + `card_H2_gammaA_eq_two`
(:110–128) fed to GEN `CentralObstruction.half_count` (CentralObstruction.lean:1074,
docstring literally "source-generic").

`exists_nonzero_varCoc_gammaA` is SPEC-word via exactly FOUR routes (its cocycle
construction + instance plumbing are source-agnostic):
1. markC_admissible ρ hρ (:69);
2. prop_5_15 (markC ρ) clause .2.2 — the perfect pairing P (B7 enters here);
3. the degree-1 word bridge: h1Equiv (WordCohBridge.lean:467) + eval (:102) +
   eval_mem_Z1w (:147) + ofZ1w (:365) + toZ1wHom_ofZ1w (:394) + h1wMk — deepest dependency;
4. varCoc_class_ne_zero (LedgerGammaA.lean:82) → obs_varCoc_eq_mixedB (:53) → 
   MixedBObs.obs_inflation (MixedBObs.lean:110, at F₄⧸NA) + gammaGen/markC_map +
   mixedB_eq_relZPair (MixedBObs.lean:79; relZPair = Γ_A relator pair, WordCoh2.lean:173)
   + WordCoh2.obs_B2_eq_zero (WordCoh2.lean:1392, at NA).

NOT a source of specificity: `exists_phiF` (LedgerGammaA.lean:315 + privates
:154/:193/:245/:265) is SPEC-type ONLY — no markC/gammaGen/prop_5_15/relator anywhere in
its proof; substance lives in the source-free Edge section of CentralObstruction.lean
(:314–597) and RadicalEdge/GammaA.lean (namespace is a misnomer: no Γ in its variable
block — cactFun*/conj_mem_T are GEN).

`card_H2_gammaA_eq_two`: obsH2_injective gives ≤2; the nonzero varCoc class gives
surjectivity → = 2. So **card_H2_gammaR = SourceData.cardH2 (ii.5 leaf) comes out of THIS
lane** — R31c owns it.

⚠ WARNING (cost-saver): do NOT mistake Roe/DRWordCoh.lean's obs_DR/obsH2_DR/
obsH2_DR_injective for the needed obs at Γ_R — those are stated at DR = maxProPQuotient 2
DRFull (the Demushkin quotient), NOT F₄⧸NR. Γ_A builds obs directly at F₄⧸NA; do the same
at F₄⧸NR (routing through phiDR would need a new argument).

Γ_R must supply (six items; items 3–5 are the shared obs layer):
1. exists_phiF_R — mechanical retype, zero math (cheapest item);
2. the degree-1 bridge h1EquivR/evalR/eval_mem_Z1wR/ofZ1wR/round-trips/eval_dZeroR —
   SHARED with ii.3 (same WordCohBridgeR file, R31b);
3. obs_inflation_R at F₄⧸NR (MixedBObs.lean:110 twin);
4. mixedB_eq_relZPair_R (MixedBObs.lean:79 twin; ingredients exist:
   Roe/Hessian.lean:258 heisMarking_wildValueR_z, Roe/WildRow.lean:219) + relZPairR
   (WordCoh2.lean:173 twin: (..tameValue.fib, ..wildValueR.fib)) + relZPairR_comap (:586);
5. obs_R/obs_B2_eq_zero_R/obs_ker_le_R/obs_ker_eq_B2_R/obsH2_R/obsH2_R_injective at
   H2 (F₄⧸NR) (ZMod 2) — WordCoh2.lean:1316–1445 block twins (obs_B2_eq_zero's proof uses
   isAdmissibleU_of_NA_le + tame/wildValue_eq_one_iff → R twins isAdmissibleUR_of_NR_le
   (Roe/GammaR route, see R4 board note) + wildValueR_eq_one_iff Roe/Words.lean:101);
6. varCoc_class_ne_zero_R + obs_varCoc_eq_mixedB_R (LedgerGammaA.lean:82/:53 twins).
Then exists_nonzero_varCoc_gammaR / card_H2_gammaR_eq_two / half_torsor_gammaR /
lemma_8_6_gammaR are line-for-line ports (GA→GR, NA→NR, markC→markC_R, prop_5_15→prop_5_15_R,
h1Equiv→h1EquivR, obsH2→obsH2_R, tfg→gammaR_topologicallyFinitelyGenerated).

GEN reuse verbatim: half_count, tComplement_nonempty, TCocycle/varCoc/varCoc_mem_Z2
(CentralObstruction GammaLayer section, abstract Γ), discreteTopology_quotient, edgeQ/edge_*/
not_noDescent_of_edge_trivial, cactFun*/cActT_toMul/conj_mem_T, MLifts(+Central)/
RadicalCoverData/NoDescent, finite_continuousMonoidHom (Reconstruction.lean:56).
