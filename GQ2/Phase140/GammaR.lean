/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Phase140.GammaR.Foundation
import GQ2.Phase140.GammaR.Hsep

/-!
# The `Γ_R` (140) counting residues  (obligation ii.6)

The Roe-candidate mirrors of the `Γ_A` (140) counting residues of `GQ2/Phase140/GammaA/`.
Where the `Γ_A` files run on the `r_A` word complex (`prop_5_15`, `z1Equiv`, `WordCoh2.obs`), these
run on the **Roe** word complex `r_R` (`prop_5_15_R`, `z1EquivR`, `WordCoh2R.obs_R`) — still with
**no B-axioms on the word side**, since the candidate route is axiom-free on both spines.

Together with `GQ2/HalfTorsorGammaR.lean` (`card_H2_gammaR`, the ii.5 leaf) and
`GQ2/RStage/GammaR.lean` (`stageR136_gammaR_of_hcard`), these four theorems complete the
`GQ2.SourceData` obligation list for `Γ_R`; each is restated in its **verbatim** `SourceData`
field type and discharged by the same plain lambda `BoundaryMaps.sourceA` uses for its `_gammaA`
twin, so R32's `sourceR` is a copy-paste.

* **`hZcard_gammaR`** — `#Z¹_{Γ_R,ρ'}(V) = #V²`.  The `#fixedPts` factor is `1` by
  `card_fixedPts_elemDual_eq_one_of_nontrivial` (`V` a simple `𝔽₂[Y_C]`-module with nontrivial
  action), exactly as on the `Γ_A` and local sides.
* **`tcocycle_card_gammaR`** — the `T`-cocycle count in the `muZero` closed form.  The
  `#fixedPts` factor is deliberately **not** reduced: it is the shared `μ₀`, and its equality
  across the two sources is what `prop_8_9`'s source-independence consumes.
* **`hsep_gammaR`** — the `(T^∨)^C`-separation, by the marking route: each nonzero invariant
  character's vanishing obstruction produces a lift through its `𝔽₂`-cover, which forces
  `χ`-agreement of the **tame and Roe-wild** relator values of a set-lift marking
  (`redValues_eq_of_coverLift_R`); `sep_word_R` converts total agreement into word-level
  corrections; the corrected marking descends by `mlift_of_relatorFree_markingR`.
* **`hpartial_gammaR`** — nondegeneracy of the obstruction pairing in the character.  Stages 1,
  3–5 and 8–9 are frame-level or `Γ`-generic and mirror the `Γ_A` proof verbatim; the two
  source-specific stages are stage 2 (`cupChi_iotaB_eq_zero_R`, on `card_H2_gammaR`) and stages
  6–7, the word-side right-slot separator `b1_of_pair_cochain_B2_R`.

## What is reused rather than cloned

* the per-character `𝔽₂`-cover layer `Phase140GammaA.charKer`/`charCover`/`charCoverMap`/
  `charCover_p_comp`/`exists_lift_charCover` — **abstract in `Γ`**, applied here at `Γ_R` with
  `htriv_gammaR`;
* the L4/L5 cover-lift kernel `RStageGammaR.redValues_eq_of_coverLift_R` /
  `lift_of_relatorFree_markingR` (`GQ2/Roe/CoverLiftR.lean`), which R31e deliberately generalised
  (abstract `π`, `Pro2Core` taken directly) so that the **non-surjective** `T`-stage here needs
  only a corestriction — `mlift_of_relatorFree_markingR` is 145 ln against the `Γ_A` original's
  221 ln of cloned descent;
* the word-free marking calculus of `RStageGammaA` (`marking_ext`, `corrMark`,
  `tameValue_correction`) and the `Γ`-free conjugation layer `RadicalEdgeGammaA.cActT`/`cactFun`.

The `Γ_A` `private` helpers that are genuinely `Γ`-free (`exists_marking_map_eq`,
`mk_eq_of_mkT_eq`, `fixed_elemDual_conj_apply`, `coe_toMul_mkM_smul`, `descend_tPart_*`,
`psiVCoord*`) are restated here — being `private`, they are not importable — binder-for-binder.

**File organisation** mirrors `GQ2/Phase140/GammaA/`: `Foundation` holds the two counts and the
`T`-stage descent, `Hsep` the word-side separator and the two final assemblies.  Private helpers
stay with their consumers; this umbrella fixes the public import path.

Axioms: std-3 only (`propext`, `Classical.choice`, `Quot.sound`) — no B-axioms.
-/
