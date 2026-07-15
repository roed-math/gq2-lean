/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Phase140.GammaA.Foundation
import GQ2.Phase140.GammaA.Hsep

/-!
# The `Γ_A` (140) counting residues

The candidate-source mirrors of the `G_ℚ₂` (140) counting residues of `GQ2/Phase140Local.lean`.
Where the local file counts `#Z¹_{Γ,ρ'}(V)` with `card_Z1_eq` (the 5.16 local Euler characteristic,
axioms B6/B7), here the same count comes from the **candidate duality** `prop_5_15` (`IsSelfDual`)
through the word-complex bridge `z1Equiv : Z1 GA A ≃+ Z1w (markC ρ')` (`WordCohBridge`) — **no
B-axioms on the word side** (the same swap as `RStageGammaA.hZcount_gammaA`).

* **`hZcard_gammaA`** — `#Z¹_{Γ_A,ρ'}(V) = #V²`, the `Γ_A` twin of `Phase140Local.hZcard_local`.
  The `#fixedPts` factor is `1` by `card_fixedPts_elemDual_eq_one_of_nontrivial` (`V` is a simple
  `𝔽₂[Y_C]`-module with nontrivial action), exactly as in the local file.
* **`hsep` machinery (`hsep_A`)** — the `(T^∨)^C`-separation at `Γ_A` runs the **marking route**
  of the Prop. 8.9 assembly (`RStageGammaA`) at the `T`-stage, since the local `prop_5_16` cup route
  (`hsep_local`'s stages) has no `Γ_A` analog:
  - `charKer`/`charCover` — the per-character `𝔽₂`-covers `B/ker χ ↠ B/T` of a nonzero
    `χ ∈ (T^∨)^C` (the `T`-stage mirror of `blockFrameImpl.scalarCover`);
  - `exists_lift_charCover` — `β_χ(c) = 0` (`chiDef ∈ B²`) yields a continuous hom lift of
    `g_c` through the `χ`-cover, by the direct `B²`-extraction `g γ := (fLift γ mod ker χ)·z^ψγ`
    — no twisted `H²(Γ,T)` theory;
  then `RStageGammaA.redValues_eq_of_coverLift` + `sep_word` + the `WordLift` correction and
  `Marking.descend` close the separation (increments B/C).

All declarations are std-3 (no B-axioms): the candidate route is axiom-free.

**File organisation.**  `Foundation` contains the candidate count, character covers, and descent layer; `Hsep` contains the word-side separator and the final separation assembly.  Private helpers stay with their consumers, while this umbrella preserves the original import path and public declaration names.

-/
