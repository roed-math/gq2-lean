# Erratum: `h₀` transcription bug (missing `d₀` factor) — resolution of the Prop 5.8 concern

**Date**: 2026-07-03 · **Found by**: P-13 (ε-exponent formalization) · **Status**: fix planned, see §5

## 1. Verdict

The Prop 5.8 "inconsistency" flagged during P-13 (commits `f1441e7`, `72dea54`) is **not a paper
error**.  It is a **transcription bug in this repo**: the auxiliary word `h₀` of paper eq. (3)
was transcribed with one factor dropped.

* **Paper, eq. (3)** (p. 2–3) and **Appendix B machine block** (p. 50), *identically*:

  ```
  h0 = (x0^g0) * x0 * dg * d0 * d0^2 * hcomm
  ```

* **Repo** (`GQ2/Words.lean:99`, and the profinite mirror `GQ2/GammaA.lean:75` `h0Hat`):

  ```
  h0 = (x0^g0) * x0 * dg *      d0^2 * hcomm     -- bare d0 missing (haplography)
  ```

The dropped bare `d₀` is load-bearing: with it, `h₀` matches Lemma 5.2's class-two word
`h_ϕ(X,D) = ϕ(X)·X·ϕ(D)·D·D²·[ϕ(D),D]` (with `ϕ = (·)^{g₀}`, `X = x₀`, `D = d₀`), so the
identity (32) and the whole §5 ledger (5.3, 5.4, 5.8's exponent count) apply to it.

## 2. How it was caught

P-13 proved, for the **repo's** word (Lean: `GQ2.FoxH.expMod2_wildValueExp`, std-3):

* mod-2 exponent vector of the repo `r_w` = `(0, 0, e+1, e+1)` for every integer `ω₂`-representative `e`
  — in particular **τ-component 0**;
* while the tame relator has vector `(0, 1, 0, 0)` (`expMod2_fgTame`);
* so the Stokes corrections (Lemma 5.7, proved) do **not** cancel in the trace, and (41) fails for
  the repo word — concrete counterexample: `C = 1`, `A = 𝔽₂`, `y = (0, id, 0, 0)`, `a = 1`
  (LHS `= 0`, RHS `= 1`; note this `y` is not a cocycle, so no descent statement is contradicted).

The paper's Prop 5.8 proof asserts `ε(r_w) = (0,1,0,0)` via "the two occurrences of `d₀` cancel"
in `h₀` — which is true only for the paper's `h₀` (occurrences: `d_g` and the bare `d₀`; the
`d₀²` pair cancels separately).  The repo's `h₀` has only one net occurrence.  That discrepancy
is what unmasked the transcription.

## 3. Corrected analysis (paper's word)

With `h₀ = x₀^{g₀}·x₀·d_g·d₀·d₀²·h_c` (`ε(d₀) = (0, e, e+1, 0)`):

* `ε(h₀) = 2·x₀ + 2·ε(d₀) + 0 + 0 = (0,0,0,0)` — for **every** `e` (paper: "zero exponent vector" ✓);
* `ε(r_w) = ε(u₁⁻¹) + ε(x₁^σ) = (0, e, 0, e) + (0,0,0,1) = (0, e, 0, e+1)`;
* every valid representative `e` of `ω₂` is **odd** (any evaluation group contains an order-2
  element, e.g. `zc 1 ∈ H(A)⋊C`, so `v₂(exponent) ≥ 1` and `omega2Exp` is odd), giving
  `ε(r_w) = (0, 1, 0, 0)` — exactly the paper's claim;
* condition (40) holds for the trace `(1,1)`: `ε(r_t) + ε(r_w) = (0,2,0,0) = 0`, the corrections
  cancel, and **(41)/(42) are provable as stated** (no correction terms, no cocycle hypotheses).
* Sanity re-check of the old counterexample: at `C = 1` the corrected wild dual row is
  `L_w(y) = y₁`, so RHS `= ⟨a, y₁ + y₁⟩ = 0 =` LHS ✓.
* Remark 5.9 ("the wild relator supplies the compensating value") is also correct for the
  paper's word.

## 4. Impact map

| Site | Kind | Action |
|---|---|---|
| `GQ2/Words.lean:99` `Marking.h0` (+ line 75 doc quote) | **definition (finite)** | insert `* t.d0` before `t.d0 ^ 2` (paper-verbatim `dg·d0·d0²`) |
| `GQ2/GammaA.lean:75` `h0Hat` | **definition (profinite)** | same insertion |
| `GQ2/FoxHeisenberg.lean` `wildValueExp` | mirror of the ledger | same insertion |
| `GQ2/FoxHeisenberg.lean` `expMod2_wildValueExp` | theorem about the word | vector becomes `![0, e, 0, e+1]`; same proof shape |
| `GQ2/FoxHeisenberg.lean` `expMod2_wildValueExp_tau` | obsolete (claim false for corrected word) | delete; un-flag the `prop_5_8_left/right` docstrings (statements provable as written) |
| `GQ2/Subdirect.lean` `map_h0`; `GQ2/GammaA.lean` `map_h0Hat` | naturality simp proofs | expected to close unchanged (one more `map_mul`) |
| `GQ2/AppendixB.lean:87`, `GQ2/Prop32.lean:180` | collapse proofs (`d₀ = 1` in context) | expected to close unchanged (`hd0` in simp set) |
| `GQ2/SectionEight.lean:756` `wildRel_of_comm2` | **statement changes** | in exponent-2 abelian groups the corrected `h₀ = 1` (not `τ`), so `wildValue = τ`: WildRel is **not** unconditional — it becomes `↔ τ = 1`. Restate; at the call site (:917) derive `τ = 1` from the TameRel component (`tameRel_iff_of_comm2`). Character counts unchanged (tame already forces `τ = 1`). |
| `GQ2/Foundations/Axioms.lean`, `scripts/check_axioms.sh` | axiom layer | **no text change** (no axiom mentions `h0`/`WildRel`); census unchanged. Semantic content of `Admissible`-consumers (Statement, Prop23, AdmissibleLimit) auto-corrects. |

All other `wildValue`/`WildRel` consumers use the words abstractly (via `Marking.map_*`
naturality) and are unaffected.

## 5. Landing plan

1. One **atomic commit**: both definition sites + `FoxHeisenberg` mirror/exponent redo +
   `SectionEight` restatement + any fallout the full `lake build GQ2` reveals; re-run
   `scripts/check_axioms.sh`.
2. **Sequencing caution**: `SectionEight.lean` (and `tickets.md`) currently carry uncommitted
   parallel-session work; land after pausing that session or hand its one-lemma repair to its owner.
3. Then P-13 resumes the wild row against the corrected word, now targeting the **paper-verbatim**
   Prop 5.8: generalized `wildValueExp_eq_wildValue_of_dvd` (order-divisibility form) + section
   homs (`C ↪ H(A)⋊C`, `A^∨⋊C ↪ H(A)⋊C` ⇒ exponent divisibilities) + `omega2Exp`-odd helper ⇒
   `hr`, `stokesEval_wild_l`, `mixedB_wildRow`, and the assembly of `prop_5_8_left/right`
   (corrections cancel).  Lemma 5.13's normal forms consume the same bridges.

## 6. External note

Appendix B states the machine block "records the exact word used in the computational
verification".  Any external verification code transcribed from the same source should be
checked for the same haplography (`dg*d0*d0^2`, not `dg*d0^2`).
