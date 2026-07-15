# Erratum: `h₀` transcription bug (missing `d₀` factor) — resolution of the Prop 5.8 concern

**Date**: 2026-07-03 · **Found during**: the ε-exponent formalization · **Status**: repaired and
regression-documented

## 1. Verdict

The Prop 5.8 "inconsistency" flagged during P-13 (commits `f1441e7`, `72dea54`) is **not a paper
error**. It was a **transcription bug in the first Lean transcription**: the auxiliary word `h₀`
of paper eq. (3) had been copied with one factor dropped. The current Lean definitions contain the
factor and agree with the paper.

* **Paper, eq. (3)** (p. 2–3) and **Appendix B machine block** (p. 50), *identically*:

  ```
  h0 = (x0^g0) * x0 * dg * d0 * d0^2 * hcomm
  ```

* **Pre-fix Lean transcription** (formerly in `GQ2/Words.lean` and its `h0Hat` mirror):

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

## 4. Repair map

| Site | Kind | Completed repair |
|---|---|---|
| `GQ2/Words.lean` `Marking.h0` | **definition (finite)** | inserted `* t.d0` before `t.d0 ^ 2` (paper-verbatim `dg·d0·d0²`) |
| `GQ2/GammaA.lean` `h0Hat` | **definition (profinite)** | made the same insertion |
| `GQ2/FoxHeisenberg/Traced.lean` `wildValueExp` | mirror of the ledger | made the same insertion |
| `GQ2/FoxHeisenberg/Traced.lean` `expMod2_wildValueExp` | theorem about the word | changed the vector to `![0, e, 0, e+1]` |
| former `expMod2_wildValueExp_tau` | obsolete claim | deleted; the corrected `prop_5_8_left/right` statements are proved |
| `GQ2/Subdirect.lean` `map_h0`; `GQ2/GammaA.lean` `map_h0Hat` | naturality simp proofs | closed with the extra multiplication factor |
| `GQ2/AppendixB.lean`, `GQ2/Prop32.lean` | collapse proofs (`d₀ = 1` in context) | closed using the existing `hd0` simplification |
| `GQ2/SectionEight/ScalarCount.lean` `wildRel_of_comm2` | **statement correction** | restated the exponent-2 abelian case with the required `τ = 1`, supplied by the tame relation at its consumer |
| `GQ2/Foundations/Axioms.lean`, `scripts/check_axioms.sh` | axiom layer | **no text change** (no axiom mentions `h0`/`WildRel`); census unchanged. Semantic content of `Admissible`-consumers (Statement, Prop23, AdmissibleLimit) auto-corrects. |

All other `wildValue`/`WildRel` consumers use the words abstractly (via `Marking.map_*`
naturality) and are unaffected.

## 5. Resolution

The finite and profinite definitions, the Fox–Heisenberg exponent ledger, and the §8 scalar-count
consumer were repaired together. The corrected word is now stated directly in the docstrings of
`Marking.h0` and `h0Hat`; `prop_5_8_left/right` and the later normal-form arguments compile against
that definition. The repository-wide build and axiom gates include this path, so the earlier
transcription cannot reappear without invalidating downstream proofs.

## 6. External note

Appendix B states the machine block "records the exact word used in the computational
verification".  Any external verification code transcribed from the same source should be
checked for the same haplography (`dg*d0*d0^2`, not `dg*d0^2`).
