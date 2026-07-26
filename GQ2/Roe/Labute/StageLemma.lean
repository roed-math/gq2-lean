/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.Labute.StageLemma.Congruence
import GQ2.Roe.Labute.StageLemma.Defect
import GQ2.Roe.Labute.StageLemma.DigitToolkit
import GQ2.Roe.Labute.StageLemma.CrossedDerivation
import GQ2.Roe.Labute.StageLemma.StageOne
import GQ2.Roe.Labute.StageLemma.StageTwo

/-!
# The defect calculus, the span theorem, and the stage lemma  (L-campaign ticket L1/L4)

**Statements final (ticket L1); fills tickets L4a (calculus + `d̄` + SL2) and L4b (span
theorem + SL1)** — the split of spike §4.8, recorded as binding in the design memo.
Design record: `docs/orchestration/labute-l1-design.md`; sources: `labute-spike.md`
§2.1–2.5 (formulas, thresholds, and the statement freeze), `labute-plan.md` §2.2.

All statements live at the calculus threshold `k ≥ 3` (spike §2.1: at `k = 2` squaring is
not additive and `λ₁`-moves change the Frattini class — *base-case territory, not calculus
territory*).

## The shift word shapes (spike §2.2, signs resolved)

In `Z_k` every sign is trivial, so the frozen formulas fix one multiplicative order:

* `r₀`-side, triple `(a, s, y)`, modification `(w₁, w₂, w₃)`:
  `d̄(w) = w₁² · [w₁,a] · [w₂,y] · [w₃,s]`  (`dbarWordR0`; the `S⁴` factor is inert, the
  `A²` factor gives the π-diagonal `w₁²[w₁,a]`, `[S,Y]` the two cross terms);
* `r₂`-side, triple `(s, x, y)`, modification `(u, v, w)`:
  `d̄(u,v,w) = w² · [w,y] · [u,x] · [v,s]`  (`dbarWordR2`; `y` is the distinguished
  squared generator, the x-block is π-inert but contributes both cross terms, `[y, y^s]`
  is fully inert).

All commutators are repo-convention (`commP`; see `TwoCentralTower.lean`).

## The span theorem (spike §2.3 — L4b's load-bearing wall)

Free pro-2 form only (`freeProTwo`): for `k ≥ 3`,
`Zₖ(F₃) ≤ ⟨Im d̄ₖ, g₂^{2^{k-1}}, g₃^{2^{k-1}}⟩` with the **relator-adapted tail pair**
(`r₀`: tails `(S, Y)` = generators 1,2; `r₂`: tails `(s, x)` = generators 0,1 — an early
spike run with the wrong pair `(x, y)` failed rank checks, so the pair is load-bearing),
and the **`2^{k-1}` exponent** (level-`k` classes; Serre §7 prints `2^h`, off by one —
spike §2.3 erratum, machine-confirmed).  Only the `≤` direction is frozen (the reverse
inclusion has no consumer).  Descent to the towers at any generating triple is a separate
statement (`span_descent_*`), via `map_twoCentralSeries_eq`.

Proof route for the fills: the no-basis-theorem structural induction of spike §2.5(a);
fallbacks O1/O2 of plan §7 (owner-gated) if it snags — the named residual risk.

## The stage lemma (spike §2.4)

`SL1` (reachability, L4b): for `T ∈ S^P_ₖ`, the defect is hit by a modification —
`∃ w ∈ (λ_{k-1}/λ_{k+1})³, d̄_T(w) = δ(T)⁻¹` (inverse form for exact composability with
the shift formula; in `Zₖ` inverses are trivial, so this is the memo's `δ ∈ Im d̄`).
`SL2` (digit adjustment, L4a): once the defect vanishes, a `ker d̄`-modification places
the corrected lift in `S^P_{k+1}` — the memo's "`ker d̄ₖ → (ℤ/2)²` is onto" collapsed to
its consumed form; the digit bookkeeping ((ℤ/2)²-ontoness, the automatic vanishing of the
π'd slot's fresh digit) is deliberately *not* frozen — it is L4a's internal proof
mechanism, with the dimension-count fallback of spike §2.5(c) equally admissible.
`stageStep` (proved here, modulo the sorried inputs): `S^P_ₖ ≠ ∅ → S^P_{k+1} ≠ ∅` — the
composability certificate for the frozen statements, and the exact interface Assembly
consumes.

## Module layout

This file is an umbrella: every declaration below lives, unchanged, in one of the six
pieces under `GQ2/Roe/Labute/StageLemma/`, imported above in dependency order.

* `StageLemma.Congruence` — the `λ`-congruence calculus and the `commP` move-rule toolkit;
* `StageLemma.Defect` — the shift formulas `defectR0_mul` / `defectR2_mul`, modification
  stability `sPR0_mul_mem` / `sPR2_mul_mem`, and the span theorem `span_free_*` /
  `span_descent_*`;
* `StageLemma.DigitToolkit` — the `2`-adic digit calculus, the χ-plumbing, and the
  `ker d̄` witnesses (shared by SL1 and SL2);
* `StageLemma.CrossedDerivation` — the finite lift group `WL N`, the two coordinate
  derivations, `d̄`-additivity, and tail separation;
* `StageLemma.StageOne` — reference words and `stageSL1R0` / `stageSL1R2`;
* `StageLemma.StageTwo` — `stageSL2R0` / `stageSL2R2` and `stageStepR0` / `stageStepR2`.

Helpers that were `private` to the single file and are now consumed across the cut are
public in the piece that declares them; they remain internal to this development.
-/
