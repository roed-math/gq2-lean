/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.Labute.GradedLie.SpanIdentities

/-!
# GL-C: the span base case `k = 3`

Design record: `docs/orchestration/span-gradedlie-plan.md` §2.2 (which follows L4b's
by-hand closure of k = 3 — "colπ-at-π-towers, tails, left-normed columns").
**Statements frozen (GL0); fills ticket GL-C.**

`Q₄(F₃)` has order `2^23` — no `decide`; the proof is structural:

1. Atomize `zLayer 3` at `j = 2` (in `Q₄`); bracket atoms exactly as in the step
   (GL-A single-slot lemmas — valid for all `k ≥ 3`).
2. Sq-atoms `mk(v²)`, `v ∈ λ₂`: expand `v` by `lambdaImage_induction` at `j = 1`;
   squaring is multiplicative on λ₂-classes mod λ₄; two atom families remain:
   * `(⁅u,ζ⁆)²`: trade via the exact identity `⁅u²,ζ⁆ = ⁅u,ζ⁆·⁅⁅u,ζ⁆,u⁆·⁅u,ζ⁆`
     for level-3 bracket atoms (`u², ⁅u,ζ⁆ ∈ λ₂`) — free by 1;
   * `u⁴` (`u` ambient): induction on a generator-word representative of `u mod λ₂`
     (λ₂-shifts die into the previous families); generator fourth powers:
     `β⁴` = the two tails (`2^{3-1} = 4`), `τ⁴ = d̄₃(τ-slot at τ²)` since
     `⁅τ²,τ⁆ = 1` (the diagonal trick).
3. Assemble.

The `u⁴` word-length induction is the risk concentration of the campaign (memo §6):
on a snag report the exact stuck subgoal and STOP — the GL-D Magnus functionals give
a finite certificate fallback at k = 3; do not invent new statements.
-/

namespace GQ2.Roe.Labute

/-- **The span base case, `r₀` shape** (memo §2.2).  Fill: GL-C. -/
theorem span_base_r0 : zLayer (freeProTwo : Type) 3 ≤ SpanTargetR0 3 := by
  sorry

/-- The span base case, `r₂` shape.  Fill: GL-C. -/
theorem span_base_r2 : zLayer (freeProTwo : Type) 3 ≤ SpanTargetR2 3 := by
  sorry

end GQ2.Roe.Labute
