/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.Labute.GradedLie.SpanStep
import GQ2.Roe.Labute.GradedLie.SpanBase

/-!
# GL-E: span assembly

The strong induction composing GL-C (base, k = 3) with GL-B (step).  **Complete as
written** (the GL0 composability certificate, L1's `stageStep` pattern) — it inherits
the upstream sorries and self-heals as GL-B/GL-C land.  `StageLemma.lean`'s frozen
`span_free_r0/r2` are filled by these theorems definitionally (`SpanTargetR0/R2` are
the verbatim statement bodies).
-/

namespace GQ2.Roe.Labute

/-- The span theorem, `r₀` shape, in span-target form (= `span_free_r0` verbatim). -/
theorem span_free_r0_proof (k : ℕ) (hk : 3 ≤ k) :
    zLayer (freeProTwo : Type) k ≤ SpanTargetR0 k := by
  induction k, hk using Nat.le_induction with
  | base => exact span_base_r0
  | succ n hn ih => exact span_step_r0 n hn ih

/-- The span theorem, `r₂` shape, in span-target form (= `span_free_r2` verbatim). -/
theorem span_free_r2_proof (k : ℕ) (hk : 3 ≤ k) :
    zLayer (freeProTwo : Type) k ≤ SpanTargetR2 k := by
  induction k, hk using Nat.le_induction with
  | base => exact span_base_r2
  | succ n hn ih => exact span_step_r2 n hn ih

end GQ2.Roe.Labute
