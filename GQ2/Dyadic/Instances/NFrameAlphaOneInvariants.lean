/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.MarkedCore.NFrameAlphaOne
import GQ2.Dyadic.Instances.EvenAlphaOne

/-!
# W70-NFRAME4, second half: the `α = 1` `N`-row invariant package

`GQ2/Dyadic/MarkedCore/NFrameAlphaOne.lean` computes the `α = 1` `q`-invariant,
`demushkinQ (D_N 1 h) = 4`, using nothing outside `MarkedCore/`.  This file composes it with the
two components that live under `Instances/` and therefore cannot be cited from there:
`EvenAlphaOne.evenAlphaOne_isDemushkin_DN` (wave 70) and `EvenModel.demushkinRank_DN` (EV-1b).

## Why this is a separate file

The composites below are the only part of the `ℤ/4` frame work that needs anything from
`Instances/`.  Keeping them here lets the frame half sit in `MarkedCore/` with `MarkedCore/`-only
imports, so no `MarkedCore/ -> Instances/` edge is created.  That edge would have been the first
of its kind in the tree, and the owner decision of 2026-08-12 (owner memo, decisions block, item
5) refused the same shape on the `SqCore`/`Count` boundary, choosing exact layering over the
convenience of one import.  This split applies that precedent.

## Names are unchanged by the split

Both theorems keep the namespace `GQ2.Dyadic.MarkedCore` they were introduced with, so their full
names are exactly what they were before the split and no consumer would have to move.  File path
and namespace are already decoupled elsewhere under `Instances/` (`EvenAlphaOne.lean` declares
into `GQ2.Dyadic.EvenAlphaOne`, not into an `Instances` namespace), so this is the existing
convention rather than an exception to it.

## The coefficient action

`DistribMulAction (D_N α h) (ZMod 2)` is a `local instance` in every file on the even route, so it
does not travel with the import and has to be restated for `IsDemushkin 2 (DN 1 h)` to elaborate
at all.  It is restated here, and only here: the frame half never mentions `IsDemushkin`.

## Variance (MC-VAR discipline)

The frame half is abelianization-layer only.  This file adds `IsDemushkin` and `demushkinRank`,
which are `H¹`/`H²` statements, but it consumes both as black-box conjuncts and unfolds neither,
so no cup form, Gram matrix or bilinear pairing is manipulated here either and the `M`/`N`
row-vs-column dictionary (`GQ2/Dyadic/MarkedCore/Variance.lean`) is still not invoked.

## Axiom scope (measured)

Both declarations print the **std-3** set `[propext, Classical.choice, Quot.sound]`; see §2.  The
package therefore costs nothing beyond what its three inputs already cost.
-/

open Multiplicative

namespace GQ2

open SectionThree

namespace Dyadic

namespace MarkedCore

open scoped GQ2.SectionThree.TopAbInstances

/-! ## §1 The invariant package

`coreRank h` is `4 + 2h` by definition, so the package reads `(rank, q) = (4 + 2h, 4)`.

The `q`-value agrees with an independently computed one from the `H²` layer.
`EvenAlphaOne.lean` §3 proves `evenAlphaOneNCupForm_self`, that the `α = 1` `N` cup form is
alternating, where the committed `α ≥ 2` form has `evenCupForm v v = v 0` and is not; the frame
half computes `q = 4` at `α = 1` where `nFrameExists_demushkinQ_DN` gives `q = 2` at `α ≥ 2`.  The
two layers therefore split at the same place and in the same direction.  The agreement is evidence
and not a proof of either statement from the other: the implication relating an alternating cup
form to `q ≠ 2` is Demushkin-theoretic and is not formalized in this tree, so neither computation
is derived from the other here. -/

/-- The coefficient action at the `N` core, as everywhere on this route. -/
noncomputable local instance nFourScalarDN (α h : ℕ) :
    DistribMulAction (DN α h : Type) (ZMod 2) :=
  scalarActionZmodTwo _

/-- Continuity of the `N`-core coefficient action. -/
local instance nFourContinuousDN (α h : ℕ) : ContinuousSMul (DN α h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **The `α = 1` `N`-row invariant package**: the core is Demushkin, of rank `4 + 2h`, with
`q = 4`, at every handle count.  The three conjuncts come from three independent places (the
cup-form computation of `EvenAlphaOne.lean`, the `H¹`-count of `EvenModel.lean`, and the frame
half's `nFrame4_demushkinQ_DN_one`), and only the third is proved in this lane. -/
theorem nFrame4_invariants_DN_one (h : ℕ) :
    IsDemushkin 2 (DN 1 h : Type) ∧ demushkinRank 2 (DN 1 h : Type) = 4 + 2 * h ∧
      demushkinQ (DN 1 h : Type) = 4 :=
  ⟨GQ2.Dyadic.EvenAlphaOne.evenAlphaOne_isDemushkin_DN h,
    GQ2.Dyadic.EvenModel.demushkinRank_DN 1 h le_rfl,
    nFrame4_demushkinQ_DN_one h⟩

/-- **The surviving point's invariants.**  The strengthening of
`EvenAlphaOne.evenAlphaOne_survivingPoint_isDemushkin` by the `q`-value: at the unique point where
an `N`-row image is a principal-unit group, the core over it is Demushkin, of rank `4 + 2h`, and
has `q = 4`.

Stated as a conjunction so the range identity is not separated from the invariants it is being
matched against.  It asserts an agreement of invariants at that point and nothing else; in
particular it makes no claim that any `DN 1 h` is the maximal pro-2 quotient of a Galois group,
which is not proved anywhere in the tree. -/
theorem nFrame4_survivingPoint_invariants (h : ℕ) :
    imChiN 1 = GQ2.Dyadic.EvenCyclotomicRange.evenRangePrin 2 ∧
      IsDemushkin 2 (DN 1 h : Type) ∧ demushkinRank 2 (DN 1 h : Type) = 4 + 2 * h ∧
        demushkinQ (DN 1 h : Type) = 4 :=
  ⟨GQ2.Dyadic.EvenUnram.evenUnram_imChiN_one_eq_prin_two,
    (nFrame4_invariants_DN_one h).1, (nFrame4_invariants_DN_one h).2.1,
    (nFrame4_invariants_DN_one h).2.2⟩

/-! ## §2 Axiom pins

The measured scope is the **std-3** set `[propext, Classical.choice, Quot.sound]`, matching the
frame half and the three cited inputs.  No census axiom appears. -/

section AxiomPins

#print axioms nFrame4_invariants_DN_one
#print axioms nFrame4_survivingPoint_invariants

end AxiomPins

end MarkedCore

end Dyadic

end GQ2
