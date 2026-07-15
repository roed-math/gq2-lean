/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/

module

public import GQ2.RamifiedPack.Basic
public import GQ2.RamifiedPack.Descent

@[expose] public section

/-!
# The ramified isotypic pack (the étale route)

Blueprint: `docs/orchestration/p16d6e4aA-pack-design.md`.  Target: the pack fields of
`SectionSix.prop_6_9_ramified`, discharging `zeroCount_qDouble_ramified_of_faithful`
(consumed by the `Γ_A` Gauss calculation in `GQ2/GaussZ/FinalGammaA.lean`).

This file builds the generic layer, bottom-up:

* §TwoPowerConj — **every conjugate of `t` is `t^{2^j}`** (the refinement of
  `tau_fixed_eq_zero_of_gen`'s conjugation calculus): the `S`-twist is squaring (the
  tame relation), its inverse is the square ROOT `t^{2^{φ(d)−1}}` (Euler — no
  multiplicative-order machinery), and the exponents compose multiplicatively.  This
  is what makes every `𝔽₂`-isotypic component `C`-stable
  (`P(t^{2^j}) = P(t)^{2^j}`, the char-2 polynomial Frobenius — design doc §3).

**File organisation.**  The implementation is split into `Basic` (the conjugation and adjoin-root foundations) and `Descent` (the pack interface, self-reciprocity, and fixed-point count).  This umbrella preserves the original import path and public declaration names.

-/
