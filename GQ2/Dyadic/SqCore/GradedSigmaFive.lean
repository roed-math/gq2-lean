/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedSigmaFour

/-!
# W58-SIGMA5: why class four is blind to `a0 = a1`, sharply

`GradedSigmaFour` section 7 measured its own residual: on the class-two-forced gauge the depth
sweep's forced sigma dressing `a0 = a1` (the dressing `v` equal to the `x0`-slot value `x`) is
read **evenly**, so class four identifies it with the trivial dressing, and

> The sweep's `a0 = a1` forcing is therefore still not a class-four slice statement: it needs
> class five (where the reading acquires channels the class-two gauge does not control) or the
> universal quotient.

The W58-SIGMA5 reconnaissance (`scripts/w58_sigma5/`, certified outputs in
`scripts/w58_sigma5/results/`, note `docs/dyadic/w58-sigma5-note.md`) built the class-five
reading on `U_6` and found that the escape is real, but that the reason class four fails is
**not** the gauge.  This file records the class-four half of that finding, which stands on the
committed carrier alone and needs nothing from the class-five one.

## Headline: at class four the diagonal is even at every marking, not merely on the gauge

⭐⭐ `sigFourRead_diag_even`.  If the `x1`-slot's three abelian columns are even then
`sigFourRead x x y` is even, with **no hypothesis whatsoever on the `x0`-slot**.  The committed
`sigFourRead_gauge_sigma_eq_x0` carries eight evenness hypotheses; three suffice, and the three
that suffice are exactly the ones the relator's own abelian rows supply
(⭐ `abelRow_even`: over `gr3R = ZMod 8`, `-4 * a + 2 * b = 0` forces `b` even, and
`(sqRelWord m).a = -4 * (m 1).a + 2 * (m 2).a` at every marking).  So class four is blind to
`a0 = a1` at **every relator-killing marking**, at every handle count, on every row, gauge or no
gauge: there is no class-four channel to open.

That is what the class-five reading changes.  Measured in `scripts/w58_sigma5/`: at class five
the same response is the functional

```text
x_{12} * y_{24} * y_{46}  +  x_{56} * y_{13} * y_{35}     (mod 2)
```

at every relator-killing marking, which is **not** identically zero.  Its second channel runs on
the `x0`-slot's fifth abelian column `x_{56}`, a matrix entry `U_5` does not have, so no
class-four hypothesis constrains it; the class-five note exhibits a marking satisfying the whole
class-two-forced gauge at which all fourteen lower rows of the dressed relator vanish and the
class-five residue is the odd `7`.

## The companion diagonals, and the class-three obstruction

The three lower class-four readings are also recorded on the diagonal, because they are what
decides whether such a dressing is a stage-three survivor at all:

```text
sigFourG x x = 0                    the third class-two row never moves
sigFourH x x = -(2 * (x.a * x.c))   the left class-three row moves EVENLY, always
sigFourI x x = x.c * x.d            the right class-three row can move ODDLY
```

⭐ `sigFourI_diag` is the sharp one: the `a0 = a1` dressing disturbs the class-three row `x_{25}`
by exactly `x.c * x.d`, so a marking with both of those columns odd is excluded before the top
row is ever read.  That is one of the two constraints the class-five census has to route around,
and it is why the separating point it exhibits carries a **live** handle block (the other being
the class-four row `x_{15}`, which a dead block leaves nothing to cancel against).

## Scope

Everything here is an identity or an evenness statement about `SqU5` marking tuples over an
arbitrary commutative ring, plus one `decide` on `ZMod 8`.  Nothing about class five is claimed
in Lean: the class-five carrier is not built here, and the class-five statements above are
**measured**, not proved.  No `sorry`, no new axiom, no `native_decide`.
-/

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The diagonal of the three lower class-four readings -/

section Diagonals

variable {R : Type} [CommRing R] (x : SqU5 R)

/-- The third class-two row does not move at all under the diagonal dressing: `sigFourG` is an
alternating pairing of the `x0`-slot's outer abelian columns against the dressing's. -/
theorem sigFourG_diag : sigFourG x x = 0 := by
  simp only [sigFourG]; ring

/-- ⭐ **The left class-three row moves evenly under the diagonal dressing, at every marking.**
No gauge is used: the symmetric part of `sigFourH` is `-2 * (x.a * x.c)` on the nose.  This is
the diagonal shadow of the committed `sigFourH_gauge_even`. -/
theorem sigFourH_diag : sigFourH x x = -(2 * (x.a * x.c)) := by
  simp only [sigFourH]; ring

/-- ⭐ **The right class-three row can move oddly**: the diagonal dressing shifts the `x_{25}`
row by exactly the product of the `x0`-slot's two inner abelian columns.  A marking with both
odd is excluded at class three, before any class-four or class-five row is read. -/
theorem sigFourI_diag : sigFourI x x = x.c * x.d := by
  simp only [sigFourI]; ring

end Diagonals

/-! ## 2 The class-four reading on the diagonal -/

section DiagRead

variable {R : Type} [CommRing R] {x y : SqU5 R}

/-- ⭐⭐ **The class-four reading is even on the diagonal at every marking whose `x1`-slot has
even abelian columns.**  The committed `sigFourRead_gauge_sigma_eq_x0` assumes five evennesses
on the `x0`-slot and three on the `x1`-slot; the three on the `x1`-slot alone suffice, and those
three are exactly what the relator's abelian rows give (`abelRow_even`).  So the sweep's
`a0 = a1` forcing has **no** class-four channel to open, on the gauge or off it. -/
theorem sigFourRead_diag_even {ya yc yd : R}
    (hya : y.a = 2 * ya) (hyc : y.c = 2 * yc) (hyd : y.d = 2 * yd) :
    ∃ k : R, sigFourRead x x y = 2 * k := by
  refine ⟨-(x.a * x.g) - 2 * (ya * yc * x.d) - 2 * (ya * yd * x.c) - 4 * (ya * yd * x.f)
      + ya * x.d * y.f - 2 * (yc * yd * x.a) + 2 * (yc * yd * x.e) + yc * x.d * y.e
      - 4 * (yd * x.a * x.c) + yd * x.a * y.f - 2 * (yd * x.c * y.e)
      + 3 * (x.a * x.c * x.d), ?_⟩
  simp only [sigFourRead, hya, hyc, hyd]
  ring

/-- The committed statement is the special case, so nothing is lost: the eight-hypothesis form
follows from the three-hypothesis one. -/
theorem sigFourRead_gauge_sigma_eq_x0_of_diag {xa xc xd xe xf ya yc yd : R}
    (_hxa : x.a = 2 * xa) (_hxc : x.c = 2 * xc) (_hxd : x.d = 2 * xd) (_hxe : x.e = 2 * xe)
    (_hxf : x.f = 2 * xf) (hya : y.a = 2 * ya) (hyc : y.c = 2 * yc) (hyd : y.d = 2 * yd) :
    ∃ k : R, sigFourRead x x y = 2 * k :=
  sigFourRead_diag_even hya hyc hyd

end DiagRead

/-! ## 3 The three hypotheses come from the relator's own abelian rows -/

section AbelRow

/-- ⭐ **The abelian rows force the `x1`-slot's columns even.**  Over `gr3R = ZMod 8` the
vanishing of an abelian row `-4 * a + 2 * b = 0` forces `b` to be even, whatever `a` is.  Each
abelian row of `sqRelWord` has exactly this shape (the handle word contributes nothing to an
abelian row), so at any relator-killing marking the three hypotheses of
`sigFourRead_diag_even` hold. -/
theorem abelRow_even (a b : gr3R) (h : -(4 * a) + 2 * b = 0) : ∃ c : gr3R, b = 2 * c := by
  revert h
  revert a b
  decide

/-- ⭐⭐ **Class four is blind to `a0 = a1` at every relator-killing marking.**  Only the three
abelian rows of the relator are used; there is no gauge hypothesis, no handle-count hypothesis
and no hypothesis on the `x0`-slot at all. -/
theorem sigFourRead_diag_even_of_abelRows {x y : SqU5 gr3R}
    (ha : -(4 * x.a) + 2 * y.a = 0) (hc : -(4 * x.c) + 2 * y.c = 0)
    (hd : -(4 * x.d) + 2 * y.d = 0) :
    ∃ k : gr3R, sigFourRead x x y = 2 * k := by
  obtain ⟨ya, hya⟩ := abelRow_even _ _ ha
  obtain ⟨yc, hyc⟩ := abelRow_even _ _ hc
  obtain ⟨yd, hyd⟩ := abelRow_even _ _ hd
  exact sigFourRead_diag_even hya hyc hyd

/-- The same conclusion as a parity: the class-four selection bit does not move when the sigma
slot is dressed by the `x0`-slot value. -/
theorem selPar_sigFourRead_diag {x y : SqU5 gr3R}
    (ha : -(4 * x.a) + 2 * y.a = 0) (hc : -(4 * x.c) + 2 * y.c = 0)
    (hd : -(4 * x.d) + 2 * y.d = 0) :
    selPar (sigFourRead x x y) = 0 := by
  obtain ⟨k, hk⟩ := sigFourRead_diag_even_of_abelRows ha hc hd
  rw [hk, selPar_two_mul]

end AbelRow

/-! ## 4 Axiom pins

Committed prints for every public declaration: all **std-3** (`propext`, `Classical.choice`,
`Quot.sound`) or a subset; no census axiom is reachable.  The single `decide` is on `ZMod 8`. -/

section AxiomPins

#print axioms sigFourG_diag
#print axioms sigFourH_diag
#print axioms sigFourI_diag
#print axioms sigFourRead_diag_even
#print axioms sigFourRead_gauge_sigma_eq_x0_of_diag
#print axioms abelRow_even
#print axioms sigFourRead_diag_even_of_abelRows
#print axioms selPar_sigFourRead_diag

end AxiomPins

end SqCore

end Dyadic

end GQ2
