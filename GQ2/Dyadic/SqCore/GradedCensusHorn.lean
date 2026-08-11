/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedGammaTwoCensus

/-!
# W65-HORN1: horn 1 of the census criterion, CLOSED, and the form it was recorded in CORRECTED

`GradedGammaTwoCensus` (W64-CENSUS5) proved the census CRITERION and left both its horns
measured.  Horn 1 is the parity horn: a binder point's sigma-knob GEARING is the `x0` slot's
fifth abelian column `x0.e`, and the census needs to know that an EVEN gearing cannot occur, so
that the dichotomy collapses onto achievability alone.  W64 recorded the missing ingredient as

> the `(1,6)`-row of `sqWord (s * x) x y * (sqWord s x y)⁻¹` is `x0.e * x1.f * x1.h` mod `2`
> under `stageN1` plus the relator's own `x1` columns.

This file proves that row in closed form and closes horn 1.  ⚠ It also refutes the sentence
above as written, by a machine-checked counterexample, and reports what the repair costs.

## ⭐⭐⭐ Headline 1: the row, and it does NOT have the recorded shape

⭐⭐⭐ `SqU6.censHorn_row_o`.  Over **any** commutative ring, with the sigma letter's `(1,2)`,
`(3,4)` and `(5,6)` columns even, the `x0` letter on `stageN1`, and the `x1` letter's five
abelian columns even,

```text
   (sqWord (s * x) x y * (sqWord s x y)⁻¹).o
     = x.e * (y.f * y.h + s.f * x.h + s.j * x.d)  +  2 * censHornWit ...
```

with `censHornWit` an explicit `207`-monomial witness.  ⭐ The right factor is NOT `y.f * y.h`:
two further monomials `s.f * x.h` and `s.j * x.d`, both reading the SIGMA slot, sit inside it.
They vanish at `fiveSigMark` and at `liveBlkSig`, which is why every measurement in the tree saw
the recorded two-letter form and nothing else.

⭐⭐ What survives, and is the whole point, is that **every** term carries the factor `x.e`.  So
the row is a multiple of the gearing whatever the sigma letter does inside the gauge, and horn 1
does not depend on identifying the cofactor at all.

## ⭐⭐⭐ Headline 2: horn 1, closed

⭐⭐⭐ `censHorn_gear_odd`.  At a marking of the one-handle-live family whose sigma letter is on
the gauge, whose `x0` letter is on `stageN1`, whose UNDRESSED frame kills the relator, and whose
DIAGONALLY dressed frame has an ODD central relator, the gearing `X.e` is **ODD**.  So
`cens_sigKnob_dichotomy`'s first horn is empty and the criterion collapses.

⚠ The undressed frame killing is not decoration: it is what forces the `x1` letter's five
abelian columns to be even (`censHorn_x1_cols_even`, from the relator's own abelian rows), which
is the hypothesis W64 named "the relator's own `x1` columns".  ⚠ The object is the DIAGONALLY
dressed frame throughout; the bare frame kills outright and sweeping it would be vacuous.

## ⭐⭐⭐ Headline 3: the census verdict, with only achievability left

⭐⭐⭐ `censHorn_verdict`.  At every such binder point, if the `gamma_2` forcing HOLDS then the
solving knob is UNACHIEVABLE:

```text
   GaTwoForces (diagonal frame)  ->  exists t, selPar t = 1 /\ c + X.e * t = 0
                                       /\ censKnob t ∉ forceLcs (image) 1.
```

This is W64's `cens_sigKnob_dichotomy` with the left disjunct deleted.  ⭐ Equivalently
`censHorn_lines_false_of_ach`: at such a point, achievability of the knob alone refutes all
three `gamma_2` lines, with no parity side condition to check.  The `67`-point census verdict
therefore stops being a two-horned measurement and becomes a theorem with ONE measured input,
achievability, exactly as the ticket asked.

## ⚠⚠⚠ Headline 4: the recorded row form is FALSE, and here is the counterexample

⚠⚠⚠ `censHorn_recorded_false`.  Take `s = <e = 1>`, `x = <d = 1, j = 1>`, `y = 1`.  All three
letters lie on `stageN1`; the `x1` letter's five abelian columns are `0`, hence even; and yet

```text
   sqWord (s * x) x y * (sqWord s x y)⁻¹  =  liftO 1,
```

a CENTRAL residue with an ODD `(1,6)` row, while the recorded form `x.e * y.f * y.h` is `0`
because `x.e` is `0`.  ⭐ `censHorn_recorded_false'` is a second, disjoint witness
`x = <f = 1, h = 1>`.  The two are the minimal supports: a search over every one-column sigma and
every two-column `x0` inside the relevant range found exactly these two, and **none at all** once
the sigma letter's fifth abelian column is required even.

⚠ **What the correction costs.**  The missing hypothesis is `2 ∣ s.e`, on the SIGMA letter, and
it is invisible to `stageN1` (which constrains only the `(1,2)` and `(3,4)` columns).  ⭐ It
costs the census verdict **nothing**: `censHorn_marks_gauged` checks that `fiveSigMark` and
`liveBlkSig`, the only sigma letters any binder point in the tree uses, both lie on the gauge, so
`censHorn_stageWit_gear_odd` and `censHorn_liveBlkWit_gear_odd` deliver horn 1 at W63-CENTRAL2's
family and at W63-LIVE5's point unconditionally.  ⚠ It is NOT a proof artefact: with an ungauged
sigma, central residues with an odd `(1,6)` row and an EVEN gearing exist in quantity
(`scripts/w65_horn1/results/`, `833` in `400000` samples), so no proof can drop it.

⚠ This is the same failure mode `GradedFiveSepZero` flagged for wave 58's two-term form, one
level up: a form measured at the committed sigma slot `E_23` was recorded as if it held at a
general slot.  Wave 58's form is `x0.a * x1.g * x1.i + x0.e * x1.f * x1.h`; on `stageN1` its
first term is even, so at `E_23` it agrees with the recorded row, and the agreement is a
coincidence of the slot, not an identity.

## PROVED versus MEASURED

**PROVED** here, with no `sorry`, no new axiom, no `native_decide`: the row identity over any
commutative ring; that the relator's abelian rows force the `x1` columns; that the diagonal
frame's relator IS the residue when the bare frame kills; horn 1; the verdict; and both
counterexamples (`decide` on `ZMod 8`).

**MEASURED** (`scripts/w65_horn1/results/`): that the gauge cannot be dropped, by sampling; and
the shape of the correction at a general slot (`17` odd monomials under `stageN1` alone, `8`
under the tree's committed `x0` gauge, `0` under the gauge used here).

**NOT proved, and not claimed**: achievability, which remains exactly as measured in W64;
that the family's other two knobs have odd gearings (this file speaks only of the sigma knob);
and any hom-level lift.  ⚠ Whether an ungauged sigma admits a FULL binder point, with the
handle block realised, is recorded as measured-only: the `833` witnesses satisfy centrality and
oddness but their bare frames were not solved for a handle block.

## Contents

* **1** the gauge, the witness and ⭐⭐⭐ the row identity;
* **2** the relator's own `x1` columns, and the residue;
* **3** ⭐⭐⭐ horn 1; **4** ⭐⭐⭐ the verdict; **5** ⚠⚠⚠ the counterexample;
* **6** the committed points; **7** axiom pins.
-/

open scoped commutatorElement

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The gauge, the witness, and the row -/

section Row

variable {R : Type} [CommRing R]

/-- ⭐ **The explicit even witness of the `(1,6)` row**, `207` monomials, machine emitted from
`scripts/w65_horn1/` and checked by `ring` in `SqU6.censHorn_row_o`.  The even columns enter
through their halves `sa, sc, se, xa, xc, ya, yb, yc, yd, ye`, so the witness is a polynomial
identity over any commutative ring and no divisibility survives into the statement. -/
def censHornWit (s x y : SqU6 R) (sa sc se xa xc ya yb yc yd ye : R) : R :=
    - 2 * s.b * x.l * xa
    - s.d * x.e * x.j
    + s.f * x.i * xc
    - 2 * s.g * x.i * xa
    - s.h * x.e * x.f
    + s.i * x.f * xc
    + s.i * x.g * xa
    - 2 * s.k * x.e * xa
    + s.l * x.b * xa
    + sa * x.b * x.l
    + sa * x.e * x.k
    + sa * x.g * x.i
    - 2 * sc * x.f * x.i
    + se * x.d * x.j
    + se * x.f * x.h
    + 2 * se * x.k * xa
    - 2 * x.b * y.l * ya
    - 2 * x.d * y.j * ye
    + x.e * y.j * yd
    + x.e * y.k * ya
    + x.f * y.h * ye
    + x.f * y.i * yc
    - 2 * x.g * y.i * ya
    - 2 * x.h * y.f * ye
    + x.i * y.f * yc
    + x.i * y.g * ya
    + 2 * x.j * yd * ye
    - 4 * x.k * ya * ye
    + 2 * x.l * ya * yb
    + xa * y.g * y.i
    + 2 * xa * y.k * ye
    + 2 * xa * y.l * yb
    - 2 * xc * y.f * y.i
    + s.b * s.h * x.e * xa
    - 2 * s.b * s.i * xa * xc
    - s.b * sa * x.e * x.h
    - 2 * s.b * sa * x.i * xc
    + 2 * s.b * sc * x.i * xa
    - 2 * s.b * se * x.h * xa
    - 2 * s.b * x.e * x.h * xa
    - s.b * x.e * y.h * ya
    - 2 * s.b * x.h * ya * ye
    - 4 * s.b * x.i * xa * xc
    - 2 * s.b * x.i * ya * yc
    - 2 * s.b * xa * y.h * ye
    - 2 * s.b * xa * y.i * yc
    - 2 * s.b * xc * y.i * ya
    + s.d * s.f * x.e * xc
    + s.d * s.g * x.e * xa
    + s.d * sa * x.e * x.g
    + s.d * sc * x.e * x.f
    + 4 * s.d * x.e * x.f * xc
    + 4 * s.d * x.e * x.g * xa
    + s.d * x.e * y.f * yc
    + s.d * x.e * y.g * ya
    + 2 * s.d * x.f * yc * ye
    + 2 * s.d * x.g * ya * ye
    + 2 * s.d * xa * y.g * ye
    + 2 * s.d * xc * y.f * ye
    - s.f * sc * x.d * x.e
    + 2 * s.f * x.d * yc * ye
    - s.g * sa * x.d * x.e
    - 2 * s.g * se * x.d * xa
    - 2 * s.g * x.d * x.e * xa
    - 2 * s.g * x.d * ya * ye
    - 2 * s.g * x.e * ya * yd
    - 4 * s.g * xa * yd * ye
    + s.h * sa * x.b * x.e
    + 4 * s.h * x.b * x.e * xa
    + 2 * s.h * x.b * ya * ye
    + 2 * s.h * x.e * ya * yb
    + 4 * s.h * xa * yb * ye
    - 4 * s.i * x.b * xa * xc
    - 2 * s.i * x.b * ya * yc
    + 2 * sa * sc * x.b * x.i
    + 2 * sa * x.d * y.g * ye
    + 4 * sa * x.h * yb * ye
    + 4 * sa * xc * y.i * yb
    - 2 * sc * se * x.d * x.f
    + 8 * sc * x.b * x.i * xa
    + 2 * sc * x.b * y.i * ya
    - 2 * sc * x.d * x.e * x.f
    - 2 * sc * x.d * y.f * ye
    - 2 * sc * x.e * y.f * yd
    - 4 * sc * x.f * yd * ye
    + 4 * sc * x.i * ya * yb
    + 4 * sc * xa * y.i * yb
    - 4 * se * x.b * x.h * xa
    - 2 * se * x.b * y.h * ya
    - 4 * se * x.d * x.f * xc
    - 4 * se * x.d * x.g * xa
    - 4 * se * x.g * ya * yd
    - 4 * se * xc * y.f * yd
    - 9 * x.b * x.e * y.h * ya
    + 2 * x.b * x.h * ya * ye
    - 18 * x.b * x.i * ya * yc
    - 10 * x.b * xa * y.h * ye
    - 10 * x.b * xa * y.i * yc
    + 2 * x.b * xc * y.i * ya
    + 8 * x.b * y.h * ya * ye
    + 8 * x.b * y.i * ya * yc
    + 4 * x.d * x.e * y.f * yc
    + 4 * x.d * x.e * y.g * ya
    + 18 * x.d * x.f * yc * ye
    + 2 * x.d * x.g * ya * ye
    + 18 * x.d * xa * y.g * ye
    + 2 * x.d * xc * y.f * ye
    - 4 * x.d * y.f * yc * ye
    - 4 * x.d * y.g * ya * ye
    - 18 * x.e * x.g * ya * yd
    + 8 * x.e * x.h * ya * yb
    - 18 * x.e * xc * y.f * yd
    - 20 * x.f * xc * yd * ye
    - 8 * x.f * yc * yd * ye
    - 20 * x.g * xa * yd * ye
    + 16 * x.g * ya * yd * ye
    + 36 * x.h * xa * yb * ye
    - 8 * x.h * ya * yb * ye
    + 16 * x.i * xc * ya * yb
    + 36 * xa * xc * y.i * yb
    - 8 * xa * y.g * yd * ye
    - 8 * xa * y.h * yb * ye
    - 8 * xa * y.i * yb * yc
    + 16 * xc * y.f * yd * ye
    - 8 * xc * y.i * ya * yb
    - 2 * s.b * s.d * sa * x.e * xc
    - 2 * s.b * s.d * sc * x.e * xa
    - 2 * s.b * s.d * x.e * ya * yc
    - 4 * s.b * s.d * xa * yc * ye
    + 2 * s.b * sa * sc * x.d * x.e
    - 4 * s.b * sa * x.d * yc * ye
    + 4 * s.b * sc * se * x.d * xa
    + 2 * s.b * sc * x.d * x.e * xa
    + 4 * s.b * sc * x.e * ya * yd
    + 8 * s.b * sc * xa * yd * ye
    - 4 * s.b * se * x.d * xa * xc
    - 8 * s.b * x.d * x.e * ya * yc
    - 12 * s.b * x.d * xa * yc * ye
    + 16 * s.b * x.d * ya * yc * ye
    - 20 * s.b * x.e * xa * yc * yd
    - 16 * s.b * x.e * xc * ya * yd
    - 4 * s.b * x.e * ya * yc * yd
    - 8 * s.b * xa * xc * yd * ye
    + 16 * s.b * xa * yc * yd * ye
    + 8 * s.b * xc * ya * yd * ye
    - 4 * s.d * sa * x.b * x.e * xc
    - 4 * s.d * sc * x.b * x.e * xa
    - 4 * s.d * sc * x.b * ya * ye
    - 12 * s.d * x.b * x.e * xa * xc
    - 6 * s.d * x.b * x.e * ya * yc
    - 20 * s.d * x.b * xa * yc * ye
    - 4 * s.d * x.b * xc * ya * ye
    + 16 * s.d * x.b * ya * yc * ye
    - 20 * s.d * x.e * xa * yb * yc
    - 4 * s.d * x.e * xc * ya * yb
    - 32 * s.d * xa * xc * yb * ye
    - 16 * s.d * xa * yb * yc * ye
    + 2 * sa * sc * x.b * x.d * x.e
    + 8 * sa * sc * x.d * yb * ye
    + 4 * sa * se * x.b * x.d * xc
    - 8 * sa * x.b * x.d * yc * ye
    + 4 * sa * x.b * x.e * yc * yd
    + 8 * sa * x.b * xc * yd * ye
    - 16 * sa * x.d * yb * yc * ye
    + 32 * sa * x.e * xc * yb * yd
    + 8 * sa * x.e * yb * yc * yd
    - 16 * sa * xc * yb * yd * ye
    + 8 * sc * se * x.b * x.d * xa
    + 8 * sc * se * x.b * ya * yd
    + 6 * sc * x.b * x.d * x.e * xa
    + 20 * sc * x.b * x.e * ya * yd
    + 40 * sc * x.b * xa * yd * ye
    - 24 * sc * x.b * ya * yd * ye
    + 16 * sc * x.d * x.e * ya * yb
    + 40 * sc * x.d * xa * yb * ye
    - 16 * sc * x.d * ya * yb * ye
    + 64 * sc * x.e * xa * yb * yd
    - 16 * sc * xa * yb * yd * ye
    + 12 * se * x.b * x.d * xa * xc
    - 8 * se * x.b * x.d * ya * yc
    + 8 * se * x.b * xc * ya * yd
    - 8 * se * x.b * ya * yc * yd
    + 8 * se * x.d * xa * yb * yc
    + 8 * se * x.d * xc * ya * yb
    + 64 * se * xa * xc * yb * yd
    + 16 * se * xa * yb * yc * yd
    - 32 * x.b * x.d * x.e * ya * yc
    - 100 * x.b * x.d * xa * yc * ye
    - 4 * x.b * x.d * xc * ya * ye
    + 16 * x.b * x.d * ya * yc * ye
    - 40 * x.b * x.e * xa * yc * yd
    + 20 * x.b * x.e * xc * ya * yd
    + 60 * x.b * x.e * ya * yc * yd
    + 120 * x.b * xa * xc * yd * ye
    + 80 * x.b * xa * yc * yd * ye
    - 24 * x.b * xc * ya * yd * ye
    - 48 * x.b * ya * yc * yd * ye
    - 40 * x.d * x.e * xa * yb * yc
    + 24 * x.d * x.e * xc * ya * yb
    - 32 * x.d * xa * xc * yb * ye
    + 48 * x.d * xa * yb * yc * ye
    + 320 * x.e * xa * xc * yb * yd
    - 56 * x.e * xa * yb * yc * yd
    - 64 * x.e * xc * ya * yb * yd
    - 272 * xa * xc * yb * yd * ye
    + 48 * xa * yb * yc * yd * ye
    + 48 * xc * ya * yb * yd * ye

set_option maxHeartbeats 2000000 in
/-- ⭐⭐⭐ **THE `(1,6)` ROW OF THE DIAGONAL RESIDUE, IN CLOSED FORM.**  Over **any** commutative
ring, with the sigma letter's `(1,2)`, `(3,4)` and `(5,6)` columns even, the `x0` letter's
`(1,2)` and `(3,4)` columns even (`stageN1`) and the `x1` letter's five abelian columns even,

```text
   (sqWord (s * x) x y * (sqWord s x y)⁻¹).o
     = x.e * (y.f * y.h + s.f * x.h + s.j * x.d) + 2 * censHornWit ...
```

⚠ The cofactor is **not** `y.f * y.h`.  The two extra monomials read the sigma slot and vanish
only when `s.f` and `s.j` do, which is what happens at `fiveSigMark` and at `liveBlkSig`.

⭐ Every term is a multiple of the GEARING `x.e`, which is the only thing horn 1 needs, and the
identity is componentwise expansion with no transport, no achievability and no gauge beyond the
ten stated columns. -/
theorem SqU6.censHorn_row_o (s x y : SqU6 R) (sa sc se xa xc ya yb yc yd ye : R)
    (hsa : s.a = 2 * sa) (hsc : s.c = 2 * sc) (hse : s.e = 2 * se)
    (hxa : x.a = 2 * xa) (hxc : x.c = 2 * xc)
    (hya : y.a = 2 * ya) (hyb : y.b = 2 * yb) (hyc : y.c = 2 * yc)
    (hyd : y.d = 2 * yd) (hye : y.e = 2 * ye) :
    (sqWord (s * x) x y * (sqWord s x y)⁻¹).o
      = x.e * (y.f * y.h + s.f * x.h + s.j * x.d)
        + 2 * censHornWit s x y sa sc se xa xc ya yb yc yd ye := by
  simp only [censHornWit, sqWord, conjP, commP, pow_succ, pow_zero, one_mul,
    SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e, SqU6.mul_f, SqU6.mul_g,
    SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l, SqU6.mul_m, SqU6.mul_n,
    SqU6.mul_o, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e, SqU6.inv_f,
    SqU6.inv_g, SqU6.inv_h, SqU6.inv_i, SqU6.inv_j, SqU6.inv_k, SqU6.inv_l, SqU6.inv_m,
    SqU6.inv_n, SqU6.inv_o, hsa, hsc, hse, hxa, hxc, hya, hyb, hyc, hyd, hye]
  ring

/-- ⭐⭐ **The row is a multiple of the GEARING.**  The parity form of `censHorn_row_o`, with the
cofactor discarded: on the gauge, an EVEN `x.e` forces an EVEN `(1,6)` row, over any commutative
ring.  ⭐ This is the whole of horn 1, before any frame is mentioned. -/
theorem SqU6.censHorn_row_even {s x y : SqU6 R}
    (hsa : (2 : R) ∣ s.a) (hsc : (2 : R) ∣ s.c) (hse : (2 : R) ∣ s.e)
    (hxa : (2 : R) ∣ x.a) (hxc : (2 : R) ∣ x.c)
    (hya : (2 : R) ∣ y.a) (hyb : (2 : R) ∣ y.b) (hyc : (2 : R) ∣ y.c)
    (hyd : (2 : R) ∣ y.d) (hye : (2 : R) ∣ y.e) (hxe : (2 : R) ∣ x.e) :
    (2 : R) ∣ (sqWord (s * x) x y * (sqWord s x y)⁻¹).o := by
  obtain ⟨sa, hsa⟩ := hsa
  obtain ⟨sc, hsc⟩ := hsc
  obtain ⟨se, hse⟩ := hse
  obtain ⟨xa, hxa⟩ := hxa
  obtain ⟨xc, hxc⟩ := hxc
  obtain ⟨ya, hya⟩ := hya
  obtain ⟨yb, hyb⟩ := hyb
  obtain ⟨yc, hyc⟩ := hyc
  obtain ⟨yd, hyd⟩ := hyd
  obtain ⟨ye, hye⟩ := hye
  obtain ⟨xe, hxe⟩ := hxe
  refine ⟨xe * (y.f * y.h + s.f * x.h + s.j * x.d)
    + censHornWit s x y sa sc se xa xc ya yb yc yd ye, ?_⟩
  rw [SqU6.censHorn_row_o s x y sa sc se xa xc ya yb yc yd ye hsa hsc hse hxa hxc hya hyb hyc
    hyd hye, hxe]
  ring

end Row

/-! ## 2 The relator's own `x1` columns, and the residue -/

section Frame

variable {R : Type} [CommRing R] {h : ℕ} {j : Fin h}

/-- ⭐⭐ **The diagonally dressed frame's relator IS the residue**, once the UNDRESSED frame
kills.  The handle block cancels against itself, so the whole class-five question is the core
word's, with no handle letter in sight.  ⚠ This is the W64-VERIFY trap discharged: the object is
the DIAGONALLY dressed frame, and the bare frame killing is a hypothesis, not the conclusion. -/
theorem censHorn_diag_eq_resid {S X Y U V : SqU6 R}
    (hbare : sqRelWord (fiveTuple R h j S X Y U V) = 1) :
    sqRelWord (fiveTuple R h j (S * X) X Y U V) = sqWord (S * X) X Y * (sqWord S X Y)⁻¹ := by
  rw [sqRelWord_fiveTuple] at hbare ⊢
  rw [eq_inv_of_mul_eq_one_right hbare]

/-- **`-4 p + 2 q = 0` in `ZMod 8` forces `q` EVEN.**  The arithmetic under the `x1` columns:
`2 q = 4 p` puts `2 q` in `{0, 4}`, and every such `q` is even. -/
theorem censHorn_abelRow_even : ∀ p q : gr3R, -4 * p + 2 * q = 0 → ∃ k : gr3R, q = 2 * k := by
  decide

/-- ⭐⭐ **"The relator's own `x1` columns"**, made precise: if the frame kills the relator then
the `x1` letter's five abelian columns are all EVEN, at every handle count and every handle.
⭐ Nothing but the relator's own five abelian rows is used, and the handle block contributes `0`
to every one of them. -/
theorem censHorn_x1_cols_even {S X Y U V : SqU6 gr3R}
    (hbare : sqRelWord (fiveTuple gr3R h j S X Y U V) = 1) :
    (2 : gr3R) ∣ Y.a ∧ (2 : gr3R) ∣ Y.b ∧ (2 : gr3R) ∣ Y.c ∧ (2 : gr3R) ∣ Y.d
      ∧ (2 : gr3R) ∣ Y.e := by
  refine ⟨censHorn_abelRow_even X.a Y.a ?_, censHorn_abelRow_even X.b Y.b ?_,
    censHorn_abelRow_even X.c Y.c ?_, censHorn_abelRow_even X.d Y.d ?_,
    censHorn_abelRow_even X.e Y.e ?_⟩
  · have hrow := SqU6.sqRelWord_a (fiveTuple gr3R h j S X Y U V)
    rw [hbare, SqU6.one_a, fiveTuple_one, fiveTuple_two] at hrow
    exact hrow.symm
  · have hrow := SqU6.sqRelWord_b (fiveTuple gr3R h j S X Y U V)
    rw [hbare, SqU6.one_b, fiveTuple_one, fiveTuple_two] at hrow
    exact hrow.symm
  · have hrow := SqU6.sqRelWord_c (fiveTuple gr3R h j S X Y U V)
    rw [hbare, SqU6.one_c, fiveTuple_one, fiveTuple_two] at hrow
    exact hrow.symm
  · have hrow := SqU6.sqRelWord_d (fiveTuple gr3R h j S X Y U V)
    rw [hbare, SqU6.one_d, fiveTuple_one, fiveTuple_two] at hrow
    exact hrow.symm
  · have hrow := SqU6.sqRelWord_e (fiveTuple gr3R h j S X Y U V)
    rw [hbare, SqU6.one_e, fiveTuple_one, fiveTuple_two] at hrow
    exact hrow.symm

end Frame

/-! ## 3 ⭐⭐⭐ Horn 1, closed -/

section Horn

variable {h : ℕ} {j : Fin h} {S X Y U V : SqU6 gr3R} {c : gr3R}

/-- ⭐⭐⭐ **HORN 1 OF THE CENSUS CRITERION, CLOSED.**  At a marking of the one-handle-live
family whose sigma letter has EVEN `(1,2)`, `(3,4)` and `(5,6)` columns, whose `x0` letter is on
`stageN1`, whose UNDRESSED frame kills the relator and whose DIAGONALLY dressed frame has an ODD
CENTRAL relator, the sigma knob's gearing `X.e` is **ODD**.

⭐ So `cens_sigKnob_dichotomy`'s first horn `selPar X.e = 0` is empty, and W64's criterion
collapses onto achievability.  ⚠ The `(5,6)`-column hypothesis on the SIGMA letter cannot be
dropped: `censHorn_recorded_false` is a counterexample with every other hypothesis in force. -/
theorem censHorn_gear_odd
    (hsa : (2 : gr3R) ∣ S.a) (hsc : (2 : gr3R) ∣ S.c) (hse : (2 : gr3R) ∣ S.e)
    (hxa : (2 : gr3R) ∣ X.a) (hxc : (2 : gr3R) ∣ X.c)
    (hbare : sqRelWord (fiveTuple gr3R h j S X Y U V) = 1)
    (hres : sqRelWord (fiveTuple gr3R h j (S * X) X Y U V) = SqU6.liftO c)
    (hodd : selPar c = 1) :
    selPar X.e = 1 := by
  by_contra hne
  obtain ⟨hya, hyb, hyc, hyd, hye⟩ := censHorn_x1_cols_even hbare
  have h0 : selPar X.e = 0 := by
    revert hne
    generalize selPar X.e = t
    revert t
    decide
  have hxe : (2 : gr3R) ∣ X.e := (selPar_eq_zero_iff X.e).mp h0
  have hco : (sqWord (S * X) X Y * (sqWord S X Y)⁻¹).o = c := by
    rw [← censHorn_diag_eq_resid hbare, hres, SqU6.liftO_o]
  have h2c : (2 : gr3R) ∣ c := by
    rw [← hco]
    exact SqU6.censHorn_row_even hsa hsc hse hxa hxc hya hyb hyc hyd hye hxe
  rw [(selPar_eq_zero_iff c).mpr h2c] at hodd
  exact absurd hodd (by decide)

/-- ⭐⭐ **The knob equation is solvable, with an ODD solution**, at every such binder point:
horn 1 makes the gearing a unit of `ZMod 8`, so `censKnob_solve` applies with no side condition
left to check. -/
theorem censHorn_knob_solvable
    (hsa : (2 : gr3R) ∣ S.a) (hsc : (2 : gr3R) ∣ S.c) (hse : (2 : gr3R) ∣ S.e)
    (hxa : (2 : gr3R) ∣ X.a) (hxc : (2 : gr3R) ∣ X.c)
    (hbare : sqRelWord (fiveTuple gr3R h j S X Y U V) = 1)
    (hres : sqRelWord (fiveTuple gr3R h j (S * X) X Y U V) = SqU6.liftO c)
    (hodd : selPar c = 1) :
    ∃ t : gr3R, selPar t = 1 ∧ c + X.e * t = 0 := by
  obtain ⟨t, ht, htpar, -⟩ :=
    censKnob_solve c X.e (censHorn_gear_odd hsa hsc hse hxa hxc hbare hres hodd)
  exact ⟨t, by rw [htpar, hodd], ht⟩

end Horn

/-! ## 4 ⭐⭐⭐ The census verdict, with only achievability left -/

section Verdict

variable {h : ℕ} {j : Fin h} {S X Y U V : SqU6 gr3R} {c : gr3R}

/-- ⭐⭐⭐ **THE CENSUS VERDICT.**  `cens_sigKnob_dichotomy` with its FIRST HORN DELETED: at a
gauged binder point of the one-handle-live family, if the `gamma_2` forcing holds then the
achievable lattice **misses** the knob that solves the sigma-slot equation, and that knob's
parameter is odd.

⭐ This is what the ticket asked for: the `67`-point census stops being a two-horned measurement
and becomes a theorem whose only remaining input is ACHIEVABILITY. -/
theorem censHorn_verdict
    (hsa : (2 : gr3R) ∣ S.a) (hsc : (2 : gr3R) ∣ S.c) (hse : (2 : gr3R) ∣ S.e)
    (hxa : (2 : gr3R) ∣ X.a) (hxc : (2 : gr3R) ∣ X.c)
    (hbare : sqRelWord (fiveTuple gr3R h j S X Y U V) = 1)
    (hres : sqRelWord (fiveTuple gr3R h j (S * X) X Y U V) = SqU6.liftO c)
    (hodd : selPar c = 1)
    (hF : GaTwoForces (fiveTuple gr3R h j (S * X) X Y U V)) :
    ∃ t : gr3R, selPar t = 1 ∧ c + X.e * t = 0 ∧ SqU6.censKnob t
      ∉ forceLcs (Subgroup.closure (Set.range (fiveTuple gr3R h j (S * X) X Y U V))) 1 := by
  rcases cens_sigKnob_dichotomy hres hodd hF with hgear | hknob
  · rw [censHorn_gear_odd hsa hsc hse hxa hxc hbare hres hodd] at hgear
    exact absurd hgear (by decide)
  · exact hknob

/-- ⭐⭐⭐ **Achievability is the ONLY remaining input.**  The contrapositive shape: if the
lattice achieves the knob solving the sigma equation, then all three `gamma_2` lines fail at the
point, with no parity hypothesis anywhere.  ⚠ Whether the lattice does achieve it is a property
of the point, measured in `scripts/w64_census5/`, and nothing here proves it. -/
theorem censHorn_lines_false_of_ach
    (hsa : (2 : gr3R) ∣ S.a) (hsc : (2 : gr3R) ∣ S.c) (hse : (2 : gr3R) ∣ S.e)
    (hxa : (2 : gr3R) ∣ X.a) (hxc : (2 : gr3R) ∣ X.c)
    (hbare : sqRelWord (fiveTuple gr3R h j S X Y U V) = 1)
    (hres : sqRelWord (fiveTuple gr3R h j (S * X) X Y U V) = SqU6.liftO c)
    (hodd : selPar c = 1)
    (hach : ∀ t : gr3R, c + X.e * t = 0 → SqU6.censKnob t
      ∈ forceLcs (Subgroup.closure (Set.range (fiveTuple gr3R h j (S * X) X Y U V))) 1) :
    ¬ GaTwoForces (fiveTuple gr3R h j (S * X) X Y U V)
      ∧ ¬ GaTwoCentral (fiveTuple gr3R h j (S * X) X Y U V)
      ∧ ¬ GaTwoOrth (fiveTuple gr3R h j (S * X) X Y U V) := by
  obtain ⟨t, -, ht⟩ := censHorn_knob_solvable hsa hsc hse hxa hxc hbare hres hodd
  exact cens_lines_false_of_sigKnob hres hodd ht (hach t ht)

end Verdict

/-! ## 5 ⚠⚠⚠ The recorded form is FALSE -/

section Cex

/-- The counterexample's sigma letter, `<e = 1>`.  It lies ON `stageN1`, whose two columns are
`0`, and its fifth abelian column is ODD, which is exactly the datum `stageN1` cannot see. -/
def censHornCexSig : SqU6 gr3R := ⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The counterexample's `x0` letter, `<d = 1, j = 1>`.  Its fifth abelian column, the sigma
knob's GEARING, is `0`: this is a would-be survivor of horn 1. -/
def censHornCexX : SqU6 gr3R := ⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩

/-- A second `x0` letter with disjoint support, `<f = 1, h = 1>`, giving an independent
counterexample on the other surviving monomial. -/
def censHornCexX' : SqU6 gr3R := ⟨0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩

/-- ⚠⚠⚠ **THE RECORDED ROW FORM IS FALSE.**  Every hypothesis W64 recorded holds at
`(censHornCexSig, censHornCexX, 1)`: all three letters lie on `stageN1`, and the `x1` letter's
five abelian columns are `0`, hence even.  The residue is `SqU6.liftO 1`, so it is CENTRAL with
an ODD `(1,6)` row, while the recorded value `x0.e * x1.f * x1.h` is `0`.

⚠ The one hypothesis that fails is the one this file adds: the sigma letter's `(5,6)` column is
`1`.  `stageN1` constrains only the `(1,2)` and `(3,4)` columns, so the recorded sentence has no
way to exclude this point. -/
theorem censHorn_recorded_false :
    (censHornCexSig ∈ stageN1 ∧ censHornCexX ∈ stageN1 ∧ (1 : SqU6 gr3R) ∈ stageN1)
      ∧ ((1 : SqU6 gr3R).a = 2 * 0 ∧ (1 : SqU6 gr3R).b = 2 * 0 ∧ (1 : SqU6 gr3R).c = 2 * 0
        ∧ (1 : SqU6 gr3R).d = 2 * 0 ∧ (1 : SqU6 gr3R).e = 2 * 0)
      ∧ sqWord (censHornCexSig * censHornCexX) censHornCexX 1
          * (sqWord censHornCexSig censHornCexX 1)⁻¹ = SqU6.liftO 1
      ∧ selPar (censHornCexX.e * (1 : SqU6 gr3R).f * (1 : SqU6 gr3R).h) = 0
      ∧ selPar censHornCexSig.e = 1 :=
  ⟨⟨⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩,
      ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩,
    ⟨by decide, by decide, by decide, by decide, by decide⟩, by decide, by decide, by decide⟩

/-- ⚠⚠ **The second witness**, on the other surviving monomial and with disjoint support: the
failure is not an accident of one letter. -/
theorem censHorn_recorded_false' :
    censHornCexX' ∈ stageN1
      ∧ sqWord (censHornCexSig * censHornCexX') censHornCexX' 1
          * (sqWord censHornCexSig censHornCexX' 1)⁻¹ = SqU6.liftO 1
      ∧ selPar (censHornCexX'.e * (1 : SqU6 gr3R).f * (1 : SqU6 gr3R).h) = 0 :=
  ⟨⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, by decide, by decide⟩

/-- ⭐ **The row theorem is not contradicted**: at both counterexamples the cofactor
`y.f * y.h + s.f * x.h + s.j * x.d` is `0` and the gearing is `0`, so `censHorn_row_o` would
predict an EVEN row.  It does not apply, because `censHornCexSig.e` is odd, and this records
that the gauge is the exact hypothesis in play. -/
theorem censHorn_cex_offGauge :
    ¬ (∃ k : gr3R, censHornCexSig.e = 2 * k)
      ∧ (∃ k : gr3R, censHornCexSig.a = 2 * k) ∧ (∃ k : gr3R, censHornCexSig.c = 2 * k) := by
  refine ⟨?_, ⟨0, by decide⟩, ⟨0, by decide⟩⟩
  decide

end Cex

/-! ## 6 The committed points: the correction costs the census nothing -/

section Committed

/-- ⭐⭐ **Both committed sigma letters lie on the gauge.**  `fiveSigMark` is `E_23` and
`liveBlkSig` is `<b = 1, d = 1>`; the `(1,2)`, `(3,4)` and `(5,6)` columns of each are `0`, so
every binder point in the tree satisfies the added hypothesis and the correction of headline 4
costs the census verdict nothing. -/
theorem censHorn_marks_gauged :
    ((∃ k : gr3R, (fiveSigMark gr3R).a = 2 * k) ∧ (∃ k : gr3R, (fiveSigMark gr3R).c = 2 * k)
        ∧ (∃ k : gr3R, (fiveSigMark gr3R).e = 2 * k))
      ∧ ((∃ k : gr3R, liveBlkSig.a = 2 * k) ∧ (∃ k : gr3R, liveBlkSig.c = 2 * k)
        ∧ (∃ k : gr3R, liveBlkSig.e = 2 * k)) :=
  ⟨⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩,
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩

/-- ⭐⭐⭐ **The verdict at W63-CENTRAL2's whole family**, at every handle count and every
handle: if the `gamma_2` forcing holds there, the achievable lattice misses the solving knob.
⭐ Horn 1 is discharged by `censHorn_gear_odd` and not by the point's own numbers: the input is
`sqRelWord_stageWit_triv` (the bare frame kills) and `sqRelWord_stageWit_diag` (the diagonal
frame is central and odd), both committed. -/
theorem censHorn_stageWit_verdict (h : ℕ) (j : Fin h)
    (hF : GaTwoForces (stageWit h j stageX)) :
    ∃ t : gr3R, selPar t = 1 ∧ (1 : gr3R) + stageX.e * t = 0 ∧ SqU6.censKnob t
      ∉ forceLcs (stageImage h j stageX) 1 := by
  rw [stageImage, stageWit]
  rw [stageWit] at hF
  exact censHorn_verdict ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩
    ⟨0, by decide⟩
    (by have hb := sqRelWord_stageWit_triv h j; rwa [stageWit, mul_one] at hb)
    (by have hd := sqRelWord_stageWit_diag h j; rwa [stageWit] at hd) (by decide) hF

/-- ⭐⭐⭐ **The verdict at W63-LIVE5's point**, at every handle count and every handle.  ⚠ W64
already proved all three lines FALSE there, because the knob is achievable
(`liveBlkWit_lines_false`); what is new is that the point needs no parity input at all, its
gearing being odd by the general theorem. -/
theorem censHorn_liveBlkWit_verdict (h : ℕ) (j : Fin h)
    (hF : GaTwoForces (liveBlkWit h j stageX)) :
    ∃ t : gr3R, selPar t = 1 ∧ (1 : gr3R) + stageX.e * t = 0 ∧ SqU6.censKnob t
      ∉ forceLcs (liveBlkImage h j stageX) 1 := by
  rw [liveBlkImage, liveBlkWit]
  rw [liveBlkWit] at hF
  exact censHorn_verdict ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩
    ⟨0, by decide⟩
    (by have hb := sqRelWord_liveBlkWit_triv h j; rwa [liveBlkWit, mul_one] at hb)
    (by have hd := sqRelWord_liveBlkWit_diag h j; rwa [liveBlkWit] at hd) (by decide) hF

end Committed

/-! ## 7 Axiom pins -/

section AxiomPins

#print axioms censHornWit
#print axioms SqU6.censHorn_row_o
#print axioms SqU6.censHorn_row_even
#print axioms censHorn_diag_eq_resid
#print axioms censHorn_abelRow_even
#print axioms censHorn_x1_cols_even
#print axioms censHorn_gear_odd
#print axioms censHorn_knob_solvable
#print axioms censHorn_verdict
#print axioms censHorn_lines_false_of_ach
#print axioms censHornCexSig
#print axioms censHornCexX
#print axioms censHornCexX'
#print axioms censHorn_recorded_false
#print axioms censHorn_recorded_false'
#print axioms censHorn_cex_offGauge
#print axioms censHorn_marks_gauged
#print axioms censHorn_stageWit_verdict
#print axioms censHorn_liveBlkWit_verdict

end AxiomPins

end SqCore

end Dyadic

end GQ2
