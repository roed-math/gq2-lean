/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFiveSepZero

/-!
# W65-CONSOL: one home for W64-SEP0H's four transported core-word rows

W64-SEP0H needed closed forms for the four core-word rows `g`, `k`, `l`, `n`, which the tree did
not have, and got all four by transporting a committed row along the shift endomorphism
`SqU6.sepShiftRow`.  The four landed as `SqU6.sqWord_g_of_shift`, `SqU6.sqWord_k_of_shift`,
`SqU6.sqWord_l_of_shift` and `SqU6.sqWord_n_of_shift`, and each of the four carries its own copy
of the same three-line transport ritual: `congrArg` a field of `map_sqWord SqU6.sepShiftRow`,
rewrite the committed source row, `simpa`.

This file gives that ritual ONE home.

## ⭐ What the one home is

`SqU6.consolShift_sqWord` is naturality of the core word along the shift, and
`SqU6.consolShift_iterate_sqWord` is the same at **arbitrary iterate depth**, which is what the
`l`-row needs (it is the class-three row shifted TWICE, and SEP0H reaches it by transporting the
already-transported `k`-row rather than by iterating).  `SqU6.consolShiftRows` then reads all
four rows off in one statement:

```text
   (sqWord s x y).g = (sqWord (shift s) (shift x) (shift y)).f      depth 1
   (sqWord s x y).k = (sqWord (shift s) (shift x) (shift y)).j      depth 1
   (sqWord s x y).l = (sqWord (shift² s) (shift² x) (shift² y)).j   depth 2
   (sqWord s x y).n = (sqWord (shift s) (shift x) (shift y)).m      depth 1
```

Nothing here is a new closed form: the content is that the four transports are ONE transport,
and that the committed row lemma each of them starts from is the only per-row input.  A fifth
row transported later needs no new ritual, only the matching `SqU6.sepShiftRow_*` projection.

## ⚠ What this file does NOT do, and the edit-window list

It **deletes nothing and edits nothing**.  `GradedFiveSepZero` keeps its four `_of_shift`
lemmas, their statements are unchanged, and every consumer of them is untouched; this file only
adds the home above them.  ⚠ So the duplication is **not yet removed** - it is made retirable.
The edit-window action, for whoever opens `GradedFiveSepZero` next:

* `SqU6.sqWord_g_of_shift`, `_k_of_shift`, `_n_of_shift`: replace the three-line body by
  `rw [(SqU6.consolShiftRows s x y).1]` (respectively `.2.1`, `.2.2.2`) followed by the same
  committed source row and `ring`.  `private theorem consolShift_g_delegate` below is that
  replacement, run, so the claim is CHECKED and not merely asserted.
* `SqU6.sqWord_l_of_shift`: same with `.2.2.1`; `private theorem consolShift_l_delegate` is the
  depth-two case, also run.
* Neither delegate is offered for reuse; both are `private` precisely so that the retirement is
  a deletion inside one file and not a name migration across two.

⚠ **Not claimed**: that the four committed statements are the sharpest closed forms of those
rows, or that the shift transports every row (it does not - it kills the sixth column, so
`e`, `i`, `l`, `n`, `o` of the image are `0` and only the four rows named above are read this
way).

## Contents

* **1** the one home: naturality along the shift, at depth `1` and at arbitrary depth;
* **2** the four transported rows in one statement, and the two delegation checks;
* **3** axiom pins.

## Merge notes

Nothing is redefined and no committed name is shadowed.  Reused: `SqU6`, `sqWord`, `map_sqWord`
(`Cores`); `SqU6.sepShiftRow`, `SqU6.sepShiftRow_f`, `SqU6.sepShiftRow_j`, `SqU6.sepShiftRow_k`,
`SqU6.sepShiftRow_m`, `SqU6.sqWord_f_core`, `SqU6.sqWord_j` and the `sqU6CoreTwo` / `sqU4Core`
shapes (`GradedFiveSepZero`, `GradedFiveDefect`, `GradedFive`).

New public names, all carrying a `consol` marker chosen against the concurrent wave-65 lanes
(`w65-horn1` and `w65-six` both touch core-word rows, so `SqU6.sqWord_*` was avoided
deliberately): `SqU6.consolShift_sqWord`, `SqU6.consolShift_iterate_sqWord`,
`SqU6.consolShiftRows`.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`, no `decide`, no `maxHeartbeats` bump.  All **3**
committed prints are **std-3** subsets; no census axiom is reachable.
-/

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The one home -/

section ConsolShift

variable {R : Type} [CommRing R]

/-- ⭐⭐ **THE ONE HOME.**  The core word commutes with the shift endomorphism, because the shift
is a monoid homomorphism and `sqWord` is natural.  This single equation is what all four of
W64-SEP0H's transported rows are instances of; the per-row work is only the choice of which
`SqU6.sepShiftRow_*` projection to read off. -/
theorem SqU6.consolShift_sqWord (s x y : SqU6 R) :
    SqU6.sepShiftRow (sqWord s x y)
      = sqWord (SqU6.sepShiftRow s) (SqU6.sepShiftRow x) (SqU6.sepShiftRow y) :=
  map_sqWord _ s x y

/-- ⭐ …and at **arbitrary iterate depth**, which is the shape the `l`-row needs.  SEP0H reaches
that row by transporting its own already-transported `k`-row, which works but does not compose;
this states the depth-`n` fact once and for all.  ⚠ It says nothing about which rows survive `n`
shifts: the shift kills the sixth column, so most rows of the image are `0` for `n` large. -/
theorem SqU6.consolShift_iterate_sqWord (n : ℕ) (s x y : SqU6 R) :
    (SqU6.sepShiftRow (R := R))^[n] (sqWord s x y)
      = sqWord ((SqU6.sepShiftRow (R := R))^[n] s) ((SqU6.sepShiftRow (R := R))^[n] x)
        ((SqU6.sepShiftRow (R := R))^[n] y) := by
  induction n generalizing s x y with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      Function.iterate_succ_apply, SqU6.consolShift_sqWord, ih]

end ConsolShift

/-! ## 2 The four transported rows, in one statement -/

section ConsolRows

variable {R : Type} [CommRing R]

/-- ⭐⭐⭐ **THE FOUR TRANSPORTED ROWS ARE ONE TRANSPORT.**  Over any commutative ring, with no
hypothesis: each of the four rows `g`, `k`, `l`, `n` of the core word is a committed row of the
core word at shifted arguments - the first, second and fourth one shift out, the third two.

⚠ What this does NOT say: it does not exhibit a closed form for any of the four.  It says that
ONE naturality equation plus the committed closed form of `f`, `j` and `m` is the whole input,
and that is exactly the redundancy W64-SEP0H's four proofs each carry a copy of. -/
theorem SqU6.consolShiftRows (s x y : SqU6 R) :
    (sqWord s x y).g
        = (sqWord (SqU6.sepShiftRow s) (SqU6.sepShiftRow x) (SqU6.sepShiftRow y)).f ∧
      (sqWord s x y).k
        = (sqWord (SqU6.sepShiftRow s) (SqU6.sepShiftRow x) (SqU6.sepShiftRow y)).j ∧
      (sqWord s x y).l
        = (sqWord (SqU6.sepShiftRow (SqU6.sepShiftRow s))
            (SqU6.sepShiftRow (SqU6.sepShiftRow x)) (SqU6.sepShiftRow (SqU6.sepShiftRow y))).j ∧
      (sqWord s x y).n
        = (sqWord (SqU6.sepShiftRow s) (SqU6.sepShiftRow x) (SqU6.sepShiftRow y)).m := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← SqU6.consolShift_sqWord, SqU6.sepShiftRow_f]
  · rw [← SqU6.consolShift_sqWord, SqU6.sepShiftRow_j]
  · rw [← SqU6.consolShift_sqWord, ← SqU6.consolShift_sqWord, SqU6.sepShiftRow_j,
      SqU6.sepShiftRow_k]
  · rw [← SqU6.consolShift_sqWord, SqU6.sepShiftRow_m]

/-- The delegation check at depth `1`: `GradedFiveSepZero.SqU6.sqWord_g_of_shift`, restated
verbatim and proved from the one home instead of from its own copy of the transport ritual.
It exists only to make the edit-window claim in the header CHECKED, and it is `private` so that
the retirement stays a deletion inside one file. -/
private theorem consolShift_g_delegate (s x y : SqU6 R) :
    (sqWord s x y).g = -4 * x.g + 2 * y.g
      + (s.b * x.c - s.c * x.b + 10 * (x.b * x.c) - 8 * (x.b * y.c) + y.b * y.c) := by
  rw [(SqU6.consolShiftRows s x y).1, SqU6.sqWord_f_core, sqU6CoreTwo]
  simp only [SqU6.sepShiftRow_a, SqU6.sepShiftRow_b, SqU6.sepShiftRow_f]

/-- The delegation check at depth `2`: `GradedFiveSepZero.SqU6.sqWord_l_of_shift`, restated
verbatim and proved from the one home. -/
private theorem consolShift_l_delegate (s x y : SqU6 R) :
    (sqWord s x y).l = -4 * x.l + 2 * y.l
      + sqU4Core (SqU6.toU4LL (SqU6.sepShiftRow (SqU6.sepShiftRow s)))
        (SqU6.toU4LL (SqU6.sepShiftRow (SqU6.sepShiftRow x)))
        (SqU6.toU4LL (SqU6.sepShiftRow (SqU6.sepShiftRow y))) := by
  rw [(SqU6.consolShiftRows s x y).2.2.1, SqU6.sqWord_j]
  simp only [SqU6.sepShiftRow_j, SqU6.sepShiftRow_k]

end ConsolRows

/-! ## 3 Axiom pins -/

section AxiomPins

#print axioms SqU6.consolShift_sqWord
#print axioms SqU6.consolShift_iterate_sqWord
#print axioms SqU6.consolShiftRows

end AxiomPins

end SqCore

end Dyadic

end GQ2
