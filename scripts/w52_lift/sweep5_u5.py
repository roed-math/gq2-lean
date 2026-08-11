#!/usr/bin/env python3
"""sweep5_u5.py.

BRACKET CONVENTION.  [NONE]
This script computes no commutators, so the convention does not arise.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

"""sweep5_u5.py.
"""

"""sweep5_u5.py.
"""

"""sweep5_u5.py.
"""

"""sweep5_u5.py.
"""

"""W52-LIFT step 6: which level-one knob flips the class-4 bit?

At F-even live points (BD odd) with odd j-residue, apply single dressing knobs,
re-solve stage 3 canonically, and record the parity shift of the j-residue.
Knobs (all class-2-legal level-one moves):
  tU : dress U-handle slot by tbar (w-component +1)  [the selTee trick]
  tV : dress V-handle slot by tbar
  uV : dress V-handle slot by Ubar
  vU : dress U-handle slot by Vbar
  t1 : dress x1-slot (slot 2) by tbar
  s0 : dress sigma-slot by tbar
  gB : the slot1.g solve branch (+2)
"""
from sweep_u5 import (M, IDX, mul, sqRelWord, U5, binder_points, letters,
                      witness_tuple, increment_set, classify_J)
from sweep2_u5 import solve_stage3
import random

random.seed(5)


def apply_knob(pt, m, knob):
    sig, Ub, Vb, X1 = letters(pt)
    m = [list(v) for v in m]
    mm = [tuple(v) for v in m]
    mm = list(mm)
    if knob == 'tU':
        mm[3] = mul(mm[3], X1)
    elif knob == 'tV':
        mm[4] = mul(mm[4], X1)
    elif knob == 'uV':
        mm[4] = mul(mm[4], Ub)
    elif knob == 'vU':
        mm[3] = mul(mm[3], Vb)
    elif knob == 't1':
        mm[2] = mul(mm[2], X1)
    elif knob == 's0':
        mm[0] = mul(mm[0], X1)
    elif knob == 'gB':
        v = list(mm[1])
        v[6] = (v[6] + 2) % M
        mm[1] = tuple(v)
    return mm


def canonical_jres(pt, m):
    m3, r3 = solve_stage3(pt, m)
    if m3 is None:
        return None
    return r3[9]


def main():
    knobs = ['tU', 'tV', 'uV', 'vU', 't1', 's0', 'gB']
    for tys in [(0, 1), (1, 0), (1, 1)]:
        print(f"== type {tys}, BD odd, F even: knob parity shifts")
        shifts = {k: set() for k in knobs}
        odd_fixed = 0
        odd_total = 0
        n = 0
        for pt in binder_points(400, types={tys}):
            if not (pt[1] % 2 and pt[3] % 2 and pt[5] % 2 == 0):
                continue
            n += 1
            if n > 25:
                break
            m, rows, need = witness_tuple(pt)
            j0 = canonical_jres(pt, m)
            if j0 is None:
                continue
            fixed = False
            for k in knobs:
                mm = apply_knob(pt, m, k)
                # knob may break class-2 rows?  measure first 7 rows after knob
                jk = canonical_jres(pt, mm)
                if jk is None:
                    shifts[k].add('stage3-fail')
                    continue
                shifts[k].add((jk - j0) % 2)
                if j0 % 2 and jk % 2 == 0:
                    fixed = True
            if j0 % 2:
                odd_total += 1
                odd_fixed += fixed
        for k in knobs:
            print(f"    {k}: parity shifts seen {sorted(map(str, shifts[k]))}")
        print(f"    odd-residue points: {odd_total}, fixable by some knob: {odd_fixed}")


if __name__ == "__main__":
    main()
