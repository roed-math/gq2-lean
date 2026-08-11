#!/usr/bin/env python3
"""sweep4_u5.py.

BRACKET CONVENTION.  [NONE]
This script computes no commutators, so the convention does not arise.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

"""sweep4_u5.py.
"""

"""sweep4_u5.py.
"""

"""sweep4_u5.py.
"""

"""sweep4_u5.py.
"""

"""W52-LIFT step 5: the live-locus engine, focused.

On the class-3 live locus (B*D odd, the committed hypothesis shape), with the
canonical two-row stage-3 solution, ask:
  (i)   with F odd: is the class-4 action surjective (odd increment) -> kill anything?
  (ii)  with F even: is the j-residue even?  If not, can flipping level-one data
        (dressing parities on the five slots) zero the class-4 bit?
  (iii) live-completion: exhibit rr-style witnesses.
Also mirrored on type (1,0) (A*C odd, E parity) and (1,1).
"""
from sweep_u5 import (M, IDX, mul, sqRelWord, U5, binder_points, lam5_gens,
                      lam3_gens, witness_tuple, classify_J, increment_set)
from sweep2_u5 import span_pairs, stage3_pair_gens, solve_stage3
from sweep3_u5 import gamma2_elt, gamma3_elt, reachable_j
import random

random.seed(4)


def live_points(n, tys, extra):
    pts = []
    while len(pts) < n:
        for pt in binder_points(50, types={tys}):
            A, B, C, D, E, F, T, S, P, Q, R, W2 = pt
            if extra(pt):
                pts.append(pt)
                if len(pts) >= n:
                    break
    return pts


def study(tag, tys, cond):
    print(f"== {tag}")
    par_odd = par_even = 0
    kill_odd = kill_even = 0
    for pt in live_points(30, tys, cond):
        m, rows, need = witness_tuple(pt)
        m3, r3 = solve_stage3(pt, m)
        if m3 is None:
            print(f"    stage3 failed at {pt}!")
            continue
        jres = r3[9]
        reach = reachable_j(pt, m3, tries=2500)
        killable = 0 in reach
        if jres % 2:
            par_odd += 1
            kill_odd += killable
        else:
            par_even += 1
            kill_even += killable
    print(f"    jres odd: {par_odd} (killable {kill_odd}), "
          f"jres even: {par_even} (killable {kill_even})")


def main():
    # class-3 live: B*D odd.  class-4 fully-live candidate: F odd too.
    study("type (0,1), BD odd, F odd", (0, 1),
          lambda p: p[1] % 2 == 1 and p[3] % 2 == 1 and p[5] % 2 == 1)
    study("type (0,1), BD odd, F even", (0, 1),
          lambda p: p[1] % 2 == 1 and p[3] % 2 == 1 and p[5] % 2 == 0)
    study("type (1,0), AC odd, E odd", (1, 0),
          lambda p: p[0] % 2 == 1 and p[2] % 2 == 1 and p[4] % 2 == 1)
    study("type (1,0), AC odd, E even", (1, 0),
          lambda p: p[0] % 2 == 1 and p[2] % 2 == 1 and p[4] % 2 == 0)
    study("type (1,1), BD odd, F odd", (1, 1),
          lambda p: p[1] % 2 == 1 and p[3] % 2 == 1 and p[5] % 2 == 1)
    study("type (1,1), BD odd, F even", (1, 1),
          lambda p: p[1] % 2 == 1 and p[3] % 2 == 1 and p[5] % 2 == 0)


if __name__ == "__main__":
    main()
