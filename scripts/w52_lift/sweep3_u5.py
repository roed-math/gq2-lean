#!/usr/bin/env python3
"""sweep3_u5.py.

BRACKET CONVENTION.  [NONE]
This script computes no commutators, so the convention does not arise.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

"""sweep3_u5.py.
"""

"""sweep3_u5.py.
"""

"""sweep3_u5.py.
"""

"""sweep3_u5.py.
"""

"""W52-LIFT step 4: honest stage-4 increment group via explicit achievable moves.

Moves on the two handle slots: products of the four lattice gamma-2 generator
ELEMENTS (e,f,g-parts, deep 0) and gamma-3 pairing elements (h,i-parts, j 0);
exponent slots: gamma-3/4 with (h,i) even-fix and j free-even.
A move is admissible if it preserves rows a..g (automatic) and rows h,i
(after the exponent-slot even fix, i.e. (dh,di) even).
Question: is the j-residue of the stage-3 survivor always reachable?
"""
from sweep_u5 import (M, IDX, mul, sqRelWord, U5, binder_points, lam5_gens,
                      lam3_gens, witness_tuple, classify_J, increment_set)
from sweep2_u5 import span_pairs, stage3_pair_gens, solve_stage3
import itertools, random

random.seed(3)


def gamma2_elt(pt, coeffs):
    L5 = lam5_gens(pt)
    z = U5()
    for k, ck in enumerate(coeffs):
        ge = U5(e=L5[k][0], f=L5[k][1], g=L5[k][2])
        for _ in range(ck % M):
            z = mul(z, ge)
    return z


def gamma3_elt(pt, coeffs):
    L3 = lam3_gens(pt)
    z = U5()
    for k, ck in zip(random.sample(range(len(L3)), min(4, len(L3))), coeffs):
        ge = U5(h=L3[k][0], i=L3[k][1])
        for _ in range(ck % M):
            z = mul(z, ge)
    return z


def reachable_j(pt, m3, tries=4000):
    """set of j-values of relator over random admissible moves."""
    base = sqRelWord(m3)
    assert all(base[k] == 0 for k in range(9))
    seen = set()
    for _ in range(tries):
        mm = list(m3)
        z3 = mul(gamma2_elt(pt, [random.randrange(M) for _ in range(4)]),
                 gamma3_elt(pt, [random.randrange(M) for _ in range(4)]))
        z4 = mul(gamma2_elt(pt, [random.randrange(M) for _ in range(4)]),
                 gamma3_elt(pt, [random.randrange(M) for _ in range(4)]))
        mm[3] = mul(mm[3], z3)
        mm[4] = mul(mm[4], z4)
        r = sqRelWord(mm)
        if any(r[k] for k in range(4, 7)):
            continue  # class-2 rows must stay dead (should be automatic)
        if r[7] % 2 or r[8] % 2:
            continue  # not fixable by exponent even-moves
        # exponent-slot fix of rows h,i: w2-slot h,i with 2*w
        fh = [w for w in range(M) if (2 * w + r[7]) % M == 0][0]
        fi = [w for w in range(M) if (2 * w + r[8]) % M == 0][0]
        mm[2] = mul(mm[2], U5(h=fh, i=fi))
        r = sqRelWord(mm)
        if all(r[k] == 0 for k in range(9)):
            seen.add(r[9])
    return seen


def main():
    print("== enriched stage-4 reachability on 60 points per type")
    for tys in [(0, 1), (1, 0), (1, 1)]:
        ok = notok = 0
        witness_examples = []
        for pt in binder_points(20, types={tys}):
            m, rows, need = witness_tuple(pt)
            m3, r3 = solve_stage3(pt, m)
            if m3 is None:
                continue
            Jnaive = increment_set(pt, m3[3], m3[4])
            reach = reachable_j(pt, m3)
            # relator killable iff 0 in reach - r3[9]... reach is set of residues
            killable = 0 in reach
            naive = (0 - r3[9]) % M in Jnaive
            if killable:
                ok += 1
            else:
                notok += 1
                witness_examples.append((pt, r3[9], sorted(reach),
                                         classify_J(Jnaive)))
        print(f"  type {tys}: killable {ok}, NOT {notok}")
        for w in witness_examples[:4]:
            print(f"    fail: pt={w[0]} jres={w[1]} reach={w[2]} Jnaive={w[3]}")


if __name__ == "__main__":
    main()
