"""W60-SHARP5: a fast `U_6(Z/8)` product, used only where the census needs volume.

`scripts/w59_force5/u6mat.py` multiplies honest 6 x 6 matrices, which costs about 450 us per
relator and is far too slow for a layered solve repeated thousands of times.  This module
does the same arithmetic on the 15 upper-triangular entries directly.  It is NOT trusted:
`crosscheck` compares it with `u6mat` entry by entry on random input, and every certified
number the lane reports is recomputed with `u6mat` before it is printed.

Index layout (identical to `u6mat`): 0..14 = a b c d e | f g h i | j k l | m n | o,
matrix entries 12 23 34 45 56 | 13 24 35 46 | 14 25 36 | 15 26 | 16.

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

import random

import u6mat as M

N = 8
ONE = (0,) * 15

POS = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5),
       (0, 2), (1, 3), (2, 4), (3, 5),
       (0, 3), (1, 4), (2, 5),
       (0, 4), (1, 5),
       (0, 5)]
IDX = {p: k for k, p in enumerate(POS)}

# for each output entry, the list of (left index, right index) cross terms
CROSS = [[(IDX[(i, t)], IDX[(t, j)]) for t in range(i + 1, j)] for (i, j) in POS]


def mul(p, q):
    out = [0] * 15
    for k in range(15):
        s = p[k] + q[k]
        for (a, b) in CROSS[k]:
            s += p[a] * q[b]
        out[k] = s % N
    return tuple(out)


def inv(p):
    """Back-substitution: the unique `x` with `p * x = 1`, entry by entry in class order."""
    out = [0] * 15
    for k in range(15):
        s = -p[k]
        for (a, b) in CROSS[k]:
            s -= p[a] * out[b]
        out[k] = s % N
    return tuple(out)


def conjP(p, g):
    return mul(mul(inv(g), p), g)


def commP(p, q):
    return mul(mul(inv(p), inv(q)), mul(p, q))


def sqWord(s, x, y):
    x3 = mul(mul(x, x), x)
    return mul(mul(mul(inv(conjP(x, s)), inv(x3)), mul(y, y)),
               commP(y, conjP(y, s)))


def relator(S, X, Y, U, V):
    return mul(sqWord(S, X, Y), commP(U, V))


def crosscheck(trials=4000, seed=60123):
    """Every operation against `u6mat`'s honest matrices."""
    rng = random.Random(seed)
    bad = 0
    for _ in range(trials):
        p = tuple(rng.randrange(N) for _ in range(15))
        q = tuple(rng.randrange(N) for _ in range(15))
        r = tuple(rng.randrange(N) for _ in range(15))
        if mul(p, q) != M.mul(p, q):
            bad += 1
        if inv(p) != M.inv(p):
            bad += 1
        if commP(p, q) != M.commP(p, q):
            bad += 1
        if conjP(p, q) != M.conjP(p, q):
            bad += 1
        if sqWord(p, q, r) != M.sqWord(p, q, r):
            bad += 1
    return bad, trials * 5
