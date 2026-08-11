"""W65-SIX: is the class-SIX sigma separation forced at `h = 0`?

The class-`N` test group is `U_{N+1}`, so class six lives in `U_7` and the tree stops at
`SqU6 = U_6` (class five).  This script settles the mathematics off-Lean, using the honest
matrix arithmetic of `u7lib.py` (no coordinate law is transcribed, so nothing can be
mis-transcribed), before any Lean carrier is paid for.

Sections:

1. certify `u7lib` at `n = 6` against the campaign's COMMITTED `SqU6` coordinate law
   (`GQ2/Dyadic/SqCore/GradedFive.lean` lines 250-273), symbolically over `Z[vars]`;
2. reproduce W64-SEP0H's class-five theorem as a pipeline check at `n = 6`;
3. run the same experiment at `n = 7`: the class-six question.
"""

import random
import sys

sys.path.insert(0, "/Users/roed/claude/cla/worktrees/w65-six/scripts/w65_six")

from u7lib import (F2Ring, IntRing, ModRing, PolyRing, cells, eye, is_one, label,
                   mmul, minv, mpw, p_const, p_mul, p_sub, p_var, rand_mat, solve_x1,
                   sqWord, sym_mat)

M = 8  # gr3R = ZMod 8


# ==========================================================================================
# 1  Certify the library at n = 6 against the committed SqU6 coordinate law.

# The fifteen SqU6 fields, in the campaign's order, with their matrix cells.
U6_FIELDS = [
    ("a", (0, 1)), ("b", (1, 2)), ("c", (2, 3)), ("d", (3, 4)), ("e", (4, 5)),
    ("f", (0, 2)), ("g", (1, 3)), ("h", (2, 4)), ("i", (3, 5)),
    ("j", (0, 3)), ("k", (1, 4)), ("l", (2, 5)),
    ("m", (0, 4)), ("n", (1, 5)),
    ("o", (0, 5)),
]
U6_CELL = dict(U6_FIELDS)


def _pv(prefix, name):
    return p_var(f"{prefix}{name}")


def certify_mul():
    """Committed `SqU6` multiplication (GradedFive.lean:250-258) vs honest matrix product."""
    P = eye(6, PolyRing)
    Q = eye(6, PolyRing)
    for nm, (r, c) in U6_FIELDS:
        P[r][c] = _pv("p", nm)
        Q[r][c] = _pv("q", nm)
    prod = mmul(P, Q, PolyRing)

    def add(*ts):
        out = PolyRing.zero
        for t in ts:
            out = PolyRing.add(out, t)
        return out

    def pq(u, v):
        return p_mul(_pv("p", u), _pv("q", v))

    committed = {
        "a": add(_pv("p", "a"), _pv("q", "a")),
        "b": add(_pv("p", "b"), _pv("q", "b")),
        "c": add(_pv("p", "c"), _pv("q", "c")),
        "d": add(_pv("p", "d"), _pv("q", "d")),
        "e": add(_pv("p", "e"), _pv("q", "e")),
        "f": add(_pv("p", "f"), _pv("q", "f"), pq("a", "b")),
        "g": add(_pv("p", "g"), _pv("q", "g"), pq("b", "c")),
        "h": add(_pv("p", "h"), _pv("q", "h"), pq("c", "d")),
        "i": add(_pv("p", "i"), _pv("q", "i"), pq("d", "e")),
        "j": add(_pv("p", "j"), _pv("q", "j"), pq("a", "g"), pq("f", "c")),
        "k": add(_pv("p", "k"), _pv("q", "k"), pq("b", "h"), pq("g", "d")),
        "l": add(_pv("p", "l"), _pv("q", "l"), pq("c", "i"), pq("h", "e")),
        "m": add(_pv("p", "m"), _pv("q", "m"), pq("a", "k"), pq("f", "h"), pq("j", "d")),
        "n": add(_pv("p", "n"), _pv("q", "n"), pq("b", "l"), pq("g", "i"), pq("k", "e")),
        "o": add(_pv("p", "o"), _pv("q", "o"), pq("a", "n"), pq("f", "l"), pq("j", "i"),
                 pq("m", "e")),
    }
    bad = []
    for nm, (r, c) in U6_FIELDS:
        if p_sub(prod[r][c], committed[nm]):
            bad.append(nm)
    return bad


def certify_inv():
    """Committed `SqU6` inverse (GradedFive.lean:260-273) vs back substitution."""
    P = eye(6, PolyRing)
    for nm, (r, c) in U6_FIELDS:
        P[r][c] = _pv("p", nm)
    invm = minv(P, PolyRing)

    def add(*ts):
        out = PolyRing.zero
        for t in ts:
            out = PolyRing.add(out, t)
        return out

    def mon(coeff, *names):
        out = p_const(coeff)
        for nm in names:
            out = p_mul(out, _pv("p", nm))
        return out

    committed = {
        "a": mon(-1, "a"), "b": mon(-1, "b"), "c": mon(-1, "c"),
        "d": mon(-1, "d"), "e": mon(-1, "e"),
        "f": add(mon(1, "a", "b"), mon(-1, "f")),
        "g": add(mon(1, "b", "c"), mon(-1, "g")),
        "h": add(mon(1, "c", "d"), mon(-1, "h")),
        "i": add(mon(1, "d", "e"), mon(-1, "i")),
        "j": add(mon(-1, "a", "b", "c"), mon(1, "a", "g"), mon(1, "c", "f"), mon(-1, "j")),
        "k": add(mon(-1, "b", "c", "d"), mon(1, "b", "h"), mon(1, "d", "g"), mon(-1, "k")),
        "l": add(mon(-1, "c", "d", "e"), mon(1, "c", "i"), mon(1, "e", "h"), mon(-1, "l")),
        "m": add(mon(1, "a", "b", "c", "d"), mon(-1, "a", "b", "h"), mon(-1, "a", "d", "g"),
                 mon(1, "a", "k"), mon(-1, "c", "d", "f"), mon(1, "d", "j"),
                 mon(1, "f", "h"), mon(-1, "m")),
        "n": add(mon(1, "b", "c", "d", "e"), mon(-1, "b", "c", "i"), mon(-1, "b", "e", "h"),
                 mon(1, "b", "l"), mon(-1, "d", "e", "g"), mon(1, "e", "k"),
                 mon(1, "g", "i"), mon(-1, "n")),
        "o": add(mon(-1, "a", "b", "c", "d", "e"), mon(1, "a", "b", "c", "i"),
                 mon(1, "a", "b", "e", "h"), mon(-1, "a", "b", "l"),
                 mon(1, "a", "d", "e", "g"), mon(-1, "a", "e", "k"), mon(-1, "a", "g", "i"),
                 mon(1, "a", "n"), mon(1, "c", "d", "e", "f"), mon(-1, "c", "f", "i"),
                 mon(-1, "d", "e", "j"), mon(-1, "e", "f", "h"), mon(1, "e", "m"),
                 mon(1, "f", "l"), mon(1, "i", "j"), mon(-1, "o")),
    }
    bad = []
    for nm, (r, c) in U6_FIELDS:
        if p_sub(invm[r][c], committed[nm]):
            bad.append(nm)
    return bad


# ==========================================================================================
# 2/3  The separation experiment at a given n.


def top_cell(n):
    return (0, n - 1)


def experiment(n, trials, seed, verbose_first=0):
    """Sample `(s, x)`, solve `sqWord s x y = 1` over `Z/8`, read the dressed top row parity.

    Returns `(tested, odd_examples, blocked)`.
    """
    rng = random.Random(seed)
    R = ModRing(M)
    tr, cr = top_cell(n)
    tested = 0
    blocked = 0
    odd = []
    shown = 0
    for _ in range(trials):
        s = rand_mat(n, rng, M)
        x = rand_mat(n, rng, M)
        y, blk = solve_x1(s, x, n, rng, M)
        if y is None:
            blocked += 1
            continue
        # relator-killing at h = 0: sqWord s x y = 1
        assert is_one(sqWord(s, x, y, R), R)
        dressed = sqWord(mmul(s, x, R), x, y, R)
        bit = dressed[tr][cr] % 2
        tested += 1
        if shown < verbose_first:
            shown += 1
            print(f"    sample: dressed top {label(tr, cr)} = {dressed[tr][cr]}  parity {bit}")
        if bit:
            odd.append((s, x, y, dressed[tr][cr]))
    return tested, odd, blocked


def profile_rows(n, trials, seed):
    """For each cell, how often is the dressed word's entry ODD at a relator-killing marking?"""
    rng = random.Random(seed)
    R = ModRing(M)
    counts = {c: 0 for c in cells(n)}
    tested = 0
    for _ in range(trials):
        s = rand_mat(n, rng, M)
        x = rand_mat(n, rng, M)
        y, blk = solve_x1(s, x, n, rng, M)
        if y is None:
            continue
        dressed = sqWord(mmul(s, x, R), x, y, R)
        tested += 1
        for c in cells(n):
            if dressed[c[0]][c[1]] % 2:
                counts[c] += 1
    return tested, counts


# ==========================================================================================

def main():
    print("=" * 90)
    print("W65-SIX section 1: certify u7lib at n = 6 against the committed SqU6 law")
    print("=" * 90)
    bm = certify_mul()
    bi = certify_inv()
    print(f"  multiplication: {'ALL 15 FIELDS AGREE' if not bm else 'MISMATCH ' + str(bm)}")
    print(f"  inverse       : {'ALL 15 FIELDS AGREE' if not bi else 'MISMATCH ' + str(bi)}")
    if bm or bi:
        print("  ABORT: the library does not model the committed group.")
        return 1

    print()
    print("=" * 90)
    print("W65-SIX section 2: pipeline check, W64-SEP0H's class-FIVE theorem at n = 6")
    print("  claim: sqWord s x y = 1  ==>  selPar (sqWord (s*x) x y).o = 0")
    print("=" * 90)
    tested, odd, blocked = experiment(6, 3000, seed=20260811, verbose_first=3)
    print(f"  markings tested: {tested}   (blocked solves: {blocked})")
    print(f"  ODD class-five responses: {len(odd)}")
    print("  -> reproduces SEP0H" if not odd else "  -> CONTRADICTS SEP0H, pipeline is wrong")
    if odd:
        return 1

    print()
    print("=" * 90)
    print("W65-SIX section 3: the class-SIX question at n = 7")
    print("  claim under test: sqWord s x y = 1  ==>  selPar (sqWord (s*x) x y).<(1,7)> = 0")
    print("=" * 90)
    tested7, odd7, blocked7 = experiment(7, 3000, seed=20260811, verbose_first=6)
    print(f"  markings tested: {tested7}   (blocked solves: {blocked7})")
    print(f"  ODD class-six responses: {len(odd7)}")
    if odd7:
        print("  ==> NOT FORCED: a handle-free relator-killing marking separates at class six.")
    else:
        print("  ==> forced in every sample; look for the row identity.")

    print()
    print("=" * 90)
    print("W65-SIX section 4: per-cell odd-frequency profile of the dressed word (n = 7)")
    print("=" * 90)
    t7, counts = profile_rows(7, 2000, seed=777)
    print(f"  markings tested: {t7}")
    for d in range(1, 7):
        row = [(c, counts[c]) for c in cells(7) if c[1] - c[0] == d]
        txt = "  ".join(f"{label(*c)}:{k}" for c, k in row)
        print(f"  class {d}: {txt}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
