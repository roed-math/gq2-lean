"""W63-LIVE5, derivation: the two shape facts the search is built on.

Both are computed symbolically over `Z` with `sympy` on the certified `U_6` law of
`scripts/w59_blind5/u6lib.py`, then re-checked numerically mod `8`.

1. **The gauge reduction.**  `blockRead(s, x) = s_45 x_56 - s_56 x_45`, so on the committed
   class-two-forced gauge (`x_45` even, `x_56` odd) its parity is `s_45` and nothing else.
   This is `SqU6.selPar_blockRead_of_gauge` in Lean; here it is checked exhaustively over
   `ZMod 8` rather than proved.

2. **The commutator's two live rows mod 2**, once both letters have even `(1,2)`- and
   `(3,4)`-columns.  This is what selects the letter family of `minimise_live5.py`.

Run: `python3 scripts/w63_live5/derive_live5.py`
"""

import random
import sys
from pathlib import Path

from sympy import expand, simplify

sys.path.insert(0, str(Path(__file__).resolve().parent))

import livelib as L  # noqa: E402
from u6lib import NAMES, U6, commP, sym  # noqa: E402


def drop_even(poly, evens):
    """Reduce a polynomial mod 2 by killing every monomial containing an `evens` symbol."""
    out = 0
    for term in expand(poly).as_ordered_terms():
        if any(s in term.free_symbols for s in evens):
            continue
        c = term.as_coeff_Mul()[0]
        if int(c) % 2 == 0:
            continue
        out += term / c
    return out


def main():
    print("W63-LIVE5 derivation")
    print("=" * 78)

    u, v = sym("u"), sym("v")
    c = commP(u, v)
    evens = [u.co["a"], u.co["c"], v.co["a"], v.co["c"]]

    print("\n1  THE COMMUTATOR'S ROWS MOD 2, at letters with even (1,2)- and (3,4)-columns")
    for k in ["f", "g", "h", "i", "j", "k", "l", "m"]:
        print(f"    [u, v]_{k} = {drop_even(c.co[k], evens)}")
    print("\n  so the (4,6) row (the block channel) needs d/e entries, and the (1,5) row")
    print("  (the class-four liveness the committed witnesses record) needs d/j or f/h.")

    print("\n2  THE GAUGE REDUCTION, exhaustive over ZMod 8")
    bad = 0
    n = 0
    for sd in range(8):
        for se in range(8):
            for xd in range(0, 8, 2):
                for xe in range(1, 8, 2):
                    n += 1
                    if (sd * xe - se * xd) % 2 != sd % 2:
                        bad += 1
    print(f"    selPar(blockRead s x) = selPar s_45 on the gauge: {n} points, {bad} failures")

    print("\n3  THE RELATOR'S ABELIAN ROWS DO NOT SEE THE SIGMA SLOT")
    rng = random.Random(7)
    mism = 0
    for _ in range(4000):
        s, s2, x, y = L.rand(rng), L.rand(rng), L.rand(rng), L.rand(rng)
        a = L.rsqWord(s, x, y)
        b = L.rsqWord(s2, x, y)
        for k in ["a", "b", "c", "d", "e"]:
            if (a.co[k] - b.co[k]) % 8 != 0:
                mism += 1
    print(f"    4000 pairs of sigma slots, 5 abelian rows each: {mism} mismatches")
    print("    (so the fifteen-row standard places NO condition on the sigma slot's (4,5)")
    print("     entry, which is why the live witness exists at all)")

    print("\n4  THE COMMITTED SIGMA MARK, AND THE MOVED ONE")
    for nm, s in [("fiveSigMark = E_23", L.FIVE_SIG),
                  ("liveBlkSig  = E_23 E_45", U6({"b": 1, "d": 1})),
                  ("blindCexS   = E_23 <e=1>", L.BLIND_S)]:
        print(f"    {nm:26s} d = {s.co['d']}, e = {s.co['e']}, "
              f"blockRead against stageX = {L.block_read(s, L.STAGE_X)}")

    print("\n" + "=" * 78)
    print(f"CHECKS: 3   FAILURES: {bad + mism}")


if __name__ == "__main__":
    main()
