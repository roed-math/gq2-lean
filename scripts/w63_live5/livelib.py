"""W63-LIVE5: the search for a class-five witness whose BLOCK channel is live.

Nothing is retyped.  The coordinate law, the inverse, `conjP`, `commP` and `sqWord` come from
`scripts/w59_blind5/u6lib.py` (certified against honest `6 x 6` matrix arithmetic); the mod-8
reduction, the relator, the block reading and the layered solve come from
`scripts/w61_block/blocklib.py`.  This module adds only

* the class-five witness STANDARD as an explicit predicate list, one entry per condition the
  two committed witnesses (`GradedFiveForce.fiveWit`, `GradedFiveStageFour.stageWit`) satisfy;
* the reduction of the block channel at a gauged witness to the sigma slot's `(4,5)`-entry;
* the search over sigma slots off the committed `fiveSigMark = E_23`.

Coordinate naming is the campaign's (`GQ2/Dyadic/SqCore/GradedFive.lean`):

    index  0  1  2  3  4   5  6  7  8   9 10 11  12 13  14
    name   a  b  c  d  e   f  g  h  i   j  k  l   m  n   o
    entry 12 23 34 45 56  13 24 35 46  14 25 36  15 26  16

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

import sys
from pathlib import Path

_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE.parent / "w59_blind5"))
sys.path.insert(0, str(_HERE.parent / "w61_block"))

from u6lib import NAMES, U6, commP, conjP, inv, mul, sqWord  # noqa: E402
from blocklib import (  # noqa: E402
    LAYERS, M, block_read, eq, handle_minor, handle_word, is_one, par, rand, red, rel_word,
    rinv, rmul, rsqWord, solve_x1,
)

# --------------------------------------------------------------------------------------
# The committed points, transcribed from the Lean files (values only, no law).

FIVE_SIG = U6({"b": 1})                                              # fiveSigMark = sigFiveMark
FORCE_X = U6({"a": 2, "e": 1})                                       # GradedFiveForce.forceX
FORCE_Y = U6({"e": 2, "f": 1, "h": 3, "i": 1, "j": 2, "k": 2,
              "l": 2, "m": 3, "n": 2, "o": 2})                       # GradedFiveForce.forceY
FORCE_U = U6({"a": 1, "c": 2, "d": 3, "f": 3, "g": 2, "h": 2, "i": 2})
FORCE_V = U6({"d": 1, "e": 2, "f": 3, "g": 2, "h": 3, "i": 3})

STAGE_X = U6({"a": 2, "e": 5})                                       # GradedFiveStageFour.stageX
STAGE_Y = U6({"e": 2, "f": 1, "g": 1, "h": 1, "m": 3, "n": 3})
STAGE_U = U6({"a": 6, "b": 7, "c": 4, "d": 1, "e": 3, "g": 5, "h": 5})
STAGE_V = U6({"a": 6, "b": 7, "c": 6, "d": 1, "e": 3, "f": 5, "g": 3, "h": 3, "i": 4})

BLIND_S = U6({"b": 1, "e": 1})                                       # GradedFiveBlind.blindCexS
BLIND_X = U6({"d": 1, "g": 1, "l": 1})
BLIND_U = U6({"d": 1})
BLIND_V = U6({"e": 1})


def liftO(w):
    return U6({"o": w % M})


def is_central(p):
    """`p = liftC6 p.o`: every coordinate but the class-five one vanishes mod 8."""
    return all(p.co[k] % M == 0 for k in NAMES if k != "o")


# --------------------------------------------------------------------------------------
# The witness standard.
#
# A five-tuple `(S, X, Y, U, V)` is a CLASS-FIVE WITNESS of the kind `fiveWit` and `stageWit`
# are when every entry below holds.  `sqRelWord (fiveTuple ...) = sqWord(S,X,Y) * [U,V]` at
# every handle count and every handle, so every condition is handle-independent.


def rel(S, X, Y, U, V):
    """`sqRelWord (fiveTuple gr3R h j S X Y U V)`, at any `h >= 1` and any handle."""
    return rmul(rsqWord(S, X, Y), red(commP(U, V)))


def dressed(S, X, Y, U, V, v):
    """The relator at the sigma dressing `v`: the sigma slot becomes `S * v`."""
    return rel(rmul(S, v), X, Y, U, V)


def std_checks(S, X, Y, U, V):
    """The witness standard, as a dict of named booleans.  Every one holds at `stageWit`."""
    r1 = rel(S, X, Y, U, V)
    rd = dressed(S, X, Y, U, V, X)
    blk = red(commP(U, V))
    return {
        # (A) the fifteen-row standard: the undressed marking kills the relator outright.
        "A_fifteen_rows": is_one(r1),
        # (B) the `a0 = a1` dressing leaves a PURELY CENTRAL residue ...
        "B_central_residue": is_central(rd),
        # ... which is ODD, so the separation is genuinely class five.
        "B_odd_residue": par(rd.co["o"]) == 1,
        # (C) stage-four soundness: every letter has an even (1,2)- and an even (3,4)-column.
        "C_stageN1_letters": all(p.co["a"] % 2 == 0 and p.co["c"] % 2 == 0
                                 for p in (S, X, Y, U, V)),
        # (D) the committed class-two-forced gauge on the two core slots.
        "D_gauge_x0": (X.co["a"] % 2 == 0 and X.co["c"] % 2 == 0 and X.co["d"] % 2 == 0
                       and X.co["f"] % 2 == 0 and X.co["g"] % 2 == 0 and X.co["b"] % M == 0),
        "D_gauge_x1": (Y.co["a"] % 2 == 0 and Y.co["c"] % 2 == 0 and Y.co["d"] % 2 == 0),
        "D_gauge_x0_e_odd": par(X.co["e"]) == 1,
        # (E) the handle block is live, and live in the class-four row.
        "E_block_live": (not is_one(blk)) and par(blk.co["m"]) == 1,
        # (F) the sigma slot keeps the `nu'`-column of `E_23`, so the pivot anchor and the
        # row-forcing argument transfer verbatim.
        "F_sigma_b_one": S.co["b"] % M == 1,
        # (G) the ten flat obstructions vanish at the `x0` slot, so the pivot is mechanical.
        "G_x0_flat": flat_obstructions(X),
    }


def flat_obstructions(g):
    """The ten hypotheses of `SqU6.zpowZtwo_of_flat`, mod 8."""
    c = g.co
    return all(t % M == 0 for t in [
        c["a"] * c["b"], c["b"] * c["c"], c["c"] * c["d"], c["d"] * c["e"],
        c["a"] * c["g"] + c["f"] * c["c"],
        c["b"] * c["h"] + c["g"] * c["d"],
        c["c"] * c["i"] + c["h"] * c["e"],
        c["a"] * c["k"] + c["f"] * c["h"] + c["j"] * c["d"],
        c["b"] * c["l"] + c["g"] * c["i"] + c["k"] * c["e"],
        c["a"] * c["n"] + c["f"] * c["l"] + c["j"] * c["i"] + c["m"] * c["e"],
    ])


def is_witness(S, X, Y, U, V):
    return all(std_checks(S, X, Y, U, V).values())


def block_live(S, X, U, V):
    """The block channel: the core reading and the handle minor, both mod 2."""
    return par(block_read(S, X)), par(handle_minor(U, V))
