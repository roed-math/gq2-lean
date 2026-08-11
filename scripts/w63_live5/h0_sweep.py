"""W63-LIVE5, the open question: is the class-five separation possible at `h = 0`?

MEASURED ONLY.  Nothing here is proved anywhere in the tree, and the Lean file says so.

At `h = 0` the relator is the bare core word, so a class-five separation would be a triple
`(s, x, y)` on the committed class-two-forced gauge with `sqWord(s, x, y) = 1` and
`sqWord(s * x, x, y)` a purely central element with an ODD class-five coordinate.  This script
sweeps for one.

⚠ Why the block instrument cannot settle it.  The instrument forces `0 < h` only when the block
reading is odd; at the block-blind core pairs the reading is even and it says nothing, and the
control in `verify_live5.py` section 5 shows those pairs really do complete at `h = 0`.  So a
negative answer here would need a different argument.

Run: `python3 scripts/w63_live5/h0_sweep.py`
"""

import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import livelib as L  # noqa: E402
from u6lib import U6  # noqa: E402

TRIALS = 200000
SEED = 2026


def gauged_x(rng):
    """An `x0` slot on the committed gauge: a, c, d, f, g even, b = 0, e odd."""
    x = L.rand(rng)
    x.co["a"] = 2 * rng.randrange(4)
    x.co["b"] = 0
    x.co["c"] = 2 * rng.randrange(4)
    x.co["d"] = 2 * rng.randrange(4)
    x.co["e"] = 2 * rng.randrange(4) + 1
    x.co["f"] = 2 * rng.randrange(4)
    x.co["g"] = 2 * rng.randrange(4)
    return x


def main():
    rng = random.Random(SEED)
    print("W63-LIVE5: the h = 0 sweep for a class-five separation")
    print("=" * 78)
    print(f"trials: {TRIALS}, seed {SEED}")

    solved = 0
    central = 0
    odd = 0
    for _ in range(TRIALS):
        s = L.rand(rng)
        s.co["b"] = 1
        s.co["a"] = 2 * rng.randrange(4)
        s.co["c"] = 2 * rng.randrange(4)
        x = gauged_x(rng)
        y, _bad = L.solve_x1(s, x, U6(), rng)
        if y is None:
            continue
        if not (y.co["a"] % 2 == 0 and y.co["c"] % 2 == 0 and y.co["d"] % 2 == 0):
            continue
        solved += 1
        d = L.rsqWord(L.rmul(s, x), x, y)
        if L.is_central(d):
            central += 1
            if L.par(d.co["o"]) == 1:
                odd += 1
                print("  SEPARATION FOUND:", s, x, y, d)

    print(f"\n  gauged relator-killing h = 0 triples found : {solved}")
    print(f"  ...whose a0 = a1 residue is purely central  : {central}")
    print(f"  ...and ODD there (a class-five separation)  : {odd}")
    print("\n  The control that the sweep is not vacuous: the committed core pair")
    y0 = U6({"c": 4, "d": 4, "e": 6, "f": 5, "g": 4, "j": 2, "k": 4, "m": 4, "o": 4})
    print(f"    sqWord(fiveSigMark, stageX, blindCoreY) = {L.rsqWord(L.FIVE_SIG, L.STAGE_X, y0)}")
    print(f"    its a0 = a1 residue                     = "
          f"{L.rsqWord(L.rmul(L.FIVE_SIG, L.STAGE_X), L.STAGE_X, y0)}")

    print("\n" + "=" * 78)
    print("VERDICT: MEASURED, NOT PROVED.  No h = 0 class-five separation was found.")
    print("This is an open question; the Lean file proves nothing about it.")


if __name__ == "__main__":
    main()
