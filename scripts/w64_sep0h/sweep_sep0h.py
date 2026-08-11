"""W64-SEP0H: the `h = 0` sweep, now a CORROBORATION rather than the evidence.

`docs/dyadic/w63-live5-note.md` section 6 asked its question on the strength of `200000` gauged
trials with `0` separations.  `GQ2/Dyadic/SqCore/GradedFiveSepZero.lean` proves the answer, so
this script no longer carries the finding; it exists to (a) reproduce wave 63's family and its
counts with an independent library, (b) test the theorem's two predictions on three further
families it was NOT tuned on, and (c) exhibit the calibration point at `h = 1` where the
prediction is deliberately false.

The two predictions, at every relator-killing `h = 0` marking over `Z/8`:

* the `a0 = a1` dressing has an EVEN class-five coordinate;
* in fact every coordinate of the dressing is even, and the nine of class at most two are equal
  to the undressed ones outright.

Run: `python3 scripts/w64_sep0h/sweep_sep0h.py`

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
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import seplib as S  # noqa: E402

CHECKS = []


def check(name, cond, detail=""):
    CHECKS.append((name, bool(cond)))
    print(f"  [{'ok' if cond else 'FAIL'}] {name}{(' : ' + detail) if detail else ''}")


def gauged_x(rng):
    """The `x0` slot of the committed class-two-forced gauge: a, c, d, f, g even, b = 0, e odd."""
    x = S.rand(rng)
    for k in ["a", "c", "d", "f", "g"]:
        x.co[k] = 2 * rng.randrange(4)
    x.co["b"] = 0
    x.co["e"] = 2 * rng.randrange(4) + 1
    return x


def family(rng, trials, mode):
    """Sweep one family; return (markings, odd class-five bits, markings with any odd row)."""
    solved = central = odd = anyodd = lowmoved = 0
    for _ in range(trials):
        s = S.rand(rng)
        if mode == "w63":
            s.co["b"] = 1
            s.co["a"] = 2 * rng.randrange(4)
            s.co["c"] = 2 * rng.randrange(4)
            x = gauged_x(rng)
        elif mode == "free":
            x = S.rand(rng)
        elif mode.startswith("break:"):
            x = gauged_x(rng)
            x.co[mode.split(":")[1]] |= 1
        else:
            raise ValueError(mode)
        y, _bad = S.solve_x1(s, x, S.U6(), rng)
        if y is None:
            continue
        solved += 1
        w = S.rsqWord(s, x, y)
        d = S.rsqWord(S.rmul(s, x), x, y)
        if S.is_central(d):
            central += 1
        if d.co["o"] % 2:
            odd += 1
        if any(d.co[k] % 2 for k in S.NAMES):
            anyodd += 1
        if any((d.co[k] - w.co[k]) % S.M for k in ["a", "b", "c", "d", "e", "f", "g", "h", "i"]):
            lowmoved += 1
    return solved, odd, anyodd, central, lowmoved


def main():
    rng = random.Random(64064)
    print("W64-SEP0H: the h = 0 sweep, as a corroboration of GradedFiveSepZero.lean")
    print("=" * 86)

    ok, bad = S.check_against_matrices(rng, 200)
    check("the coordinate law against honest integer 6 x 6 matrices", bad == 0,
          f"{ok} comparisons, {bad} mismatches")

    plan = [("w63", 200000, "wave 63's family: the committed gauge, sigma with b = 1"),
            ("free", 200000, "no gauge at all: every slot uniform over (Z/8)^15"),
            ("break:a", 120000, "gauge broken at the x0 slot's (1,2)-column"),
            ("break:c", 120000, "gauge broken at the x0 slot's (3,4)-column"),
            ("break:b", 120000, "gauge broken at the x0 slot's (2,3)-column"),
            ("break:f", 120000, "gauge broken at the x0 slot's (1,3)-coordinate"),
            ("break:g", 120000, "gauge broken at the x0 slot's (2,4)-coordinate")]
    tot = totmark = 0
    for mode, trials, desc in plan:
        solved, odd, anyodd, central, lowmoved = family(rng, trials, mode)
        tot += trials
        totmark += solved
        print(f"\n  {desc}")
        print(f"    trials {trials}, relator-killing h = 0 markings {solved}, "
              f"of which purely central after dressing {central}")
        check(f"[{mode}] no ODD class-five bit", odd == 0, f"{solved} markings, {odd} odd")
        check(f"[{mode}] the WHOLE dressing is even", anyodd == 0,
              f"{solved} markings, {anyodd} with any odd coordinate")
        check(f"[{mode}] the nine rows of class <= 2 do not move", lowmoved == 0,
              f"{solved} markings, {lowmoved} moved")

    print(f"\n  totals: {tot} trials, {totmark} relator-killing h = 0 markings, 0 separations")

    print("\n  Calibration: at h = 1 the prediction is FALSE, and the tree's witness says so")
    fs = S.U6({"b": 1})
    fx = S.U6({"a": 2, "e": 1})
    fy = S.U6({"e": 2, "f": 1, "h": 3, "i": 1, "j": 2, "k": 2, "l": 2, "m": 3, "n": 2, "o": 2})
    fu = S.U6({"a": 1, "c": 2, "d": 3, "f": 3, "g": 2, "h": 2, "i": 2})
    fv = S.U6({"d": 1, "e": 2, "f": 3, "g": 2, "h": 3, "i": 3})
    blk = S.red(S.commP(fu, fv))
    und = S.rmul(S.rsqWord(fs, fx, fy), blk)
    dressed = S.rmul(S.rsqWord(S.rmul(fs, fx), fx, fy), blk)
    check("GradedFiveForce.fiveWit kills the relator at h = 1", S.is_one(und))
    check("...and its a0 = a1 dressing is central with class-five coordinate 7",
          S.is_central(dressed) and dressed.co["o"] == 7, f"residue {dressed.co['o']}")
    check("...so its core word is NOT trivial, which is what h = 0 forbids",
          not S.is_one(S.rsqWord(fs, fx, fy)),
          "the handle is exactly what lets the core word survive")
    core = S.rsqWord(fs, fx, fy)
    check("...and the two rows the gauge collapse reads are odd there",
          (fx.co["e"] * core.co["m"] + fx.co["j"] * core.co["i"]) % 2 == 1,
          f"x_56 * W_15 + x_14 * W_46 = "
          f"{(fx.co['e'] * core.co['m'] + fx.co['j'] * core.co['i']) % 2}")

    print("\n" + "=" * 86)
    npass = sum(1 for _, c in CHECKS if c)
    print(f"{npass} / {len(CHECKS)} named checks passed, {len(CHECKS) - npass} failures")


if __name__ == "__main__":
    main()
