"""W61-BLOCK, part 1: derive the block reading symbolically and certify its parity law.

Sections
--------
1  the `U_6` coordinate law against honest `6 x 6` matrices (imported certification);
2  the `(4,6)` row of the core word at an arbitrary sigma slot, symbolically over `Z`;
3  ⭐⭐ THE BLOCK PARITY LAW, checked EXHAUSTIVELY over `ZMod 8`;
4  the class-five bit collapse, symbolically;
5  the class-two corner: which quotient can express the law.

Run: `python3 scripts/w61_block/derive_block.py > scripts/w61_block/results/derive_block.txt`
"""

import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "w59_blind5"))

from sympy import Symbol, expand  # noqa: E402

import u6lib  # noqa: E402
from u6lib import NAMES, U6, check_group_law, sqWord, sqWord_matrix, sym  # noqa: E402

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok)))
    print(f"[{'ok ' if ok else 'FAIL'}] {name}{('  ' + detail) if detail else ''}")


rng = random.Random(61061)

print("=" * 86)
print("W61-BLOCK  derive_block.py   the handle block's (4,6) coordinate, and what pins it")
print("=" * 86)

# ---------------------------------------------------------------------------------------
print("\n## 1  the coordinate law against honest 6 x 6 matrices\n")

good, bad = check_group_law(rng, trials=400)
check("U_6 coordinate law vs honest matrices", bad == 0, f"{good} comparisons, {bad} mismatches")

mm = 0
for _ in range(60):
    s = U6({k: rng.randrange(-4, 5) for k in NAMES})
    x = U6({k: rng.randrange(-4, 5) for k in NAMES})
    y = U6({k: rng.randrange(-4, 5) for k in NAMES})
    if sqWord_matrix(s, x, y) != sqWord(s, x, y):
        mm += 1
check("sqWord by both routes", mm == 0, f"60 markings, {mm} mismatches")

# ---------------------------------------------------------------------------------------
print("\n## 2  the (4,6) row of the core word, at an ARBITRARY sigma slot\n")

S, X, Y = sym("s"), sym("x"), sym("y")
W = sqWord(S, X, Y)

closed_i = (-4 * X.i + 2 * Y.i
            + (S.d * X.e - S.e * X.d + 10 * (X.d * X.e) - 8 * (X.d * Y.e) + Y.d * Y.e))
check("W.i closed form (= Lean `SqU6.sqWord_i`)", expand(W.i - closed_i) == 0)
print("    W_46 = -4*x_46 + 2*y_46 + (s_45*x_56 - s_56*x_45)")
print("                            + 10*x_45*x_56 - 8*x_45*y_56 + y_45*y_56")
print()
print("    the sigma pairing  s_45*x_56 - s_56*x_45  is the ONLY term the wave-58 note dropped")
print("    (it computed at sigma = E_23, where s_45 = s_56 = 0).")

# the two abelian rows of the core word, for the record
check("W.d abelian row", expand(W.d - (-4 * X.d + 2 * Y.d)) == 0)
check("W.e abelian row", expand(W.e - (-4 * X.e + 2 * Y.e)) == 0)

# ---------------------------------------------------------------------------------------
print("\n## 3  THE BLOCK PARITY LAW, exhaustively over ZMod 8\n")
print("    claim:  at every marking whose relator's (4,5)-row vanishes,")
print("            W_46  ==  s_45*x_56 - s_56*x_45   (mod 2).")
print("    W.i depends on exactly eight coordinates: s.d s.e x.d x.e x.i y.d y.e y.i,")
print("    and the (4,5)-row `-4*x.d + 2*y.d = 0` pins y.d to one of two values per x.d.")

bad = 0
tot = 0
for xd in range(8):
    for yd in range(8):
        if (-4 * xd + 2 * yd) % 8 != 0:
            continue
        for sd in range(8):
            for se in range(8):
                for xe in range(8):
                    for ye in range(8):
                        for xi in range(8):
                            for yi in range(8):
                                wi = (-4 * xi + 2 * yi + sd * xe - se * xd
                                      + 10 * xd * xe - 8 * xd * ye + yd * ye) % 8
                                blk = (sd * xe - se * xd) % 8
                                tot += 1
                                if (wi - blk) % 2 != 0:
                                    bad += 1
check("block parity law, EXHAUSTIVE on ZMod 8", bad == 0, f"{tot} points, {bad} failures")

print("\n    …and it needs only the (4,5)-row.  Dropping it:")
bad0 = 0
for xd in range(8):
    for yd in range(8):
        for xe in range(8):
            for ye in range(8):
                wi = (10 * xd * xe - 8 * xd * ye + yd * ye) % 8
                if wi % 2 != 0:
                    bad0 += 1
check("…and WITHOUT the (4,5)-row it FAILS", bad0 > 0, f"{bad0} of 4096 correction terms odd")

print("\n    the (5,6)-row does the same job by symmetry:")
bad1 = 0
for xe in range(8):
    for ye in range(8):
        if (-4 * xe + 2 * ye) % 8 != 0:
            continue
        for xd in range(8):
            for yd in range(8):
                wi = (10 * xd * xe - 8 * xd * ye + yd * ye) % 8
                if wi % 2 != 0:
                    bad1 += 1
check("block parity law from the (5,6)-row instead", bad1 == 0)

# the exact integral form, not merely the parity
print("\n    the exact form, over ZMod 8, with y_45 = 2*k:")
bad2 = 0
for xd in range(8):
    for k in range(8):
        yd = (2 * k) % 8
        for sd in range(8):
            for se in range(8):
                for xe in range(8):
                    for ye in range(8):
                        for xi in range(8):
                            for yi in range(8):
                                wi = (-4 * xi + 2 * yi + sd * xe - se * xd
                                      + 10 * xd * xe - 8 * xd * ye + yd * ye) % 8
                                blk = (sd * xe - se * xd) % 8
                                wit = (-2 * xi + yi + 5 * xd * xe - 4 * xd * ye + k * ye) % 8
                                if (wi - blk - 2 * wit) % 8 != 0:
                                    bad2 += 1
check("exact witness  W_46 = blockRead + 2*(-2x_46 + y_46 + 5x_45x_56 - 4x_45y_56 + k*y_56)",
      bad2 == 0)

# ---------------------------------------------------------------------------------------
print("\n## 4  the class-five bit collapse, symbolically\n")

V = sym("v")
# the coupling GradedFive.SqU6.sqWord_j_dress produces
cpl = (V.a * X.g - V.g * X.a + V.f * X.c - V.c * X.f
       - S.b * (V.a * X.c + V.c * X.a))
SV = u6lib.mul(S, V)
dj = expand(sqWord(SV, X, Y).j - W.j)
check("sqWord_j_dress at v.b = x.b = y.b = 0",
      expand((dj - cpl).subs({Symbol("vb"): 0, Symbol("xb"): 0, Symbol("yb"): 0})) == 0)

print("    so, from GradedFive.SqU6.sqRelWord_sigFiveDress_o,")
print()
print("      Delta_v (relator top row) - Delta_v (core top row)  =  coupling(v,s,x) * H_46")
print()
print("    and section 3 pins  H_46 = -W_46 == -(s_45 x_56 - s_56 x_45)  (mod 2).  Hence")
print()
print("      selPar[ Delta_v relator.o ]  =  selPar[ Delta_v coreword.o ]")
print("                                    + selPar[ coupling(v,s,x) ] * selPar[ blockRead(s,x) ]")
print()
print("    ⭐⭐ every symbol on the right is a CORE slot.  The handle letters are gone.")

# ---------------------------------------------------------------------------------------
print("\n## 5  which quotient can express the law\n")

print("    blockRead(s,x) = s.d*x.e - s.e*x.d  and  H_46  use coordinates d, e, i only.")
print("    toU5L keeps (a,b,c,d,f,g,h,j,k,m):  e and i are DROPPED  -> cannot express it.")
print("    toU5R keeps (b,c,d,e,g,h,i,k,l,n):  d, e, i all present  -> CAN express it.")
print("    toU4RR keeps (c,d,e,h,i,l):         d, e, i all present  -> CAN express it.")
print()
print("    but toU5R carries the class-five sigma marking E_23 = <b=1> to <a=1> in SqU5,")
print("    NOT to sigFourMark = <b=1>.  So the corner that can see the block is not the")
print("    corner any committed sigma instrument is built on.")
lhs = set("de i".replace(" ", ""))
check("blockRead lives in the toU5R corner", lhs <= set("bcdeghikln"))
check("blockRead does NOT live in the toU5L corner", not (lhs <= set("abcdfghjkm")))

# ---------------------------------------------------------------------------------------
print("\n" + "=" * 86)
okc = sum(1 for _, o in CHECKS if o)
print(f"{okc} of {len(CHECKS)} checks passed, {len(CHECKS) - okc} failures")
print("=" * 86)
sys.exit(0 if okc == len(CHECKS) else 1)
