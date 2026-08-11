"""W63-SECOND, part 1: derive the second block reading and certify its parity law.

Sections
--------
1  anchors: the `U_6` coordinate law and `sqWord` against honest `6 x 6` matrices;
2  ⭐ ALL FOUR class-two rows of the core word, symbolically over `Z`, at an arbitrary sigma
   slot: they have the SAME shape, so the `(3,5)` row is a reading exactly as the `(4,6)` row
   is;
3  ⭐⭐ THE SECOND BLOCK PARITY LAW, checked EXHAUSTIVELY over `ZMod 8`, with its controls;
4  the `(5,6)`-row variant of wave 61's FIRST block equation (the cheap item of
   `docs/dyadic/w61-block-note.md` section 6.3);
5  the relator rows: no cross term at any class-two row, and the block coordinate is the sum of
   the handles' wedges, checked against honestly collected relators;
6  ⭐ which quotient can express the second law, and the answer differs from wave 61's;
7  ⚠ the corner symmetry, precisely: the flip pairs `(1,3)` with `(4,6)` and `(2,4)` with
   `(3,5)`, so the second reading is NOT the flip image of the first.

Run: `python3 scripts/w63_second/derive_second.py > scripts/w63_second/results/derive_second.txt`

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

from sympy import Symbol, expand, zeros  # noqa: E402

import secondlib  # noqa: E402
from secondlib import (  # noqa: E402
    COL_ENTRY, ROWS, ROW_ENTRY, U6, collect, handle_block, minor_sum,
)
from u6lib import CELL, NAMES, check_group_law, sqWord, sqWord_matrix, sym  # noqa: E402

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok)))
    print(f"[{'ok ' if ok else 'FAIL'}] {name}{('  ' + detail) if detail else ''}")


rng = random.Random(63063)

print("=" * 86)
print("W63-SECOND  derive_second.py   the (3,5) block reading, and the family it belongs to")
print("=" * 86)

# ---------------------------------------------------------------------------------------
print("\n## 1  anchors\n")

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
print("\n## 2  ALL FOUR class-two rows of the core word, at an ARBITRARY sigma slot\n")

S, X, Y = sym("s"), sym("x"), sym("y")
W = sqWord(S, X, Y)

print("    U_6 has four class-two coordinates, and each is the wedge of the two abelian")
print("    columns beneath it.  The claim is that the core word has the SAME shape at all")
print("    four, so the sigma pairing wave 61 read at (4,6) is one of four:")
print()
for row, (lo, hi) in ROWS.items():
    cand = (-4 * X.co[row] + 2 * Y.co[row]
            + (S.co[lo] * X.co[hi] - S.co[hi] * X.co[lo]
               + 10 * (X.co[lo] * X.co[hi]) - 8 * (X.co[lo] * Y.co[hi])
               + Y.co[lo] * Y.co[hi]))
    ok = expand(W.co[row] - cand) == 0
    check(f"W.{row} closed form, row {ROW_ENTRY[row]}, columns "
          f"{COL_ENTRY[lo]}/{COL_ENTRY[hi]}", ok)

print()
print("    In particular, the row this lane is about, spelled out in the campaign's naming:")
print()
print("      W_35 = -4*x_35 + 2*y_35 + (s_34*x_45 - s_45*x_34)")
print("                              + 10*x_34*x_45 - 8*x_34*y_45 + y_34*y_45")
print()
print("    which is the committed `SqU6.sqWord_i` with (d, e, i) replaced by (c, d, h),")
print("    and the committed `SqU6.sqWord_f` with (a, b, f) replaced by (c, d, h).")
print()
print("    ⭐⭐ THE SECOND BLOCK READING is the bracket:  blockReadCD(s, x) = s_34*x_45 - s_45*x_34.")

# the two abelian rows this reading needs, for the record
check("W.c abelian row", expand(W.c - (-4 * X.c + 2 * Y.c)) == 0)
check("W.d abelian row", expand(W.d - (-4 * X.d + 2 * Y.d)) == 0)

# ---------------------------------------------------------------------------------------
print("\n## 3  THE SECOND BLOCK PARITY LAW, exhaustively over ZMod 8\n")
print("    claim:  at every marking whose relator's (3,4)-row vanishes,")
print("            W_35  ==  s_34*x_45 - s_45*x_34   (mod 2).")
print("    W.h depends on exactly eight coordinates: s.c s.d x.c x.d x.h y.c y.d y.h,")
print("    and the (3,4)-row `-4*x.c + 2*y.c = 0` pins y.c to one of two values per x.c.")

bad = 0
tot = 0
for xc in range(8):
    for yc in range(8):
        if (-4 * xc + 2 * yc) % 8 != 0:
            continue
        for sc in range(8):
            for sd in range(8):
                for xd in range(8):
                    for yd in range(8):
                        for xh in range(8):
                            for yh in range(8):
                                wh = (-4 * xh + 2 * yh + sc * xd - sd * xc
                                      + 10 * xc * xd - 8 * xc * yd + yc * yd) % 8
                                blk = (sc * xd - sd * xc) % 8
                                tot += 1
                                if (wh - blk) % 2 != 0:
                                    bad += 1
check("second block parity law, EXHAUSTIVE on ZMod 8", bad == 0,
      f"{tot} points, {bad} failures")

print("\n    …and it needs the abelian row.  Dropping it:")
bad0 = 0
for xc in range(8):
    for yc in range(8):
        for xd in range(8):
            for yd in range(8):
                wh = (10 * xc * xd - 8 * xc * yd + yc * yd) % 8
                if wh % 2 != 0:
                    bad0 += 1
check("…and WITHOUT the (3,4)-row it FAILS", bad0 > 0,
      f"{bad0} of 4096 correction terms odd")

print("\n    the (4,5)-row does the same job for this reading, by the same symmetry:")
bad1 = 0
for xd in range(8):
    for yd in range(8):
        if (-4 * xd + 2 * yd) % 8 != 0:
            continue
        for xc in range(8):
            for yc in range(8):
                wh = (10 * xc * xd - 8 * xc * yd + yc * yd) % 8
                if wh % 2 != 0:
                    bad1 += 1
check("second block parity law from the (4,5)-row instead", bad1 == 0)

print("\n    the exact form, over ZMod 8, with y_34 = 2*k:")
bad2 = 0
for xc in range(8):
    for k in range(8):
        yc = (2 * k) % 8
        for sc in range(8):
            for sd in range(8):
                for xd in range(8):
                    for yd in range(8):
                        for xh in range(8):
                            for yh in range(8):
                                wh = (-4 * xh + 2 * yh + sc * xd - sd * xc
                                      + 10 * xc * xd - 8 * xc * yd + yc * yd) % 8
                                blk = (sc * xd - sd * xc) % 8
                                wit = (-2 * xh + yh + 5 * xc * xd - 4 * xc * yd + k * yd) % 8
                                if (wh - blk - 2 * wit) % 8 != 0:
                                    bad2 += 1
check("exact witness  W_35 = blockReadCD + 2*(-2x_35 + y_35 + 5x_34x_45 - 4x_34y_45 + k*y_45)",
      bad2 == 0)

# the same identity symbolically over Z, which is the form the Lean lemma takes
K = Symbol("kk")
wit_h = expand(W.co["h"].subs(Y.co["c"], 2 * K)
               - (S.c * X.d - S.d * X.c)
               - 2 * (-2 * X.co["h"] + Y.co["h"] + 5 * (X.c * X.d) - 4 * (X.c * Y.d) + K * Y.d))
check("…and it is an identity over Z, not only over ZMod 8", wit_h == 0)

# ---------------------------------------------------------------------------------------
print("\n## 4  the (5,6)-row variant of wave 61's FIRST block equation\n")
print("    `docs/dyadic/w61-block-note.md` section 6.3 item 1, priced at one line in Lean:")
print("    the committed `SqU6.sqWord_i_eq_blockRead` uses the relator's (4,5)-row to force")
print("    y_45 even; the (5,6)-row forces y_56 even and does the same job.")

bad3 = 0
tot3 = 0
for xe in range(8):
    for k in range(8):
        ye = (2 * k) % 8
        for sd in range(8):
            for se in range(8):
                for xd in range(8):
                    for yd in range(8):
                        for xi in range(8):
                            for yi in range(8):
                                wi = (-4 * xi + 2 * yi + sd * xe - se * xd
                                      + 10 * xd * xe - 8 * xd * ye + yd * ye) % 8
                                blk = (sd * xe - se * xd) % 8
                                wit = (-2 * xi + yi + 5 * xd * xe - 8 * xd * k + k * yd) % 8
                                tot3 += 1
                                if (wi - blk - 2 * wit) % 8 != 0:
                                    bad3 += 1
check("(5,6)-row variant, exact witness, EXHAUSTIVE on ZMod 8", bad3 == 0,
      f"{tot3} points, {bad3} failures")

wit_i = expand(W.i.subs(Y.e, 2 * K)
               - (S.d * X.e - S.e * X.d)
               - 2 * (-2 * X.i + Y.i + 5 * (X.d * X.e) - 8 * (X.d * K) + K * Y.d))
check("…and it too is an identity over Z", wit_i == 0)

# ---------------------------------------------------------------------------------------
print("\n## 5  the relator's class-two rows, symbolically\n")
print("    The handle block's five abelian columns vanish, so the class-two rows of")
print("    `sqRelWord m = sqWord(m0,m1,m2) * handleWord` carry no cross term at any of the")
print("    four class-two coordinates: the `U_6` product law contributes `p.lo * q.hi` there,")
print("    and `q = handleWord` has `q.hi = 0`.  Hence `handleWord.row = -sqWord.row` at every")
print("    relator-killing marking, at all four rows.  Checked symbolically:")

HW = sym("t")
for row, (lo, hi) in ROWS.items():
    prod = secondlib.mul(W, U6({k: HW.co[k] for k in NAMES if k not in "abcde"}))
    check(f"no cross term at row {ROW_ENTRY[row]}",
          expand(prod.co[row] - W.co[row] - HW.co[row]) == 0)

print()
print("    The census against honestly collected relator-killing markings is section 1 of")
print("    `results/census_second.txt`; it is not repeated here.")

# ---------------------------------------------------------------------------------------
print("\n## 6  which quotient can express the second law\n")

u5l = set("abcdfghjkm")
u5r = set("bcdeghikln")
u4rr = set("cdehil")
print("    blockRead  (4,6) uses  d, e, i;   blockReadCD (3,5) uses  c, d, h.")
print("    toU5L keeps (a,b,c,d,f,g,h,j,k,m)")
print("    toU5R keeps (b,c,d,e,g,h,i,k,l,n)")
print("    toU4RR keeps (c,d,e,h,i,l)")
print()
check("blockRead does NOT live in the toU5L corner (wave 61)", not (set("dei") <= u5l))
check("blockRead lives in the toU5R corner (wave 61)", set("dei") <= u5r)
check("⭐ blockReadCD lives in the toU5L corner", set("cdh") <= u5l)
check("⭐ blockReadCD ALSO lives in the toU5R corner", set("cdh") <= u5r)
check("blockReadCD lives in the toU4RR corner too", set("cdh") <= u4rr)
print()
print("    ⭐ THE DIFFERENCE FROM WAVE 61.  `results/derive_block.txt` section 5 records that")
print("    the first reading survives only in the toU5R corner, and that toU5R carries the")
print("    class-five sigma marking E_23 = <b=1> to <a=1>, not to sigFourMark = <b=1>, so")
print("    'the corner that can see the block is not the corner any committed sigma instrument")
print("    is built on'.  The second reading survives in BOTH corners, and toU5L carries")
print("    E_23 = <b=1> to sigFourMark = <b=1> (`toU5L_fiveSigMark`, committed).  So the")
print("    second reading is expressible in the corner the committed sigma instruments live in,")
print("    and the first is not.  That is a structural difference, not a numerical one.")

# ---------------------------------------------------------------------------------------
print("\n## 7  the corner symmetry, precisely\n")
print("    `w61-block-note.md` section 6.3 says the (3,5) coordinate has 'the same shape as'")
print("    the (4,6) coordinate 'under the campaign's corner symmetry'.  Section 2 above")
print("    certifies the same-shape half directly, for all four rows at once.  The symmetry")
print("    half needs care, and this section is the correction.")
print()
print("    U_6's outer symmetry is the flip  p |-> J (p^{-1})^T J,  J the antidiagonal.")

Jm = zeros(6, 6)
for r in range(6):
    Jm[r, 5 - r] = 1


def flip(p):
    m = p.matrix()
    return U6.of_matrix(Jm * m.inv().T * Jm)


badf = 0
for _ in range(120):
    p = U6({k: rng.randrange(-4, 5) for k in NAMES})
    q = U6({k: rng.randrange(-4, 5) for k in NAMES})
    if flip(secondlib.mul(p, q)) != secondlib.mul(flip(p), flip(q)):
        badf += 1
    # the image really is unitriangular, so reading it back off the fifteen cells loses nothing
    raw = Jm * p.matrix().inv().T * Jm
    if raw != flip(p).matrix():
        badf += 1
check("the flip is an automorphism of U_6", badf == 0, f"120 pairs, {badf} failures")

# it is a group automorphism, so it commutes with every word map, sqWord included
badw = 0
for _ in range(20):
    s = U6({k: rng.randrange(-3, 4) for k in NAMES})
    x = U6({k: rng.randrange(-3, 4) for k in NAMES})
    y = U6({k: rng.randrange(-3, 4) for k in NAMES})
    if flip(sqWord(s, x, y)) != sqWord(flip(s), flip(x), flip(y)):
        badw += 1
check("…so it commutes with sqWord", badw == 0, f"20 markings, {badw} mismatches")

# the induced permutation on the nine coordinates that matter here
perm = {}
for k in ["a", "b", "c", "d", "e", "f", "g", "h", "i"]:
    r, c = CELL[k]
    tgt = [n for n, (r2, c2) in CELL.items() if (r2, c2) == (5 - c, 5 - r)][0]
    perm[k] = tgt
print()
print("    on entries it is  (i,j) |-> (7-j, 7-i), so on the campaign's names:")
print("      " + ",  ".join(f"{k} -> {perm[k]}" for k in
                            ["a", "b", "c", "d", "e", "f", "g", "h", "i"]))
check("the flip pairs the (1,3) and (4,6) rows", perm["f"] == "i" and perm["i"] == "f")
check("⚠ the flip pairs the (2,4) and (3,5) rows, NOT (3,5) with (4,6)",
      perm["g"] == "h" and perm["h"] == "g")
print()
print("    ⚠ SCOPE CORRECTION.  The second reading is therefore NOT the flip image of the")
print("    first: the flip image of the (4,6) reading is the (1,3) reading, and the flip image")
print("    of the (3,5) reading is the (2,4) reading.  The four readings fall into two")
print("    flip-orbits {(1,3),(4,6)} and {(2,4),(3,5)}, and the second reading is in the orbit")
print("    the campaign has never looked at.  Nothing about the second reading follows from")
print("    wave 61 by symmetry; everything here is derived.")

# ---------------------------------------------------------------------------------------
print("\n" + "=" * 86)
okc = sum(1 for _, o in CHECKS if o)
print(f"{okc} of {len(CHECKS)} checks passed, {len(CHECKS) - okc} failures")
print("=" * 86)
sys.exit(0 if okc == len(CHECKS) else 1)
