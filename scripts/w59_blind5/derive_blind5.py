"""W59-BLIND5: the two closed-form derivations the class-five blindness theorems need.

Sections
  1  validation of the transcribed U_6 law against honest 6 x 6 matrices
  2  the (4,6) row of the core word, for an arbitrary sigma slot        [theorem (a)]
  3  the coupling coefficient is the committed `sigFourH`               [theorem (a)]
  4  the forced parity of the handle block's (4,6) coordinate           [theorem (a)]
  5  the twelve rows of class <= 3 on the class-two-forced gauge        [theorem (b)]
  6  the three rows that CAN be odd there, with a witness over Z/8      [theorem (b)]
  7  sharpness: which gauge hypotheses each row actually consumes

Run:  python3 scripts/w59_blind5/derive_blind5.py > scripts/w59_blind5/results/derive_blind5.txt

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

import itertools
import random
import sys

from sympy import Poly, Symbol, expand, prod, symbols

sys.path.insert(0, __file__.rsplit("/", 1)[0])

from u6lib import NAMES, ONE, SIG_FIVE, U6, check_group_law, commP, conjP, inv, mul, pw, sym  # noqa: E402
from u6lib import sqWord, sqWord_matrix  # noqa: E402

CHECKS = []


def check(name, ok):
    CHECKS.append((name, bool(ok)))
    print(f"  [{'ok ' if ok else 'FAIL'}] {name}")


def halve(expr):
    """Return `expr / 2` as a polynomial over Z, or None if `expr` is not even."""
    e = expand(expr)
    p = Poly(e, *sorted(e.free_symbols, key=str)) if e.free_symbols else None
    if p is None:
        return e / 2 if e % 2 == 0 else None
    for co in p.coeffs():
        if co % 2 != 0:
            return None
    return expand(e / 2)


print("=" * 78)
print("W59-BLIND5  derive_blind5.py   exact integer arithmetic, no floating point")
print("=" * 78)

# ---------------------------------------------------------------- 1 validation
print("\n## 1  The transcribed U_6 law against honest 6 x 6 matrices\n")

rng = random.Random(59059)
good, bad = check_group_law(rng, trials=400)
check(f"coordinate law vs 6x6 matrices: {good} comparisons, {bad} mismatches", bad == 0)

bad = 0
for _ in range(60):
    s = U6({k: rng.randrange(-4, 5) for k in NAMES})
    x = U6({k: rng.randrange(-4, 5) for k in NAMES})
    y = U6({k: rng.randrange(-4, 5) for k in NAMES})
    if sqWord(s, x, y) != sqWord_matrix(s, x, y):
        bad += 1
check(f"sqWord: coordinate route vs honest matrix route, 60 markings, {bad} mismatches",
      bad == 0)

# ------------------------------------------------------- 2 the (4,6) core row
print("\n## 2  The (4,6) row of the core word, arbitrary sigma slot\n")

S, X, Y = sym("s"), sym("x"), sym("y")
W = sqWord(S, X, Y)

claim_i = (-4 * X.i + 2 * Y.i
           + (S.d * X.e - S.e * X.d + 10 * (X.d * X.e) - 8 * (X.d * Y.e) + Y.d * Y.e))
check("sqWord_i  =  -4 x.i + 2 y.i + (s.d x.e - s.e x.d + 10 x.d x.e - 8 x.d y.e + y.d y.e)",
      expand(W.i - claim_i) == 0)
print("      W.i =", expand(W.i))

claim_f = (-4 * X.f + 2 * Y.f
           + (S.a * X.b - S.b * X.a + 10 * (X.a * X.b) - 8 * (X.a * Y.b) + Y.a * Y.b))
check("...and it is the committed sqWord_f with (a,b,f) -> (d,e,i)", expand(W.f - claim_f) == 0)

Wsig = sqWord(SIG_FIVE, X, Y)
check("at the committed sigma slot the s-term drops: W.i = -4x.i+2y.i+10x.d x.e-8x.d y.e+y.d y.e",
      expand(Wsig.i - (-4 * X.i + 2 * Y.i + 10 * (X.d * X.e) - 8 * (X.d * Y.e) + Y.d * Y.e)) == 0)
print("\n  NOTE-CHECK  w58-sigma5-note.md section 4.2 prints")
print("      W_46 = -4x_46 + 2y_46 + 10 x_45 x_56 - 8 x_45 y_56 + y_45 y_56")
print("  which is the sigma slot E_23 instance.  At an ARBITRARY sigma slot the row")
print("  carries the extra pairing  s_45 x_56 - s_56 x_45,  which is not forced even by")
print("  the relator's abelian rows.  See section 4 for a certified counterexample.")

# ------------------------------------------- 3 the coupling coefficient is sigFourH
print("\n## 3  The coupling coefficient is the committed class-four functional sigFourH\n")

V = sym("v")
dressed = sqWord(mul(S, V), X, Y)
resp_j = expand(dressed.j - W.j)
claim_j = expand(V.a * X.g - V.g * X.a + V.f * X.c - V.c * X.f - S.b * (V.a * X.c + V.c * X.a))
# the committed `SqU6.sqWord_j_dress` holds on the nu'-gauge x.b = y.b = v.b = 0
gauge0 = {Symbol("xb"): 0, Symbol("yb"): 0, Symbol("vb"): 0}
check("sqWord_j_dress reproduced on the nu'-gauge",
      expand(resp_j.subs(gauge0) - claim_j.subs(gauge0)) == 0)

# GradedSigmaFour.sigFourH v x = v.a*(x.f - x.c) - v.c*(x.a + x.e) + v.e*x.c - v.f*x.a
# through toU5L: SqU5 (a,b,c,d,e,f,g,h,i,j) = SqU6 (a,b,c,d,f,g,h,j,k,m)
sigFourH_toU5L = (V.a * (X.g - X.c) - V.c * (X.a + X.f) + V.f * X.c - V.g * X.a)
check("sqWord_j_dress at the sigma slot E_23  =  sigFourH (toU5L v) (toU5L x)",
      expand(claim_j.subs({Symbol("sb"): 1}) - sigFourH_toU5L) == 0)

# ------------------------------------------- 4 the forced parity of the block
print("\n## 4  The handle block's (4,6) coordinate at a relator-killing marking\n")

print("  relator row i :  (W*H).i = W.i + H.i + W.d * H.e = W.i + H.i   (H.e = 0)")
print("  so  H.i = -W.i.  Abelian rows d, e of the relator give  -4x.d+2y.d = 0,")
print("  -4x.e+2y.e = 0, which over Z/8 force y.d and y.e even; then")
print("      W.i = -4x.i + 2y.i + s.d x.e - s.e x.d + 10 x.d x.e - 8 x.d y.e + y.d y.e")
print("  is even as soon as  s.d x.e - s.e x.d  is.")

# the counterexample to the sigma-slot-free reading, over Z/8
found = None
for sd, se, xd, xe, yd, ye in itertools.product(range(8), repeat=6):
    if (-4 * xd + 2 * yd) % 8 or (-4 * xe + 2 * ye) % 8:
        continue
    val = (sd * xe - se * xd + 10 * xd * xe - 8 * xd * ye + yd * ye) % 8
    if val % 2 == 1:
        found = (sd, se, xd, xe, yd, ye, val)
        break
check("over Z/8 the abelian rows alone do NOT force W.i even at an arbitrary sigma slot",
      found is not None)
print(f"      witness (s.d,s.e,x.d,x.e,y.d,y.e) = {found[:6]},  W.i core term = {found[6]} (odd)")

cnt = 0
for sd, se, xd, xe, yd, ye in itertools.product(range(8), repeat=6):
    if (-4 * xd + 2 * yd) % 8 or (-4 * xe + 2 * ye) % 8:
        continue
    cnt += 1
    if sd == 0 and se == 0:
        val = (10 * xd * xe - 8 * xd * ye + yd * ye) % 8
        assert val % 2 == 0
check(f"...but with s.d = s.e = 0 it is even at every one of the {cnt // 64} (x,y) solutions",
      True)

# ------------------------------------------- 5 the twelve rows on the gauge
print("\n## 5  The class-five gauge parity theorem: the twelve rows of class <= 3\n")

xa, xc, xd, xe, xf, xg, xh, xi = symbols("XA XC XD XE XF XG XH XI")
ya, yc, yd, ye = symbols("YA YC YD YE")

GAUGE = {
    Symbol("xa"): 2 * xa, Symbol("xb"): 0, Symbol("xc"): 2 * xc, Symbol("xd"): 2 * xd,
    Symbol("xe"): 2 * xe, Symbol("xf"): 2 * xf, Symbol("xg"): 2 * xg, Symbol("xh"): 2 * xh,
    Symbol("xi"): 2 * xi,
    Symbol("ya"): 2 * ya, Symbol("yb"): 0, Symbol("yc"): 2 * yc, Symbol("yd"): 2 * yd,
    Symbol("ye"): 2 * ye,
}

rows = {k: expand(Wsig.co[k].subs(GAUGE)) for k in NAMES}

LOWER = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l"]
halves = {}
for k in LOWER:
    hv = halve(rows[k])
    halves[k] = hv
    check(f"row {k} (class {'1' if k in 'abcde' else '2' if k in 'fghi' else '3'}) is even",
          hv is not None)
check("row b vanishes outright", expand(rows["b"]) == 0)

print("\n  the halves, for transcription into Lean:")
for k in LOWER:
    print(f"    {k} : {halves[k]}")

print("\n  the three top rows over Z (the class-four and class-five rows):")
for k in ["m", "n", "o"]:
    print(f"\n    {k} : {expand(rows[k])}")

print("\n  the same three reduced mod 2 (only odd-coefficient monomials kept):")
for k in ["m", "n", "o"]:
    e = expand(rows[k])
    p = Poly(e, *sorted(e.free_symbols, key=str))
    odd = sum(co % 2 * mon for co, mon in
              zip(p.coeffs(), [prod([g ** m for g, m in zip(p.gens, mono)])
                               for mono in p.monoms()]))
    print(f"    {k} : {expand(odd)}")

# ------------------------------------------- 6 the odd witness over Z/8
print("\n## 6  A gauge point at which all three of m, n, o are odd\n")


def eval_z8(xd_, yd_):
    x = U6(xd_)
    y = U6(yd_)
    w = sqWord(SIG_FIVE, x, y)
    return {k: int(w.co[k]) % 8 for k in NAMES}


# search over the deep coordinates the gauge leaves free
best = None
free_x = ["j", "k", "l", "m", "n", "o"]
free_y = ["f", "g", "h", "i", "j", "k", "l", "m", "n", "o"]
rng2 = random.Random(1959)
for _ in range(40000):
    xd_ = {k: rng2.randrange(0, 2) for k in free_x}
    yd_ = {k: rng2.randrange(0, 2) for k in free_y}
    r = eval_z8(xd_, yd_)
    if all(r[k] % 2 == 0 for k in LOWER) and all(r[k] % 2 == 1 for k in "mno"):
        w = sum(xd_.values()) + sum(yd_.values())
        if best is None or w < best[0]:
            best = (w, dict(xd_), dict(yd_), r)
check("a gauge point with all twelve lower rows even and all three top rows odd exists",
      best is not None)
if best:
    print(f"      x = {best[1]}")
    print(f"      y = {best[2]}")
    print(f"      sqWord rows mod 8 = {best[3]}")
    print("      x as a fifteen-tuple:",
          [int(U6(best[1]).co[k]) for k in NAMES])
    print("      y as a fifteen-tuple:",
          [int(U6(best[2]).co[k]) for k in NAMES])

# ------------------------------------------- 7 sharpness
print("\n## 7  Which gauge hypotheses each of the three non-quotient rows consumes\n")

for k in ["e", "i", "l"]:
    used = []
    for name, repl in GAUGE.items():
        partial = dict(GAUGE)
        del partial[name]
        if halve(expand(Wsig.co[k].subs(partial))) is None:
            used.append(str(name))
    print(f"    row {k}: needs {used if used else 'no gauge hypothesis at all'}")

print("\n  rows a,b,c,d,f,g,h,j,k are the nine lower rows of the LEFT U_5 quotient, and")
print("  toU5L(E_23) = sigFourMark, so GradedFourCleared.sqWord_sigFourMark_gauge_even")
print("  supplies them verbatim; only e, i, l need new work at class five.")

# ------------------------------------------- summary
print("\n" + "=" * 78)
ok = sum(1 for _, v in CHECKS if v)
print(f"{ok} of {len(CHECKS)} named checks passed, {len(CHECKS) - ok} failures")
print("=" * 78)
