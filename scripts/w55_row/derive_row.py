"""W55-ROW step 1: validate the library against the committed class-four facts, then derive
the displaced binder point.

Every committed statement of GradedSigmaFour / GradedFourHom that this lane leans on is
re-checked numerically here before anything new is derived.

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from u5lib import *

fails = 0


def check(name, got, want):
    global fails
    ok = (got == want)
    if not ok:
        fails += 1
    print(("PASS " if ok else "FAIL ") + name + ("" if ok else "  got %s want %s" % (got, want)))


print("== 1. library validation against committed GradedSigmaFour facts ==")
check("sqRelWord_sigFourWit_triv", sqRelWord(sigFourWit(ONE)), ONE)
check("sqRelWord_sigFourWit_V", sqRelWord(sigFourWit(sigFourV)), liftC(2))
check("sqRelWord_sigFourWit_U", sqRelWord(sigFourWit(sigFourU)), liftC(1))
check("sqRelWord_sigFourWit_V_complete",
      sqRelWord(sigLift(sigFourWit(sigFourV), ONE, ONE, liftC(7), ONE, ONE)), ONE)
check("sigFourX_eq", mul(sigFourV, (0, 0, 0, 0, 0, 0, 0, 0, 1, 6)), sigFourX)
check("commP(sigFourU,sigFourV)=1", commP(sigFourU, sigFourV), ONE)
check("sqWord(mark,X,Y)=1", sqWord(sigFourMark, sigFourX, sigFourY), ONE)
# the sigma reading, as a functional
for v in [sigFourU, sigFourV, sigFourX, sigFourY, (3, 0, 5, 2, 7, 1, 4, 6, 2, 5)]:
    vv = (v[0], 0) + tuple(v[2:])          # nu'-trivial: b = 0
    lhs = sqRelWord(sigFourWit(vv))[9]
    rhs = (sqRelWord(sigFourWit(ONE))[9] + sigFourRead(vv, sigFourX, sigFourY)) % N
    check("sqRelWord_sigFourDress j-row at v=%s" % (vv,), lhs, rhs)
    check("sqRelWord_sigFourDress g-row at v=%s" % (vv,), sqRelWord(sigFourWit(vv))[6],
          (sqRelWord(sigFourWit(ONE))[6] + sigFourG(vv, sigFourX)) % N)
    check("sqRelWord_sigFourDress h-row at v=%s" % (vv,), sqRelWord(sigFourWit(vv))[7],
          (sqRelWord(sigFourWit(ONE))[7] + sigFourH(vv, sigFourX)) % N)
    check("sqRelWord_sigFourDress i-row at v=%s" % (vv,), sqRelWord(sigFourWit(vv))[8],
          (sqRelWord(sigFourWit(ONE))[8] + sigFourI(vv, sigFourX)) % N)

print()
print("== 2. the pivot image P(c) = Phi(sqPivot) = sigma-slot * (x0-slot^c)^{-1} ==")


def pivot_image(S, X, c, n=N):
    """Phi(w) with w = sigma * x0^{-c}, using the flatTwo closed form for x0^c.

    Only valid when the six flatTwo conditions hold at X with obstruction 2*w0; we verify
    the closed form against honest repeated multiplication for the integer representatives
    of c below."""
    Xc = zpow_closed(X, c, n)
    return mul(S, inv(Xc, n), n)


def zpow_closed(X, c, n=N):
    """The flatTwo closed form of X^c: linear in c except for the class-four coordinate,
    which carries (c^2 - c) * w0 with 2*w0 the class-four obstruction."""
    a, b, cc, d, e, f, g, h, i, j = X
    ob = (a * i + e * g + h * d) % n
    assert ob % 2 == 0, "class-four obstruction must be even"
    w0 = ob // 2
    assert (a * b) % n == 0 and (b * cc) % n == 0 and (cc * d) % n == 0
    assert (a * f + e * cc) % n == 0 and (b * g + f * d) % n == 0
    return red((c * a, c * b, c * cc, c * d, c * e, c * f, c * g, c * h, c * i,
                c * j + (c * c - c) * w0), n)


# validate zpow_closed against honest repeated multiplication for every residue of c
for c in range(N):
    check("zpow_closed(sigFourX,%d)" % c, zpow_closed(sigFourX, c), power(sigFourX, c))

for c in range(N):
    P = pivot_image(sigFourMark, sigFourX, c)
    want = red((-(2 * c), 1, 0, 0, 0, 0, 0, 0, -c, c * c + c))
    check("sigFourHom_sqPivot closed form at c=%d" % c, P, want)

print()
print("== 3. the displaced binder point ==")
rowS = sigFourMark
rowX = sigFourX
rowY = sigFourY
rowU = (0, 0, 0, 1, 0, 0, 0, 0, 0, 0)
rowV0 = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)          # = sigFourU: the cleared V-letter


def rowFourV(c, n=N):
    return mul(rowV0, pivot_image(rowS, rowX, c, n), n)


def rowFourMark(c, n=N):
    """The marking on the five generators: the v-slot is displaced by the pivot."""
    return [rowS, rowX, rowY, rowU, rowFourV(c, n)]


def rowFourWit(v, n=N):
    """The frame image at sigma-dressing value v: the v-slot is the CLEARED letter."""
    return [mul(rowS, v, n), rowX, rowY, rowU, rowV0]


for c in range(N):
    check("rowFourV closed form at c=%d" % c, rowFourV(c),
          red((1 - 2 * c, 1, 0, 0, 1, 0, 0, 0, -c, c * c)))
    check("sqRelWord(rowFourMark) = 1 at c=%d" % c, sqRelWord(rowFourMark(c)), ONE)

check("sqRelWord(rowFourWit 1) = 1", sqRelWord(rowFourWit(ONE)), ONE)

print()
print("== 4. the three verdicts at the displaced point ==")
rowV0sq = mul(rowV0, rowV0)
check("rowV0^2", rowV0sq, sigFourV)
check("verdict trivial", sqRelWord(rowFourWit(ONE)), ONE)
check("verdict V0^2 (chi_a = 2)", sqRelWord(rowFourWit(rowV0sq)), liftC(2))
check("verdict V0   (chi_a = 1)", sqRelWord(rowFourWit(rowV0)), liftC(1))
check("verdict U    (chi_a = 0)", sqRelWord(rowFourWit(rowU)), ONE)
check("V0^2 dies to one gamma_4 move",
      sqRelWord(sigLift(rowFourWit(rowV0sq), ONE, ONE, liftC(7), ONE, ONE)), ONE)

print()
print("== 5. the reading at the displaced point is the same functional ==")
for v in [ONE, rowU, rowV0, rowV0sq, (5, 0, 0, 4, 2, 0, 3, 7, 6, 1)]:
    check("read(%s) = v.a - 2 v.g - 2 v.i" % (v,), sigFourRead(v, rowX, rowY),
          (v[0] - 2 * v[6] - 2 * v[8]) % N)
    check("relator j-row at v=%s" % (v,), sqRelWord(rowFourWit(v))[9],
          sigFourRead(v, rowX, rowY))

print()
print("== 6. class-three blindness at the displaced point ==")
for nm, v in [("triv", ONE), ("V0^2", rowV0sq), ("V0", rowV0), ("U", rowU)]:
    r = sqRelWord(rowFourWit(v))
    check("toU4L trivial at %s" % nm, (r[0], r[1], r[2], r[4], r[5], r[7]), (0,) * 6)
    check("toU4R trivial at %s" % nm, (r[1], r[2], r[3], r[5], r[6], r[8]), (0,) * 6)

print()
print("== 7. the b-column is the uncleared row nuSel 1 0 0 1 ==")
# b-column of the marking against gr3Pi(toAdd(nu'(gen)));  nu' = nuSel 1 0 0 1
nu_row = [1, 0, 0, 0, 1]
for c in range(N):
    m = rowFourMark(c)
    check("b-column at c=%d" % c, [s[1] for s in m], nu_row)

print()
print("TOTAL FAILURES: %d" % fails)
sys.exit(1 if fails else 0)
