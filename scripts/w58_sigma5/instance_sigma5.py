"""W58-SIGMA5 step 2: the explicit class-five points.

  (A) the committed class-four witness, lifted coordinatewise: it already kills all FIFTEEN
      rows, at every handle count and every handle, and its class-five row is BLIND (every
      live coefficient of the reading vanishes there);
  (B) three points at which a single class-five channel is live, so that the class-five
      selection bit is one clean F_2-character of the sigma dressing - including v46, a
      character that does not exist at class four;
  (C) *** THE SEPARATING POINT: a marking, satisfying the whole class-two-forced gauge as
      `GradedSigmaFour` states it, at which the depth sweep's forced sigma dressing `a0 = a1`
      kills all fourteen lower rows and leaves the ODD class-five residue 7.  Class four is
      provably blind there (its own row of the dressed relator vanishes);
  (D) the handle-block audit at every point: the block enters the class-five response through
      exactly one coupling term, and that term is even at every relator-killing marking.

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'w57_cleared'))
from u6lib import *                                    # noqa: F403
import sigfive_forms as F
import u5lib as U5

fails = 0
checks = 0


def check(name, got, want=True):
    global fails, checks
    checks += 1
    ok = (got == want)
    if not ok:
        fails += 1
    print(("PASS " if ok else "FAIL ") + name + ("" if ok else "  got %s want %s" % (got, want)))


HS = [(h, j) for h in (1, 2, 3, 4) for j in range(h)]

sigFiveX = named(a=2, k=1)
sigFiveY = named(f=1, h=4, k=2)
sigFiveU = named(a=1)
sigFiveV = named(a=2)


def fiveWit(h, j, v):
    return mirTuple(h, j, mul(sigFiveMark, v), sigFiveX, sigFiveY, sigFiveU, sigFiveV)


# =======================================================================================
print("== A. the committed class-four witness, lifted ==")
check("the lift restricts to the committed sigFourX, sigFourY, sigFourU, sigFourV",
      (toU5L(sigFiveX), toU5L(sigFiveY), toU5L(sigFiveU), toU5L(sigFiveV)),
      (U5.sigFourX, U5.sigFourY, U5.sigFourU, U5.sigFourV))
ok = all(sqRelWord(fiveWit(h, j, ONE)) == ONE for h, j in HS)
check("all fifteen rows die at every handle count h = 1..4 and every handle", ok)
for nm, d, want in [("1", ONE, ONE), ("U (chi_a = 1)", sigFiveU, named(m=1)),
                    ("V (chi_a = 2)", sigFiveV, named(m=2))]:
    vals = {sqRelWord(fiveWit(h, j, d)) for h, j in HS}
    check("dressing by %-14s leaves %s at every (h, j)" % (nm, show(want)),
          vals, {want})
print("   -> the three committed verdicts are the class-four ones, in the (1,5) row; the")
print("      class-five row (1,6) is ZERO at all three: this point is class-five blind.")
check("the class-five row is blind here: every live coefficient of the reading vanishes",
      (sigFiveX[11] + sigFiveX[13], sigFiveX[12], sigFiveX[9]), (0, 0, 0))

# =======================================================================================
print()
print("== B. points where one class-five channel is live ==")
LIVE = [("v46 (a character class four does not have)", named(a=2, j=1), named(f=1, j=2), 8),
        ("v56 (the new outermost abelian column)", named(a=2, m=1), named(f=1, m=2), 4),
        ("v12 (the chi_a character, in the top row)", named(a=2, n=1), named(f=1, n=2, o=2), 0)]
random.seed(58)
for tag, X, Y, ch in LIVE:
    m0 = [sigFiveMark, X, Y, ONE, ONE]
    check("  relator dies at the %-42s point" % tag.split(' ')[0], sqRelWord(m0) == ONE)
    bad = 0
    for _ in range(4000):
        v = [random.randrange(8) for _ in range(15)]
        v[1] = 0
        v = tuple(v)
        R = sqRelWord([mul(sigFiveMark, v), X, Y, ONE, ONE])
        if R[14] % 2 != v[ch] % 2:
            bad += 1
    check("  the class-five bit is exactly selPar(v.%s), 4000 dressings"
          % COORDS[ch], bad, 0)
print("   -> class five reads characters of the sigma dressing that class four cannot: the")
print("      channel v46 lives on a matrix entry that U_5 does not have at all.")

# =======================================================================================
print()
print("== C. *** THE SEPARATING POINT: the sweep's `a0 = a1` dressing, decided ==")
sepU = (1, 0, 2, 3, 0, 3, 2, 2, 2, 0, 0, 0, 0, 0, 0)      # <a=1, c=2, d=3, f=3, g=2, h=2, i=2>
sepV = named(d=1, e=2, f=3, g=2, h=3, i=3)
sepX = named(a=2, e=1)
sepY = named(e=2, f=1, h=3, i=1, j=2, k=2, l=2, m=3, n=2, o=2)
print("   U  = %s" % show(sepU))
print("   V  = %s" % show(sepV))
print("   x0 = %s" % show(sepX))
print("   x1 = %s" % show(sepY))
print("   handle block [U, V] = %s   *** LIVE, and live at class four (x15 = 3)" % show(commP(sepU, sepV)))


def sepWit(h, j, v):
    return mirTuple(h, j, mul(sigFiveMark, v), sepX, sepY, sepU, sepV)


check("the undressed marking kills all fifteen rows, h = 1", sqRelWord(sepWit(1, 0, ONE)) == ONE)
Rd = sqRelWord(sepWit(1, 0, sepX))
check("*** the `a0 = a1` dressing leaves exactly liftC 7: fourteen rows dead, top row ODD",
      Rd, liftC(7))
check("    all fourteen lower rows of the dressed relator vanish",
      all(Rd[k] == 0 for k in range(14)))
check("    the class-FOUR row of the dressed relator is zero: class four is blind here",
      Rd[12], 0)
check("    the whole class-four relator is trivial at both dressings (through toU5L)",
      (U5.sqRelWord([U5.mul(U5.sigFourMark, toU5L(sepX)), toU5L(sepX), toU5L(sepY),
                     toU5L(sepU), toU5L(sepV)]),
       U5.sqRelWord([U5.sigFourMark, toU5L(sepX), toU5L(sepY), toU5L(sepU), toU5L(sepV)])),
      (U5.ONE, U5.ONE))
print()
print("   THE GAUGE AUDIT (GradedSigmaFour's class-two-forced gauge, transposed verbatim):")
print("     x0 abelian columns   x12 = %d, x34 = %d, x45 = %d   (nu'-column x23 = %d)"
      % (sepX[0], sepX[2], sepX[3], sepX[1]))
print("     x0 lower class-two   x13 = %d, x24 = %d" % (sepX[5], sepX[6]))
print("     x1 abelian columns   y12 = %d, y34 = %d, y45 = %d" % (sepY[0], sepY[2], sepY[3]))
check("    every datum the class-four gauge constrains is EVEN here",
      all(t % 2 == 0 for t in [sepX[0], sepX[2], sepX[3], sepX[5], sepX[6],
                               sepY[0], sepY[2], sepY[3]]) and sepX[1] == 0)
print("     the ONE odd datum is  x0's fifth abelian column x56 = %d," % sepX[4])
print("     a matrix entry that does not exist in U_5: the class-four gauge cannot mention it.")
print()
print("   THE CLOSED FORM.  At every relator-killing marking the `a0 = a1` response is")
print("     x12 * y24 * y46  +  x56 * y13 * y35   (mod 2),")
print("   here  %d*%d*%d + %d*%d*%d = %d."
      % (sepX[0], sepY[6], sepY[8], sepX[4], sepY[5], sepY[7],
         (sepX[0] * sepY[6] * sepY[8] + sepX[4] * sepY[5] * sepY[7]) % 2))
check("    the closed form predicts the observed parity",
      (sepX[0] * sepY[6] * sepY[8] + sepX[4] * sepY[5] * sepY[7]) % 2, Rd[14] % 2)
ok = all(sqRelWord(sepWit(h, j, ONE)) == ONE and sqRelWord(sepWit(h, j, sepX)) == liftC(7)
         for h, j in HS)
check("    the whole verdict holds at every handle count h = 1..4 and every handle", ok)

# =======================================================================================
print()
print("== D. the handle-block audit ==")
print("   the relator's top row is  (W*H).o = W.o + H.o + W.a*H.n + W.f*H.l + W.j*H.i,")
print("   and a sigma dressing moves neither W.a nor W.f, so")
print("     Delta(top) = sigFiveRead(v, x, y) + sigFourH(v, x) * H.i.")
random.seed(581)
bad = 0
tot = 0
for _ in range(3000):
    def r(nu=True):
        t = [random.randrange(8) for _ in range(15)]
        if nu:
            t[1] = 0
        return tuple(t)
    v, x, y, U, V = r(), r(), r(), r(False), r(False)
    m0 = mirTuple(1, 0, sigFiveMark, x, y, U, V)
    m1 = mirTuple(1, 0, mul(sigFiveMark, v), x, y, U, V)
    H = commP(U, V)
    sfH = (v[0] * (x[6] - x[2]) - v[2] * (x[0] + x[5]) + v[5] * x[2] - v[6] * x[0]) % 8
    want = (F.apply('o', v, x, y) + sfH * H[8]) % 8
    got = (sqRelWord(m1)[14] - sqRelWord(m0)[14]) % 8
    tot += 1
    if got != want:
        bad += 1
check("   the coupling formula holds at 3000 random markings (any letters, live or dead)",
      (tot, bad), (3000, 0))
print("   the block therefore does NOT cancel identically, as it did at class four")
print("   (GradedFourCleared.sqRelWord_sigFourDress_handle_blind).  But:")
random.seed(582)
oddH = 0
tot = 0
for _ in range(2000):
    def r(nu=True):
        t = [random.randrange(8) for _ in range(15)]
        if nu:
            t[1] = 0
        return tuple(t)
    x, y = r(), r()
    # impose only the relator's abelian rows over Z/8: 2*y_col = 4*x_col
    y = list(y)
    for k in (0, 2, 3, 4):
        y[k] = (2 * x[k] + 4 * random.randrange(2)) % 8
    y = tuple(y)
    W = sqWord(sigFiveMark, x, y)
    tot += 1
    if W[8] % 2:
        oddH += 1
check("   H.i = -W.i is EVEN at every marking whose abelian rows vanish, 2000 instances",
      oddH, 0)
print("   -> the class-five selection bit is handle-blind, at every handle count, on every")
print("      row, with no gauge hypothesis: the block coordinate it meets is forced even.")
random.seed(583)
bad = 0
for _ in range(2000):
    def r(nu=True):
        t = [random.randrange(8) for _ in range(15)]
        if nu:
            t[1] = 0
        return tuple(t)
    v, x, y = r(), r(), r()
    U1, V1, U2, V2 = r(False), r(False), r(False), r(False)
    # the same core slots, two ARBITRARY and different handle blocks
    d1 = (sqRelWord(mirTuple(1, 0, mul(sigFiveMark, v), x, y, U1, V1))[14]
          - sqRelWord(mirTuple(1, 0, sigFiveMark, x, y, U1, V1))[14]) % 8
    d2 = (sqRelWord(mirTuple(1, 0, mul(sigFiveMark, v), x, y, U2, V2))[14]
          - sqRelWord(mirTuple(1, 0, sigFiveMark, x, y, U2, V2))[14]) % 8
    sfH = (v[0] * (x[6] - x[2]) - v[2] * (x[0] + x[5]) + v[5] * x[2] - v[6] * x[0]) % 8
    if (d1 - d2) % 8 != (sfH * (commP(U1, V1)[8] - commP(U2, V2)[8])) % 8:
        bad += 1
check("   two arbitrary blocks differ by exactly sigFourH(v,x)*(H1.i - H2.i), 2000 markings",
      bad, 0)
print("   -> that discrepancy is the whole failure of wave 57's identical cancellation, and it")
print("      dies mod 2 the moment the relator's abelian rows hold (H.i even).")

print()
print("TOTAL CHECKS: %d   FAILURES: %d" % (checks, fails))
sys.exit(1 if fails else 0)
