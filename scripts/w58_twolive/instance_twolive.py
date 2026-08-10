"""W58-TWOLIVE: every explicit claim of GQ2/Dyadic/SqCore/GradedFourTwoLive.lean, checked
numerically at h = 1, 2, 3, 4, every handle j (and every ordered handle pair j1 < j2), and
every pivot residue c.

The library is validated against the COMMITTED GradedSigmaFour / GradedFourHom /
GradedFourRow / GradedFourMirror / GradedFourCleared facts first; only then is anything new
asserted.  Every comparison is counted.

Run:  python3 scripts/w58_twolive/instance_twolive.py
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from u5lib import (N, ONE, mul, inv, power, conjP, commP, sqWord, handleWord, sqRelWord,
                   liftC, is_ga_three, is_ga_four, selPar, sigFourMark, sigFourX, sigFourY,
                   sigFourU, sigFourV, sigFourRead, rowPivotVal, mirTuple, twoTuple,
                   in_live_frame, mirFourU, mirFourV, rowFourU, rowFourV,
                   mirLiveU, mirLiveV, liveRowY, rowLiveU, rowLiveV, dblLiveU, dblLiveV,
                   twoLiveU, twoLiveV, oddLiveU, oddLiveV, hiLiveU, hiLiveV, hiLiveY,
                   liveFourU, liveFourV, liveFourY)

R8 = range(8)
HS = (1, 2, 3, 4)
CMP = [0]
BAD = []


def cmp(name, a, b):
    CMP[0] += 1
    if a != b:
        BAD.append((name, a, b))
        if len(BAD) < 8:
            print("  ** MISMATCH ** %s : %s vs %s" % (name, a, b))


def istrue(name, c):
    cmp(name, bool(c), True)


def mirFourUGen(c):
    return (1 - 2 * c) % 8, 1, 0, 0, 0, 0, 0, 0, (-c) % 8, (c * c + c) % 8


def rowFourVGen(c):
    return (1 - 2 * c) % 8, 1, 0, 0, 1, 0, 0, 0, (-c) % 8, (c * c) % 8


def dblLiveVGen(c):
    return (1 - 2 * c) % 8, 1, 0, 0, 1, 4, 0, 0, (-c) % 8, (c * c) % 8


def hiLiveUGen(c):
    return ((1 - 4 * c) % 8, 2, 0, 0, (-(2 * c)) % 8, 0, 0, 0, (-(2 * c)) % 8,
            (4 * c * c + 2 * c) % 8)


def liveWit(h, j, y, U, V, v):
    return mirTuple(h, j, mul(sigFourMark, v), sigFourX, y, U, V)


def twoLiveWit(h, j1, j2, U, V, v):
    return twoTuple(h, j1, j2, mul(sigFourMark, v), sigFourX, sigFourY, U, V, V, U)


def sigLift_at(m, j, z0, w1, w2, z3, z4):
    m = list(m)
    m[0] = mul(m[0], z0)
    m[1] = mul(m[1], w1)
    m[2] = mul(m[2], w2)
    m[3 + 2 * j] = mul(m[3 + 2 * j], z3)
    m[4 + 2 * j] = mul(m[4 + 2 * j], z4)
    return m


print("=" * 78)
print("W58-TWOLIVE instance validation")
print("=" * 78)

print("\n## A  regression against the committed tree")
for hh in HS:
    for j in range(hh):
        cmp("committed sigFourWit relator h=%d j=%d" % (hh, j),
            sqRelWord(liveWit(hh, j, sigFourY, sigFourU, sigFourV, ONE)), ONE)
        cmp("committed odd residue h=%d j=%d" % (hh, j),
            sqRelWord(liveWit(hh, j, sigFourY, sigFourU, sigFourV, sigFourU)), liftC(1))
        cmp("committed even residue h=%d j=%d" % (hh, j),
            sqRelWord(liveWit(hh, j, sigFourY, sigFourU, sigFourV,
                              mul(sigFourU, sigFourU))), liftC(2))
        cmp("W57 live relator h=%d j=%d" % (hh, j),
            sqRelWord(liveWit(hh, j, liveFourY, liveFourU, liveFourV, ONE)), ONE)
        cmp("W57 live block h=%d j=%d" % (hh, j), commP(liveFourU, liveFourV),
            (0, 0, 0, 0, 0, 0, 0, 2, 0, 0))
        for c in R8:
            cmp("W56 mirror marking h=%d j=%d c=%d" % (hh, j, c),
                sqRelWord(liveWit(hh, j, sigFourY, mirFourUGen(c), mirFourV, ONE)), ONE)
            cmp("W56 row marking h=%d j=%d c=%d" % (hh, j, c),
                sqRelWord(liveWit(hh, j, sigFourY, rowFourU, rowFourVGen(c), ONE)), ONE)
            cmp("W56 doubly marking h=%d j=%d c=%d" % (hh, j, c),
                sqRelWord(liveWit(hh, j, sigFourY, mirFourUGen(c), rowFourVGen(c), ONE)), ONE)
            cmp("rowPivotVal displacement (mirror) c=%d" % c,
                mirFourUGen(c), mul(rowPivotVal(c), mirFourU))
            cmp("rowPivotVal displacement (row) c=%d" % c,
                rowFourVGen(c), mul(rowFourV, rowPivotVal(c)))
            cmp("rowPivotVal displacement (doubly v) c=%d" % c,
                dblLiveVGen(c), mul(dblLiveV, rowPivotVal(c)))
            cmp("pivot square displacement c=%d" % c,
                hiLiveUGen(c), mul(power(rowPivotVal(c), 2), sigFourU))

print("\n## B  the sided displacement calculus (Lean sec 3)")
import random
random.seed(20260810)
for _ in range(180000):
    P = tuple(random.randrange(8) for _ in range(10))
    Q = tuple(random.randrange(8) for _ in range(10))
    U = tuple(random.randrange(8) for _ in range(10))
    V = tuple(random.randrange(8) for _ in range(10))
    cmp("commP_left_displace", commP(mul(P, U), V),
        mul(conjP(commP(P, V), U), commP(U, V)))
    cmp("commP_right_displace", commP(U, mul(V, Q)),
        mul(commP(U, Q), conjP(commP(U, V), Q)))
    cmp("commP_swap", mul(commP(U, V), commP(V, U)), ONE)
for hh, ii, jj in itertools.product(R8, repeat=3):
    z = (0, 0, 0, 0, 0, 0, 0, hh, ii, jj)
    for c in R8:
        Q = rowPivotVal(c)
        cmp("conjP_gaThree at c=%d" % c, conjP(z, Q),
            mul(z, liftC((Q[3] * hh - Q[0] * ii) % 8)))
for _ in range(20000):
    U = tuple(random.randrange(8) for _ in range(10))
    V = tuple(random.randrange(8) for _ in range(10))
    U = U[:2] + (0,) + U[3:]
    V = V[:2] + (0,) + V[3:]
    U = (U[0], 0) + U[2:]
    V = (V[0], 0) + V[2:]
    b = commP(U, V)
    if is_ga_three(b):
        for c in R8:
            Q = rowPivotVal(c)
            cmp("commP_rowPivot_right_defect c=%d" % c, commP(U, mul(V, Q)),
                mul(commP(U, Q), mul(b, liftC((2 * c * b[8]) % 8))))

print("\n## C  the three displaced live points and the second-power point")
POINTS = [
    ("mirLive", 1, 0, liveRowY, mirLiveU, mirLiveV,
     lambda c: mirFourUGen(c), lambda c: mirLiveV, mirLiveU),
    ("rowLive", 0, 1, liveRowY, rowLiveU, rowLiveV,
     lambda c: rowLiveU, lambda c: rowFourVGen(c), rowLiveV),
    ("dblLive", 1, 1, liveRowY, dblLiveU, dblLiveV,
     lambda c: mirFourUGen(c), lambda c: dblLiveVGen(c), dblLiveU),
    ("hiLive", 2, 0, hiLiveY, hiLiveU, hiLiveV,
     lambda c: hiLiveUGen(c), lambda c: hiLiveV, hiLiveU),
]
for name, t, s, y, U, V, Ug, Vg, openL in POINTS:
    blk = commP(U, V)
    for hh in HS:
        for j in range(hh):
            cmp("%s frame relator h=%d j=%d" % (name, hh, j),
                sqRelWord(liveWit(hh, j, y, U, V, ONE)), ONE)
            cmp("%s odd verdict h=%d j=%d" % (name, hh, j),
                sqRelWord(liveWit(hh, j, y, U, V, openL)), liftC(1))
            cmp("%s even verdict h=%d j=%d" % (name, hh, j),
                sqRelWord(liveWit(hh, j, y, U, V, mul(openL, openL))), liftC(2))
            cmp("%s even completion h=%d j=%d" % (name, hh, j),
                sqRelWord(sigLift_at(liveWit(hh, j, y, U, V, mul(openL, openL)), j,
                                     ONE, ONE, liftC(7), ONE, ONE)), ONE)
            for c in R8:
                cmp("%s marking relator h=%d j=%d c=%d" % (name, hh, j, c),
                    sqRelWord(liveWit(hh, j, y, Ug(c), Vg(c), ONE)), ONE)
                cmp("%s block preserved h=%d j=%d c=%d" % (name, hh, j, c),
                    commP(Ug(c), Vg(c)), blk)
                cmp("%s u-slot b-column h=%d j=%d c=%d" % (name, hh, j, c),
                    Ug(c)[1], t % 8)
                cmp("%s v-slot b-column h=%d j=%d c=%d" % (name, hh, j, c),
                    Vg(c)[1], s % 8)
                istrue("%s slots in liveFrameSub h=%d j=%d c=%d" % (name, hh, j, c),
                       all(in_live_frame(p) for p in
                           [sigFourMark, sigFourX, y, Ug(c), Vg(c), ONE]))
    istrue("%s block is live" % name, blk != ONE)
    istrue("%s block is gamma_3" % name, is_ga_three(blk))
    istrue("%s block is even in class three" % name, blk[7] % 2 == 0 and blk[8] % 2 == 0)
    istrue("%s open channel is odd" % name, selPar(openL[0]) == 1)
    istrue("%s open letter is clean (f = 0 mod 4)" % name, openL[5] % 4 == 0)
print("   block orders: %s"
      % {nm: next(k for k in range(1, 9) if power(commP(U, V), k) == ONE)
         for nm, _, _, _, U, V, _, _, _ in POINTS})

print("\n## D  the selection bit is blind to the WHOLE handle block")
for name, t, s, y, U, V, Ug, Vg, openL in POINTS:
    for hh in HS:
        for j in range(hh):
            for _ in range(200):
                v = tuple(random.randrange(8) for _ in range(10))
                v = (v[0], 0) + v[2:]
                m0 = liveWit(hh, j, y, U, V, ONE)
                m1 = liveWit(hh, j, y, U, V, v)
                cmp("%s bit h=%d j=%d" % (name, hh, j),
                    (sqRelWord(m1)[9] - sqRelWord(m0)[9]) % 2, selPar(v[0]))
                cmp("%s dress h-row h=%d j=%d" % (name, hh, j),
                    (sqRelWord(m1)[7] - sqRelWord(m0)[7]) % 8, (-2 * (v[2] + v[5])) % 8)
                cmp("%s dress g-row h=%d j=%d" % (name, hh, j),
                    sqRelWord(m1)[6], sqRelWord(m0)[6])
                cmp("%s dress i-row h=%d j=%d" % (name, hh, j),
                    sqRelWord(m1)[8], sqRelWord(m0)[8])

print("\n## E  the two-live-handle point")
for hh in (2, 3, 4):
    for j1 in range(hh):
        for j2 in range(hh):
            if j1 >= j2:
                continue
            cmp("two-live relator h=%d (%d,%d)" % (hh, j1, j2),
                sqRelWord(twoLiveWit(hh, j1, j2, twoLiveU, twoLiveV, ONE)), ONE)
            cmp("two-live odd verdict h=%d (%d,%d)" % (hh, j1, j2),
                sqRelWord(twoLiveWit(hh, j1, j2, twoLiveU, twoLiveV, twoLiveU)), liftC(1))
            cmp("two-live even verdict h=%d (%d,%d)" % (hh, j1, j2),
                sqRelWord(twoLiveWit(hh, j1, j2, twoLiveU, twoLiveV,
                                     mul(twoLiveU, twoLiveU))), liftC(2))
            cmp("two-live even completion h=%d (%d,%d)" % (hh, j1, j2),
                sqRelWord(sigLift_at(twoLiveWit(hh, j1, j2, twoLiveU, twoLiveV,
                                                mul(twoLiveU, twoLiveU)), j1,
                                     ONE, ONE, liftC(7), ONE, ONE)), ONE)
            cmp("two-live relator for ARBITRARY letters h=%d (%d,%d)" % (hh, j1, j2),
                {sqRelWord(twoTuple(hh, j1, j2, sigFourMark, sigFourX, sigFourY,
                                    U, V, V, U))
                 for U, V in [(tuple(random.randrange(8) for _ in range(10)),
                               tuple(random.randrange(8) for _ in range(10)))
                              for _ in range(120)]}, {ONE})
            for _ in range(40):
                v = tuple(random.randrange(8) for _ in range(10))
                v = (v[0], 0) + v[2:]
                cmp("two-live bit h=%d (%d,%d)" % (hh, j1, j2),
                    sqRelWord(twoLiveWit(hh, j1, j2, twoLiveU, twoLiveV, v))[9] % 2,
                    selPar(v[0]))
cmp("two-live blocks", (commP(twoLiveU, twoLiveV), commP(twoLiveV, twoLiveU)),
    ((0, 0, 0, 0, 0, 0, 0, 2, 0, 0), (0, 0, 0, 0, 0, 0, 0, 6, 0, 0)))
istrue("two-live slots in liveFrameSub",
       all(in_live_frame(p) for p in [sigFourMark, sigFourX, sigFourY, twoLiveU, twoLiveV]))

print("\n## F  no cross-handle coupling, and what the relator still forces")
for _ in range(120000):
    U1 = tuple(random.randrange(8) for _ in range(10))
    V1 = tuple(random.randrange(8) for _ in range(10))
    U2 = tuple(random.randrange(8) for _ in range(10))
    V2 = tuple(random.randrange(8) for _ in range(10))
    U2 = U2[:2] + (0,) + U2[3:]
    V2 = V2[:2] + (0,) + V2[3:]
    A, B = commP(U1, V1), commP(U2, V2)
    cmp("no coupling", mul(A, B)[9], (A[9] + B[9]) % 8)
    cmp("second block g vanishes", B[6], 0)

print("\n## G  the ODD two-live marking: the forcing FAILS")
D1 = commP(oddLiveU, oddLiveV)
cmp("odd block", D1, (0, 0, 0, 0, 0, 0, 0, 1, 0, 0))
istrue("odd block is gamma_3", is_ga_three(D1))
istrue("odd block has ODD class-three coordinate", D1[7] % 2 == 1)
istrue("odd letter leaves liveFrameSub", not in_live_frame(oddLiveV))
for hh in (2, 3, 4):
    for j1 in range(hh):
        for j2 in range(hh):
            if j1 >= j2:
                continue
            cmp("odd two-live relator h=%d (%d,%d)" % (hh, j1, j2),
                sqRelWord(twoLiveWit(hh, j1, j2, oddLiveU, oddLiveV, ONE)), ONE)
            cmp("odd two-live odd residue h=%d (%d,%d)" % (hh, j1, j2),
                sqRelWord(twoLiveWit(hh, j1, j2, oddLiveU, oddLiveV, oddLiveU)), liftC(1))
            cmp("odd two-live KILL h=%d (%d,%d)" % (hh, j1, j2),
                sqRelWord(sigLift_at(twoLiveWit(hh, j1, j2, oddLiveU, oddLiveV, oddLiveU),
                                     j1, ONE, ONE, liftC(3), D1, ONE)), ONE)
            cmp("odd two-live SUM is even h=%d (%d,%d)" % (hh, j1, j2),
                mul(D1, commP(oddLiveV, oddLiveU))[7] % 2, 0)

print("\n## H  the block-order separation across the catalogue")
cmp("cleared row block order four", commP(liveFourU, liveFourV)[7], 2)
cmp("second-power block order four", commP(sigFourU, hiLiveV)[7], 2)
cmp("mirror block order two", commP(mirFourU, mirLiveV)[7], 4)
cmp("row block order two", commP(rowLiveU, rowFourV)[7], 4)
cmp("doubly block order two", commP(mirFourU, dblLiveV)[7], 4)

print()
print("=" * 78)
print("comparisons: %d, mismatches: %d" % (CMP[0], len(BAD)))
if BAD:
    print("FAILED:", BAD[:10])
print("=" * 78)
