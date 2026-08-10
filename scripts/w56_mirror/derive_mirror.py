"""W56-MIRROR step 1: validate the library against the committed class-four facts and against
wave 55's row lane, then derive the two new points.

Rows, in the `nuSel 1 j t s` naming (`t = nu'(u_0)`, `s = nu'(v_0)`):

    (t, s) = (0, 0)   cleared row            GradedSigmaFour / GradedFourHom   (committed)
    (t, s) = (0, 1)   uncleared v-row        GradedFourRow                     (wave 55)
    (t, s) = (1, 0)   THE MIRROR ROW         this lane
    (t, s) = (1, 1)   doubly-uncleared row   this lane

The Eichler correction is *asymmetric*: `sqEichV = v_0 * w^{-s}` (pivot power on the RIGHT of
the v-slot) while `sqEichU = w^{-t} * u_0` (pivot power on the LEFT of the u-slot).  So the
marking's handle slots are

    Phi(u_0) = P^t * U0 ,      Phi(v_0) = V0 * P^s ,      P = Phi(w) the pivot image,

and the class-two e-row of the relator moves, for a LEFT displacement by P and a RIGHT
displacement by Q, by

    (P.a*V0.b - P.b*V0.a) + (U0.a*Q.b - U0.b*Q.a) + (P.a*Q.b - P.b*Q.a).

The last term is the INTERACTION of the two displacements: they do not simply add.  It is the
alternating pairing of the two displacing elements against each other, and it vanishes exactly
when they are aligned - in particular when both are powers of the same pivot, which is the only
case the rows produce.  With the cleared letters nu'-trivial (`U0.b = V0.b = 0`), `P.b = t`,
`Q.b = s` and `P.a*Q.b = P.b*Q.a`, this is `s*U0.a - t*V0.a`, so the UNIFIED obstruction at
every selected row is

    s * chi_a(U0)  =  t * chi_a(V0).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from u5lib import *

fails = 0
checks = 0


def check(name, got, want):
    global fails, checks
    checks += 1
    ok = (got == want)
    if not ok:
        fails += 1
    print(("PASS " if ok else "FAIL ") + name + ("" if ok else "  got %s want %s" % (got, want)))


# --------------------------------------------------------------------------------------
print("== 1. library validation against committed GradedSigmaFour / GradedFourHom facts ==")
check("sqRelWord_sigFourWit_triv", sqRelWord(sigFourWit(ONE)), ONE)
check("sqRelWord_sigFourWit_V", sqRelWord(sigFourWit(sigFourV)), liftC(2))
check("sqRelWord_sigFourWit_U", sqRelWord(sigFourWit(sigFourU)), liftC(1))
check("sqRelWord_sigFourWit_V_complete",
      sqRelWord(sigLift(sigFourWit(sigFourV), ONE, ONE, liftC(7), ONE, ONE)), ONE)
check("sqWord(mark,X,Y)=1", sqWord(sigFourMark, sigFourX, sigFourY), ONE)
check("commP(sigFourU,sigFourV)=1", commP(sigFourU, sigFourV), ONE)


def zpow_closed(X, c, n=N):
    """The flatTwo closed form of X^c (GradedFourHom.SqU5.zpowZtwo_of_flatTwo)."""
    a, b, cc, d, e, f, g, h, i, j = X
    ob = (a * i + e * g + h * d) % n
    assert ob % 2 == 0, "class-four obstruction must be even"
    w0 = ob // 2
    assert (a * b) % n == 0 and (b * cc) % n == 0 and (cc * d) % n == 0
    assert (a * f + e * cc) % n == 0 and (b * g + f * d) % n == 0
    return red((c * a, c * b, c * cc, c * d, c * e, c * f, c * g, c * h, c * i,
                c * j + (c * c - c) * w0), n)


for c in range(N):
    check("zpow_closed(sigFourX,%d)" % c, zpow_closed(sigFourX, c), power(sigFourX, c))


def pivot_image(c, n=N):
    """Phi(w) = Phi(sigma) * Phi(x0)^{-c}, i.e. GradedFourRow.rowPivotVal."""
    return mul(sigFourMark, inv(zpow_closed(sigFourX, c, n), n), n)


for c in range(N):
    check("rowPivotVal closed form at c=%d" % c, pivot_image(c),
          red((-(2 * c), 1, 0, 0, 0, 0, 0, 0, -c, c * c + c)))

# --------------------------------------------------------------------------------------
print()
print("== 1b. validation against the committed wave-55 row lane (GradedFourRow) ==")
rowFourU = (0, 0, 0, 1, 0, 0, 0, 0, 0, 0)
rowFourV = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)


def rowFourVGen(c):
    return mul(rowFourV, pivot_image(c))


def rowFourMark(c):
    return [sigFourMark, sigFourX, sigFourY, rowFourU, rowFourVGen(c)]


def rowFourWit(v):
    return [mul(sigFourMark, v), sigFourX, sigFourY, rowFourU, rowFourV]


for c in range(N):
    check("rowFourVGen at c=%d" % c, rowFourVGen(c), red((1 - 2 * c, 1, 0, 0, 1, 0, 0, 0, -c, c * c)))
    check("sqRelWord_rowFourMark at c=%d" % c, sqRelWord(rowFourMark(c)), ONE)
check("sqRelWord_rowFourWit_triv", sqRelWord(rowFourWit(ONE)), ONE)
check("sqRelWord_rowFourWit_V", sqRelWord(rowFourWit(rowFourV)), liftC(1))
check("sqRelWord_rowFourWit_Vsq", sqRelWord(rowFourWit(mul(rowFourV, rowFourV))), liftC(2))
check("rowFourWit_commP_zero_two", commP(sigFourMark, sigFourY), (0,) * 8 + (4, 0))
check("rowFourWit_commP_two_handleU", commP(sigFourY, rowFourU), ONE)
check("rowFourWit_commP_two_handleV", commP(sigFourY, rowFourV), (0,) * 9 + (6,))

# --------------------------------------------------------------------------------------
print()
print("== 2. the general displacement identity and the unified obstruction ==")
# (sqWord S X Y * commP (P*U) (V*Q)).e  -  (sqWord S X Y * commP U V).e
#   =  (P.a*V.b - P.b*V.a) + (U.a*Q.b - U.b*Q.a) + (P.a*Q.b - P.b*Q.a)
import random
random.seed(20560810)


def rnd():
    return tuple(random.randrange(N) for _ in range(10))


bad2 = 0
for trial in range(400):
    S, X, Y, U, V, P, Q = (rnd() for _ in range(7))
    lhs = mul(sqWord(S, X, Y), commP(mul(P, U), mul(V, Q)))[4]
    rhs = (mul(sqWord(S, X, Y), commP(U, V))[4]
           + (P[0] * V[1] - P[1] * V[0]) + (U[0] * Q[1] - U[1] * Q[0])
           + (P[0] * Q[1] - P[1] * Q[0])) % N
    if lhs != rhs:
        bad2 += 1
check("two-sided e-displacement: 400 random tuples", bad2, 0)

# the interaction term is genuinely there: dropping it fails
bad_naive = 0
for trial in range(400):
    S, X, Y, U, V, P, Q = (rnd() for _ in range(7))
    lhs = mul(sqWord(S, X, Y), commP(mul(P, U), mul(V, Q)))[4]
    rhs = (mul(sqWord(S, X, Y), commP(U, V))[4]
           + (P[0] * V[1] - P[1] * V[0]) + (U[0] * Q[1] - U[1] * Q[0])) % N
    if lhs != rhs:
        bad_naive += 1
print("  (control: dropping the interaction term fails on %d of 400 random tuples)" % bad_naive)

# the specialisations
badR = badL = 0
for trial in range(200):
    S, X, Y, U, V, P = (rnd() for _ in range(6))
    lhs = mul(sqWord(S, X, Y), commP(U, mul(V, P)))[4]
    rhs = (mul(sqWord(S, X, Y), commP(U, V))[4] + (U[0] * P[1] - U[1] * P[0])) % N
    if lhs != rhs:
        badR += 1
    lhs = mul(sqWord(S, X, Y), commP(mul(P, U), V))[4]
    rhs = (mul(sqWord(S, X, Y), commP(U, V))[4] + (P[0] * V[1] - P[1] * V[0])) % N
    if lhs != rhs:
        badL += 1
check("RIGHT e-displacement (wave 55's identity): 200 random tuples", badR, 0)
check("LEFT  e-displacement (the mirror's):      200 random tuples", badL, 0)

# the unified obstruction, exhaustively over the aligned shapes the rows produce:
#   U.b = V.b = 0, P = w^t, Q = w^s, both relators trivial  ==>  P.b * V.a = Q.b * U.a,
#   i.e. t * chi_a(V0) = s * chi_a(U0).
bad = 0
tested = 0
for t in range(2):
    for s in range(2):
        for c in range(N):
            P = pivot_image(c) if t else ONE
            Q = pivot_image(c) if s else ONE
            assert (P[0] * Q[1] - P[1] * Q[0]) % N == 0, "aligned"
            for ua in range(N):
                for va in range(N):
                    for ud in range(N):
                        U = (ua, 0, 0, ud, 0, 0, 0, 0, 0, 0)
                        V = (va, 0, 0, 0, 0, 0, 0, 0, 0, 0)
                        m_ok = mul(sqWord(sigFourMark, sigFourX, sigFourY),
                                   commP(mul(P, U), mul(V, Q))) == ONE
                        f_ok = mul(sqWord(sigFourMark, sigFourX, sigFourY),
                                   commP(U, V)) == ONE
                        if m_ok and f_ok:
                            tested += 1
                            if (t * V[0]) % N != (s * U[0]) % N:
                                bad += 1
check("unified obstruction  t*chi_a(V0) = s*chi_a(U0)  (%d admissible shapes)" % tested, bad, 0)

# --------------------------------------------------------------------------------------
print()
print("== 3. THE MIRROR POINT, row (t,s) = (1,0) ==")
mirU = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)       # the cleared U-letter: chi_a = 1, the odd channel
mirV = (0, 0, 0, 1, 0, 0, 0, 0, 0, 0)       # the V-letter: chi_a = 0 (FORCED), chi_d = 1


def mirUGen(c):
    """Phi(u_0) = P * U0: the LEFT displacement."""
    return mul(pivot_image(c), mirU)


def mirMark(c, h=1, j=0):
    """The marking at h handles: handle j carries (P*U0, V0), every other handle is (1,1)."""
    m = [sigFourMark, sigFourX, sigFourY]
    for k in range(h):
        m += [mirUGen(c), mirV] if k == j else [ONE, ONE]
    return m


def mirWit(v, h=1, j=0):
    m = [mul(sigFourMark, v), sigFourX, sigFourY]
    for k in range(h):
        m += [mirU, mirV] if k == j else [ONE, ONE]
    return m


for c in range(N):
    check("mirUGen closed form at c=%d" % c, mirUGen(c),
          red((1 - 2 * c, 1, 0, 0, 0, 0, 0, 0, -c, c * c + c)))
    check("commP(P*U0, V0) = 1 at c=%d" % c, commP(mirUGen(c), mirV), ONE)
check("commP(U0, V0) = 1", commP(mirU, mirV), ONE)
check("mirror chi_a(V0) = 0 (forced)", mirV[0], 0)
check("mirror chi_a(U0) = 1 (odd channel)", mirU[0], 1)

for h in range(1, 5):
    for j in range(h):
        for c in range(N):
            check("sqRelWord(mirMark) = 1 at h=%d j=%d c=%d" % (h, j, c),
                  sqRelWord(mirMark(c, h, j)), ONE)
        check("sqRelWord(mirWit 1) = 1 at h=%d j=%d" % (h, j), sqRelWord(mirWit(ONE, h, j)), ONE)

mirUsq = mul(mirU, mirU)
check("U0^2 = sigFourV", mirUsq, sigFourV)
for h in range(1, 5):
    check("mirror verdict U0   (chi_a=1) at h=%d" % h, sqRelWord(mirWit(mirU, h)), liftC(1))
    check("mirror verdict U0^2 (chi_a=2) at h=%d" % h, sqRelWord(mirWit(mirUsq, h)), liftC(2))
    check("mirror verdict V0   (chi_a=0) at h=%d" % h, sqRelWord(mirWit(mirV, h)), ONE)
check("mirror even residue dies to one gamma_4 move",
      sqRelWord(sigLift(mirWit(mirUsq), ONE, ONE, liftC(7), ONE, ONE)), ONE)

# b-column = nu' row  (nuSel h j 1 0: sigma=1, x0=0, x1=0, u_0=1, v_0=0, others 0)
for h in range(1, 4):
    for j in range(h):
        for c in range(N):
            want = [1, 0, 0] + sum(([1, 0] if k == j else [0, 0] for k in range(h)), [])
            check("mirror b-column at h=%d j=%d c=%d" % (h, j, c),
                  [p[1] for p in mirMark(c, h, j)], want)

# --------------------------------------------------------------------------------------
print()
print("== 4. THE DOUBLY-UNCLEARED POINT, row (t,s) = (1,1) ==")
dblU = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
dblV = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)       # chi_a(U0) = chi_a(V0) = 1: the FORCED equality


def dblUGen(c):
    return mul(pivot_image(c), dblU)


def dblVGen(c):
    return mul(dblV, pivot_image(c))


def dblMark(c, h=1, j=0):
    m = [sigFourMark, sigFourX, sigFourY]
    for k in range(h):
        m += [dblUGen(c), dblVGen(c)] if k == j else [ONE, ONE]
    return m


def dblWit(v, h=1, j=0):
    m = [mul(sigFourMark, v), sigFourX, sigFourY]
    for k in range(h):
        m += [dblU, dblV] if k == j else [ONE, ONE]
    return m


for c in range(N):
    check("dblUGen closed form at c=%d" % c, dblUGen(c),
          red((1 - 2 * c, 1, 0, 0, 0, 0, 0, 0, -c, c * c + c)))
    check("dblVGen closed form at c=%d" % c, dblVGen(c),
          red((1 - 2 * c, 1, 0, 0, 1, 0, 0, 0, -c, c * c)))
    check("commP(P*U0, V0*P) = 1 at c=%d" % c, commP(dblUGen(c), dblVGen(c)), ONE)
check("commP(U0, V0) = 1", commP(dblU, dblV), ONE)
check("doubly chi_a(U0) = chi_a(V0)", dblU[0], dblV[0])

for h in range(1, 5):
    for j in range(h):
        for c in range(N):
            check("sqRelWord(dblMark) = 1 at h=%d j=%d c=%d" % (h, j, c),
                  sqRelWord(dblMark(c, h, j)), ONE)
        check("sqRelWord(dblWit 1) = 1 at h=%d j=%d" % (h, j), sqRelWord(dblWit(ONE, h, j)), ONE)

for h in range(1, 5):
    check("doubly verdict U0   (chi_a=1) at h=%d" % h, sqRelWord(dblWit(dblU, h)), liftC(1))
    check("doubly verdict U0^2 (chi_a=2) at h=%d" % h, sqRelWord(dblWit(mul(dblU, dblU), h)),
          liftC(2))
check("doubly even residue dies to one gamma_4 move",
      sqRelWord(sigLift(dblWit(mul(dblU, dblU)), ONE, ONE, liftC(7), ONE, ONE)), ONE)

for h in range(1, 4):
    for j in range(h):
        for c in range(N):
            want = [1, 0, 0] + sum(([1, 1] if k == j else [0, 0] for k in range(h)), [])
            check("doubly b-column at h=%d j=%d c=%d" % (h, j, c),
                  [p[1] for p in dblMark(c, h, j)], want)

# --------------------------------------------------------------------------------------
print()
print("== 5. the sigma reading and the selection bit at both new points ==")
for nm, X, Y in [("mirror/doubly (committed x0, x1 slots)", sigFourX, sigFourY)]:
    for v in [ONE, mirU, mirV, mirUsq, (5, 0, 0, 4, 2, 0, 3, 7, 6, 1), (3, 0, 5, 2, 7, 1, 4, 6, 2, 5)]:
        check("read(%s) = v.a - 2 v.g - 2 v.i" % (v,), sigFourRead(v, X, Y),
              (v[0] - 2 * v[6] - 2 * v[8]) % N)
for v in [ONE, mirU, mirV, mirUsq, (5, 0, 0, 4, 2, 0, 3, 7, 6, 1)]:
    check("mirror relator j-row at v=%s" % (v,), sqRelWord(mirWit(v))[9],
          sigFourRead(v, sigFourX, sigFourY))
    check("mirror bit at v=%s" % (v,), sqRelWord(mirWit(v))[9] % 2, v[0] % 2)
    check("doubly relator j-row at v=%s" % (v,), sqRelWord(dblWit(v))[9],
          sigFourRead(v, sigFourX, sigFourY))
    check("doubly bit at v=%s" % (v,), sqRelWord(dblWit(v))[9] % 2, v[0] % 2)

# --------------------------------------------------------------------------------------
print()
print("== 6. class-three blindness at both new points ==")
for nm, wit in [("mirror", mirWit), ("doubly", dblWit)]:
    for tag, v in [("triv", ONE), ("U0", mirU), ("U0^2", mirUsq), ("V0", mirV)]:
        r = sqRelWord(wit(v))
        check("%s toU4L trivial at %s" % (nm, tag), (r[0], r[1], r[2], r[4], r[5], r[7]), (0,) * 6)
        check("%s toU4R trivial at %s" % (nm, tag), (r[1], r[2], r[3], r[5], r[6], r[8]), (0,) * 6)

# --------------------------------------------------------------------------------------
print()
print("== 7. the extended-lattice data: the three x1-slot commutators ==")
for nm, U, V in [("mirror", mirU, mirV), ("doubly", dblU, dblV)]:
    print("  %s: commP(sigma,x1) = %s" % (nm, commP(sigFourMark, sigFourY)))
    print("  %s: commP(x1,U0)    = %s" % (nm, commP(sigFourY, U)))
    print("  %s: commP(x1,V0)    = %s" % (nm, commP(sigFourY, V)))
check("mirror commP(sigma,x1)", commP(sigFourMark, sigFourY), (0,) * 8 + (4, 0))
check("mirror commP(x1,U0)", commP(sigFourY, mirU), (0,) * 9 + (6,))
check("mirror commP(x1,V0)", commP(sigFourY, mirV), ONE)
check("doubly commP(x1,U0)", commP(sigFourY, dblU), (0,) * 9 + (6,))
check("doubly commP(x1,V0)", commP(sigFourY, dblV), (0,) * 9 + (6,))

print()
print("TOTAL CHECKS: %d   FAILURES: %d" % (checks, fails))
sys.exit(1 if fails else 0)
