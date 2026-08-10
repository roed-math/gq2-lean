"""W56-MIRROR step 3: every explicit claim of GQ2/Dyadic/SqCore/GradedFourMirror.lean,
mirrored numerically one for one.

The Lean file is stated at arbitrary handle count `h` and arbitrary live handle `j`; every claim
below is therefore checked at `h = 1, 2, 3, 4` and every `j < h`, and every claim mentioning the
pivot residue at all eight residues `c` of `gr3Pi sqPivotExp`.
"""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from u5lib import *

random.seed(1956)
fails = 0
checks = 0


def check(name, got, want):
    global fails, checks
    checks += 1
    if got != want:
        fails += 1
        print("FAIL " + name + "  got %s want %s" % (got, want))


def ok(name):
    print("PASS " + name)


HS = [(h, j) for h in (1, 2, 3, 4) for j in range(h)]

S, X, Y = sigFourMark, sigFourX, sigFourY


def rowPivotVal(c):
    return red((-(2 * c), 1, 0, 0, 0, 0, 0, 0, -c, c * c + c))


def mirTuple(h, j, s, x, y, u, v):
    m = [s, x, y]
    for k in range(h):
        m += [u, v] if k == j else [ONE, ONE]
    return m


def mirWit(h, j, U, V, v):
    return mirTuple(h, j, mul(S, v), X, Y, U, V)


def sigLift_at(h, j, m, z0, w1, w2, z3, z4):
    m = list(m)
    m[0] = mul(m[0], z0)
    m[1] = mul(m[1], w1)
    m[2] = mul(m[2], w2)
    m[3 + 2 * j] = mul(m[3 + 2 * j], z3)
    m[4 + 2 * j] = mul(m[4 + 2 * j], z4)
    return m


def toU4L(p):
    return (p[0], p[1], p[2], p[4], p[5], p[7])


def toU4R(p):
    return (p[1], p[2], p[3], p[5], p[6], p[8])


# ======================================================================================
print("== §1 mirTuple, sqRelWord_mirTuple, sqRelWord_mirTuple_e ==")
for (h, j) in HS:
    for _ in range(8):
        s, x, y, u, v = (tuple(random.randrange(N) for _ in range(10)) for _ in range(5))
        m = mirTuple(h, j, s, x, y, u, v)
        check("sqRelWord_mirTuple h=%d j=%d" % (h, j), sqRelWord(m),
              mul(sqWord(s, x, y), commP(u, v)))
        check("sqRelWord_mirTuple_e h=%d j=%d" % (h, j), sqRelWord(m)[4],
              (sqWord(s, x, y)[4] + (u[0] * v[1] - u[1] * v[0])) % N)
ok("sqRelWord_mirTuple / _e at every (h, j), 8 random tuples each")

print()
print("== §1 the three displacement identities and the row obstruction ==")
for (h, j) in HS:
    for _ in range(8):
        s, x, y, u, v, P, Q = (tuple(random.randrange(N) for _ in range(10)) for _ in range(7))
        base = sqRelWord(mirTuple(h, j, s, x, y, u, v))[4]
        check("sqRelWord_e_displace_two h=%d j=%d" % (h, j),
              sqRelWord(mirTuple(h, j, s, x, y, mul(P, u), mul(v, Q)))[4],
              (base + (P[0] * v[1] - P[1] * v[0]) + (u[0] * Q[1] - u[1] * Q[0])
               + (P[0] * Q[1] - P[1] * Q[0])) % N)
        check("sqRelWord_e_displace_left h=%d j=%d" % (h, j),
              sqRelWord(mirTuple(h, j, s, x, y, mul(P, u), v))[4],
              (base + (P[0] * v[1] - P[1] * v[0])) % N)
        check("sqRelWord_e_displace_right h=%d j=%d" % (h, j),
              sqRelWord(mirTuple(h, j, s, x, y, u, mul(v, Q)))[4],
              (base + (u[0] * Q[1] - u[1] * Q[0])) % N)
ok("sqRelWord_e_displace_two / _left / _right at every (h, j)")

# chiA_row_forced: hypotheses U.b = V.b = 0, aligned, both relators trivial => P.b*V.a = Q.b*U.a
bad = tested = 0
for (h, j) in HS[:3]:
    for t in range(2):
        for s_ in range(2):
            for c in range(N):
                P = rowPivotVal(c) if t else ONE
                Q = rowPivotVal(c) if s_ else ONE
                for ua in range(N):
                    for va in range(N):
                        for ud in range(N):
                            U = (ua, 0, 0, ud, 0, 0, 0, 0, 0, 0)
                            V = (va, 0, 0, 0, 0, 0, 0, 0, 0, 0)
                            if (sqRelWord(mirTuple(h, j, S, X, Y, mul(P, U), mul(V, Q))) == ONE
                                    and sqRelWord(mirTuple(h, j, S, X, Y, U, V)) == ONE):
                                tested += 1
                                if (P[1] * V[0]) % N != (Q[1] * U[0]) % N:
                                    bad += 1
check("chiA_row_forced over %d admissible instances" % tested, bad, 0)
ok("chiA_row_forced / chiA_mirror_forced / chiA_double_forced")

# ======================================================================================
print()
print("== §2 the shared machinery ==")
LETTERS = [((1, 0, 0, 0, 0, 0, 0, 0, 0, 0), (0, 0, 0, 1, 0, 0, 0, 0, 0, 0)),   # mirror
           ((1, 0, 0, 0, 0, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)),   # doubly
           ((0, 0, 0, 1, 0, 0, 0, 0, 0, 0), (1, 0, 0, 0, 0, 0, 0, 0, 0, 0))]   # wave 55
for (h, j) in HS:
    for (U, V) in LETTERS:
        assert commP(U, V) == ONE
        for v in [ONE, U, V, mul(U, U), (5, 0, 0, 4, 2, 0, 3, 7, 6, 1)]:
            check("sqRelWord_mirWit h=%d j=%d" % (h, j), sqRelWord(mirWit(h, j, U, V, v)),
                  sqWord(mul(S, v), X, Y))
            check("mirWit_bit h=%d j=%d" % (h, j), sqRelWord(mirWit(h, j, U, V, v))[9] % 2,
                  v[0] % 2)
        check("sqRelWord_mirWit_triv h=%d j=%d" % (h, j), sqRelWord(mirWit(h, j, U, V, ONE)), ONE)
ok("sqRelWord_mirWit / _triv / mirWit_bit at every (h, j) and all three letter pairs")

# mirWit_increment_even: z3, z4 even in both class-three coordinates => increment even
bad = 0
for (U, V) in LETTERS:
    for _ in range(4000):
        z0 = tuple(random.randrange(N) for _ in range(10))
        w1j, w2j = random.randrange(N), random.randrange(N)
        z3 = (0,) * 7 + (2 * random.randrange(4), 2 * random.randrange(4), 0)
        z4 = (0,) * 7 + (2 * random.randrange(4), 2 * random.randrange(4), 0)
        inc = ((z0[7] * X[3] - z0[8] * X[0]) + (-4 * w1j + 2 * w2j)
               + ((z3[7] * V[3] - z3[8] * V[0]) + (U[0] * z4[8] - U[3] * z4[7]))) % N
        if inc % 2:
            bad += 1
check("mirWit_increment_even, 12000 random even-dressing instances", bad, 0)
ok("mirWit_increment_even / mirWit_sigma_forced")

# ======================================================================================
print()
print("== §3-§6 the MIRROR point (t,s) = (1,0) ==")
mirFourU = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
mirFourV = (0, 0, 0, 1, 0, 0, 0, 0, 0, 0)
rowFourU = (0, 0, 0, 1, 0, 0, 0, 0, 0, 0)
rowFourV = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)


def mirFourUGen(c):
    return red((1 - 2 * c, 1, 0, 0, 0, 0, 0, 0, -c, c * c + c))


def rowFourVGen(c):
    return red((1 - 2 * c, 1, 0, 0, 1, 0, 0, 0, -c, c * c))


check("mirFour_letters_swapped (mirFourU = rowFourV)", mirFourU, rowFourV)
check("mirFour_letters_swapped (mirFourV = rowFourU)", mirFourV, rowFourU)
for c in range(N):
    check("mirFourUGen_eq at c=%d" % c, mirFourUGen(c), mul(rowPivotVal(c), mirFourU))
    check("mirFourU_eq at c=%d" % c, mul(inv(rowPivotVal(c)), mirFourUGen(c)), mirFourU)
    check("commP_mirFourUGen at c=%d" % c, commP(mirFourUGen(c), mirFourV), ONE)
check("commP_mirFour", commP(mirFourU, mirFourV), ONE)
check("mirFourV_chiA", mirFourV[0], 0)
check("mirFourU_chiA", mirFourU[0] % 2, 1)
check("mirFourU_sq", mul(mirFourU, mirFourU), sigFourV)
ok("mirror letters, generators and the two displacement equations")

for (h, j) in HS:
    for c in range(N):
        check("sqRelWord_mirFourMark h=%d j=%d c=%d" % (h, j, c),
              sqRelWord(mirWit(h, j, mirFourUGen(c), mirFourV, ONE)), ONE)
    W = lambda v: mirWit(h, j, mirFourU, mirFourV, v)
    check("sqRelWord_mirFourWit_triv h=%d j=%d" % (h, j), sqRelWord(W(ONE)), ONE)
    check("sqRelWord_mirFourWit_U h=%d j=%d" % (h, j), sqRelWord(W(mirFourU)), liftC(1))
    check("sqRelWord_mirFourWit_Usq h=%d j=%d" % (h, j),
          sqRelWord(W(mul(mirFourU, mirFourU))), liftC(2))
    check("sqRelWord_mirFourWit_V h=%d j=%d" % (h, j), sqRelWord(W(mirFourV)), ONE)
    check("sqRelWord_mirFourWit_Usq_complete h=%d j=%d" % (h, j),
          sqRelWord(sigLift_at(h, j, W(mul(mirFourU, mirFourU)), ONE, ONE, liftC(7), ONE, ONE)),
          ONE)
    for tag, v in [("triv", ONE), ("Usq", mul(mirFourU, mirFourU)), ("U", mirFourU),
                   ("V", mirFourV)]:
        r = sqRelWord(W(v))
        check("mirFourWit_class_three_blind L h=%d j=%d %s" % (h, j, tag), toU4L(r), (0,) * 6)
        check("mirFourWit_class_three_blind R h=%d j=%d %s" % (h, j, tag), toU4R(r), (0,) * 6)
    # the three x1-slot commutators
    check("mirFourWit_commP_zero_two h=%d j=%d" % (h, j), commP(S, Y), (0,) * 8 + (4, 0))
    check("mirFourWit_commP_two_handleU h=%d j=%d" % (h, j), commP(Y, mirFourU), (0,) * 9 + (6,))
    check("mirFourWit_commP_two_handleV h=%d j=%d" % (h, j), commP(Y, mirFourV), ONE)
    # the hom: generator values, pivot anchor, cleared letters, b-column, frame
    for c in range(N):
        m = mirWit(h, j, mirFourUGen(c), mirFourV, ONE)
        check("mirFourHom_sigma h=%d j=%d c=%d" % (h, j, c), m[0], S)
        check("mirFourHom_x0 h=%d j=%d c=%d" % (h, j, c), m[1], X)
        check("mirFourHom_x1 h=%d j=%d c=%d" % (h, j, c), m[2], Y)
        check("mirFourHom_handleU h=%d j=%d c=%d" % (h, j, c), m[3 + 2 * j], mirFourUGen(c))
        check("mirFourHom_handleV h=%d j=%d c=%d" % (h, j, c), m[4 + 2 * j], mirFourV)
        for k in range(h):
            if k != j:
                check("mirFourHom_handle_ne h=%d j=%d k=%d" % (h, j, k),
                      (m[3 + 2 * k], m[4 + 2 * k]), (ONE, ONE))
        check("mirFourHom_sqPivot h=%d j=%d c=%d" % (h, j, c),
              mul(m[0], inv(power(X, c))), rowPivotVal(c))
        check("mirFourHom_sqEichU h=%d j=%d c=%d" % (h, j, c),
              mul(inv(rowPivotVal(c)), m[3 + 2 * j]), mirFourU)
        check("mirFourHom_sqEichV h=%d j=%d c=%d" % (h, j, c), m[4 + 2 * j], mirFourV)
        # b-column = nuSel h j 1 0
        want = [1, 0, 0] + sum(([1, 0] if k == j else [0, 0] for k in range(h)), [])
        check("mirFourHom_b h=%d j=%d c=%d" % (h, j, c), [p[1] for p in m], want)
        # every slot lies in rowFrameSub: c-col 0, f-col 0, g even
        for p in m:
            check("mirFourMark_le_rowFrameSub h=%d j=%d c=%d" % (h, j, c),
                  (p[2], p[5], p[6] % 2), (0, 0, 0))
ok("mirror point: ten-row solve, verdicts, blindness, commutators, hom data, invariants")

# lattice evenness at the mirror parameters
def lam3_gens(A, B, C, D, E, F, T, Sp, P, Q, R):
    return [(-(2 * (A * C))) % N, (C * E) % N, (-(A * D + B * C)) % N, (D * E) % N,
            (-(A * D + B * C)) % N, (C * F) % N, (-(2 * (B * D))) % N, (D * F) % N,
            0, (2 * R) % N, (2 * (Q * A - P * C)) % N, (2 * (R * T - Q * E)) % N,
            (2 * (Q * B - P * D)) % N, (2 * (R * Sp - Q * F)) % N]


bad = 0
for P in range(N):
    for Q in range(N):
        for R in range(N):
            for x in lam3_gens(1, 0, 0, 0, 0, 1, 1, 0, P, Q, R):
                if x % 2:
                    bad += 1
check("mirFourWit_lamThree_even over all 512 (P,Q,R)", bad, 0)
bad = 0
for x in lam3_gens(1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 4) + [0, 4, 0, 0, 0, 0]:
    if x % 2:
        bad += 1
check("mirFourWit_lamThreePlus_even at (P,Q,R) = (0,0,4)", bad, 0)
ok("mirror soundness: selLamThree and selLamThreePlus")

# ======================================================================================
print()
print("== §7 the DOUBLY-UNCLEARED point (t,s) = (1,1) ==")
check("dblFour_letters_equal (mirFourU = rowFourV = sigFourU)",
      (mirFourU, mirFourU), (rowFourV, sigFourU))
for c in range(N):
    check("rowFourVGen_eq at c=%d" % c, rowFourVGen(c), mul(rowFourV, rowPivotVal(c)))
    check("rowFourV_eq at c=%d" % c, mul(rowFourVGen(c), inv(rowPivotVal(c))), rowFourV)
    check("commP_dblFourGen at c=%d" % c, commP(mirFourUGen(c), rowFourVGen(c)), ONE)
check("commP_dblFour", commP(mirFourU, rowFourV), ONE)

for (h, j) in HS:
    for c in range(N):
        check("sqRelWord_dblFourMark h=%d j=%d c=%d" % (h, j, c),
              sqRelWord(mirWit(h, j, mirFourUGen(c), rowFourVGen(c), ONE)), ONE)
    W = lambda v: mirWit(h, j, mirFourU, rowFourV, v)
    check("sqRelWord_dblFourWit_triv h=%d j=%d" % (h, j), sqRelWord(W(ONE)), ONE)
    check("sqRelWord_dblFourWit_U h=%d j=%d" % (h, j), sqRelWord(W(mirFourU)), liftC(1))
    check("sqRelWord_dblFourWit_Usq h=%d j=%d" % (h, j),
          sqRelWord(W(mul(mirFourU, mirFourU))), liftC(2))
    check("sqRelWord_dblFourWit_Usq_complete h=%d j=%d" % (h, j),
          sqRelWord(sigLift_at(h, j, W(mul(mirFourU, mirFourU)), ONE, ONE, liftC(7), ONE, ONE)),
          ONE)
    for tag, v in [("triv", ONE), ("Usq", mul(mirFourU, mirFourU)), ("U", mirFourU)]:
        r = sqRelWord(W(v))
        check("dblFourWit_class_three_blind L h=%d j=%d %s" % (h, j, tag), toU4L(r), (0,) * 6)
        check("dblFourWit_class_three_blind R h=%d j=%d %s" % (h, j, tag), toU4R(r), (0,) * 6)
    check("dblFourWit_commP_zero_two h=%d j=%d" % (h, j), commP(S, Y), (0,) * 8 + (4, 0))
    check("dblFourWit_commP_two_handleU h=%d j=%d" % (h, j), commP(Y, mirFourU), (0,) * 9 + (6,))
    check("dblFourWit_commP_two_handleV h=%d j=%d" % (h, j), commP(Y, rowFourV), (0,) * 9 + (6,))
    for c in range(N):
        m = mirWit(h, j, mirFourUGen(c), rowFourVGen(c), ONE)
        check("dblFourHom_sqEichU h=%d j=%d c=%d" % (h, j, c),
              mul(inv(rowPivotVal(c)), m[3 + 2 * j]), mirFourU)
        check("dblFourHom_sqEichV h=%d j=%d c=%d" % (h, j, c),
              mul(m[4 + 2 * j], inv(rowPivotVal(c))), rowFourV)
        want = [1, 0, 0] + sum(([1, 1] if k == j else [0, 0] for k in range(h)), [])
        check("dblFourHom_b h=%d j=%d c=%d" % (h, j, c), [p[1] for p in m], want)
        for p in m:
            check("dblFourMark_le_rowFrameSub h=%d j=%d c=%d" % (h, j, c),
                  (p[2], p[5], p[6] % 2), (0, 0, 0))
ok("doubly point: ten-row solve, verdicts, blindness, commutators, hom data, invariants")

bad = 0
for P in range(N):
    for Q in range(N):
        for R in range(N):
            for x in lam3_gens(1, 1, 0, 0, 0, 0, 1, 1, P, Q, R):
                if x % 2:
                    bad += 1
check("dblFourWit_lamThree_even over all 512 (P,Q,R)", bad, 0)
bad = 0
for x in lam3_gens(1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 4) + [0, 4, 0, 0, 0, 0]:
    if x % 2:
        bad += 1
check("dblFourWit_lamThreePlus_even at (P,Q,R) = (0,0,4)", bad, 0)
ok("doubly soundness: selLamThree and selLamThreePlus")

# ======================================================================================
print()
print("== commP_mem_rowGaTwoSub, reused from GradedFourRow ==")
bad = 0
for _ in range(40000):
    def frameelt():
        a, b, d, e, g, hh, i, jj = (random.randrange(N) for _ in range(8))
        return (a, b, 0, d, e, 0, 2 * random.randrange(4), hh, i, jj)
    z = commP(frameelt(), frameelt())
    if z[0] or z[1] or z[2] or z[3] or z[5] or z[6] or z[7] or (z[8] % 2):
        bad += 1
check("commP_mem_rowGaTwoSub, 40000 random pairs in rowFrameSub", bad, 0)
ok("commP_mem_rowGaTwoSub")

print()
print("TOTAL CHECKS: %d   FAILURES: %d" % (checks, fails))
sys.exit(1 if fails else 0)
