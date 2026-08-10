"""W55-ROW step 3: every explicit Lean claim of GQ2/Dyadic/SqCore/GradedFourRow.lean, checked
numerically one for one.  Each block names the Lean declaration it mirrors.
"""
import sys, os, random, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from u5lib import *

random.seed(20260811)
fails = 0


def check(name, got, want):
    global fails
    ok = (got == want)
    if not ok:
        fails += 1
    print(("PASS " if ok else "FAIL ") + name + ("" if ok else "  got %s want %s" % (got, want)))


def rowPivotVal(c):
    return red((-(2 * c), 1, 0, 0, 0, 0, 0, 0, -c, c * c + c))


rowFourV = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
rowFourU = (0, 0, 0, 1, 0, 0, 0, 0, 0, 0)


def rowFourVGen(c):
    return red((1 - 2 * c, 1, 0, 0, 1, 0, 0, 0, -c, c * c))


def rowTuple(S, X, Y, U, V):
    return [S, X, Y, U, V]


def rowFourMark(c):
    return rowTuple(sigFourMark, sigFourX, sigFourY, rowFourU, rowFourVGen(c))


def rowFourWit(v):
    return rowTuple(mul(sigFourMark, v), sigFourX, sigFourY, rowFourU, rowFourV)


print("== section 1: sqRelWord_e_displace, rowFour_chiA_handleU_forced ==")
bad = 0
for _ in range(4000):
    S, X, Y, U, V, P = [tuple(random.randrange(N) for _ in range(10)) for _ in range(6)]
    lhs = sqRelWord(rowTuple(S, X, Y, U, mul(V, P)))[4]
    rhs = (sqRelWord(rowTuple(S, X, Y, U, V))[4] + (U[0] * P[1] - U[1] * P[0])) % N
    if lhs != rhs:
        bad += 1
check("sqRelWord_e_displace at 4000 random tuples", bad, 0)
# the corollary: both relators trivial, P.b = 1, U.b = 0  =>  U.a = 0
bad = 0
for _ in range(200000):
    U = (random.randrange(N), 0) + tuple(random.randrange(N) for _ in range(8))
    P = (random.randrange(N), 1) + tuple(random.randrange(N) for _ in range(8))
    V = tuple(random.randrange(N) for _ in range(10))
    S, X, Y = [tuple(random.randrange(N) for _ in range(10)) for _ in range(3)]
    if (sqRelWord(rowTuple(S, X, Y, U, mul(V, P))) == ONE
            and sqRelWord(rowTuple(S, X, Y, U, V)) == ONE and U[0] != 0):
        bad += 1
check("rowFour_chiA_handleU_forced: no counterexample in 200000 random draws", bad, 0)

print()
print("== section 2: the point ==")
for c in range(N):
    check("rowFourVGen_eq at c=%d" % c, rowFourVGen(c), mul(rowFourV, rowPivotVal(c)))
    check("rowFourV_eq at c=%d" % c, mul(rowFourVGen(c), inv(rowPivotVal(c))), rowFourV)
    check("sqRelWord_rowFourMark at c=%d" % c, sqRelWord(rowFourMark(c)), ONE)
check("sqRelWord_rowFourWit_triv", sqRelWord(rowFourWit(ONE)), ONE)
check("rowFourU_chiA", rowFourU[0], 0)
check("rowFourV_chiA", selPar(rowFourV[0]), 1)
check("rowFourV_sq", mul(rowFourV, rowFourV), sigFourV)

print()
print("== section 3: the verdicts ==")
check("sqRelWord_rowFourWit_Vsq", sqRelWord(rowFourWit(sigFourV)), liftC(2))
check("sqRelWord_rowFourWit_V", sqRelWord(rowFourWit(rowFourV)), liftC(1))
check("sqRelWord_rowFourWit_U", sqRelWord(rowFourWit(rowFourU)), ONE)
check("sqRelWord_rowFourWit_Vsq_complete",
      sqRelWord(sigLift(rowFourWit(sigFourV), ONE, ONE, liftC(7), ONE, ONE)), ONE)
for nm, v in [("1", ONE), ("Vsq", sigFourV), ("V", rowFourV), ("U", rowFourU)]:
    r = sqRelWord(rowFourWit(v))
    check("rowFourWit_class_three_blind toU4L at %s" % nm,
          (r[0], r[1], r[2], r[4], r[5], r[7]), (0,) * 6)
    check("rowFourWit_class_three_blind toU4R at %s" % nm,
          (r[1], r[2], r[3], r[5], r[6], r[8]), (0,) * 6)

print()
print("== section 4/5: the b-column and the bit ==")
nu_row = [1, 0, 0, 0, 1]
for c in range(N):
    check("rowFourHom_b at c=%d" % c, [s[1] for s in rowFourMark(c)], nu_row)
bad = 0
for _ in range(20000):
    v = (random.randrange(N), 0) + tuple(random.randrange(N) for _ in range(8))
    if sqRelWord(rowFourWit(v))[9] % 2 != v[0] % 2:
        bad += 1
check("rowFourWit_bit at 20000 random nu'-trivial dressings", bad, 0)

print()
print("== section 6: soundness ==")
check("rowFourWit_commP_zero_two", commP(rowFourWit(ONE)[0], rowFourWit(ONE)[2]),
      (0, 0, 0, 0, 0, 0, 0, 0, 4, 0))
check("rowFourWit_commP_two_handleU", commP(rowFourWit(ONE)[2], rowFourWit(ONE)[3]), ONE)
check("rowFourWit_commP_two_handleV", commP(rowFourWit(ONE)[2], rowFourWit(ONE)[4]),
      (0, 0, 0, 0, 0, 0, 0, 0, 0, 6))
# rowFourMark_le_rowFrameSub: the three invariants on every slot, at every residue
bad = 0
for c in range(N):
    for s in rowFourMark(c):
        if s[2] != 0 or s[5] != 0 or s[6] % 2:
            bad += 1
check("rowFourMark_le_rowFrameSub: c-column 0, f-column 0, g even on every slot", bad, 0)
# commP_mem_rowGaTwoSub, as a general algebraic fact
bad = 0
for _ in range(40000):
    def frame_elt():
        p = [random.randrange(N) for _ in range(10)]
        p[2] = 0
        p[5] = 0
        p[6] = 2 * random.randrange(4)
        return tuple(p)
    z = commP(frame_elt(), frame_elt())
    if z[0] or z[1] or z[2] or z[3] or z[5] or z[6] or z[7] or (z[8] % 2):
        bad += 1
check("commP_mem_rowGaTwoSub at 40000 random invariant pairs", bad, 0)
# rowFourWit_increment_even: the closed-form increment against the translation identity
bad = 0
for _ in range(20000):
    z0 = red((0, 0, 0, 0, 0, 0, 0, random.randrange(N), random.randrange(N),
              random.randrange(N)))
    z3 = red((0, 0, 0, 0, 0, 0, 0, 2 * random.randrange(4), 2 * random.randrange(4), 0))
    z4 = red((0, 0, 0, 0, 0, 0, 0, 2 * random.randrange(4), 2 * random.randrange(4), 0))
    w1, w2 = liftC(random.randrange(N)), liftC(random.randrange(N))
    v = (random.randrange(N), 0) + tuple(random.randrange(N) for _ in range(8))
    m = rowFourWit(v)
    incr = ((z0[7] * m[1][3] - z0[8] * m[1][0]) + (-4 * w1[9] + 2 * w2[9])
            + ((z3[7] * m[4][3] - z3[8] * m[4][0]) + (m[3][0] * z4[8] - m[3][3] * z4[7]))) % N
    if incr % 2:
        bad += 1
    if sqRelWord(sigLift(m, z0, w1, w2, z3, z4)) != mul(sqRelWord(m), liftC(incr)):
        bad += 1
check("sqRelWord_sigLift + rowFourWit_increment_even at 20000 random moves", bad, 0)

print()
print("TOTAL FAILURES: %d" % fails)
sys.exit(1 if fails else 0)
