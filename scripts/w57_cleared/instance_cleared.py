"""W57-CLEARED step 3: every explicit claim of GQ2/Dyadic/SqCore/GradedFourCleared.lean,
mirrored numerically one for one.

The Lean file is stated at arbitrary handle count `h` and arbitrary live handle `j`, so every
claim below is checked at `h = 1, 2, 3, 4` and every `j < h`, and every claim mentioning the
pivot residue at all eight residues `c` of `gr3Pi sqPivotExp`.

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
from u5lib import *

random.seed(1957)
fails = 0
checks = 0


def check(name, got, want):
    global fails, checks
    checks += 1
    if got != want:
        fails += 1
        print("FAIL " + name + "  got %s want %s" % (got, want))


def bulk(name, n, bad):
    """Record `n` individual comparisons of which `bad` failed."""
    global fails, checks
    checks += n
    fails += bad
    print(("PASS " if bad == 0 else "FAIL ") + name + "  (%d comparisons)" % n)


def ok(name):
    print("PASS " + name)


HS = [(h, j) for h in (1, 2, 3, 4) for j in range(h)]
S, X, Y = sigFourMark, sigFourX, sigFourY


def clrWit(h, j, v):
    return cwWit(h, j, sigFourY, clrFourU, clrFourV, v)


def liveWit(h, j, v):
    return cwWit(h, j, liveFourY, liveFourU, liveFourV, v)


# ======================================================================================
print("== §1 the cleared row nuSel h j 0 0 at every handle count ==")
check("commP_clrFour", commP(clrFourU, clrFourV), ONE)
check("clrFourU_chiA", clrFourU[0] % 2, 1)
check("sigFourU squared is sigFourV", mul(clrFourU, clrFourU), clrFourV)
for (h, j) in HS:
    check("sqRelWord_clrFourMark h=%d j=%d" % (h, j), sqRelWord(clrWit(h, j, ONE)), ONE)
    check("sqRelWord_clrFourWit_triv h=%d j=%d" % (h, j), sqRelWord(clrWit(h, j, ONE)), ONE)
    for v in [ONE, clrFourU, clrFourV, mul(clrFourU, clrFourU), (5, 0, 0, 4, 2, 0, 3, 7, 6, 1)]:
        check("sqRelWord_clrFourWit h=%d j=%d" % (h, j), sqRelWord(clrWit(h, j, v)),
              sqWord(mul(S, v), X, Y))
    check("sqRelWord_clrFourWit_U h=%d j=%d" % (h, j), sqRelWord(clrWit(h, j, clrFourU)),
          liftC(1))
    check("sqRelWord_clrFourWit_Usq h=%d j=%d" % (h, j),
          sqRelWord(clrWit(h, j, mul(clrFourU, clrFourU))), liftC(2))
    check("sqRelWord_clrFourWit_V h=%d j=%d" % (h, j), sqRelWord(clrWit(h, j, clrFourV)),
          liftC(2))
    check("sqRelWord_clrFourWit_Usq_complete h=%d j=%d" % (h, j),
          sqRelWord(sigLift_at(h, j, clrWit(h, j, mul(clrFourU, clrFourU)), ONE, ONE, liftC(7),
                               ONE, ONE)), ONE)
    for tag, v in [("triv", ONE), ("Usq", mul(clrFourU, clrFourU)), ("U", clrFourU)]:
        r = sqRelWord(clrWit(h, j, v))
        check("clrFourWit_class_three_blind L h=%d j=%d %s" % (h, j, tag), toU4L(r), (0,) * 6)
        check("clrFourWit_class_three_blind R h=%d j=%d %s" % (h, j, tag), toU4R(r), (0,) * 6)
    m = clrWit(h, j, ONE)
    check("clrFourMark_zero h=%d j=%d" % (h, j), m[0], S)
    check("clrFourMark_one h=%d j=%d" % (h, j), m[1], X)
    check("clrFourMark_two h=%d j=%d" % (h, j), m[2], Y)
    check("clrFourMark_handleU h=%d j=%d" % (h, j), m[3 + 2 * j], clrFourU)
    check("clrFourMark_handleV h=%d j=%d" % (h, j), m[4 + 2 * j], clrFourV)
    for k in range(h):
        if k != j:
            check("clrFourMark_handle_ne h=%d j=%d k=%d" % (h, j, k),
                  (m[3 + 2 * k], m[4 + 2 * k]), (ONE, ONE))
    for c in range(N):
        check("clrFourHom_sqPivot h=%d j=%d c=%d" % (h, j, c), mul(m[0], inv(power(X, c))),
              rowPivotVal(c))
    # the row is cleared, so both Eichler letters are the raw generators
    check("clrFourHom_sqEichU h=%d j=%d" % (h, j), m[3 + 2 * j], clrFourU)
    check("clrFourHom_sqEichV h=%d j=%d" % (h, j), m[4 + 2 * j], clrFourV)
    check("clrFourHom_b h=%d j=%d" % (h, j), [p[1] for p in m], [1, 0, 0] + [0] * (2 * h))
    check("clrFourWit_commP_zero_two h=%d j=%d" % (h, j), commP(m[0], m[2]), (0,) * 8 + (4, 0))
    check("clrFourWit_commP_two_handleU h=%d j=%d" % (h, j), commP(m[2], m[3 + 2 * j]),
          (0,) * 9 + (6,))
    check("clrFourWit_commP_two_handleV h=%d j=%d" % (h, j), commP(m[2], m[4 + 2 * j]),
          (0,) * 9 + (4,))
    for p in m:
        check("clrFourMark_le_rowFrameSub h=%d j=%d" % (h, j), in_row_frame(p), True)
ok("cleared row: ten-row solve, verdicts, blindness, hom data, commutators, invariants")


def lam3_gens(A, B, C, D, E, F, T, Sp, P, Q, R):
    return [(-(2 * (A * C))) % N, (C * E) % N, (-(A * D + B * C)) % N, (D * E) % N,
            (-(A * D + B * C)) % N, (C * F) % N, (-(2 * (B * D))) % N, (D * F) % N,
            0, (2 * R) % N, (2 * (Q * A - P * C)) % N, (2 * (R * T - Q * E)) % N,
            (2 * (Q * B - P * D)) % N, (2 * (R * Sp - Q * F)) % N]


bad = 0
for P in range(N):
    for Q in range(N):
        for R in range(N):
            for x in lam3_gens(1, 2, 0, 0, 0, 0, 1, 0, P, Q, R):
                if x % 2:
                    bad += 1
check("clrFourWit_lamThree_even over all 512 (P,Q,R)", bad, 0)
bad = 0
for x in lam3_gens(1, 2, 0, 0, 0, 0, 1, 0, 0, 0, 4) + [0, 4, 0, 6, 0, 4]:
    if x % 2:
        bad += 1
check("clrFourWit_lamThreePlus_even at (P,Q,R) = (0,0,4)", bad, 0)
ok("cleared soundness: selLamThree and selLamThreePlus")

# ======================================================================================
print()
print("== §2 the handle block is invisible to the sigma forcing ==")
bad = 0
n = 0
for _ in range(30000):
    x = tuple(random.randrange(N) for _ in range(10)); x = (x[0], 0) + x[2:]
    y = tuple(random.randrange(N) for _ in range(10)); y = (y[0], 0) + y[2:]
    v = tuple(random.randrange(N) for _ in range(10)); v = (v[0], 0) + v[2:]
    h, j = random.choice(HS)
    U1, V1, U2, V2 = (tuple(random.randrange(N) for _ in range(10)) for _ in range(4))
    m1 = mirTuple(h, j, S, x, y, U1, V1)
    m2 = mirTuple(h, j, S, x, y, U2, V2)
    d1 = mirTuple(h, j, mul(S, v), x, y, U1, V1)
    d2 = mirTuple(h, j, mul(S, v), x, y, U2, V2)
    for k in (6, 7, 8, 9):
        n += 1
        if ((sqRelWord(d1)[k] - sqRelWord(m1)[k]) % N
                != (sqRelWord(d2)[k] - sqRelWord(m2)[k]) % N):
            bad += 1
bulk("sqRelWord_sigFourDress_handle_blind, 30000 random pairs of markings", n, bad)

bad = 0
for _ in range(30000):
    x = tuple(random.randrange(N) for _ in range(10)); x = (x[0], 0) + x[2:]
    y = tuple(random.randrange(N) for _ in range(10)); y = (y[0], 0) + y[2:]
    v = tuple(random.randrange(N) for _ in range(10)); v = (v[0], 0) + v[2:]
    h, j = random.choice(HS)
    U1, V1 = (tuple(random.randrange(N) for _ in range(10)) for _ in range(2))
    m1 = mirTuple(h, j, S, x, y, U1, V1)
    d1 = mirTuple(h, j, mul(S, v), x, y, U1, V1)
    if ((sqRelWord(d1)[9] - sqRelWord(m1)[9]) % N) != sigFourRead(v, x, y):
        bad += 1
    if ((sqRelWord(d1)[6] - sqRelWord(m1)[6]) % N) != sigFourG(v, x):
        bad += 1
    if ((sqRelWord(d1)[7] - sqRelWord(m1)[7]) % N) != sigFourH(v, x):
        bad += 1
    if ((sqRelWord(d1)[8] - sqRelWord(m1)[8]) % N) != sigFourI(v, x):
        bad += 1
bulk("sqRelWord_mirTuple_dress_response(_low), 30000 random instances", 120000, bad)

bad = 0
for _ in range(30000):
    y = (0, 0, 0, 0, random.randrange(N), random.randrange(N), random.randrange(N),
         random.randrange(N), random.randrange(N), random.randrange(N))
    v = tuple(random.randrange(N) for _ in range(10)); v = (v[0], 0) + v[2:]
    h, j = random.choice(HS)
    U1, V1 = (tuple(random.randrange(N) for _ in range(10)) for _ in range(2))
    m1 = mirTuple(h, j, S, X, y, U1, V1)
    d1 = mirTuple(h, j, mul(S, v), X, y, U1, V1)
    if (sqRelWord(d1)[9] % 2) != ((sqRelWord(m1)[9] + v[0]) % 2):
        bad += 1
bulk("mirTuple_sigma_bit, arbitrary handle letters", 30000, bad)

bad = 0
for _ in range(30000):
    s = tuple(random.randrange(N) for _ in range(10))
    x = tuple(random.randrange(N) for _ in range(10))
    y = tuple(random.randrange(N) for _ in range(10))
    U1, V1 = (tuple(random.randrange(N) for _ in range(10)) for _ in range(2))
    h, j = random.choice(HS)
    W, C = sqWord(s, x, y), commP(U1, V1)
    if (sqRelWord(mirTuple(h, j, s, x, y, U1, V1))[9]
            != (W[9] + (C[9] + W[0] * C[8] + W[4] * C[6])) % N):
        bad += 1
bulk("sqRelWord_mirTuple_j, arbitrary core and arbitrary block", 30000, bad)
ok("handle-blindness of the four top responses and of the selection bit")

# ======================================================================================
print()
print("== §3 the gauge parity theorem and the automatic evenness of a live block ==")
bad = tried = 0
for _ in range(100000):
    x = (2 * random.randrange(4), 0, 2 * random.randrange(4), 2 * random.randrange(4),
         2 * random.randrange(4), 2 * random.randrange(4), 2 * random.randrange(4),
         random.randrange(N), random.randrange(N), random.randrange(N))
    y = (2 * random.randrange(4), 0, 2 * random.randrange(4), 2 * random.randrange(4),
         random.randrange(N), random.randrange(N), random.randrange(N),
         random.randrange(N), random.randrange(N), random.randrange(N))
    w = sqWord(S, x, y)
    tried += 1
    if any(w[k] % 2 for k in range(9)) or w[1] != 0:
        bad += 1
bulk("sqWord_sigFourMark_gauge_even over random gauge-legal (x, y)", tried, bad)
bad = 0
for _ in range(100000):
    x = (2 * random.randrange(4), 0, 2 * random.randrange(4), 2 * random.randrange(4),
         2 * random.randrange(4), 2 * random.randrange(4), 2 * random.randrange(4),
         random.randrange(N), random.randrange(N), random.randrange(N))
    y = (2 * random.randrange(4), 0, 2 * random.randrange(4), 2 * random.randrange(4),
         random.randrange(N), random.randrange(N), random.randrange(N),
         random.randrange(N), random.randrange(N), random.randrange(N))
    C = inv(sqWord(S, x, y))            # the block the relator forces
    if C[7] % 2 or C[8] % 2:
        bad += 1
bulk("commP_gaThree_even_of_relator over random gauge-legal cores", 100000, bad)
ok("gauge parity, and the forced block is even where the increment reads it")

# ======================================================================================
print()
print("== §4-§5 the live-handle-block point ==")
check("liveFourU_eq", liveFourU, sigFourU)
check("liveFourY_eq", liveFourY, mul(sigFourY, (0,) * 7 + (3, 0, 0)))
check("liveFourV_eq", liveFourV, mul((0, 0, 0, 0, 0, 2, 0, 0, 0, 0), sigFourV))
check("commP_liveFour", commP(liveFourU, liveFourV), (0,) * 7 + (2, 0, 0))
check("commP_liveFour_ne_one", commP(liveFourU, liveFourV) != ONE, True)
check("the block has order four", [(2 * k) % N for k in (1, 2)], [2, 4])
check("sqWord_liveFour", sqWord(S, X, liveFourY), (0,) * 7 + (6, 0, 0))
check("sqWord_clrFour", sqWord(S, X, sigFourY), ONE)
check("liveFourU_chiA", liveFourU[0] % 2, 1)
for (h, j) in HS:
    check("sqRelWord_liveFourMark h=%d j=%d" % (h, j), sqRelWord(liveWit(h, j, ONE)), ONE)
    for v in [ONE, liveFourU, mul(liveFourU, liveFourU), (5, 0, 0, 4, 2, 0, 3, 7, 6, 1)]:
        check("sqRelWord_liveFourWit h=%d j=%d" % (h, j), sqRelWord(liveWit(h, j, v)),
              mul(sqWord(mul(S, v), X, liveFourY), commP(liveFourU, liveFourV)))
    check("sqRelWord_liveFourWit_U h=%d j=%d" % (h, j), sqRelWord(liveWit(h, j, liveFourU)),
          liftC(1))
    check("sqRelWord_liveFourWit_Usq h=%d j=%d" % (h, j),
          sqRelWord(liveWit(h, j, mul(liveFourU, liveFourU))), liftC(2))
    check("sqRelWord_liveFourWit_Usq_complete h=%d j=%d" % (h, j),
          sqRelWord(sigLift_at(h, j, liveWit(h, j, mul(liveFourU, liveFourU)), ONE, ONE,
                               liftC(7), ONE, ONE)), ONE)
    for tag, v in [("triv", ONE), ("Usq", mul(liveFourU, liveFourU)), ("U", liveFourU)]:
        r = sqRelWord(liveWit(h, j, v))
        check("liveFourWit_class_three_blind L h=%d j=%d %s" % (h, j, tag), toU4L(r), (0,) * 6)
        check("liveFourWit_class_three_blind R h=%d j=%d %s" % (h, j, tag), toU4R(r), (0,) * 6)
    m = liveWit(h, j, ONE)
    check("liveFourMark_zero h=%d j=%d" % (h, j), m[0], S)
    check("liveFourMark_one h=%d j=%d" % (h, j), m[1], X)
    check("liveFourMark_two h=%d j=%d" % (h, j), m[2], liveFourY)
    check("liveFourMark_handleU h=%d j=%d" % (h, j), m[3 + 2 * j], liveFourU)
    check("liveFourMark_handleV h=%d j=%d" % (h, j), m[4 + 2 * j], liveFourV)
    for k in range(h):
        if k != j:
            check("liveFourMark_handle_ne h=%d j=%d k=%d" % (h, j, k),
                  (m[3 + 2 * k], m[4 + 2 * k]), (ONE, ONE))
    for c in range(N):
        check("liveFourHom_sqPivot h=%d j=%d c=%d" % (h, j, c), mul(m[0], inv(power(X, c))),
              rowPivotVal(c))
    check("liveFourHom_commP_ne_one h=%d j=%d" % (h, j),
          commP(m[3 + 2 * j], m[4 + 2 * j]) != ONE, True)
    check("liveFourHom_b h=%d j=%d" % (h, j), [p[1] for p in m], [1, 0, 0] + [0] * (2 * h))
    check("liveFourWit_commP_data h=%d j=%d" % (h, j),
          (commP(m[0], m[2]), commP(m[2], m[3 + 2 * j]), commP(m[2], m[4 + 2 * j])),
          ((0,) * 8 + (4, 0), (0,) * 9 + (6,), (0,) * 9 + (4,)))
    for p in m:
        check("liveFourMark_le_liveFrameSub h=%d j=%d" % (h, j), in_live_frame(p), True)
    check("...and the v-letter is NOT in rowFrameSub h=%d j=%d" % (h, j),
          in_row_frame(liveFourV), False)
    check("sqArbFrame_sigma_bit_live h=%d j=%d" % (h, j),
          [sqRelWord(liveWit(h, j, v))[9] % 2
           for v in (ONE, liveFourU, mul(liveFourU, liveFourU))], [0, 1, 0])
ok("live point: ten-row solve with a LIVE block, verdicts, blindness, hom data, invariants")

check("commP_liveFour_even", (commP(liveFourU, liveFourV)[7] % 2,
                              commP(liveFourU, liveFourV)[8] % 2), (0, 0))
bad = 0
for P in range(N):
    for Q in range(N):
        for R in range(N):
            for x in lam3_gens(1, 2, 0, 0, 0, 0, 1, 0, P, Q, R):
                if x % 2:
                    bad += 1
check("liveFourWit_lamThree_even (the committed parameters) over all 512 (P,Q,R)", bad, 0)

# ======================================================================================
print()
print("== §6 the widened invariants ==")


def frame_elt():
    a, b, d, e, hh, i, jj = (random.randrange(N) for _ in range(7))
    return (a, b, 0, d, e, 2 * random.randrange(4), 2 * random.randrange(4), hh, i, jj)


bad = 0
for _ in range(40000):
    p, q = frame_elt(), frame_elt()
    check_mul = mul(p, q)
    check_inv = inv(p)
    if not (in_live_frame(check_mul) and in_live_frame(check_inv)):
        bad += 1
bulk("liveFrameSub is a subgroup, random pairs", 40000, bad)
bad = 0
for _ in range(40000):
    z = commP(frame_elt(), frame_elt())
    if z[0] or z[1] or z[2] or z[3] or z[5] or z[6] or (z[7] % 2) or (z[8] % 2):
        bad += 1
bulk("commP_mem_liveGaTwoSub, random pairs in liveFrameSub", 40000, bad)
bad = 0
for _ in range(40000):
    p = (random.randrange(N), random.randrange(N), 0, random.randrange(N), random.randrange(N),
         0, 2 * random.randrange(4), random.randrange(N), random.randrange(N),
         random.randrange(N))
    if not in_live_frame(p):
        bad += 1
bulk("rowFrameSub_le_liveFrameSub, random rowFrameSub elements", 40000, bad)


def row_frame_b0():
    a, d, e, hh, i, jj = (random.randrange(N) for _ in range(6))
    return (a, 0, 0, d, e, 0, 2 * random.randrange(4), hh, i, jj)


bad = 0
for _ in range(40000):
    z = commP(row_frame_b0(), row_frame_b0())
    if z[:9] != (0,) * 9:
        bad += 1
bulk("commP_central_of_rowFrameSub: inside the wave-55 invariants a nu'-trivial block is "
     "CENTRAL", 40000, bad)
check("liveFour_not_rowGaTwoSub (the block's h-coordinate does not vanish)",
      commP(liveFourU, liveFourV)[7] != 0, True)
ok("liveFrameSub / liveGaTwoSub / commP_mem_liveGaTwoSub / the sharpest bound")

# ======================================================================================
print()
print("== §7 the forcing at the live point ==")
bad = 0
for _ in range(40000):
    z0 = tuple(random.randrange(N) for _ in range(10))
    w1j, w2j = random.randrange(N), random.randrange(N)
    z3 = (0,) * 7 + (2 * random.randrange(4), 2 * random.randrange(4), 0)
    z4 = (0,) * 7 + (2 * random.randrange(4), 2 * random.randrange(4), 0)
    inc = ((z0[7] * X[3] - z0[8] * X[0]) + (-4 * w1j + 2 * w2j)
           + ((z3[7] * liveFourV[3] - z3[8] * liveFourV[0])
              + (liveFourU[0] * z4[8] - liveFourU[3] * z4[7]))) % N
    if inc % 2:
        bad += 1
bulk("liveFourWit_increment_even, random even-dressing instances", 40000, bad)

# the forcing itself, exhaustively over the achievable refinements at the live point
ACH = [red((0,) * 7 + (2 * a, 2 * k, 0)) for a in range(4) for k in range(4)]
for (h, j) in HS[:3]:
    kills = 0
    for z0 in ACH:
        for z3 in ACH:
            for z4 in ACH:
                for w1 in range(N):
                    for w2 in range(N):
                        if sqRelWord(sigLift_at(h, j, liveWit(h, j, liveFourU), z0, liftC(w1),
                                                liftC(w2), z3, z4)) == ONE:
                            kills += 1
    bulk("liveFourWit_sigma_forced h=%d j=%d: the odd dressing survives every achievable "
         "refinement" % (h, j), len(ACH) ** 3 * 64, kills)
ok("liveFourWit_increment_even / _sigma_forced / sqArbFrame_sigma_forced_live")

check("liveFour_forcing_nonvacuous (chi_a of the u-letter is odd)", liveFourU[0] % 2, 1)
for (h, j) in HS:
    check("liveFour_escape_separates h=%d j=%d" % (h, j),
          (commP(liveFourU, liveFourV) != ONE,
           sqRelWord(liveWit(h, j, mul(liveFourU, liveFourU))),
           sqRelWord(liveWit(h, j, liveFourU))), (True, liftC(2), liftC(1)))
ok("liveFour_escape_separates, at every handle count")

print()
print("TOTAL CHECKS: %d   FAILURES: %d" % (checks, fails))
sys.exit(1 if fails else 0)
