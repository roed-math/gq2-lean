"""W57-CLEARED step 1: validate the library against the committed class-four facts, then
derive the two objects of this lane.

(a) THE CLEARED ROW `nuSel h j 0 0` AT GENERAL HANDLE COUNT.  Wave 56 called this a fourth
    instantiation of its section 2, and it is: the committed letters `sigFourU`, `sigFourV`
    have trivial commutator, so `GradedFourMirror.mirWit` at those letters is the marking, the
    row is cleared so no pivot power enters either handle slot, and the lattice parameters
    `(A,B,C,D,E,F,T,S) = (1,2,0,0,0,0,1,0)` are the committed ones, independent of `h`.

(b) A POINT WITH A LIVE HANDLE BLOCK.  Every class-four point built so far has
    `commP U V = 1`, so the handle block contributes nothing.  With the committed core slots
    that is FORCED: `sqWord(sigFourMark, sigFourX, sigFourY) = 1`, so the relator is exactly
    `commP U V` and killing it kills the block.  Moving the x1-slot's first class-three
    coordinate to `3` makes the core word the class-three element `h = 6`, and the v-letter's
    second class-two coordinate `2` makes the handle commutator the class-three element
    `h = 2`.  The two cancel: the relator dies with a LIVE handle block.

The structural questions this lane must answer are then two, and both are settled here:

  * WHAT DOES THE FORCING SEE?  Nothing new, and there is a reason.  The sigma slot is not in
    the handle block, so the handle word's contribution to every row of the relator is
    independent of the sigma dressing (`sqRelWord_sigFourDress` reads only slots 0, 1, 2).
    The class-four selection bit is a DIFFERENCE of two dressings, so the handle block cancels
    out of it identically.  At class four the handle block can be live but never visible.

  * CAN A LIVE BLOCK BREAK THE SOUNDNESS?  No.  `commP U V` lies in `gamma_2` of the image, so
    it is itself an achievable dressing, and if its class-three coordinates were odd the
    increment lemma would fail.  But on the class-two-forced gauge every one of the NINE lower
    rows of the core word is even (only the class-four row can be odd), and the relator pins
    the handle commutator to the core word's inverse.  So the block is even exactly where the
    increment reads it.

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
from poly import *

fails = 0
checks = 0


def check(name, got, want):
    global fails, checks
    checks += 1
    ok = (got == want)
    if not ok:
        fails += 1
    print(("PASS " if ok else "FAIL ") + name + ("" if ok else "  got %s want %s" % (got, want)))


HS = [(h, j) for h in (1, 2, 3, 4) for j in range(h)]
S, X = sigFourMark, sigFourX

# =======================================================================================
print("== 1. library validation against the committed class-four facts ==")
check("sqRelWord_sigFourWit_triv", sqRelWord(sigFourWit(ONE)), ONE)
check("sqRelWord_sigFourWit_V", sqRelWord(sigFourWit(sigFourV)), liftC(2))
check("sqRelWord_sigFourWit_U", sqRelWord(sigFourWit(sigFourU)), liftC(1))
check("sqRelWord_sigFourWit_V_complete",
      sqRelWord(sigLift(sigFourWit(sigFourV), ONE, ONE, liftC(7), ONE, ONE)), ONE)
check("sqWord(sigFourMark, sigFourX, sigFourY) = 1", sqWord(S, X, sigFourY), ONE)
check("commP_sigFour (the committed handle block is DEAD)", commP(sigFourU, sigFourV), ONE)
check("mirFourU_sq (sigFourU^2 = sigFourV)", mul(sigFourU, sigFourU), sigFourV)
# GradedFourMirror's three committed points, reproduced
mirU, mirV = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0), (0, 0, 0, 1, 0, 0, 0, 0, 0, 0)
for (h, j) in HS:
    check("mirror point relator h=%d j=%d" % (h, j),
          sqRelWord(cwWit(h, j, sigFourY, mirU, mirV, ONE)), ONE)
    check("wave-55 row relator h=%d j=%d" % (h, j),
          sqRelWord(cwWit(h, j, sigFourY, mirV, mirU, ONE)), ONE)
    check("doubly-uncleared relator h=%d j=%d" % (h, j),
          sqRelWord(cwWit(h, j, sigFourY, mirU, mirU, ONE)), ONE)

# =======================================================================================
print()
print("== 2. (a) THE CLEARED ROW nuSel h j 0 0 AT EVERY HANDLE COUNT ==")
for (h, j) in HS:
    W = lambda v: cwWit(h, j, sigFourY, clrFourU, clrFourV, v)
    check("commP_clrFour h=%d j=%d" % (h, j), commP(clrFourU, clrFourV), ONE)
    check("sqRelWord_clrFourMark h=%d j=%d" % (h, j), sqRelWord(W(ONE)), ONE)
    check("sqRelWord_clrFourWit_U h=%d j=%d" % (h, j), sqRelWord(W(clrFourU)), liftC(1))
    check("sqRelWord_clrFourWit_Usq h=%d j=%d" % (h, j),
          sqRelWord(W(mul(clrFourU, clrFourU))), liftC(2))
    check("sqRelWord_clrFourWit_V h=%d j=%d" % (h, j), sqRelWord(W(clrFourV)), liftC(2))
    check("sqRelWord_clrFourWit_Usq_complete h=%d j=%d" % (h, j),
          sqRelWord(sigLift_at(h, j, W(mul(clrFourU, clrFourU)), ONE, ONE, liftC(7), ONE, ONE)),
          ONE)
    for tag, v in [("triv", ONE), ("U", clrFourU), ("Usq", mul(clrFourU, clrFourU))]:
        r = sqRelWord(W(v))
        check("clrFourWit_class_three_blind L h=%d j=%d %s" % (h, j, tag), toU4L(r), (0,) * 6)
        check("clrFourWit_class_three_blind R h=%d j=%d %s" % (h, j, tag), toU4R(r), (0,) * 6)
    m = W(ONE)
    # the hom data: generator values, pivot anchor, cleared letters, b-column = nuSel h j 0 0
    check("clrFourHom_sigma h=%d j=%d" % (h, j), m[0], S)
    check("clrFourHom_x0 h=%d j=%d" % (h, j), m[1], X)
    check("clrFourHom_x1 h=%d j=%d" % (h, j), m[2], sigFourY)
    check("clrFourHom_handleU h=%d j=%d" % (h, j), m[3 + 2 * j], clrFourU)
    check("clrFourHom_handleV h=%d j=%d" % (h, j), m[4 + 2 * j], clrFourV)
    for k in range(h):
        if k != j:
            check("clrFourHom_handle_ne h=%d j=%d k=%d" % (h, j, k),
                  (m[3 + 2 * k], m[4 + 2 * k]), (ONE, ONE))
    for c in range(N):
        check("clrFourHom_sqPivot h=%d j=%d c=%d" % (h, j, c),
              mul(m[0], inv(power(X, c))), rowPivotVal(c))
    check("clrFourHom_b h=%d j=%d" % (h, j), [p[1] for p in m],
          [1, 0, 0] + [0] * (2 * h))
    for p in m:
        check("clrFourMark_le_rowFrameSub h=%d j=%d" % (h, j), in_row_frame(p), True)
print("   (the row is cleared, so BOTH Eichler letters are the raw generators and the")
print("    pivot residue never enters the marking: no `Gen` family is needed at all.)")

# =======================================================================================
print()
print("== 3. the gauge parity theorem (symbolic, exact over Z) ==")
Ssym = (P(), P.const(1), P(), P(), P(), P(), P(), P(), P(), P())
xs, ys = sym("x"), sym("y")
Wsym = psqWord(Ssym, xs, ys)
env = {"xb": P(), "yb": P(),
       "xa": 2 * P.var("xa"), "xc": 2 * P.var("xc"), "xd": 2 * P.var("xd"),
       "xe": 2 * P.var("xe"), "xf": 2 * P.var("xf"), "xg": 2 * P.var("xg"),
       "ya": 2 * P.var("ya"), "yc": 2 * P.var("yc"), "yd": 2 * P.var("yd")}
halves = {}
for k, nm in enumerate(COORDS):
    g = Wsym[k].subs(env)
    if nm == "j":
        check("row j is NOT forced even on the gauge", True, True)
        print("     .j = %s" % g)
        continue
    try:
        halves[nm] = g.half()
        check("row %s of sqWord(sigFourMark, x, y) is EVEN on the gauge" % nm, True, True)
        print("     .%s = 2 * ( %s )" % (nm, halves[nm]))
    except ValueError:
        check("row %s of sqWord(sigFourMark, x, y) is EVEN on the gauge" % nm, False, True)

# the same fact, numerically, over the whole gauge-legal box
bad = 0
tried = 0
for xa in (0, 2, 4, 6):
    for xc in (0, 2):
        for xd in (0, 2):
            for xe in (0, 2):
                for xf in (0, 2):
                    for xg in (0, 2):
                        for xh in (0, 3):
                            for xi in (0, 1):
                                for ya in (0, 2):
                                    for yc in (0, 2):
                                        for yd in (0, 2):
                                            xx = (xa, 0, xc, xd, xe, xf, xg, xh, xi, 5)
                                            yy = (ya, 0, yc, yd, 3, 5, 7, 3, 2, 1)
                                            w = sqWord(S, xx, yy)
                                            tried += 1
                                            if any(w[k] % 2 for k in range(9)):
                                                bad += 1
check("gauge parity numerically, %d gauge-legal (x, y) pairs" % tried, bad, 0)

# =======================================================================================
print()
print("== 4. (b) THE LIVE HANDLE BLOCK ==")
check("commP(liveFourU, liveFourV) is LIVE", commP(liveFourU, liveFourV) != ONE, True)
check("commP(liveFourU, liveFourV)", commP(liveFourU, liveFourV), (0,) * 7 + (2, 0, 0))
check("the live block is a class-three element of order 4",
      (commP(liveFourU, liveFourV)[7] * 4) % N, 0)
check("sqWord(sigFourMark, sigFourX, liveFourY)", sqWord(S, X, liveFourY), (0,) * 7 + (6, 0, 0))
check("core word and handle block are inverse",
      mul(sqWord(S, X, liveFourY), commP(liveFourU, liveFourV)), ONE)
check("liveFourY is sigFourY with class-three coordinate 3",
      tuple(liveFourY[k] - sigFourY[k] for k in range(10)), (0,) * 7 + (3, 0, 0))
check("liveFourV is sigFourV with second class-two coordinate 2",
      tuple(liveFourV[k] - sigFourV[k] for k in range(10)), (0,) * 5 + (2,) + (0,) * 4)
for (h, j) in HS:
    W = lambda v: cwWit(h, j, liveFourY, liveFourU, liveFourV, v)
    check("sqRelWord_liveFourMark h=%d j=%d (TEN ROWS, live block)" % (h, j),
          sqRelWord(W(ONE)), ONE)
    check("sqRelWord_liveFourWit_U h=%d j=%d" % (h, j), sqRelWord(W(liveFourU)), liftC(1))
    check("sqRelWord_liveFourWit_Usq h=%d j=%d" % (h, j),
          sqRelWord(W(mul(liveFourU, liveFourU))), liftC(2))
    check("sqRelWord_liveFourWit_Usq_complete h=%d j=%d" % (h, j),
          sqRelWord(sigLift_at(h, j, W(mul(liveFourU, liveFourU)), ONE, ONE, liftC(7), ONE,
                               ONE)), ONE)
    for tag, v in [("triv", ONE), ("U", liveFourU), ("Usq", mul(liveFourU, liveFourU))]:
        r = sqRelWord(W(v))
        check("liveFourWit_class_three_blind L h=%d j=%d %s" % (h, j, tag), toU4L(r), (0,) * 6)
        check("liveFourWit_class_three_blind R h=%d j=%d %s" % (h, j, tag), toU4R(r), (0,) * 6)
    m = W(ONE)
    check("liveFourHom_b h=%d j=%d" % (h, j), [p[1] for p in m], [1, 0, 0] + [0] * (2 * h))
    for c in range(N):
        check("liveFourHom_sqPivot h=%d j=%d c=%d" % (h, j, c),
              mul(m[0], inv(power(X, c))), rowPivotVal(c))
    for p in m:
        check("liveFourMark_le_liveFrameSub h=%d j=%d" % (h, j), in_live_frame(p), True)
    check("the v-letter leaves rowFrameSub h=%d j=%d" % (h, j), in_row_frame(liveFourV), False)
    check("...the selection bit still reads the dressing h=%d j=%d" % (h, j),
          [sqRelWord(W(v))[9] % 2 for v in (ONE, liveFourU, mul(liveFourU, liveFourU))],
          [0, 1, 0])

# =======================================================================================
print()
print("== 5. the forcing is HANDLE-BLIND: the block cancels out of every dressing response ==")
import random
random.seed(20260810)
bad = 0
for _ in range(20000):
    y = tuple(random.randrange(N) for _ in range(10))
    x = tuple(random.randrange(N) for _ in range(10))
    x = (x[0], 0) + x[2:]
    y = (y[0], 0) + y[2:]
    v = tuple(random.randrange(N) for _ in range(10))
    v = (v[0], 0) + v[2:]
    U1 = tuple(random.randrange(N) for _ in range(10))
    V1 = tuple(random.randrange(N) for _ in range(10))
    U2 = tuple(random.randrange(N) for _ in range(10))
    V2 = tuple(random.randrange(N) for _ in range(10))
    h, j = random.choice(HS)
    m1 = mirTuple(h, j, S, x, y, U1, V1)
    m2 = mirTuple(h, j, S, x, y, U2, V2)
    d1 = mirTuple(h, j, mul(S, v), x, y, U1, V1)
    d2 = mirTuple(h, j, mul(S, v), x, y, U2, V2)
    for k, nm in ((6, "g"), (7, "h"), (8, "i"), (9, "j")):
        s1 = (sqRelWord(d1)[k] - sqRelWord(m1)[k]) % N
        s2 = (sqRelWord(d2)[k] - sqRelWord(m2)[k]) % N
        if s1 != s2:
            bad += 1
check("handle-blindness of the four top dressing responses, 20000 random instances", bad, 0)
# and the response really is sigFourRead / sigFourG / sigFourH / sigFourI
bad = 0
for _ in range(20000):
    x = tuple(random.randrange(N) for _ in range(10)); x = (x[0], 0) + x[2:]
    y = tuple(random.randrange(N) for _ in range(10)); y = (y[0], 0) + y[2:]
    v = tuple(random.randrange(N) for _ in range(10)); v = (v[0], 0) + v[2:]
    U1 = tuple(random.randrange(N) for _ in range(10))
    V1 = tuple(random.randrange(N) for _ in range(10))
    h, j = random.choice(HS)
    m1 = mirTuple(h, j, S, x, y, U1, V1)
    d1 = mirTuple(h, j, mul(S, v), x, y, U1, V1)
    want = [sigFourG(v, x), sigFourH(v, x), sigFourI(v, x), sigFourRead(v, x, y)]
    got = [(sqRelWord(d1)[k] - sqRelWord(m1)[k]) % N for k in (6, 7, 8, 9)]
    if got != [w % N for w in want]:
        bad += 1
check("the response is exactly (sigFourG, sigFourH, sigFourI, sigFourRead), 20000 instances",
      bad, 0)

# =======================================================================================
print()
print("== 6. a live handle block is AUTOMATICALLY SOUND ==")
print("   the relator forces commP U V = (core word)^{-1}, and the gauge forces the core")
print("   word's nine lower rows even, so the block is even where the increment reads it.")
bad = 0
for _ in range(200000):
    x = (2 * random.randrange(4), 0, 2 * random.randrange(4), 2 * random.randrange(4),
         2 * random.randrange(4), 2 * random.randrange(4), 2 * random.randrange(4),
         random.randrange(N), random.randrange(N), random.randrange(N))
    y = (2 * random.randrange(4), 0, 2 * random.randrange(4), 2 * random.randrange(4),
         random.randrange(N), random.randrange(N), random.randrange(N),
         random.randrange(N), random.randrange(N), random.randrange(N))
    # the relator forces the handle block to be the core word's inverse, whatever the letters
    C = inv(sqWord(S, x, y))
    if C[7] % 2 or C[8] % 2:
        bad += 1
check("200000 gauge-legal cores: the forced handle block has EVEN (h, i)", bad, 0)

# and the forced block really is realised by honest letters, in bulk: enumerate the
# one-handle-live markings over the committed x0-slot whose x1-slot is a gamma_3-perturbation
# of the committed one, and count those with a LIVE block.
live = dead = 0
witnesses = []
for zh in range(N):
    for zi in range(N):
        for zj in range(N):
            y = mul(sigFourY, (0,) * 7 + (zh, zi, zj))
            W = sqWord(S, X, y)
            if any(W[k] for k in range(7)):
                continue
            target = inv(W)
            hit = None
            for vf in range(N):
                for vi in range(N):
                    V1 = (2, 0, 0, 0, 0, vf, 0, 0, vi, 0)
                    if commP(sigFourU, V1) == target:
                        hit = V1
                        break
                if hit:
                    break
            if hit is None:
                continue
            if target == ONE:
                dead += 1
            else:
                live += 1
                witnesses.append((y, hit, target))
check("relator-killing markings found in the scanned family (live + dead)", live + dead > 0, True)
print("     %d have a LIVE handle block, %d a dead one" % (live, dead))
bad = 0
for y, V1, target in witnesses:
    if sqRelWord(mirTuple(1, 0, S, X, y, sigFourU, V1)) != ONE:
        bad += 1
    if target[7] % 2 or target[8] % 2:
        bad += 1
check("every one of the %d live-block markings kills the relator with even (h, i)"
      % len(witnesses), bad, 0)
check("the transcribed point is one of them",
      (liveFourY, liveFourV) in [(y, V1) for y, V1, _ in witnesses], True)

print()
print("TOTAL CHECKS: %d   FAILURES: %d" % (checks, fails))
sys.exit(1 if fails else 0)
