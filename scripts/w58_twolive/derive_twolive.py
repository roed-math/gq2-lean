"""W58-TWOLIVE: derivation of every explicit claim of GQ2/Dyadic/SqCore/GradedFourTwoLive.lean.

Exact integer arithmetic mod 8 (and symbolic over Z through `poly.py`).  Every named check
below is mirrored one for one by a Lean declaration; `results/derive_twolive.txt` is the
committed transcript.

Run:  python3 scripts/w58_twolive/derive_twolive.py
"""
import itertools
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from u5lib import (N, ONE, red, mul, inv, power, conjP, commP, sqWord, handleWord,
                   sqRelWord, liftC, is_ga_two, is_ga_three, is_ga_four, selPar,
                   sigFourMark, sigFourX, sigFourY, sigFourU, sigFourV, sigFourRead,
                   sigFourG, sigFourH, sigFourI, rowPivotVal, mirTuple, twoTuple,
                   in_live_frame, in_row_frame,
                   mirFourU, mirFourV, rowFourU, rowFourV,
                   mirLiveU, mirLiveV, mirLiveY, rowLiveU, rowLiveV, rowLiveY,
                   dblLiveU, dblLiveV, dblLiveY, twoLiveU, twoLiveV,
                   oddLiveU, oddLiveV, hiLiveU, hiLiveV, hiLiveY,
                   liveFourU, liveFourV, liveFourY)
from poly import P, sym, pmul, pinv, pconj, pcomm, psqWord, PONE

R8 = range(8)
OK = [0]
BAD = []


def check(name, cond):
    OK[0] += 1
    if not cond:
        BAD.append(name)
        print("  ** FAIL ** %s" % name)


def core(y):
    return sqWord(sigFourMark, sigFourX, y)


def order(p):
    k, q = 1, p
    while q != ONE:
        q = mul(q, p)
        k += 1
    return k


print("=" * 78)
print("W58-TWOLIVE derivation")
print("=" * 78)

# ---------------------------------------------------------------------------------------
print("\n## 0  regression against the committed tree")
check("sqWord committed core is trivial", core(sigFourY) == ONE)
check("W57 live core", core(liveFourY) == (0, 0, 0, 0, 0, 0, 0, 6, 0, 0))
check("W57 live block", commP(liveFourU, liveFourV) == (0, 0, 0, 0, 0, 0, 0, 2, 0, 0))
check("W57 live relator", mul(core(liveFourY), commP(liveFourU, liveFourV)) == ONE)
check("W56 mirror block dead", commP(mirFourU, mirFourV) == ONE)
check("W56 row block dead", commP(rowFourU, rowFourV) == ONE)
check("W56 mirror displaced block dead",
      all(commP(mul(rowPivotVal(c), mirFourU), mirFourV) == ONE for c in R8))
check("W56 doubly displaced block dead",
      all(commP(mul(rowPivotVal(c), mirFourU), mul(rowFourV, rowPivotVal(c))) == ONE
          for c in R8))
check("committed odd residue", sqWord(mul(sigFourMark, sigFourU), sigFourX, sigFourY)
      == liftC(1))
check("committed even residue",
      sqWord(mul(sigFourMark, mul(sigFourU, sigFourU)), sigFourX, sigFourY) == liftC(2))

# ---------------------------------------------------------------------------------------
print("\n## 1  the two displacement identities, as group identities")
random.seed(20260810)
bad_l = bad_r = bad_inv = 0
for _ in range(120000):
    Pp = tuple(random.randrange(8) for _ in range(10))
    Q = tuple(random.randrange(8) for _ in range(10))
    U = tuple(random.randrange(8) for _ in range(10))
    V = tuple(random.randrange(8) for _ in range(10))
    if commP(mul(Pp, U), V) != mul(conjP(commP(Pp, V), U), commP(U, V)):
        bad_l += 1
    if commP(U, mul(V, Q)) != mul(commP(U, Q), conjP(commP(U, V), Q)):
        bad_r += 1
    if mul(commP(U, V), commP(V, U)) != ONE:
        bad_inv += 1
check("left displacement identity  [PU,V] = [P,V]^U * [U,V]", bad_l == 0)
check("right displacement identity [U,VQ] = [U,Q] * [U,V]^Q", bad_r == 0)
check("swap identity [U,V]*[V,U] = 1", bad_inv == 0)
print("   (120000 random quadruples each, 0 mismatches)")

print("\n## 2  conjugation on gamma_3, and the pivot's defect")
bad = 0
for c in R8:
    Pp = rowPivotVal(c)
    for hh, ii, jj in itertools.product(R8, repeat=3):
        z = (0, 0, 0, 0, 0, 0, 0, hh, ii, jj)
        if conjP(z, Pp) != (0, 0, 0, 0, 0, 0, 0, hh, ii, (jj + 2 * c * ii) % 8):
            bad += 1
check("gamma_3 conjugation by any g:  z^g = z * liftC(g.d*z.h - g.a*z.i)",
      all(conjP((0, 0, 0, 0, 0, 0, 0, hh, ii, jj), g)
          == mul((0, 0, 0, 0, 0, 0, 0, hh, ii, jj), liftC(g[3] * hh - g[0] * ii))
          for hh, ii, jj in itertools.product(range(0, 8, 3), repeat=3)
          for g in [tuple(random.randrange(8) for _ in range(10)) for _ in range(200)]))
check("pivot conjugation on gamma_3 is  j |-> j + 2c*i", bad == 0)

print("\n## 3  the block-preservation criteria at each selected row")


def preserved(t, s, U, V):
    b = commP(U, V)
    return all(commP(mul(power(rowPivotVal(c), t), U), mul(V, power(rowPivotVal(c), s))) == b
               for c in R8)


def rand_letter():
    return (random.randrange(8), 0, 0, random.randrange(8), random.randrange(8),
            2 * random.randrange(4), 2 * random.randrange(4), random.randrange(8),
            random.randrange(8), random.randrange(8))


tested = 0
bad_m = bad_r2 = bad_hi = 0
for _ in range(200000):
    U, V = rand_letter(), rand_letter()
    b = commP(U, V)
    tested += 1
    if preserved(1, 0, U, V) != (V[0] == 0 and V[5] % 4 == 0 and V[6] == 0 and V[8] % 4 == 0):
        bad_m += 1
    if preserved(0, 1, U, V) != (U[0] == 0 and U[5] % 4 == 0 and U[6] == 0
                                 and (U[8] + b[8]) % 4 == 0):
        bad_r2 += 1
    if preserved(2, 0, U, V) != (V[0] % 4 == 0 and V[6] % 4 == 0 and V[8] % 2 == 0):
        bad_hi += 1
check("MIRROR (1,0) criterion: V.a = 0, V.f = 0 (4), V.g = 0, V.i = 0 (4)", bad_m == 0)
check("UNCLEARED-v (0,1) criterion: U.a = 0, U.f = 0 (4), U.g = 0, U.i + block.i = 0 (4)",
      bad_r2 == 0)
check("HIGHER (2,0) criterion: V.a = 0 (4), V.g = 0 (4), V.i even", bad_hi == 0)
print("   (%d random cleared-letter pairs, 0 mismatches)" % tested)
print("   >> the LEFT displacement leaves the block alone; the RIGHT one CONJUGATES it,")
print("      and the defect 2c*block.i must be absorbed by the u-letter's own i-column.")

print("\n## 4  the achievable core words on the class-two-forced gauge")
img = {}
for ye, yf, yg, yh, yi, yj in itertools.product(R8, repeat=6):
    y = (0, 0, 0, 0, ye, yf, yg, yh, yi, yj)
    img.setdefault(core(y), y)
check("every gauge core word lies in gamma_2", all(k[:4] == (0,) * 4 for k in img))
check("every gauge core word is EVEN in its NINE lower rows (W57 gauge parity)",
      all(all(x % 2 == 0 for x in k[:9]) for k in img))
gam3 = sorted((k[7], k[8], k[9]) for k in img if k[4:7] == (0, 0, 0))
check("the gamma_3 core words are exactly the 64 triples of even (h, i, j)",
      gam3 == sorted(itertools.product(range(0, 8, 2), repeat=3)))
print("   %d distinct core words; %d of them in gamma_3" % (len(img), len(gam3)))


def solve_core(target):
    for yh, yi, yj in itertools.product(R8, repeat=3):
        y = (0, 0, 0, 0, 1, 0, 4, yh, yi, yj)
        if core(y) == target:
            return y
    return None


print("\n## 5  the three DISPLACED live points")
for name, t, s, U, V, Y in [
        ("MIRROR      (1,0)", 1, 0, mirLiveU, mirLiveV, mirLiveY),
        ("UNCLEARED-v (0,1)", 0, 1, rowLiveU, rowLiveV, rowLiveY),
        ("DOUBLY      (1,1)", 1, 1, dblLiveU, dblLiveV, dblLiveY)]:
    b = commP(U, V)
    print("  %s  U0=%s V0=%s" % (name, U, V))
    print("      block = %s  order %d ; x1-slot %s" % (b, order(b), Y))
    check("%s block is LIVE" % name, b != ONE)
    check("%s block is in gamma_3" % name, is_ga_three(b))
    check("%s block has even class-three coordinates" % name, b[7] % 2 == 0 and b[8] % 2 == 0)
    check("%s core word cancels the block" % name, mul(core(Y), b) == ONE)
    check("%s frame relator dies at every handle count" % name,
          all(sqRelWord(mirTuple(hh, jj, sigFourMark, sigFourX, Y, U, V)) == ONE
              for hh in (1, 2, 3, 4) for jj in range(hh)))
    check("%s marking relator dies at every handle count and residue" % name,
          all(sqRelWord(mirTuple(hh, jj, sigFourMark, sigFourX, Y,
                                 mul(power(rowPivotVal(c), t), U),
                                 mul(V, power(rowPivotVal(c), s)))) == ONE
              for hh in (1, 2, 3, 4) for jj in range(hh) for c in R8))
    check("%s marking block equals frame block" % name, preserved(t, s, U, V))
    check("%s cleared letters are nu'-trivial" % name, U[1] == 0 and V[1] == 0)
    check("%s slots lie in liveFrameSub" % name,
          all(in_live_frame(p) for p in [sigFourMark, sigFourX, Y, U, V, ONE]))
    check("%s displaced slots lie in liveFrameSub" % name,
          all(in_live_frame(mul(power(rowPivotVal(c), t), U))
              and in_live_frame(mul(V, power(rowPivotVal(c), s))) for c in R8))
    open_letter = U if U[0] % 2 else V
    check("%s the open letter is CLEAN (f = 0 mod 4), so the odd residue is central" % name,
          open_letter[5] % 4 == 0)
    check("%s the block's class-three part has order at most two" % name,
          b[7] % 4 == 0 and b[8] % 4 == 0)
    print("      relator at the open dressing  : %s"
          % (mul(sqWord(mul(sigFourMark, open_letter), sigFourX, Y), b),))
    print("      relator at its square         : %s"
          % (mul(sqWord(mul(sigFourMark, mul(open_letter, open_letter)), sigFourX, Y), b),))
    check("%s open dressing -> liftC 1" % name,
          mul(sqWord(mul(sigFourMark, open_letter), sigFourX, Y), b) == liftC(1))
    check("%s squared dressing -> liftC 2" % name,
          mul(sqWord(mul(sigFourMark, mul(open_letter, open_letter)), sigFourX, Y), b)
          == liftC(2))
    check("%s trivial dressing -> 1" % name, mul(core(Y), b) == ONE)

print("\n## 6  the DOUBLY row's coupling, and the row obstruction at each point")
check("MIRROR: chi_a(V0) = 0 forced", mirLiveV[0] == 0)
check("MIRROR: chi_a(U0) is odd - the open channel", mirLiveU[0] % 2 == 1)
check("UNCLEARED-v: chi_a(U0) = 0 forced", rowLiveU[0] == 0)
check("UNCLEARED-v: chi_a(V0) is odd - the open channel", rowLiveV[0] % 2 == 1)
check("DOUBLY: chi_a(U0) = chi_a(V0), both odd", dblLiveU[0] == dblLiveV[0] == 1)
check("HIGHER (2,0): 2*chi_a(V0) = 0, and chi_a(V0) is even", 2 * hiLiveV[0] % 8 == 0
      and hiLiveV[0] % 2 == 0)

print("\n## 7  the TWO-LIVE-HANDLE point")
C1 = commP(twoLiveU, twoLiveV)
C2 = commP(twoLiveV, twoLiveU)
print("   C1 = %s   C2 = %s   C1*C2 = %s" % (C1, C2, mul(C1, C2)))
check("two-live blocks are inverse", mul(C1, C2) == ONE)
check("two-live blocks are LIVE", C1 != ONE and C2 != ONE)
check("two-live blocks have order four", order(C1) == 4 and order(C2) == 4)
check("two-live relator dies at the COMMITTED core slots, every h >= 2 and every pair",
      all(sqRelWord(twoTuple(hh, j1, j2, sigFourMark, sigFourX, sigFourY,
                             twoLiveU, twoLiveV, twoLiveV, twoLiveU)) == ONE
          for hh in (2, 3, 4) for j1 in range(hh) for j2 in range(hh) if j1 != j2))
bad = 0
for _ in range(20000):
    U = tuple(random.randrange(8) for _ in range(10))
    V = tuple(random.randrange(8) for _ in range(10))
    for hh in (2, 3):
        for j1 in range(hh):
            for j2 in range(hh):
                if j1 == j2:
                    continue
                if sqRelWord(twoTuple(hh, j1, j2, sigFourMark, sigFourX, sigFourY,
                                      U, V, V, U)) != ONE:
                    bad += 1
check("...for ARBITRARY handle letters (the cancellation is a group identity)", bad == 0)
check("two-live verdict: trivial dressing -> 1",
      sqRelWord(twoTuple(2, 0, 1, sigFourMark, sigFourX, sigFourY,
                         twoLiveU, twoLiveV, twoLiveV, twoLiveU)) == ONE)
check("two-live verdict: open dressing -> liftC 1",
      sqRelWord(twoTuple(2, 0, 1, mul(sigFourMark, twoLiveU), sigFourX, sigFourY,
                         twoLiveU, twoLiveV, twoLiveV, twoLiveU)) == liftC(1))
check("two-live verdict: squared dressing -> liftC 2",
      sqRelWord(twoTuple(2, 0, 1, mul(sigFourMark, mul(twoLiveU, twoLiveU)),
                         sigFourX, sigFourY, twoLiveU, twoLiveV, twoLiveV, twoLiveU))
      == liftC(2))
check("two-live slots lie in liveFrameSub",
      all(in_live_frame(p) for p in [sigFourMark, sigFourX, sigFourY, twoLiveU, twoLiveV]))
check("two-live blocks are even in class three", C1[7] % 2 == 0 and C1[8] % 2 == 0
      and C2[7] % 2 == 0 and C2[8] % 2 == 0)
check("the sharper W55 bound is FALSE at the two-live point", C1[7] != 0)

print("\n## 8  no cross-handle coupling inside the campaign's invariants")
bad = 0
for _ in range(200000):
    U1, V1 = rand_letter(), rand_letter()
    U2, V2 = rand_letter(), rand_letter()
    A, B = commP(U1, V1), commP(U2, V2)
    if mul(A, B)[9] != (A[9] + B[9]) % 8:
        bad += 1
check("(C1*C2).j = C1.j + C2.j for blocks of nu'-trivial, c-free letters", bad == 0)
bad = 0
for _ in range(50000):
    U2 = tuple(random.randrange(8) for _ in range(10))
    V2 = tuple(random.randrange(8) for _ in range(10))
    U2 = U2[:2] + (0,) + U2[3:]
    V2 = V2[:2] + (0,) + V2[3:]
    if commP(U2, V2)[6] != 0:
        bad += 1
check("a block of two c-free letters has vanishing third class-two coordinate", bad == 0)
print("   >> the class-four cross-handle coupling C1.e * C2.g is identically ZERO")
print("      whenever the second pair's letters have vanishing c-column.")

print("\n## 9  the two-live obstruction: the relator no longer forces the block even")
D1 = commP(oddLiveU, oddLiveV)
D2 = commP(oddLiveV, oddLiveU)
print("   D1 = %s   D2 = %s" % (D1, D2))
check("odd two-live relator dies at the committed slots",
      all(sqRelWord(twoTuple(hh, j1, j2, sigFourMark, sigFourX, sigFourY,
                             oddLiveU, oddLiveV, oddLiveV, oddLiveU)) == ONE
          for hh in (2, 3, 4) for j1 in range(hh) for j2 in range(hh) if j1 != j2))
check("its blocks have ODD first class-three coordinate", D1[7] % 2 == 1 and D2[7] % 2 == 1)
check("their sum is even (all the relator controls)", (D1[7] + D2[7]) % 2 == 0)
check("the odd letter leaves liveFrameSub", not in_live_frame(oddLiveV))
check("W57's one-handle theorem still holds at one live handle: no such single block",
      all(mul(core(y), commP(oddLiveU, oddLiveV)) != ONE
          for y in [(0, 0, 0, 0, ye, yf, yg, yh, yi, yj)
                    for ye, yf, yg, yh, yi, yj in itertools.product(R8, repeat=6)]))

# the refinement that kills the odd dressing
def increment(m, j, z0, w1, w2, z3, z4):
    x, U, V = m[1], m[3 + 2 * j], m[4 + 2 * j]
    return ((z0[7] * x[3] - z0[8] * x[0]) + (-4 * w1[9] + 2 * w2[9])
            + (z3[7] * V[3] - z3[8] * V[0]) + (U[0] * z4[8] - U[3] * z4[7])) % 8


mo = twoTuple(2, 0, 1, mul(sigFourMark, oddLiveU), sigFourX, sigFourY,
              oddLiveU, oddLiveV, oddLiveV, oddLiveU)
check("the odd dressing leaves the residue liftC 1 at the odd two-live point",
      sqRelWord(mo) == liftC(1))
inc = increment(mo, 0, ONE, ONE, liftC(3), D1, ONE)
check("the achievable refinement (z0=1, w1=1, w2=liftC 3, z3=D1, z4=1) has increment 7",
      inc == 7)
check("...and it KILLS the odd dressing", mul(sqRelWord(mo), liftC(inc)) == ONE)
check("z3 = D1 is a legal gamma_3 dressing", is_ga_three(D1))
check("chi_a of the killed dressing is ODD", selPar(oddLiveU[0]) == 1)
print("   >> the class-four sigma forcing is FALSE at the odd two-live point.")

print("\n## 10  the HIGHER pivot power row (2, 0)")
bhi = commP(hiLiveU, hiLiveV)
print("   block = %s  order %d" % (bhi, order(bhi)))
check("higher-power block is LIVE of order four", bhi == (0, 0, 0, 0, 0, 0, 0, 2, 0, 0))
check("higher-power block equals W57's live block", bhi == commP(liveFourU, liveFourV))
check("higher-power core cancels it", mul(core(hiLiveY), bhi) == ONE)
check("higher-power marking block equals frame block", preserved(2, 0, hiLiveU, hiLiveV))
check("higher-power relator dies at every handle count and residue",
      all(sqRelWord(mirTuple(hh, jj, sigFourMark, sigFourX, hiLiveY,
                             mul(power(rowPivotVal(c), 2), hiLiveU), hiLiveV)) == ONE
          for hh in (1, 2, 3, 4) for jj in range(hh) for c in R8))
check("higher-power b-column of the u-slot is 2",
      all(mul(power(rowPivotVal(c), 2), hiLiveU)[1] == 2 for c in R8))
check("higher-power open channel is the u-letter", selPar(hiLiveU[0]) == 1)
check("higher-power open dressing -> liftC 1",
      mul(sqWord(mul(sigFourMark, hiLiveU), sigFourX, hiLiveY), bhi) == liftC(1))
check("higher-power squared dressing -> liftC 2",
      mul(sqWord(mul(sigFourMark, mul(hiLiveU, hiLiveU)), sigFourX, hiLiveY), bhi)
      == liftC(2))
# the order bound at the three first-power rows, with a CLEAN open dressing letter
pairs = [(rand_letter(), rand_letter()) for _ in range(120000)]
n1 = n2 = n3 = 0
b1 = b2 = b3 = 0
for U, V in pairs:
    bb = commP(U, V)
    if preserved(1, 0, U, V) and U[5] % 4 == 0:
        n1 += 1
        if bb[7] % 4 or bb[8] % 4:
            b1 += 1
    if preserved(0, 1, U, V) and V[5] % 4 == 0:
        n2 += 1
        if bb[7] % 4 or bb[8] % 4:
            b2 += 1
    if preserved(1, 1, U, V) and U[5] % 4 == 0 and V[5] % 4 == 0:
        n3 += 1
        if bb[7] % 4 or bb[8] % 4:
            b3 += 1
check("MIRROR: a clean-dressing live block has class-three part of order <= 2", b1 == 0)
check("UNCLEARED-v: same", b2 == 0)
check("DOUBLY: same", b3 == 0)
print("   (%d / %d / %d admissible pairs at the three first-power rows, 0 violations)"
      % (n1, n2, n3))
check("...but at the SECOND power the block has order four", bhi[7] % 4 == 2)
check("...and at the CLEARED row too (W57)", commP(liveFourU, liveFourV)[7] % 4 == 2)

print("\n## 11  the pivot square")
for c in R8:
    Pp = rowPivotVal(c)
    check("pivot square closed form at c = %d" % c,
          power(Pp, 2) == red((-4 * c, 2, 0, 0, -2 * c, 0, 0, 0, -2 * c, 4 * c * c + 2 * c)))

print()
print("=" * 78)
print("named checks: %d, failures: %d" % (OK[0], len(BAD)))
if BAD:
    print("FAILED:", BAD)
print("=" * 78)
