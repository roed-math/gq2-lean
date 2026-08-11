"""W58-SIGMA5 step 1: derive the CLASS-FIVE sigma reading and settle the two questions
`GradedSigmaFour` section 7 and `GradedFourCleared` section 2 left open.

The class-four picture (committed):

  * `GradedSigmaFour` section 5: on the class-two-forced gauge the class-four reading collapses
    to `v.a*(x.g + x.i) + v.d*x.h + v.e*x.g` mod 2 - THREE live channels;
  * section 7: the depth sweep's forced sigma dressing `a0 = a1` (the dressing v equal to the
    x0-slot value x) has all three channels even there, so class four identifies `a0 = a1` with
    `a0 = 1`.  "That piece needs class five, or the universal quotient."
  * `GradedFourCleared` section 2: the handle block cancels IDENTICALLY out of every class-four
    dressing response, because the two coefficients it meets in the top row - the core word's
    `a`- and `e`-coordinates - are not moved by a sigma dressing at all.

This file transposes the reading to U_6 (class five, fifteen coordinates) and asks both
questions there.  Everything is exact integer arithmetic; the fifteen-row response is derived
symbolically over Z, machine-emitted into `sigfive_forms.py`, and certified against honest
group evaluation in `instance_sigma5.py` / `sweep_sigma5.py`.

BRACKET CONVENTION.  [NONE]
This script computes no commutators, so the convention does not arise.
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
from u6lib import _mat, _tup
from poly6 import *                                    # noqa: F403
from unilib import Uni
import sigfive_forms as F
import u5lib as U5                                     # the committed class-four library
import poly as P5                                      # the committed class-four symbolic ring

fails = 0
checks = 0


def check(name, got, want=True):
    global fails, checks
    checks += 1
    ok = (got == want)
    if not ok:
        fails += 1
    print(("PASS " if ok else "FAIL ") + name + ("" if ok else "  got %s want %s" % (got, want)))


def rnd(nu_trivial=True):
    t = [random.randrange(8) for _ in range(15)]
    if nu_trivial:
        t[1] = 0
    return tuple(t)


# =======================================================================================
print("== 1. the class-five carrier U_6, and its two U_5 quotients ==")
random.seed(2026)
G6 = Uni(6, 8)
ok_assoc = ok_inv = ok_mat = ok_gen = ok_L = ok_R = True
for _ in range(4000):
    p, q, r = rnd(False), rnd(False), rnd(False)
    ok_assoc &= mul(mul(p, q), r) == mul(p, mul(q, r))
    ok_inv &= mul(p, inv(p)) == ONE and mul(inv(p), p) == ONE
    ok_mat &= _tup(matmul(_mat(p), _mat(q))) == mul(p, q) and _tup(matinv(_mat(p))) == inv(p)
    ok_gen &= _tup(G6.mul(_mat(p), _mat(q))) == mul(p, q) and _tup(G6.inv(_mat(p))) == inv(p)
    ok_L &= U5.mul(toU5L(p), toU5L(q)) == toU5L(mul(p, q)) and U5.inv(toU5L(p)) == toU5L(inv(p))
    ok_R &= U5.mul(toU5R(p), toU5R(q)) == toU5R(mul(p, q)) and U5.inv(toU5R(p)) == toU5R(inv(p))
check("U_6 is a group (associativity, inverses), 4000 instances", ok_assoc and ok_inv)
check("the coordinate law agrees with honest 6x6 matrix arithmetic", ok_mat)
check("...and with the generic unitriangular library `unilib`", ok_gen)
check("toU5L is a homomorphism onto the COMMITTED SqU5", ok_L)
check("toU5R is a homomorphism onto the COMMITTED SqU5", ok_R)
check("toU5L(sigFiveMark) = the committed sigFourMark", toU5L(sigFiveMark) == U5.sigFourMark)
ok_word = True
for _ in range(2000):
    s, x, y = rnd(), rnd(), rnd()
    ok_word &= U5.sqWord(toU5L(s), toU5L(x), toU5L(y)) == toU5L(sqWord(s, x, y))
check("the core word commutes with toU5L (so every class-four fact survives)", ok_word)

# the committed class-four witness, lifted coordinatewise
sigFiveX = named(a=2, k=1)                 # lift of sigFourX = <a=2, i=1>
sigFiveY = named(f=1, h=4, k=2)            # lift of sigFourY = <e=1, g=4, i=2>
sigFiveU = named(a=1)
sigFiveV = named(a=2)
check("the lift restricts to sigFourX", toU5L(sigFiveX) == U5.sigFourX)
check("the lift restricts to sigFourY", toU5L(sigFiveY) == U5.sigFourY)


def fiveWit(v, h=1, j=0):
    return mirTuple(h, j, mul(sigFiveMark, v), sigFiveX, sigFiveY, sigFiveU, sigFiveV)


check("*** the lift already kills all FIFTEEN rows: sqRelWord(fiveWit 1) = 1",
      sqRelWord(fiveWit(ONE)) == ONE)
check("the committed class-four verdict U (odd residue 1) is the left corner of the lift",
      toU5L(sqRelWord(fiveWit(sigFiveU))) == U5.liftC(1))
check("the committed class-four verdict V (even residue 2) likewise",
      toU5L(sqRelWord(fiveWit(sigFiveV))) == U5.liftC(2))

# =======================================================================================
print()
print("== 2. the fifteen-row class-five sigma response ==")
v = list(sym('v')); x = list(sym('x')); y = list(sym('y'))
for t in (v, x, y):
    t[1] = P()                                        # nu'-triviality: the b-column vanishes
v, x, y = tuple(v), tuple(x), tuple(y)
MK = pconst(sigFiveMark)
D = [a - b for a, b in zip(psqWord(pmul(MK, v), x, y), psqWord(MK, x, y))]

check("rows a,b,c,d,e (abelian) do not move", all(D[k].is_zero() for k in range(5)))
check("rows f (x13) and g (x24) do not move either", D[5].is_zero() and D[6].is_zero())
print("   the seven rows a..g are sigma-INVARIANT; every deeper row moves.")

# the committed class-four functionals, transcribed into U_6 letters through toU5L
va, vc, vd, ve, vf, vg = v[0], v[2], v[3], v[4], v[5], v[6]
xa, xc, xd, xe, xf, xg = x[0], x[2], x[3], x[4], x[5], x[6]
sigFourG_L = vc * xd - vd * xc
sigFourH_L = va * (xg - xc) - vc * (xa + xf) + vf * xc - vg * xa
sigFourI_L = vd * (xc - xg) + vg * xd
check("D[x35] is the committed sigFourG", (D[7] - sigFourG_L).is_zero())
check("D[x14] is the committed sigFourH", (D[9] - sigFourH_L).is_zero())
check("D[x25] is the committed sigFourI", (D[10] - sigFourI_L).is_zero())

L = {'a': 0, 'b': 1, 'c': 2, 'd': 3, 'e': 5, 'f': 6, 'g': 7, 'h': 9, 'i': 10, 'j': 12}


def LL(t, c):
    return t[L[c]]


def sigFourRead_L(v, x, y):
    return (LL(v, 'a') * (4 * (LL(x, 'c') * LL(x, 'd')) - 2 * (LL(x, 'c') * LL(y, 'd'))
                          - 4 * (LL(x, 'd') * LL(x, 'f')) + 2 * (LL(x, 'f') * LL(y, 'd'))
                          - LL(x, 'g') + LL(x, 'i') - LL(y, 'c') * LL(y, 'd')
                          + LL(y, 'd') * LL(y, 'f'))
            + LL(v, 'c') * (3 * (LL(x, 'a') * LL(x, 'd')) - 2 * (LL(x, 'a') * LL(y, 'd'))
                            + 3 * (LL(x, 'd') * LL(x, 'e')) - 2 * (LL(x, 'e') * LL(y, 'd'))
                            - LL(y, 'a') * LL(y, 'd') - 2 * (LL(y, 'd') * LL(y, 'e')))
            + LL(v, 'd') * (LL(x, 'a') * LL(x, 'f') + LL(x, 'c') * LL(x, 'e') - LL(x, 'h')
                            - LL(y, 'a') * LL(y, 'c') + LL(y, 'a') * LL(y, 'f')
                            + LL(y, 'c') * LL(y, 'e'))
            + LL(v, 'e') * (-4 * (LL(x, 'c') * LL(x, 'd')) + 2 * (LL(x, 'c') * LL(y, 'd'))
                            + LL(x, 'g') + LL(y, 'c') * LL(y, 'd'))
            + LL(v, 'f') * (3 * (LL(x, 'a') * LL(x, 'd')) - 2 * (LL(x, 'a') * LL(y, 'd'))
                            - 2 * (LL(y, 'a') * LL(y, 'd')))
            + LL(v, 'g') * (-LL(x, 'a') - LL(x, 'e')) + LL(v, 'h') * LL(x, 'd')
            - LL(v, 'i') * LL(x, 'a')
            + (LL(v, 'a') * LL(v, 'd') * (LL(x, 'f') - LL(x, 'c'))
               - LL(v, 'a') * LL(v, 'f') * LL(x, 'd') - LL(v, 'c') * LL(v, 'e') * LL(x, 'd')
               + LL(v, 'd') * LL(v, 'e') * LL(x, 'c')))


check("*** D[x15] is the committed sigFourRead, verbatim",
      (D[12] - sigFourRead_L(v, x, y)).is_zero())
print("   -> the class-four reading is the (1,5) row of the class-five one: nothing is lost.")
print()
print("   THE CLASS-FIVE READING sigFiveRead = D[x16], %d terms:" % len(D[14].d))
print("   " + str(D[14]))
print()
print("   channel decomposition (the coefficient of each dressing coordinate):")
rest = D[14]
for c in COORDS:
    A, rest = rest.coeff_in('v' + c)
    if not A.is_zero():
        print("     v.%s (v%d%d) : %s" % (c, POS[COORDS.index(c)][0], POS[COORDS.index(c)][1], A))
check("the reading has no dressing-free part", rest.is_zero())

# =======================================================================================
print()
print("== 3. the gauge collapse ==")
# the WEAK gauge: the direct transposition of GradedSigmaFour.sigFourRead_gauge - the x0 slot's
# abelian columns and its two LOWER class-two coordinates even, the x1 slot's abelian columns
# even, everything deeper free.
WEAK = {nm: 2 * P.var(nm.upper()) for nm in
        ['xa', 'xc', 'xd', 'xe', 'xf', 'xg', 'ya', 'yc', 'yd', 'ye']}
# the HONEST class-two-forced gauge: the x0 slot is U^{-S} V^T times a gamma_3 element, so ALL
# four of its class-two coordinates vanish on the nose.
HONEST = dict(WEAK)
HONEST.update({'xf': P(), 'xg': P(), 'xh': P(), 'xi': P()})

weak = D[14].subs(WEAK).mod(2)
honest = D[14].subs(HONEST).mod(2)
print("   on the WEAK gauge (all four abelian columns of x0 even, the two lower")
print("   class-two coordinates even, the x1 slot's abelian columns even), mod 2:")
print("     " + str(weak))
print("   on the HONEST class-two-forced gauge (x0 = forced value times a gamma_3 element,")
print("   so all four of its class-two coordinates vanish), mod 2:")
print("     " + str(honest))
print()
print("   LIVE CHANNELS there (class four had THREE: v.a = v12, v.d = v45, v.e = v13):")
print("     v.a (v12) -> x36 + x26        [class-three + class-four coordinates of x0]")
print("     v.e (v56) -> x15              [class-four]")
print("     v.f (v13) -> x36              [class-three]")
print("     v.i (v46) -> x14              [class-three]   *** NEW: a class-two channel")
print("     plus the quadratic cross-term v.a*v.e*x25 and the x1-slot terms v.a*y24*y46,")
print("     v.e*y13*y35 - the class-five reading is NOT linear in the dressing.")
check("the honest-gauge reading is exactly those eight monomials", len(honest.d) == 8)
for mon in ['va*xl', 'va*xn', 've*xm', 'vf*xl', 'vi*xj', 'va*ve*xk', 'va*yg*yi', 've*yf*yh']:
    key = tuple(sorted(mon.split('*')))
    check("   channel %s present" % mon, key in honest.d)

# =======================================================================================
print()
print("== 4. (b) DOES THE `a0 = a1` FORCING BECOME VISIBLE? ==")
DIAG = {('v' + c): P.var('x' + c) for c in COORDS}
diag = D[14].subs(DIAG)
print("   Careful with the gauge.  The two substitutions above make ALL FOUR abelian columns of")
print("   the x0 slot even, including the fifth entry x56 - a matrix entry U_5 does not have, so")
print("   GradedSigmaFour's class-two-forced gauge says nothing about it.  Call that stronger")
print("   hypothesis set the EXTENDED gauge, and the committed one (x12, x34, x45 even; x13, x24")
print("   even; the x1 slot's abelian columns even) the COMMITTED gauge.")
check("*** on the EXTENDED gauge the diagonal dressing v = x is read evenly (weak form)",
      diag.subs(WEAK).mod(2).is_zero())
check("*** on the EXTENDED gauge likewise in the honest form", diag.subs(HONEST).mod(2).is_zero())
COMMITTED = {nm: 2 * P.var(nm.upper()) for nm in
             ['xa', 'xc', 'xd', 'xf', 'xg', 'ya', 'yc', 'yd']}
comm = diag.subs(COMMITTED).mod(2)
print("   on the COMMITTED gauge (x56 left free) the diagonal is:  %s" % comm)
check("*** on the COMMITTED gauge the diagonal is NOT even: the channel x56*y13*y35 is open",
      not comm.is_zero())
print("   -> POSITIVE: class five DOES separate the sweep's forced dressing, through the")
print("      x0-slot's fifth abelian column, which no class-four hypothesis constrains.")
print()
print("   On the EXTENDED gauge it dies, and the reason is worth recording: the reading's")
print("   (dressing, x0)-bilinear part is ALTERNATING over F_2.")
print()
print("   No channel has the form v.p * x.p, and every off-diagonal pair has b_pq + b_qp even -")
print("      v.i*x14 and v.j*x46 enter as  v.j*x.i - v.i*x.j   (exactly alternating),")
print("      v.e*x15 and v.m*x56 as         v.m*x.e - v.e*x.m,")
print("      v.a*x26 and v.n*x12 as         v.a*x.n - v.n*x.a,")
print("      v.f*x36 and v.l*x13 as         v.f*x.l - v.l*x.f,")
print("      v.a*x36 and v.l*x12 as        -v.a*x.l - v.l*x.a   (symmetric: 2*(..) mod 2 = 0).")
print("   A bilinear form with even diagonal and even symmetrisation vanishes on v = x, which")
print("   is why the escape has to come from a channel the extended gauge closes by hand.")
print()
print("   The vanishing is in any case no longer IDENTICAL.  Impose only the relator's own abelian")
print("   rows (-4x + 2y = 0 in each column over Z/8, whence every abelian column of the x1")
print("   slot is even) and compare the two classes:")
ABEL = {nm: 2 * P.var(nm.upper()) for nm in ['ya', 'yc', 'yd', 'ye']}
print("     class five :", diag.subs(ABEL).mod(2))
v4 = list(P5.sym('v')); x4 = list(P5.sym('x')); y4 = list(P5.sym('y'))
for t in (v4, x4, y4):
    t[1] = P5.P()
v4, x4, y4 = tuple(v4), tuple(x4), tuple(y4)
sig4 = (P5.P(), P5.P.const(1)) + tuple(P5.P() for _ in range(8))
D4 = P5.psqWord(P5.pmul(sig4, v4), x4, y4)[9] - P5.psqWord(sig4, x4, y4)[9]
d4 = D4.subs({('v' + c): P5.P.var('x' + c) for c in 'acdefghij'})
ABEL4 = {nm: 2 * P5.P.var(nm.upper()) for nm in ['ya', 'yc', 'yd']}
print("     class four :", d4.subs(ABEL4).mod(2))
check("*** at class FOUR the diagonal is even at EVERY relator-killing marking",
      d4.subs(ABEL4).mod(2).is_zero())
check("*** at class FIVE it is the nonzero functional  x12*y24*y46 + x56*y13*y35",
      diag.subs(ABEL).mod(2).d == {tuple(sorted(['xa', 'yg', 'yi'])): 1,
                                   tuple(sorted(['xe', 'yf', 'yh'])): 1})
print("   -> class five is the FIRST level at which the `a0 = a1` response is not identically")
print("      even; it vanishes on the class-two-forced gauge only because that gauge makes the")
print("      x0-slot's abelian columns x12 and x56 even.  The residual has moved from `no")
print("      channel exists` to `the channel exists and the gauge closes it`.")

# =======================================================================================
print()
print("== 5. (c) DOES THE HANDLE BLOCK BECOME VISIBLE? ==")
Wv = sym('W'); Hs = list(sym('H'))
for k in range(5):
    Hs[k] = P()                                       # the handle word lies in gamma_2
Hh = tuple(Hs)
top = pmul(Wv, Hh)[14]
print("   the relator's top row at any marking:  (W*H).o = %s" % top)
check("the block meets the top row through exactly three coefficients: W.a, W.f, W.j",
      len(top.d) == 5)
print("   a sigma dressing does not move W.a or W.f (section 2), so the response is")
print("     Delta(W*H).o = sigFiveRead(v,x,y)  +  sigFourH(v,x) * H.i          (H.i = block_46)")
print("   *** the wave-57 IDENTICAL cancellation FAILS at class five: the block is present.")
print()
print("   Two independent evennesses kill it anyway.")
check("   (i) sigFourH(v,x) is even on the class-two-forced gauge (the committed"
      " sigFourH_gauge_even)", sigFourH_L.subs(WEAK).mod(2).is_zero())
diag_h = sigFourH_L.subs(DIAG)
print("   (i') on the diagonal it is even at EVERY marking:  sigFourH(x,x) = %s" % diag_h)
check("       sigFourH(x,x) = -2*x12*x34", diag_h.mod(2).is_zero())
Wsym = psqWord(MK, x, y)
print("   (ii) the relator pins the block to the core word's inverse, and")
print("        W.i (x46) = %s" % Wsym[8])
print("        so W.i = y45*y56 mod 2, and the relator's abelian rows (W.d = -4*x45 + 2*y45 = 0,")
print("        W.e = -4*x56 + 2*y56 = 0 over Z/8) force y45 and y56 EVEN.")
check("   W.i is even once the x1 slot's outer abelian columns are even",
      Wsym[8].subs({'yd': 2 * P.var('YD'), 'ye': 2 * P.var('YE')}).mod(2).is_zero())
print("   -> H.i = -W.i is EVEN at every relator-killing marking, at every handle count, on")
print("      every row, with NO gauge hypothesis at all.")
print()
print("   *** NEGATIVE at class five: the class-five selection bit is handle-blind.")

print()
print("   The general shape, at every class c (carrier U_{c+1}, top row (1, c+1)):")
print("     Delta(relator top) = [class-c reading] + sum_{m=2}^{c-1} [class-(m-1) reading]*H_{m,c+1}")
print("   because the (1,m) entry only sees the corner (1..m), on which the marking restricts to")
print("   the class-(m-1) one.  The two factors of each coupling term:")
print("     coefficient [class-(m-1) reading]:  identically 0 for m <= 3;")
print("                                          EVEN on the gauge for m = 4 (sigFourH);")
print("                                          odd-able for m >= 5 (sigFourRead onwards).")
print("     block coordinate H_{m,c+1}: for m >= 3 the corner (m..c+1) misses the sigma letter")
print("     E_23 entirely, so the core word restricts there to x^{-4} y^2 and the block to its")
print("     inverse.  Parity of those coordinates, given the relator's abelian rows:")
for k in (3, 4, 5, 6):
    Uk = Uni(k, None)
    xs = Uk.symbolic('x'); ys = Uk.symbolic('y')
    Wk = Uk.mul(Uk.inv(Uk.power(xs, 4)), Uk.power(ys, 2))
    Wik = Uk.inv(Wk)
    env = {('y%d%d' % (i, i + 1)): 2 * P.var('Y%d%d' % (i, i + 1)) for i in range(1, k)}
    for c in range(1, k):
        odd = [(i, i + c) for i in range(1, k - c + 1)
               if not Wik[i - 1][i + c - 1].subs(env).mod(2).is_zero()]
        if c == 1:
            continue
        print("       corner size %d, class %d : %s" % (k, c, "can be ODD %s" % odd if odd
                                                        else "always EVEN"))
    check("      corner size %d: every block coordinate of class <= 3 is even" % k,
          all(Uk.inv(Uk.mul(Uk.inv(Uk.power(xs, 4)), Uk.power(ys, 2)))[i - 1][i + c - 1]
              .subs(env).mod(2).is_zero()
              for c in range(1, min(4, k)) for i in range(1, k - c + 1)))
print()
print("   COMBINING: a coupling term can be odd only when the coefficient is odd-able")
print("   (m >= 5, or m = 4 off the gauge) AND the block coordinate is odd-able (class")
print("   c + 1 - m >= 4).  So")
print("     on the class-two-forced gauge : need m >= 5 and c >= m + 3, first opening CLASS 8;")
print("     off it                        : need m >= 4 and c >= m + 3, first opening CLASS 7.")
print("   Classes four, five, six and seven are handle-blind on the gauge; class five is the")
print("   first at which the block is PRESENT in the response at all.")

# =======================================================================================
print()
print("== 6. the class-five gauge parity theorem ==")
print("   (the transposition of GradedFourCleared's sqWord_sigFourMark_gauge_even)")
oddrows = []
for k in range(15):
    r = Wsym[k].subs(HONEST).mod(2)
    if not r.is_zero():
        oddrows.append((COORDS[k], POS[k], r))
check("on the honest class-two-forced gauge the twelve rows of class <= 3 are all EVEN",
      all(c not in [t[0] for t in oddrows] for c in 'abcdefghijkl'))
for c, p, r in oddrows:
    print("   W.%s (x%d%d, class %d) can be odd:  %s" % (c, p[0], p[1], p[1] - p[0], r))
print("   -> at class four only ONE row could be odd; at class five THREE can, and the two new")
print("      ones are the class-four rows x15 and x26.  The class-two-forced gauge controls")
print("      exactly the rows of class <= 3, at either level.")

# =======================================================================================
print()
print("== 7. the generated closed forms agree with honest group evaluation ==")
random.seed(58)
bad = 0
cmps = 0
for _ in range(20000):
    vv, xx, yy = rnd(), rnd(), rnd()
    W1 = sqWord(mul(sigFiveMark, vv), xx, yy)
    W0 = sqWord(sigFiveMark, xx, yy)
    for k, name in enumerate(COORDS):
        want = (W1[k] - W0[k]) % 8
        got = F.apply(name, vv, xx, yy) if name in F.ROWS else 0
        cmps += 1
        if got != want:
            bad += 1
check("300000 row comparisons against honest U_6 collection, zero mismatches",
      (cmps, bad), (300000, 0))

print()
print("TOTAL CHECKS: %d   FAILURES: %d" % (checks, fails))
sys.exit(1 if fails else 0)
