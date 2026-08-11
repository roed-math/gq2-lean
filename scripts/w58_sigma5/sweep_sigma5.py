"""W58-SIGMA5 step 3: the censuses.

  1. SOUNDNESS at the separating point: the lower central series of the image, the parities of
     its achievable dressings, and the refinement sweep - no achievable refinement moves the
     class-five residue by an odd amount, while unrestricted ones do (so achievability is
     load-bearing here exactly as at the committed class-four points).
  2. The `a0 = a1` census over relator-killing markings: how often the class-five response is
     odd, always matching the closed form `x12*y24*y46 + x56*y13*y35`.
  3. The DEAD-BLOCK census: with a trivial handle block the separation is unreachable among
     stage-three survivors, so the class-five escape needs a LIVE handle block even though the
     block never enters the bit.
  4. The handle-block coupling census.

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
from u6lib import *                                    # noqa: F403
import sigfive_forms as F

fails = 0
checks = 0


def check(name, got, want=True):
    global fails, checks
    checks += 1
    ok = (got == want)
    if not ok:
        fails += 1
    print(("PASS " if ok else "FAIL ") + name + ("" if ok else "  got %s want %s" % (got, want)))


def closure(seeds, gens, cap=2000000):
    seen = {ONE}
    frontier = [ONE]
    mult = [s for s in seeds if s != ONE]
    mult = mult + [inv(s) for s in mult]
    while frontier:
        nxt = []
        for p in frontier:
            for g in mult:
                q = mul(p, g)
                if q not in seen:
                    seen.add(q)
                    nxt.append(q)
            for g in gens:
                q = conjP(p, g)
                if q not in seen:
                    seen.add(q)
                    nxt.append(q)
        frontier = nxt
        if len(seen) > cap:
            return seen, False
    return seen, True


sepU = (1, 0, 2, 3, 0, 3, 2, 2, 2, 0, 0, 0, 0, 0, 0)
sepV = named(d=1, e=2, f=3, g=2, h=3, i=3)
sepX = named(a=2, e=1)
sepY = named(e=2, f=1, h=3, i=1, j=2, k=2, l=2, m=3, n=2, o=2)
slots = [sigFiveMark, sepX, sepY, sepU, sepV]

# =======================================================================================
print("== 1. SOUNDNESS at the separating point ==")
gens = slots
g3, _ = closure([commP(commP(a, b), c) for a in gens for b in gens for c in gens], gens)
g4, _ = closure([commP(z, g) for z in g3 for g in gens], gens)
g5, _ = closure([commP(z, g) for z in g4 for g in gens], gens)
print("   |gamma_3 of the image| = %d, |gamma_4| = %d, |gamma_5| = %d"
      % (len(g3), len(g4), len(g5)))
check("   every achievable gamma_3-dressing has EVEN class-three coordinates (x14, x25, x36)",
      sorted({(z[9] % 2, z[10] % 2, z[11] % 2) for z in g3}), [(0, 0, 0)])
check("   every achievable gamma_4-dressing has EVEN class-four coordinates (x15, x26)",
      sorted({(z[12] % 2, z[13] % 2) for z in g4}), [(0, 0)])
check("   every achievable gamma_5-dressing has EVEN class-five coordinate (x16)",
      sorted({z[14] % 2 for z in g5}), [0])
base = [mul(sigFiveMark, sepX), sepX, sepY, sepU, sepV]
check("   the dressed relator is liftC 7", sqRelWord(base), liftC(7))
flip = 0
tot = 0
for i in range(5):
    for z in (g4 if i in (0, 3, 4) else g5):
        m = list(base)
        m[i] = mul(m[i], z)
        tot += 1
        if sqRelWord(m)[14] % 2 != 1:
            flip += 1
check("   %d single-slot ACHIEVABLE refinements: parity never flips" % tot, flip, 0)
random.seed(2026)
flip = 0
tot = 0
for _ in range(60000):
    m = list(base)
    for i in range(5):
        m[i] = mul(m[i], random.choice(list(g4)) if i in (0, 3, 4) else random.choice(list(g5)))
    tot += 1
    if sqRelWord(m)[14] % 2 != 1:
        flip += 1
check("   %d random FIVE-SLOT achievable refinements: parity never flips" % tot, flip, 0)
uf = 0
ut = 0
for a in range(8):
    for b in range(8):
        z = named(m=a, n=b)
        for i in range(5):
            mm = list(base)
            mm[i] = mul(mm[i], z)
            ut += 1
            if sqRelWord(mm)[14] % 2 != 1:
                uf += 1
print("   UNRESTRICTED gamma_4 moves: %d of %d flip the parity, so achievability is"
      " load-bearing" % (uf, ut))
check("   ...and it is: some unrestricted move does flip it", uf > 0)

# =======================================================================================
print()
print("== 2. the `a0 = a1` census over relator-killing markings ==")
random.seed(5820)
tot = 0
odd = 0
mismatch = 0
gauge_tot = 0
gauge_odd = 0
for _ in range(120000):
    x = [random.randrange(8) for _ in range(15)]
    x[1] = 0
    y = [random.randrange(8) for _ in range(15)]
    y[1] = 0
    for k in (0, 2, 3, 4):                       # the relator's abelian rows over Z/8
        y[k] = (2 * x[k] + 4 * random.randrange(2)) % 8
    x, y = tuple(x), tuple(y)
    got = F.apply('o', x, x, y) % 2
    want = (x[0] * y[6] * y[8] + x[4] * y[5] * y[7]) % 2
    tot += 1
    if got != want:
        mismatch += 1
    if got:
        odd += 1
    if x[0] % 2 == 0 and x[2] % 2 == 0 and x[3] % 2 == 0 and x[4] % 2 == 0:
        gauge_tot += 1
        if got:
            gauge_odd += 1
check("   the closed form x12*y24*y46 + x56*y13*y35 matches on %d markings" % tot, mismatch, 0)
print("   odd in %d of %d (%.1f%%) of markings with vanishing abelian rows" %
      (odd, tot, 100.0 * odd / tot))
check("   ...and in %d of %d with ALL FOUR abelian columns of x0 even (the full gauge)"
      % (gauge_odd, gauge_tot), gauge_odd, 0)
print("   -> the class-two-forced gauge of GradedSigmaFour constrains x12, x34, x45 only;")
print("      x56 is the escape, and it is a column U_5 does not have.")

# =======================================================================================
print()
print("== 3. the DEAD-BLOCK census: a live block is necessary for the escape ==")
print("   with a trivial handle block the relator forces H = 1, hence the core word W = 1.")
print("   Row x13 then gives x12 EVEN, and the class-four row x15 of the core word is")
print("     W.m = x12*x35 + y13*y35   (mod 2),")
print("   which the block cannot help to kill.  So y13*y35 must be even, and the `a0 = a1`")
print("   response x12*y24*y46 + x56*y13*y35 is even too.  The escape needs a block that is")
print("   LIVE IN THE x15 ROW - and the separating point's block has x15 = 3, odd.")
BYCLASS = {}
for k in range(15):
    BYCLASS.setdefault(cls(k), []).append(k)


def solve_x1(s, x, letters, limit=64):
    """Every x1-slot value killing all fifteen rows, found class by class: a class-c coordinate
    of the x1 slot occurs in exactly one class-c row, so the solve is triangular."""
    out = [ONE]
    for c in sorted(BYCLASS):
        nxt = []
        for base in out:
            combos = [list(base)]
            for k in BYCLASS[c]:
                good = [val for val in range(8)
                        if sqRelWord([s, x, tuple(base[:k] + (val,) + base[k + 1:])]
                                     + list(letters))[k] == 0]
                combos = [c2[:k] + [g] + c2[k + 1:] for c2 in combos for g in good][:limit]
            nxt.extend(tuple(c2) for c2 in combos)
        out = nxt[:limit]
        if not out:
            return []
    return [t for t in out if sqRelWord([s, x, t] + list(letters)) == ONE]


random.seed(5821)
tot = 0
bad = 0
survivors = 0
scanned = 0
while tot < 2000 and scanned < 600:
    scanned += 1
    x = [random.randrange(8) for _ in range(15)]
    x[1] = 0
    x[0] = 2 * random.randrange(4)                 # a dead block forces x12 even (row x13)
    x = tuple(x)
    for y in solve_x1(sigFiveMark, x, [ONE, ONE], limit=8):
        tot += 1
        if (y[5] * y[7]) % 2:                     # y13 * y35
            bad += 1
        if F.apply('o', x, x, y) % 2:
            survivors += 1
check("   over %d dead-block relator-killing markings: y13*y35 is always EVEN" % tot, bad, 0)
check("   ...and NONE of them separates the `a0 = a1` dressing", survivors, 0)
print("   -> with a dead handle block the class-five escape is invisible among stage-three")
print("      survivors: the separating point NEEDS a live block, though the block never")
print("      enters the selection bit itself.")

# =======================================================================================
print()
print("== 4. the handle-block coupling census ==")
random.seed(5822)
tot = 0
bad = 0
liveblocks = 0
for _ in range(40000):
    def r(nu=True):
        t = [random.randrange(8) for _ in range(15)]
        if nu:
            t[1] = 0
        return tuple(t)
    v, x, y, U, V = r(), r(), r(), r(False), r(False)
    for h in (1, 2):
        m0 = mirTuple(h, 0, sigFiveMark, x, y, U, V)
        m1 = mirTuple(h, 0, mul(sigFiveMark, v), x, y, U, V)
        H = commP(U, V)
        if H != ONE:
            liveblocks += 1
        sfH = (v[0] * (x[6] - x[2]) - v[2] * (x[0] + x[5]) + v[5] * x[2] - v[6] * x[0]) % 8
        want = (F.apply('o', v, x, y) + sfH * H[8]) % 8
        got = (sqRelWord(m1)[14] - sqRelWord(m0)[14]) % 8
        tot += 1
        if got != want:
            bad += 1
check("   the coupling formula holds at %d markings (h = 1, 2; %d with a live block)"
      % (tot, liveblocks), bad, 0)

print()
print("TOTAL CHECKS: %d   FAILURES: %d" % (checks, fails))
sys.exit(1 if fails else 0)
