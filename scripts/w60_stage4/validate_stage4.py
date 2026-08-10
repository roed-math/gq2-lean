"""W60-STAGE4 step 4: every form the Lean file writes down, checked against honest collection.

Nothing here reads a Lean file; the forms are re-typed from the derivation and compared to
6 x 6 matrix collection over four rings at random points.  The Lean statements are the same
forms, so a mismatch here would mean the Lean file is wrong even though it compiles.

Sections
  0. the two independent group-law implementations agree;
  1. `gaThreeHandle`, the commutator under a two-sided `gamma_3`-dressing;
  2. `gaThreeCore`, the core word under a three-slot `gamma_3`-dressing, and the vanishing of
     the quadratic block that the class-four precedent carries;
  3. `gaThreeShift`, the five-slot relator identity, at handle counts 0 to 4;
  4. the stage-four soundness: the class-five row of the shift is even under the file's
     hypotheses, checked by brute force rather than by the proof;
  5. the witness point's verdicts and the wave-59 comparison.
"""
import sys
import os
import random

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_defect5"))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))

import u6poly as Q                                            # noqa: E402
import u6mat as M                                             # noqa: E402
import pointlib as P                                          # noqa: E402

COORDS = Q.COORDS
fails = 0
checks = 0


def check(name, ok):
    global fails, checks
    checks += 1
    if not ok:
        fails += 1
    print(("PASS " if ok else "FAIL ") + name)


def note(s):
    print("   " + s)


# ------------------------------------------------------------------ a ring-generic carrier
class G:
    """A `SqU6` element over Z or Z/N, by honest 6 x 6 matrices."""

    def __init__(self, d, mod=None):
        self._c = {c: (d.get(c, 0) % mod if mod else d.get(c, 0)) for c in COORDS}
        self.mod = mod

    @staticmethod
    def rand(rng, mod, live=COORDS):
        return G({c: rng.randrange(mod if mod else 40) - (0 if mod else 20)
                  for c in live}, mod)

    def mat(self):
        return Q.mat_of(self._c)

    def __mul__(a, b):
        return G(Q.coords_of_mat(Q.mat_mul(a.mat(), b.mat(), a.mod)), a.mod)

    def inv(a):
        return G(Q.coords_of_mat(Q.mat_inv(a.mat(), a.mod)), a.mod)

    def __eq__(a, b):
        return all((a._c[c] - b._c[c]) % (a.mod if a.mod else 1) == 0 for c in COORDS) \
            if a.mod else all(a._c[c] == b._c[c] for c in COORDS)

    def __getattr__(self, c):
        if c in COORDS:
            return self._c[c]
        raise AttributeError(c)

    def __repr__(self):
        return "<" + ", ".join("%s=%d" % (c, self._c[c]) for c in COORDS if self._c[c]) + ">"


def one(mod):
    return G({}, mod)


def commP(p, q):
    return p.inv() * q.inv() * p * q


def conjP(p, g):
    return g.inv() * p * g


def sqWord(s, x, y):
    return conjP(x, s).inv() * (x * x * x).inv() * (y * y) * commP(y, conjP(y, s))


def sqRelWord(m):
    h = (len(m) - 3) // 2
    r = sqWord(m[0], m[1], m[2])
    for k in range(h):
        r = r * commP(m[3 + 2 * k], m[4 + 2 * k])
    return r


# ------------------------------------------------------------------ the emitted Lean forms
def gaThreePairL(z, L):
    return z.j * L.d - z.k * L.a


def gaThreePairR(z, L):
    return z.k * L.e - z.l * L.b


def gaThreePair(z, L):
    return (z.m * L.e - z.n * L.a + z.j * L.i - z.l * L.f
            + z.l * (L.a * L.b) - z.k * (L.a * L.e))


def sqFoxX6(s, x, y, mod):
    return G({c: 10 * x._c[c] - s._c[c] - 8 * y._c[c] for c in COORDS}, mod)


def gaThreeCorr(s, x, y, z0, z1, z2):
    return (z0.j * (-(s.d * x.e) + s.e * x.d - 4 * (x.d * x.e) + 2 * (x.d * y.e) + y.d * y.e)
            + z0.k * (8 * (x.a * x.e) - 2 * (x.a * y.e) - 2 * (x.e * y.a) - 2 * (y.a * y.e))
            + z0.l * (s.a * x.b - s.b * x.a - 4 * (x.a * x.b) + 2 * (x.b * y.a) + y.a * y.b)
            + z1.j * (3 * (s.d * x.e) - 2 * (s.d * y.e) + s.e * x.d - 20 * (x.d * x.e)
                      + 20 * (x.d * y.e) - 4 * (y.d * y.e))
            + z1.k * (2 * (s.a * s.e) - 14 * (s.a * x.e) + 10 * (s.a * y.e) - 14 * (s.e * x.a)
                      + 10 * (s.e * y.a) + 130 * (x.a * x.e) - 100 * (x.a * y.e)
                      - 100 * (x.e * y.a) + 80 * (y.a * y.e))
            + z1.l * (-2 * (s.a * s.b) + 11 * (s.a * x.b) - 8 * (s.a * y.b) + 13 * (s.b * x.a)
                      - 10 * (s.b * y.a) - 110 * (x.a * x.b) + 80 * (x.a * y.b)
                      + 100 * (x.b * y.a) - 76 * (y.a * y.b))
            + z2.j * (-2 * (s.d * y.e) + s.e * y.d)
            + z2.k * (s.a * y.e + s.e * y.a)
            + z2.l * (s.a * y.b - 2 * (s.b * y.a)))


def gaThreeCore(s, x, y, z0, z1, z2, mod):
    fx = sqFoxX6(s, x, y, mod)
    return G({
        "j": -4 * z1.j + 2 * z2.j,
        "k": -4 * z1.k + 2 * z2.k,
        "l": -4 * z1.l + 2 * z2.l,
        "m": (-4 * z1.m + 2 * z2.m
              + gaThreePairL(z0, x) + gaThreePairL(z1, fx) + gaThreePairL(z2, y)),
        "n": (-4 * z1.n + 2 * z2.n
              + gaThreePairR(z0, x) + gaThreePairR(z1, fx) + gaThreePairR(z2, y)),
        "o": (-4 * z1.o + 2 * z2.o
              + gaThreePair(z0, x) + gaThreePair(z1, fx) + gaThreePair(z2, y)
              + gaThreeCorr(s, x, y, z0, z1, z2)),
    }, mod)


def gaThreeHandle(p, q, z, w, mod):
    return G({
        "m": gaThreePairL(z, q) - gaThreePairL(w, p),
        "n": gaThreePairR(z, q) - gaThreePairR(w, p),
        "o": (gaThreePair(z, q) - gaThreePair(w, p)
              - (p.d * q.e - p.e * q.d) * (z.j + w.j)
              + (p.a * q.b - p.b * q.a) * (z.l + w.l)),
    }, mod)


def handleWord(us, vs, mod):
    r = one(mod)
    for u, v in zip(us, vs):
        r = r * commP(u, v)
    return r


def gaThreeShift(m, z, mod):
    h = (len(m) - 3) // 2
    us = [m[3 + 2 * k] for k in range(h)]
    vs = [m[4 + 2 * k] for k in range(h)]
    zus = [z[3 + 2 * k] for k in range(h)]
    zvs = [z[4 + 2 * k] for k in range(h)]
    hs = [gaThreeHandle(us[k], vs[k], zus[k], zvs[k], mod) for k in range(h)]
    blk = handleWord(us, vs, mod)
    coll = (blk.i * (-4 * z[1].j + 2 * z[2].j) - blk.f * (-4 * z[1].l + 2 * z[2].l))
    return (gaThreeCore(m[0], m[1], m[2], z[0], z[1], z[2], mod)
            * G({"m": sum(t.m for t in hs), "n": sum(t.n for t in hs),
                 "o": sum(t.o for t in hs)}, mod)
            * G({"o": coll}, mod))


GA3 = ["j", "k", "l", "m", "n", "o"]
MODS = [None, 4, 8, 16]

# =========================================================================================
print("== 0. the two group-law implementations agree ==")
random.seed(60101)
bad = 0
cmp = 0
for _ in range(600):
    p = {c: random.randrange(8) for c in COORDS}
    q = {c: random.randrange(8) for c in COORDS}
    P8, Q8 = G(p, 8), G(q, 8)
    pt = tuple(p[c] for c in COORDS)
    qt = tuple(q[c] for c in COORDS)
    for got, want in (((P8 * Q8)._c, M.mul(pt, qt)), (P8.inv()._c, M.inv(pt)),
                      (commP(P8, Q8)._c, M.commP(pt, qt)),
                      (sqWord(P8, Q8, P8 * Q8)._c, M.sqWord(pt, qt, M.mul(pt, qt)))):
        cmp += 1
        if tuple(got[c] for c in COORDS) != want:
            bad += 1
check("%d comparisons against the wave-59 matrix library, %d mismatches" % (cmp, bad), bad == 0)

# =========================================================================================
print()
print("== 1. gaThreeHandle: the commutator under a two-sided gamma_3-dressing ==")
random.seed(60102)
bad = 0
cmp = 0
for mod in MODS:
    for _ in range(400):
        p, q = G.rand(random, mod), G.rand(random, mod)
        z, w = G.rand(random, mod, GA3), G.rand(random, mod, GA3)
        cmp += 1
        if not (commP(p * z, q * w) == commP(p, q) * gaThreeHandle(p, q, z, w, mod)):
            bad += 1
check("%d comparisons over Z, Z/4, Z/8, Z/16, %d mismatches" % (cmp, bad), bad == 0)

# =========================================================================================
print()
print("== 2. gaThreeCore: the core word under a three-slot gamma_3-dressing ==")
random.seed(60103)
bad = 0
cmp = 0
for mod in MODS:
    for _ in range(300):
        s, x, y = G.rand(random, mod), G.rand(random, mod), G.rand(random, mod)
        z0, z1, z2 = (G.rand(random, mod, GA3), G.rand(random, mod, GA3),
                      G.rand(random, mod, GA3))
        cmp += 1
        if not (sqWord(s * z0, x * z1, y * z2)
                == sqWord(s, x, y) * gaThreeCore(s, x, y, z0, z1, z2, mod)):
            bad += 1
check("%d comparisons over Z, Z/4, Z/8, Z/16, %d mismatches" % (cmp, bad), bad == 0)

note("the class-four precedent's quadratic block, evaluated here, is NOT part of the form:")
note("  GradedGammaTwo.gaTwoQuad transposes to")
note("  (z0.j*z1.l - z0.l*z1.j) + 10*(z1.j*z1.l) - 8*(z1.j*z2.l) + z2.j*z2.l,")
random.seed(60104)
nonzero = 0
for _ in range(400):
    z0, z1, z2 = (G.rand(random, None, GA3), G.rand(random, None, GA3),
                  G.rand(random, None, GA3))
    qd = ((z0.j * z1.l - z0.l * z1.j) + 10 * (z1.j * z1.l) - 8 * (z1.j * z2.l) + z2.j * z2.l)
    if qd:
        nonzero += 1
check("that transposed block is generically NON-zero (%d of 400) yet absent from the identity,"
      " which is the structural finding" % nonzero, nonzero > 300)

# =========================================================================================
print()
print("== 3. gaThreeShift: the five-slot relator identity ==")
random.seed(60105)
bad = 0
cmp = 0
for mod in MODS:
    for h in range(5):
        for _ in range(60):
            m = [G.rand(random, mod) for _ in range(3 + 2 * h)]
            z = [G.rand(random, mod, GA3) for _ in range(3 + 2 * h)]
            cmp += 1
            if not (sqRelWord([m[i] * z[i] for i in range(len(m))])
                    == sqRelWord(m) * gaThreeShift(m, z, mod)):
                bad += 1
check("%d comparisons over Z, Z/4, Z/8, Z/16 at handle counts 0 to 4, %d mismatches"
      % (cmp, bad), bad == 0)

print()
print("== 3b. the gamma_4 specialisation reproduces the committed class-five identity ==")
random.seed(60106)
bad = 0
for _ in range(300):
    m = [G.rand(random, 8) for _ in range(5)]
    z = [G.rand(random, 8, ["m", "n", "o"]) for _ in range(5)]
    sh = gaThreeShift(m, z, 8)
    # GradedFiveDefect.conFiveShift, re-typed
    conFive = ((m[1].e * z[0].m - m[1].a * z[0].n)
               + ((10 * m[1].e - m[0].e - 8 * m[2].e) * z[1].m
                  - (10 * m[1].a - m[0].a - 8 * m[2].a) * z[1].n)
               + (m[2].e * z[2].m - m[2].a * z[2].n)
               + ((z[3].m * m[4].e - z[3].n * m[4].a) + (m[3].a * z[4].n - m[3].e * z[4].m)))
    want = G({"m": -4 * z[1].m + 2 * z[2].m, "n": -4 * z[1].n + 2 * z[2].n,
              "o": -4 * z[1].o + 2 * z[2].o + conFive}, 8)
    if not (sh == want):
        bad += 1
check("300 comparisons against GradedFiveDefect's conFiveShift, %d mismatches" % bad, bad == 0)

# =========================================================================================
print()
print("== 4. the stage-four soundness, by brute force ==")
SIG = M.sigFiveMark
stageX = M.named(a=2, e=5)
stageY = M.named(e=2, f=1, g=1, h=1, m=3, n=3)
stageU = M.named(a=6, b=7, c=4, d=1, e=3, g=5, h=5)
stageV = M.named(a=6, b=7, c=6, d=1, e=3, f=5, g=3, h=3, i=4)


def toG(t):
    return G({c: t[i] for i, c in enumerate(COORDS)}, 8)


random.seed(60107)
bad = 0
for h in range(1, 4):
    base = [toG(M.mul(SIG, stageX)), toG(stageX), toG(stageY)]
    for k in range(h):
        base += [toG(stageU), toG(stageV)] if k == h - 1 else [one(8), one(8)]
    for _ in range(1500):
        z = [G({c: (2 * random.randrange(4) if c in ("j", "l", "m")
                    else random.randrange(8)) for c in GA3}, 8)
             for _ in range(len(base))]
        if gaThreeShift(base, z, 8).o % 2:
            bad += 1
check("4500 dressings with j, l, m even: the shift's class-five row is always even"
      " (%d exceptions)" % bad, bad == 0)

note("…and the hypothesis is sharp: dropping it produces odd shifts.")
random.seed(60108)
odd = 0
base = [toG(M.mul(SIG, stageX)), toG(stageX), toG(stageY), toG(stageU), toG(stageV)]
for _ in range(1500):
    z = [G({c: random.randrange(8) for c in GA3}, 8) for _ in range(5)]
    if gaThreeShift(base, z, 8).o % 2:
        odd += 1
check("without it, %d of 1500 unrestricted dressings move the row oddly" % odd, odd > 500)

# =========================================================================================
print()
print("== 5. the witness point and the wave-59 comparison ==")
for h, jj in ((1, 0), (2, 1), (3, 2)):
    r0 = M.sqRelWord(P.mirTuple(h, jj, SIG, stageX, stageY, stageU, stageV))
    r1 = P.residue(SIG, stageX, stageY, stageU, stageV, h, jj)
    check("h=%d j=%d : undressed trivial and dressed = <o=1>" % (h, jj),
          r0 == M.ONE and r1 == M.named(o=1))
check("every letter of the new point has an even (1,2)-column",
      all(z[0] % 2 == 0 for z in (SIG, stageX, stageY, stageU, stageV)))
check("every letter of the new point has an even (3,4)-column",
      all(z[2] % 2 == 0 for z in (SIG, stageX, stageY, stageU, stageV)))
check("wave 59's U-letter does NOT have an even (1,2)-column (forceU.a = %d)" % M.sepU[0],
      M.sepU[0] % 2 == 1)
kill = M.commP(M.commP(SIG, M.sepU), M.sepY)
check("wave 59's killing dressing [[sigma, U], x1] = %s has an ODD class-four coordinate"
      % M.show(kill), kill[12] % 2 == 1)
blk = M.commP(stageU, stageV)
check("the new point's handle block is live with an odd class-four row (%s)" % M.show(blk),
      blk != M.ONE and blk[12] % 2 == 1)

print()
print("TOTAL CHECKS: %d   FAILURES: %d" % (checks, fails))
