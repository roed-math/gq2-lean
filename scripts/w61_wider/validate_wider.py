"""W61-WIDER step 10: every form the Lean file writes down, checked against honest collection.

Nothing here reads a Lean file.  The correction and quadratic blocks come from `forms.py`, which
`emit_lean.py` produced from the same certified polynomial data as the Lean `def`s, and the rest
is re-typed from the derivation; all of it is compared against 6 x 6 unitriangular MATRIX
collection, a group law with no shared code with the transcribed one.  A mismatch here would
mean the Lean file is wrong even though it compiles.

Sections
  0. the two group-law implementations agree;
  1. the six pairing forms, `[gamma_2 element, letter]`;
  2. `gaTwoHandle`, the commutator under a two-sided `gamma_2`-dressing;
  3. `gaTwoCore`, the core word under a three-slot `gamma_2`-dressing;
  4. `gaTwoShift`, the five-slot relator identity, at handle counts 0 to 4;
  4b. the `gamma_3` specialisation reproduces `GradedFiveStageFour.gaThreeShift`;
  5. the soundness, by brute force: the class-five row is the channel functional mod two;
  6. the sharpness: dropping the hypotheses produces odd shifts, and the class-four RIGHT row
     is odd even with them.

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""
import sys
import os
import random

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_defect5"))
sys.path.insert(0, HERE)

import u6poly as Q                                            # noqa: E402
import forms as F                                             # noqa: E402

COORDS = Q.COORDS
GA2 = ["f", "g", "h", "i", "j", "k", "l", "m", "n", "o"]
GA3 = ["j", "k", "l", "m", "n", "o"]
fails = 0
checks = 0


def check(name, ok):
    global fails, checks
    checks += 1
    if not ok:
        fails += 1
    print(("PASS " if ok else "FAIL ") + name)


class G:
    """A `SqU6` element over Z or Z/N, carried by an honest 6 x 6 matrix."""

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


def red(v, mod):
    return v % mod if mod else v


# --------------------------------------------------------------- the emitted Lean forms
def pairJ(z, L):
    return z.f * L.c - z.g * L.a


def pairK(z, L):
    return z.g * L.d - z.h * L.b


def pairL(z, L):
    return z.h * L.e - z.i * L.c


def pairM(z, L):
    return (z.j * L.d - z.k * L.a + z.f * L.h - z.h * L.f
            + z.h * (L.a * L.b) - z.g * (L.a * L.d))


def pairN(z, L):
    return (z.k * L.e - z.l * L.b + z.g * L.i - z.i * L.g
            + z.i * (L.b * L.c) - z.h * (L.b * L.e))


def pairO(z, L):
    return (z.m * L.e - z.n * L.a + z.j * L.i - z.i * L.j + z.f * L.l - z.l * L.f
            + z.l * (L.a * L.b) - z.k * (L.a * L.e) + z.i * (L.a * L.g) - z.g * (L.a * L.i)
            + z.i * (L.c * L.f) - z.h * (L.e * L.f) + z.f * z.i * L.c - z.f * z.h * L.e
            - z.i * (L.a * L.b * L.c) + z.h * (L.a * L.b * L.e))


def foxX6(s, x, y, mod):
    return G({c: 10 * x._c[c] - s._c[c] - 8 * y._c[c] for c in COORDS}, mod)


def u6Comm3L(p, q):
    return (p.a * q.g - p.g * q.a + p.f * q.c - p.c * q.f
            + p.a * p.c * q.b - p.a * p.b * q.c + p.c * q.a * q.b - p.b * q.a * q.c)


def u6Comm3R(p, q):
    return (p.c * q.i - p.i * q.c + p.h * q.e - p.e * q.h
            + p.c * p.e * q.d - p.c * p.d * q.e + p.e * q.c * q.d - p.d * q.c * q.e)


def handleX(p, q, z, w):
    return (w.f * ((q.c - p.c) * z.i - q.e * z.h - p.c * (p.d * q.e - p.e * q.d))
            + w.g * (p.a * (z.i + (p.d * q.e - p.e * q.d)))
            + w.h * (p.e * (z.f + (p.a * q.b - p.b * q.a)))
            + w.i * ((q.c - p.c) * z.f - q.a * z.g - p.c * (p.a * q.b - p.b * q.a)))


def gaTwoHandle(p, q, z, w, mod):
    return G({
        "j": pairJ(z, q) - pairJ(w, p),
        "k": pairK(z, q) - pairK(w, p),
        "l": pairL(z, q) - pairL(w, p),
        "m": (pairM(z, q) - pairM(w, p) + (z.f * w.h - z.h * w.f)
              + (p.a * q.b - p.b * q.a) * (z.h + w.h)
              - (p.c * q.d - p.d * q.c) * (z.f + w.f)),
        "n": (pairN(z, q) - pairN(w, p) + (z.g * w.i - z.i * w.g)
              + (p.b * q.c - p.c * q.b) * (z.i + w.i)
              - (p.d * q.e - p.e * q.d) * (z.g + w.g)),
        "o": (pairO(z, q) - pairO(w, p) + (z.f * w.l - z.l * w.f) + (z.j * w.i - z.i * w.j)
              + (p.a * q.b - p.b * q.a) * (z.l + w.l) - u6Comm3R(p, q) * (z.f + w.f)
              + u6Comm3L(p, q) * (z.i + w.i) - (p.d * q.e - p.e * q.d) * (z.j + w.j)
              + handleX(p, q, z, w)),
    }, mod)


def gaTwoCore(s, x, y, z0, z1, z2, mod):
    fx = foxX6(s, x, y, mod)
    return G({
        "f": -4 * z1.f + 2 * z2.f, "g": -4 * z1.g + 2 * z2.g,
        "h": -4 * z1.h + 2 * z2.h, "i": -4 * z1.i + 2 * z2.i,
        "j": -4 * z1.j + 2 * z2.j + (pairJ(z0, x) + pairJ(z1, fx) + pairJ(z2, y)),
        "k": -4 * z1.k + 2 * z2.k + (pairK(z0, x) + pairK(z1, fx) + pairK(z2, y)),
        "l": -4 * z1.l + 2 * z2.l + (pairL(z0, x) + pairL(z1, fx) + pairL(z2, y)),
        "m": (-4 * z1.m + 2 * z2.m + (pairM(z0, x) + pairM(z1, fx) + pairM(z2, y))
              + F.gaTwoCorrM(s, x, y, z0, z1, z2) + F.gaTwoQuadM(z0, z1, z2)),
        "n": (-4 * z1.n + 2 * z2.n + (pairN(z0, x) + pairN(z1, fx) + pairN(z2, y))
              + F.gaTwoCorrN(s, x, y, z0, z1, z2) + F.gaTwoQuadN(z0, z1, z2)),
        "o": (-4 * z1.o + 2 * z2.o + (pairO(z0, x) + pairO(z1, fx) + pairO(z2, y))
              + F.gaTwoCorrO(s, x, y, z0, z1, z2) + F.gaTwoQuadO(s, x, y, z0, z1, z2)),
    }, mod)


def sqCross(xs, ys):
    return sum(xs[a] * ys[b] for b in range(len(ys)) for a in range(b))


def blocks(us, vs):
    return {
        "f": sum(u.a * v.b - v.a * u.b for u, v in zip(us, vs)),
        "g": sum(u.b * v.c - v.b * u.c for u, v in zip(us, vs)),
        "h": sum(u.c * v.d - v.c * u.d for u, v in zip(us, vs)),
        "i": sum(u.d * v.e - v.d * u.e for u, v in zip(us, vs)),
        "j": sum(u6Comm3L(u, v) for u, v in zip(us, vs)),
        "l": sum(u6Comm3R(u, v) for u, v in zip(us, vs)),
    }


def gaTwoHandleSum(us, vs, zus, zvs, mod):
    Ds = [gaTwoHandle(us[k], vs[k], zus[k], zvs[k], mod) for k in range(len(us))]
    d = {co: sum(getattr(D, co) for D in Ds) for co in GA3}
    d["o"] += (sqCross([D.j for D in Ds], [u.d * v.e - v.d * u.e for u, v in zip(us, vs)])
               - sqCross([D.l for D in Ds], [u.a * v.b - v.a * u.b for u, v in zip(us, vs)]))
    return G(d, mod)


def gaTwoShift(m, zs, mod):
    h = (len(m) - 3) // 2
    us = [m[3 + 2 * k] for k in range(h)]
    vs = [m[4 + 2 * k] for k in range(h)]
    zus = [zs[3 + 2 * k] for k in range(h)]
    zvs = [zs[4 + 2 * k] for k in range(h)]
    C = gaTwoCore(m[0], m[1], m[2], zs[0], zs[1], zs[2], mod)
    T = gaTwoHandleSum(us, vs, zus, zvs, mod)
    B = blocks(us, vs)
    K = G({"m": C.f * B["h"] - C.h * B["f"],
           "n": C.g * B["i"] - C.i * B["g"],
           "o": C.f * B["l"] - C.l * B["f"] + C.j * B["i"] - C.i * B["j"]}, mod)
    return C * (T * K)


def channel(z, L):
    return z.m * L.e + z.i * L.j + z.l * L.f


def shiftChan(m, zs, mod):
    h = (len(m) - 3) // 2
    t = (channel(zs[0], m[1]) + channel(zs[1], foxX6(m[0], m[1], m[2], mod))
         + channel(zs[2], m[2]))
    for k in range(h):
        t += (channel(zs[3 + 2 * k], m[4 + 2 * k]) - channel(zs[4 + 2 * k], m[3 + 2 * k]))
    return t


RINGS = [None, 4, 8, 16]
rng = random.Random(6161)

print("=" * 92)
print("== 0. the two group-law implementations agree ==")
bad = 0
for _ in range(400):
    for mod in RINGS:
        a, b = G.rand(rng, mod), G.rand(rng, mod)
        pa = Q.U6(**{c: Q.pconst(a._c[c]) for c in COORDS})
        pb = Q.U6(**{c: Q.pconst(b._c[c]) for c in COORDS})
        prod = pa * pb
        got = {c: red(Q.peval(getattr(prod, c), {}), mod) for c in COORDS}
        want = (a * b)._c
        if any(got[c] != want[c] for c in COORDS):
            bad += 1
check("1600 comparisons of the transcribed group law against 6 x 6 matrices, %d mismatches"
      % bad, bad == 0)
print()

print("=" * 92)
print("== 1. the six pairing forms ==")
bad = 0
for _ in range(400):
    for mod in RINGS:
        z = G.rand(rng, mod, GA2)
        L = G.rand(rng, mod)
        c = commP(z, L)
        want = {"j": pairJ(z, L), "k": pairK(z, L), "l": pairL(z, L),
                "m": pairM(z, L), "n": pairN(z, L), "o": pairO(z, L)}
        if any(red(want[co], mod) != getattr(c, co) for co in GA3):
            bad += 1
        if any(getattr(c, co) != 0 for co in ["a", "b", "c", "d", "e", "f", "g", "h", "i"]):
            bad += 1
check("1600 comparisons over Z, Z/4, Z/8, Z/16, %d mismatches" % bad, bad == 0)
print()

print("=" * 92)
print("== 2. gaTwoHandle: the commutator under a two-sided gamma_2-dressing ==")
bad = 0
for _ in range(400):
    for mod in RINGS:
        p, q = G.rand(rng, mod), G.rand(rng, mod)
        z, w = G.rand(rng, mod, GA2), G.rand(rng, mod, GA2)
        lhs = commP(p * z, q * w)
        rhs = commP(p, q) * gaTwoHandle(p, q, z, w, mod)
        if not (lhs == rhs):
            bad += 1
check("1600 comparisons over Z, Z/4, Z/8, Z/16, %d mismatches" % bad, bad == 0)
print()

print("=" * 92)
print("== 3. gaTwoCore: the core word under a three-slot gamma_2-dressing ==")
bad = 0
for _ in range(300):
    for mod in RINGS:
        s, x, y = (G.rand(rng, mod) for _ in range(3))
        z0, z1, z2 = (G.rand(rng, mod, GA2) for _ in range(3))
        lhs = sqWord(s * z0, x * z1, y * z2)
        rhs = sqWord(s, x, y) * gaTwoCore(s, x, y, z0, z1, z2, mod)
        if not (lhs == rhs):
            bad += 1
check("1200 comparisons over Z, Z/4, Z/8, Z/16, %d mismatches" % bad, bad == 0)
print()

print("=" * 92)
print("== 4. gaTwoShift: the five-slot relator identity, handle counts 0 to 4 ==")
bad = 0
for h in range(5):
    for _ in range(60):
        for mod in RINGS:
            m = [G.rand(rng, mod) for _ in range(3 + 2 * h)]
            zs = [G.rand(rng, mod, GA2) for _ in range(3 + 2 * h)]
            lhs = sqRelWord([m[i] * zs[i] for i in range(len(m))])
            rhs = sqRelWord(m) * gaTwoShift(m, zs, mod)
            if not (lhs == rhs):
                bad += 1
check("1200 comparisons over Z, Z/4, Z/8, Z/16 at handle counts 0 to 4, %d mismatches" % bad,
      bad == 0)
print()

print("=" * 92)
print("== 4b. the gamma_3 specialisation reproduces the committed stage-four identity ==")
bad = 0
for h in range(3):
    for _ in range(50):
        for mod in RINGS:
            m = [G.rand(rng, mod) for _ in range(3 + 2 * h)]
            zs = [G.rand(rng, mod, GA3) for _ in range(3 + 2 * h)]
            lhs = sqRelWord([m[i] * zs[i] for i in range(len(m))])
            rhs = sqRelWord(m) * gaTwoShift(m, zs, mod)
            if not (lhs == rhs):
                bad += 1
check("600 comparisons with gamma_3-shaped dressings, %d mismatches" % bad, bad == 0)
print()

print("=" * 92)
print("== 5. the soundness, by brute force ==")


def lattice_point(rng, mod, h):
    """A marking with even (1,2)- and (3,4)-columns and a dressing with even f, h, j."""
    m, zs = [], []
    for _ in range(3 + 2 * h):
        d = {c: rng.randrange(mod) for c in COORDS}
        d["a"] = 2 * rng.randrange(mod // 2)
        d["c"] = 2 * rng.randrange(mod // 2)
        m.append(G(d, mod))
        e = {c: rng.randrange(mod) for c in GA2}
        e["f"] = 2 * rng.randrange(mod // 2)
        e["h"] = 2 * rng.randrange(mod // 2)
        e["j"] = 2 * rng.randrange(mod // 2)
        zs.append(G(e, mod))
    return m, zs


bad = 0
for h in range(5):
    for _ in range(300):
        for mod in (8, 16):
            m, zs = lattice_point(rng, mod, h)
            d = (gaTwoShift(m, zs, mod).o - shiftChan(m, zs, mod)) % mod
            if d % 2 != 0:
                bad += 1
check("3000 achievable dressings: the class-five row equals the channel functional mod two, "
      "%d exceptions" % bad, bad == 0)

# and the quadratic block alone
bad = 0
for _ in range(1200):
    for mod in (8, 16):
        m, zs = lattice_point(rng, mod, 1)
        if F.gaTwoQuadO(m[0], m[1], m[2], zs[0], zs[1], zs[2]) % 2 != 0:
            bad += 1
check("2400 achievable dressings: gaTwoQuadO is EVEN, %d exceptions" % bad, bad == 0)

nz = 0
for _ in range(1200):
    m = [G.rand(rng, 8) for _ in range(5)]
    zs = [G.rand(rng, 8, GA2) for _ in range(5)]
    if F.gaTwoQuadO(m[0], m[1], m[2], zs[0], zs[1], zs[2]) % 8 != 0:
        nz += 1
check("…and the block is not vacuous: %d of 1200 unrestricted dressings make it non-zero" % nz,
      nz > 0)
print()

print("=" * 92)
print("== 6. sharpness ==")
odd = 0
for _ in range(1500):
    mod = 8
    m = [G.rand(rng, mod) for _ in range(5)]
    zs = [G.rand(rng, mod, GA2) for _ in range(5)]
    if (gaTwoShift(m, zs, mod).o - shiftChan(m, zs, mod)) % 2 != 0:
        odd += 1
check("without the hypotheses, %d of 1500 unrestricted dressings move the row oddly" % odd,
      odd > 0)

oddN = 0
for _ in range(1200):
    for mod in (8,):
        m, zs = lattice_point(rng, mod, 1)
        if F.gaTwoQuadN(zs[0], zs[1], zs[2]) % 2 != 0:
            oddN += 1
check("the class-four RIGHT quadratic block is NOT even on the lattice: %d of 1200 odd" % oddN,
      oddN > 0)
print()

print("TOTAL CHECKS: %d   FAILURES: %d" % (checks, fails))
sys.exit(1 if fails else 0)
