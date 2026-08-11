"""Exact integer polynomial arithmetic and the class-five carrier `SqU6` over it.

Shared engine for the W59-DEFECT5 derivation.  Polynomials are dictionaries from
sorted variable tuples (monomials, with repetition) to integer coefficients; the
zero polynomial is the empty dictionary.  Nothing here is floating point and
nothing here is symbolic beyond exact integer arithmetic, which is the campaign's
proven derivation workflow (scripts/w58_five/, scripts/w58_sigma5/).

The `SqU6` group law transcribed below is the committed one from
`GQ2/Dyadic/SqCore/GradedFive.lean` (the `Mul` and `Inv` instances), coordinate for
coordinate.  `validate_defect5.py` checks it against honest 6 x 6 matrix collection.

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

from itertools import product

COORDS = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o"]

# The strictly-upper entry each coordinate names, as (row, col) 1-indexed.
ENTRY = {
    "a": (1, 2), "b": (2, 3), "c": (3, 4), "d": (4, 5), "e": (5, 6),
    "f": (1, 3), "g": (2, 4), "h": (3, 5), "i": (4, 6),
    "j": (1, 4), "k": (2, 5), "l": (3, 6),
    "m": (1, 5), "n": (2, 6),
    "o": (1, 6),
}


# ---------------------------------------------------------------- polynomials


def pzero():
    return {}


def pconst(c):
    return {(): int(c)} if c else {}


def pvar(name):
    return {(name,): 1}


def padd(*ps):
    out = {}
    for p in ps:
        for mon, c in p.items():
            nc = out.get(mon, 0) + c
            if nc:
                out[mon] = nc
            elif mon in out:
                del out[mon]
    return out


def pneg(p):
    return {mon: -c for mon, c in p.items()}


def psub(p, q):
    return padd(p, pneg(q))


def pmul(p, q):
    out = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            mon = tuple(sorted(m1 + m2))
            nc = out.get(mon, 0) + c1 * c2
            if nc:
                out[mon] = nc
            elif mon in out:
                del out[mon]
    return out


def pscale(k, p):
    k = int(k)
    if k == 0:
        return {}
    return {mon: k * c for mon, c in p.items()}


def pvars(p):
    s = set()
    for mon in p:
        s.update(mon)
    return s


def pdeg(p):
    return max((len(mon) for mon in p), default=0)


def peval(p, env):
    """Evaluate a polynomial at an integer assignment (a dict name -> int)."""
    total = 0
    for mon, c in p.items():
        v = c
        for name in mon:
            v *= env[name]
        total += v
    return total


# ------------------------------------------------------------------ the group


class U6:
    """An element of `SqU6 R` with polynomial coordinates."""

    __slots__ = tuple(COORDS)

    def __init__(self, **kw):
        for co in COORDS:
            setattr(self, co, kw.get(co, pzero()))

    @staticmethod
    def one():
        return U6()

    @staticmethod
    def gen(prefix):
        """The generic element with coordinates `prefix_a`, ..., `prefix_o`."""
        return U6(**{co: pvar(prefix + "_" + co) for co in COORDS})

    def coords(self):
        return {co: getattr(self, co) for co in COORDS}

    def __mul__(p, q):
        return U6(
            a=padd(p.a, q.a),
            b=padd(p.b, q.b),
            c=padd(p.c, q.c),
            d=padd(p.d, q.d),
            e=padd(p.e, q.e),
            f=padd(p.f, q.f, pmul(p.a, q.b)),
            g=padd(p.g, q.g, pmul(p.b, q.c)),
            h=padd(p.h, q.h, pmul(p.c, q.d)),
            i=padd(p.i, q.i, pmul(p.d, q.e)),
            j=padd(p.j, q.j, pmul(p.a, q.g), pmul(p.f, q.c)),
            k=padd(p.k, q.k, pmul(p.b, q.h), pmul(p.g, q.d)),
            l=padd(p.l, q.l, pmul(p.c, q.i), pmul(p.h, q.e)),
            m=padd(p.m, q.m, pmul(p.a, q.k), pmul(p.f, q.h), pmul(p.j, q.d)),
            n=padd(p.n, q.n, pmul(p.b, q.l), pmul(p.g, q.i), pmul(p.k, q.e)),
            o=padd(p.o, q.o, pmul(p.a, q.n), pmul(p.f, q.l), pmul(p.j, q.i),
                   pmul(p.m, q.e)),
        )

    def inv(p):
        ab, bc, cd, de = pmul(p.a, p.b), pmul(p.b, p.c), pmul(p.c, p.d), pmul(p.d, p.e)
        return U6(
            a=pneg(p.a), b=pneg(p.b), c=pneg(p.c), d=pneg(p.d), e=pneg(p.e),
            f=psub(ab, p.f), g=psub(bc, p.g), h=psub(cd, p.h), i=psub(de, p.i),
            j=padd(pneg(pmul(ab, p.c)), pmul(p.a, p.g), pmul(p.c, p.f), pneg(p.j)),
            k=padd(pneg(pmul(bc, p.d)), pmul(p.b, p.h), pmul(p.d, p.g), pneg(p.k)),
            l=padd(pneg(pmul(cd, p.e)), pmul(p.c, p.i), pmul(p.e, p.h), pneg(p.l)),
            m=padd(pmul(pmul(ab, p.c), p.d), pneg(pmul(ab, p.h)),
                   pneg(pmul(pmul(p.a, p.d), p.g)), pmul(p.a, p.k),
                   pneg(pmul(cd, p.f)), pmul(p.d, p.j), pmul(p.f, p.h), pneg(p.m)),
            n=padd(pmul(pmul(bc, p.d), p.e), pneg(pmul(bc, p.i)),
                   pneg(pmul(pmul(p.b, p.e), p.h)), pmul(p.b, p.l),
                   pneg(pmul(de, p.g)), pmul(p.e, p.k), pmul(p.g, p.i), pneg(p.n)),
            o=padd(
                pneg(pmul(pmul(pmul(ab, p.c), p.d), p.e)),
                pmul(pmul(ab, p.c), p.i),
                pmul(pmul(ab, p.e), p.h),
                pneg(pmul(ab, p.l)),
                pmul(pmul(p.a, de), p.g),
                pneg(pmul(pmul(p.a, p.e), p.k)),
                pneg(pmul(pmul(p.a, p.g), p.i)),
                pmul(p.a, p.n),
                pmul(pmul(cd, p.e), p.f),
                pneg(pmul(pmul(p.c, p.f), p.i)),
                pneg(pmul(de, p.j)),
                pneg(pmul(pmul(p.e, p.f), p.h)),
                pmul(p.e, p.m),
                pmul(p.f, p.l),
                pmul(p.i, p.j),
                pneg(p.o),
            ),
        )

    def pow(p, n):
        assert n >= 0
        out = U6.one()
        for _ in range(n):
            out = out * p
        return out

    def is_zero(p):
        return all(not getattr(p, co) for co in COORDS)

    def sub_coords(p, q):
        """Coordinatewise difference, as a dict."""
        return {co: psub(getattr(p, co), getattr(q, co)) for co in COORDS}


def conjP(p, g):
    """The repo convention `x ^ g = g⁻¹ * x * g`."""
    return g.inv() * p * g


def commP(p, q):
    """The repo convention `[x, y] = x⁻¹ * y⁻¹ * x * y`."""
    return p.inv() * q.inv() * p * q


def sqWord(s, x, y):
    """`(x₀^σ)⁻¹ · x₀⁻³ · x₁² · [x₁, x₁^σ]`, the committed core word shape."""
    return conjP(x, s).inv() * x.pow(3).inv() * y.pow(2) * commP(y, conjP(y, s))


def handleWord(us, vs):
    """`∏_{j<h} [u_j, v_j]` in the fixed left-to-right order."""
    out = U6.one()
    for u, v in zip(us, vs):
        out = out * commP(u, v)
    return out


def sqRelWord(m, h):
    """`sqWord (m 0) (m 1) (m 2) * handleWord`, with handles at `3+2j`, `4+2j`."""
    us = [m[3 + 2 * j] for j in range(h)]
    vs = [m[4 + 2 * j] for j in range(h)]
    return sqWord(m[0], m[1], m[2]) * handleWord(us, vs)


# ------------------------------------------------------------- honest 6 x 6


def mat_of(vals):
    """The honest 6 x 6 unitriangular matrix of an integer coordinate dict."""
    M = [[1 if r == c else 0 for c in range(6)] for r in range(6)]
    for co in COORDS:
        r, c = ENTRY[co]
        M[r - 1][c - 1] = vals[co]
    return M


def mat_mul(A, B, mod=None):
    C = [[0] * 6 for _ in range(6)]
    for r in range(6):
        for c in range(6):
            v = sum(A[r][t] * B[t][c] for t in range(6))
            C[r][c] = v % mod if mod else v
    return C


def mat_inv(A, mod=None):
    """Inverse of a unitriangular matrix by back substitution (exact)."""
    N = [[0] * 6 for _ in range(6)]
    for r in range(6):
        N[r][r] = 1
    for d in range(1, 6):
        for r in range(6 - d):
            c = r + d
            v = -A[r][c] - sum(A[r][t] * N[t][c] for t in range(r + 1, c))
            N[r][c] = v % mod if mod else v
    return N


def coords_of_mat(M):
    return {co: M[ENTRY[co][0] - 1][ENTRY[co][1] - 1] for co in COORDS}


# ------------------------------------------------------------------ printing


def poly_terms(p):
    """Sorted (monomial, coefficient) pairs: by degree, then lexicographically."""
    return sorted(p.items(), key=lambda kv: (len(kv[0]), kv[0]))


def poly_str(p, namer=lambda v: v):
    if not p:
        return "0"
    out = []
    for mon, c in poly_terms(p):
        factors = [namer(v) for v in mon]
        body = " * ".join(factors) if factors else "1"
        out.append((c, body))
    return " + ".join(("%d * %s" % (c, b)) if c != 1 else b for c, b in out)
