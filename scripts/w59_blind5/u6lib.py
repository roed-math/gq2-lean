"""W59-BLIND5: exact U_6 arithmetic, in coordinates and as honest 6 x 6 matrices.

Coordinate naming is the campaign's, matching `GQ2/Dyadic/SqCore/GradedFive.lean`:

    index  0  1  2  3  4   5  6  7  8   9 10 11  12 13  14
    name   a  b  c  d  e   f  g  h  i   j  k  l   m  n   o
    entry 12 23 34 45 56  13 24 35 46  14 25 36  15 26  16

Nothing here is trusted: `check_group_law` compares the transcribed coordinate law against
honest 6 x 6 matrix multiplication over Z, and every derived closed form is re-checked
numerically before it is emitted.

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

from sympy import Matrix, Symbol, expand

NAMES = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o"]

# (row, col) of each coordinate in the 6 x 6 matrix, zero-indexed.
CELL = {
    "a": (0, 1), "b": (1, 2), "c": (2, 3), "d": (3, 4), "e": (4, 5),
    "f": (0, 2), "g": (1, 3), "h": (2, 4), "i": (3, 5),
    "j": (0, 3), "k": (1, 4), "l": (2, 5),
    "m": (0, 4), "n": (1, 5),
    "o": (0, 5),
}


class U6:
    """A U_6 element as a dict of fifteen coefficients."""

    __slots__ = ("co",)

    def __init__(self, coeffs=None):
        self.co = {k: 0 for k in NAMES}
        if coeffs:
            for k, v in coeffs.items():
                self.co[k] = v

    def __getattr__(self, k):
        if k in CELL:
            return self.co[k]
        raise AttributeError(k)

    def __repr__(self):
        return "U6(" + ", ".join(f"{k}={self.co[k]}" for k in NAMES if self.co[k] != 0) + ")"

    def matrix(self):
        m = Matrix.eye(6)
        for k, (r, s) in CELL.items():
            m[r, s] = self.co[k]
        return m

    @staticmethod
    def of_matrix(m):
        return U6({k: expand(m[r, s]) for k, (r, s) in CELL.items()})

    def __eq__(self, other):
        return all(expand(self.co[k] - other.co[k]) == 0 for k in NAMES)


def sym(prefix):
    """A generic U_6 element with symbolic coordinates `prefix_a`, ..., `prefix_o`."""
    return U6({k: Symbol(f"{prefix}{k}") for k in NAMES})


ONE = U6()


def mul(p, q):
    """The transcribed Lean multiplication (`SqU6.mul_*`)."""
    return U6({
        "a": p.a + q.a,
        "b": p.b + q.b,
        "c": p.c + q.c,
        "d": p.d + q.d,
        "e": p.e + q.e,
        "f": p.f + q.f + p.a * q.b,
        "g": p.g + q.g + p.b * q.c,
        "h": p.h + q.h + p.c * q.d,
        "i": p.i + q.i + p.d * q.e,
        "j": p.j + q.j + p.a * q.g + p.f * q.c,
        "k": p.k + q.k + p.b * q.h + p.g * q.d,
        "l": p.l + q.l + p.c * q.i + p.h * q.e,
        "m": p.m + q.m + p.a * q.k + p.f * q.h + p.j * q.d,
        "n": p.n + q.n + p.b * q.l + p.g * q.i + p.k * q.e,
        "o": p.o + q.o + p.a * q.n + p.f * q.l + p.j * q.i + p.m * q.e,
    })


def inv(p):
    """The transcribed Lean inverse (`SqU6.inv_*`)."""
    return U6({
        "a": -p.a, "b": -p.b, "c": -p.c, "d": -p.d, "e": -p.e,
        "f": p.a * p.b - p.f,
        "g": p.b * p.c - p.g,
        "h": p.c * p.d - p.h,
        "i": p.d * p.e - p.i,
        "j": -(p.a * p.b * p.c) + p.a * p.g + p.c * p.f - p.j,
        "k": -(p.b * p.c * p.d) + p.b * p.h + p.d * p.g - p.k,
        "l": -(p.c * p.d * p.e) + p.c * p.i + p.e * p.h - p.l,
        "m": (p.a * p.b * p.c * p.d - p.a * p.b * p.h - p.a * p.d * p.g + p.a * p.k
              - p.c * p.d * p.f + p.d * p.j + p.f * p.h - p.m),
        "n": (p.b * p.c * p.d * p.e - p.b * p.c * p.i - p.b * p.e * p.h + p.b * p.l
              - p.d * p.e * p.g + p.e * p.k + p.g * p.i - p.n),
        "o": (-(p.a * p.b * p.c * p.d * p.e) + p.a * p.b * p.c * p.i + p.a * p.b * p.e * p.h
              - p.a * p.b * p.l + p.a * p.d * p.e * p.g - p.a * p.e * p.k - p.a * p.g * p.i
              + p.a * p.n + p.c * p.d * p.e * p.f - p.c * p.f * p.i - p.d * p.e * p.j
              - p.e * p.f * p.h + p.e * p.m + p.f * p.l + p.i * p.j - p.o),
    })


def pw(p, n):
    r = ONE
    for _ in range(n):
        r = mul(r, p)
    return r


def conjP(x, g):
    """`conjP x g = g⁻¹ * x * g`."""
    return mul(mul(inv(g), x), g)


def commP(x, y):
    """`commP x y = x⁻¹ * y⁻¹ * x * y`."""
    return mul(mul(mul(inv(x), inv(y)), x), y)


def sqWord(s, x, y):
    """`sqWord s x y = (conjP x s)⁻¹ * (x ^ 3)⁻¹ * y ^ 2 * commP y (conjP y s)`."""
    return mul(mul(mul(inv(conjP(x, s)), inv(pw(x, 3))), pw(y, 2)), commP(y, conjP(y, s)))


def normalise(p):
    return U6({k: expand(p.co[k]) for k in NAMES})


def check_group_law(rng, trials=400):
    """Compare the coordinate law against honest 6 x 6 matrix arithmetic over Z."""
    bad = 0
    for _ in range(trials):
        p = U6({k: rng.randrange(-6, 7) for k in NAMES})
        q = U6({k: rng.randrange(-6, 7) for k in NAMES})
        if U6.of_matrix(p.matrix() * q.matrix()) != mul(p, q):
            bad += 1
        if U6.of_matrix(p.matrix().inv()) != inv(p):
            bad += 1
        if U6.of_matrix(p.matrix() ** 3) != pw(p, 3):
            bad += 1
        gm = q.matrix()
        if U6.of_matrix(gm.inv() * p.matrix() * gm) != conjP(p, q):
            bad += 1
        pm, qm = p.matrix(), q.matrix()
        if U6.of_matrix(pm.inv() * qm.inv() * pm * qm) != commP(p, q):
            bad += 1
    return trials * 5 - bad, bad


def sqWord_matrix(s, x, y):
    """`sqWord` computed entirely with honest 6 x 6 matrices."""
    sm, xm, ym = s.matrix(), x.matrix(), y.matrix()
    cxs = sm.inv() * xm * sm
    cys = sm.inv() * ym * sm
    w = (cxs.inv() * (xm ** 3).inv() * (ym ** 2)
         * (ym.inv() * cys.inv() * ym * cys))
    return U6.of_matrix(w)


SIG_FIVE = U6({"b": 1})
