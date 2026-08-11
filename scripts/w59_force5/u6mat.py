"""W59-FORCE5: an INDEPENDENT U_6(Z/8) implementation, built from honest 6 x 6 matrices.

Nothing here is transcribed from `scripts/w58_sigma5/u6lib.py`: the group law is matrix
multiplication and the inverse is Gaussian back-substitution (not a Neumann series), so the
two libraries agree only if both are right.  `verify_force5.py` section 0 checks them against
each other on random input before any measurement is taken.

Coordinates, in the campaign's class-graded naming (GradedFive.lean):

    index  0  1  2  3  4    5  6  7  8    9 10 11   12 13   14
    name   a  b  c  d  e    f  g  h  i    j  k  l    m  n    o
    entry 12 23 34 45 56   13 24 35 46   14 25 36   15 26   16

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

N = 8

COORDS = "abcdefghijklmno"
POS = [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6),
       (1, 3), (2, 4), (3, 5), (4, 6),
       (1, 4), (2, 5), (3, 6),
       (1, 5), (2, 6),
       (1, 6)]
IDX = {p: k for k, p in enumerate(POS)}
ONE = (0,) * 15


def cls(k):
    (r, c) = POS[k]
    return c - r


def mat(p):
    M = [[0] * 6 for _ in range(6)]
    for r in range(6):
        M[r][r] = 1
    for k, (i, j) in enumerate(POS):
        M[i - 1][j - 1] = p[k] % N
    return M


def tup(M):
    return tuple(M[i - 1][j - 1] % N for (i, j) in POS)


def mmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(6)) % N for j in range(6)] for i in range(6)]


def minv(A):
    """Back-substitution inverse of a unitriangular matrix: X with A X = I, column by column."""
    X = [[0] * 6 for _ in range(6)]
    for j in range(6):
        for i in range(j, -1, -1):
            rhs = (1 if i == j else 0) - sum(A[i][k] * X[k][j] for k in range(i + 1, 6))
            X[i][j] = rhs % N                       # A[i][i] = 1, so no division is needed
    return X


def mul(p, q):
    return tup(mmul(mat(p), mat(q)))


def inv(p):
    return tup(minv(mat(p)))


def power(p, k):
    r = ONE
    for _ in range(k):
        r = mul(r, p)
    return r


def conjP(p, g):
    """x ^ g = g^{-1} x g."""
    return mul(mul(inv(g), p), g)


def commP(p, q):
    """[p, q] = p^{-1} q^{-1} p q."""
    return mul(mul(inv(p), inv(q)), mul(p, q))


def sqWord(s, x, y):
    """(x^s)^{-1} * (x^3)^{-1} * y^2 * [y, y^s]   (GQ2/Dyadic/SqCore/Cores.lean:118)."""
    return mul(mul(mul(inv(conjP(x, s)), inv(power(x, 3))), power(y, 2)),
               commP(y, conjP(y, s)))


def handleWord(us, vs):
    r = ONE
    for u, v in zip(us, vs):
        r = mul(r, commP(u, v))
    return r


def sqRelWord(m):
    """m = (sigma, x0, x1, u_0, v_0, u_1, v_1, ...)."""
    h = (len(m) - 3) // 2
    us = [m[3 + 2 * k] for k in range(h)]
    vs = [m[4 + 2 * k] for k in range(h)]
    return mul(sqWord(m[0], m[1], m[2]), handleWord(us, vs))


def liftC(w):
    return (0,) * 14 + (w % N,)


def named(**kw):
    t = [0] * 15
    for key, val in kw.items():
        t[COORDS.index(key)] = val % N
    return tuple(t)


def show(p):
    parts = ["%s=%d" % (COORDS[k], p[k]) for k in range(15) if p[k]]
    return "<" + ", ".join(parts) + ">" if parts else "<1>"


def toU5L(p):
    """Forget row/column 6: U_5 coordinates (a,b,c,d, f,g,h, j,k, m)."""
    return (p[0], p[1], p[2], p[3], p[5], p[6], p[7], p[9], p[10], p[12])


def toU5R(p):
    """Forget row/column 1: U_5 coordinates (b,c,d,e, g,h,i, k,l, n)."""
    return (p[1], p[2], p[3], p[4], p[6], p[7], p[8], p[10], p[11], p[13])


def is_ga(p, c):
    return all(p[k] == 0 for k in range(15) if cls(k) < c)


def mirTuple(h, j, s, x, y, u, v):
    m = [s, x, y]
    for k in range(h):
        m += [u, v] if k == j else [ONE, ONE]
    return m


# ---- the point of `docs/dyadic/w58-sigma5-note.md` section 3.2 ---------------------------

sigFiveMark = named(b=1)
sepU = named(a=1, c=2, d=3, f=3, g=2, h=2, i=2)
sepV = named(d=1, e=2, f=3, g=2, h=3, i=3)
sepX = named(a=2, e=1)
sepY = named(e=2, f=1, h=3, i=1, j=2, k=2, l=2, m=3, n=2, o=2)
