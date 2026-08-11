"""Exact SqU6 = U_6(Z/n) arithmetic: the class-FIVE carrier, one level above
`GQ2/Dyadic/SqCore/GradedFour.lean`'s `SqU5 = U_5(R)`.

U_6(R) is the unitriangular 6 x 6 group over a commutative ring, carried on the fifteen
strictly-upper entries.  The naming continues `GradedFour`'s class-graded convention
(abelian columns first, then class two, then class three, then class four, then class five):

    index  0  1  2  3  4    5  6  7  8    9 10 11   12 13   14
    name   a  b  c  d  e    f  g  h  i    j  k  l    m  n    o
    entry 12 23 34 45 56   13 24 35 46   14 25 36   15 26   16

    [1 a f j m o]
    [0 1 b g k n]
    [0 0 1 c h l]
    [0 0 0 1 d i]
    [0 0 0 0 1 e]
    [0 0 0 0 0 1]

with (x*y)_{ik} = x_{ik} + y_{ik} + sum_{i<m<k} x_{im} * y_{mk}.

The group law is NOT transcribed by hand: `mul` is generated from the matrix formula over the
index table, and `inv` is the Neumann series I - N + N^2 - N^3 + N^4 - N^5 on the honest 6 x 6
matrix.  `matmul` / `matinv` give a second, fully independent implementation used to certify the
coordinate one (`sweep_sigma5.py` section 1).

Class filtration: gamma_2 = {a..e = 0}, gamma_3 = gamma_2 and {f..i = 0},
gamma_4 = gamma_3 and {j,k,l = 0}, gamma_5 = the centre = {only o}.

All arithmetic is plain Python integers reduced mod N (default 8); no external packages.

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

# ---- the index table -------------------------------------------------------------------

COORDS = "abcdefghijklmno"

# (row, col) with 1-based matrix indices, in the class-graded order above
POS = [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6),
       (1, 3), (2, 4), (3, 5), (4, 6),
       (1, 4), (2, 5), (3, 6),
       (1, 5), (2, 6),
       (1, 6)]

IDX = {p: k for k, p in enumerate(POS)}
NAME = {p: COORDS[k] for k, p in enumerate(POS)}

ONE = (0,) * 15


def cls(k):
    """The lower-central class of coordinate index k: col - row."""
    (r, c) = POS[k]
    return c - r


def red(p, n=N):
    return tuple(x % n for x in p)


def mul(p, q, n=N):
    """(p*q)_{ik} = p_{ik} + q_{ik} + sum_{i<m<k} p_{im} q_{mk}."""
    out = []
    for (i, k) in POS:
        s = p[IDX[(i, k)]] + q[IDX[(i, k)]]
        for m in range(i + 1, k):
            s += p[IDX[(i, m)]] * q[IDX[(m, k)]]
        out.append(s)
    return red(tuple(out), n)


def _mat(p):
    """The honest 6 x 6 unitriangular matrix of the coordinate tuple."""
    M = [[0] * 6 for _ in range(6)]
    for r in range(6):
        M[r][r] = 1
    for k, (i, j) in enumerate(POS):
        M[i - 1][j - 1] = p[k]
    return M


def _tup(M, n=N):
    return red(tuple(M[i - 1][j - 1] for (i, j) in POS), n)


def matmul(A, B, n=N):
    return [[sum(A[i][k] * B[k][j] for k in range(6)) % n for j in range(6)] for i in range(6)]


def matinv(A, n=N):
    """Inverse of a unitriangular matrix: I - N + N^2 - N^3 + N^4 - N^5, N = A - I."""
    Nm = [[(A[i][j] - (1 if i == j else 0)) % n for j in range(6)] for i in range(6)]
    R = [[1 if i == j else 0 for j in range(6)] for i in range(6)]
    P = [[1 if i == j else 0 for j in range(6)] for i in range(6)]
    sign = 1
    for _ in range(5):
        P = matmul(P, Nm, n)
        sign = -sign
        R = [[(R[i][j] + sign * P[i][j]) % n for j in range(6)] for i in range(6)]
    return R


def inv(p, n=N):
    return _tup(matinv(_mat(p), n), n)


def power(p, k, n=N):
    r = ONE
    for _ in range(k):
        r = mul(r, p, n)
    return r


def conjP(p, g, n=N):
    """x ^ g = g^{-1} x g, the repo convention."""
    return mul(mul(inv(g, n), p, n), g, n)


def commP(p, q, n=N):
    """[p, q] = p^{-1} q^{-1} p q, the repo convention."""
    return mul(mul(inv(p, n), inv(q, n), n), mul(p, q, n), n)


def sqWord(s, x, y, n=N):
    """(x^s)^{-1} * (x^3)^{-1} * y^2 * [y, y^s]  (GQ2/Dyadic/SqCore/Cores.lean:118)."""
    return mul(mul(mul(inv(conjP(x, s, n), n), inv(power(x, 3, n), n), n),
                   power(y, 2, n), n),
               commP(y, conjP(y, s, n), n), n)


def handleWord(us, vs, n=N):
    r = ONE
    for u, v in zip(us, vs):
        r = mul(r, commP(u, v, n), n)
    return r


def sqRelWord(m, n=N):
    """m = (slot0 = sigma, slot1 = x0, slot2 = x1, then the handle pairs u_0, v_0, ...)."""
    h = (len(m) - 3) // 2
    us = [m[3 + 2 * k] for k in range(h)]
    vs = [m[4 + 2 * k] for k in range(h)]
    return mul(sqWord(m[0], m[1], m[2], n), handleWord(us, vs, n), n)


def liftC(w, n=N):
    """The central class-five element with top coordinate w."""
    return red((0,) * 14 + (w,), n)


def is_ga(p, c):
    """p lies in gamma_c, i.e. every coordinate of class < c vanishes."""
    return all(p[k] == 0 for k in range(15) if cls(k) < c)


def is_ga_two(p):
    return is_ga(p, 2)


def is_ga_three(p):
    return is_ga(p, 3)


def is_ga_four(p):
    return is_ga(p, 4)


def is_ga_five(p):
    return is_ga(p, 5)


def selPar(x):
    return x % 2


# ---- the two U_5 quotients ---------------------------------------------------------------
#
# U_5 coordinates (GradedFour.lean): (a,b,c,d, e,f,g, h,i, j)
#                                  = (12,23,34,45, 13,24,35, 14,25, 15).

def toU5L(p):
    """Forget the sixth row and column: the U_5 on matrix indices 1..5."""
    return (p[0], p[1], p[2], p[3], p[5], p[6], p[7], p[9], p[10], p[12])


def toU5R(p):
    """Forget the first row and column: the U_5 on matrix indices 2..6."""
    return (p[1], p[2], p[3], p[4], p[6], p[7], p[8], p[10], p[11], p[13])


# ---- the class-five sigma objects ---------------------------------------------------------
#
# The class-four sigma marking is E_23 (`GradedSigmaFour.sigFourMark = <0,1,0,...>`); the
# class-five marking is the same elementary matrix in U_6, which is the unique lift with
# toU5L(sigFiveMark) = sigFourMark.  nu'-triviality of a dressing is again `v.b = 0`.

sigFiveMark = (0, 1) + (0,) * 13


def elem(name, val=1):
    """The elementary tuple with the named coordinate equal to `val`."""
    t = [0] * 15
    t[COORDS.index(name)] = val
    return tuple(t)


def named(**kw):
    """Build a tuple from named coordinates, e.g. named(a=2, k=1)."""
    t = [0] * 15
    for key, val in kw.items():
        t[COORDS.index(key)] = val
    return tuple(t)


def show(p):
    """A readable rendering: only the nonzero coordinates."""
    parts = ["%s=%d" % (COORDS[k], p[k]) for k in range(15) if p[k]]
    return "<" + ", ".join(parts) + ">" if parts else "<1>"


def sigFiveDress(m, v, n=N):
    """Dress slot 0 (the sigma slot) by v, leaving every other slot alone."""
    m = list(m)
    m[0] = mul(m[0], v, n)
    return m


def mirTuple(h, j, s, x, y, u, v, n=N):
    """Core slots (s, x, y), the j-th handle pair (u, v), every other handle letter trivial."""
    m = [s, x, y]
    for k in range(h):
        m += [u, v] if k == j else [ONE, ONE]
    return m
