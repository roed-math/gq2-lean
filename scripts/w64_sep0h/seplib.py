"""W64-SEP0H: exact `U_6` arithmetic in PLAIN Python, numeric and symbolic.

Two layers, both written here so that nothing in this lane depends on `sympy`:

* a numeric layer over `Z` and over `Z/8`, transcribing the same coordinate law as
  `scripts/w59_blind5/u6lib.py` (which certifies it against honest `6 x 6` matrices);
  `check_against_matrices` re-certifies it here with integer `6 x 6` matrix arithmetic
  implemented from scratch, so the transcription is checked a second time, independently;
* a symbolic layer over `Z[vars]`, monomials as sorted tuples, coefficients plain `int`.

Coordinate naming is the campaign's (`GQ2/Dyadic/SqCore/GradedFive.lean`):

    index  0  1  2  3  4   5  6  7  8   9 10 11  12 13  14
    name   a  b  c  d  e   f  g  h  i   j  k  l   m  n   o
    entry 12 23 34 45 56  13 24 35 46  14 25 36  15 26  16
"""

NAMES = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o"]

CELL = {
    "a": (0, 1), "b": (1, 2), "c": (2, 3), "d": (3, 4), "e": (4, 5),
    "f": (0, 2), "g": (1, 3), "h": (2, 4), "i": (3, 5),
    "j": (0, 3), "k": (1, 4), "l": (2, 5),
    "m": (0, 4), "n": (1, 5),
    "o": (0, 5),
}

M = 8

# ------------------------------------------------------------------------------------------
# Symbolic scalars: dict from monomial (sorted tuple of variable names) to int coefficient.


def s_const(c):
    return {(): c} if c else {}


def s_var(v):
    return {(v,): 1}


def s_add(p, q):
    out = dict(p)
    for m, c in q.items():
        n = out.get(m, 0) + c
        if n:
            out[m] = n
        else:
            out.pop(m, None)
    return out


def s_neg(p):
    return {m: -c for m, c in p.items()}


def s_sub(p, q):
    return s_add(p, s_neg(q))


def s_mul(p, q):
    out = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = tuple(sorted(m1 + m2))
            n = out.get(m, 0) + c1 * c2
            if n:
                out[m] = n
            else:
                out.pop(m, None)
    return out


def s_scal(k, p):
    if k == 0:
        return {}
    return {m: k * c for m, c in p.items()}


def s_mod(p, n):
    out = {}
    for m, c in p.items():
        r = c % n
        if r:
            out[m] = r
    return out


def s_subst(p, table):
    """Substitute variables by polynomials; `table` maps a variable name to a polynomial."""
    out = {}
    for m, c in p.items():
        term = s_const(c)
        for v in m:
            term = s_mul(term, table.get(v, s_var(v)))
        out = s_add(out, term)
    return out


def s_str(p):
    if not p:
        return "0"
    parts = []
    for m in sorted(p, key=lambda t: (len(t), t)):
        c = p[m]
        mono = "*".join(m) if m else "1"
        parts.append(f"{c}*{mono}" if c != 1 or not m else mono)
    return " + ".join(parts)


# ------------------------------------------------------------------------------------------
# A tiny scalar interface so the SAME group code runs on ints and on polynomials.


class IntRing:
    zero = 0

    @staticmethod
    def add(p, q):
        return p + q

    @staticmethod
    def sub(p, q):
        return p - q

    @staticmethod
    def mul(p, q):
        return p * q

    @staticmethod
    def neg(p):
        return -p

    @staticmethod
    def scal(k, p):
        return k * p


class PolyRing:
    zero = {}
    add = staticmethod(s_add)
    sub = staticmethod(s_sub)
    mul = staticmethod(s_mul)
    neg = staticmethod(s_neg)
    scal = staticmethod(s_scal)


# ------------------------------------------------------------------------------------------
# The group, generic over the scalar ring.


class U6:
    __slots__ = ("co", "R")

    def __init__(self, coeffs=None, R=IntRing):
        self.R = R
        self.co = {k: R.zero for k in NAMES}
        if coeffs:
            for k, v in coeffs.items():
                self.co[k] = v

    def __getattr__(self, k):
        if k in CELL:
            return self.co[k]
        raise AttributeError(k)

    def __repr__(self):
        nz = [f"{k}={self.co[k]}" for k in NAMES if self.co[k] != self.R.zero]
        return "U6(" + ", ".join(nz) + ")"


def one(R=IntRing):
    return U6(None, R)


def mul(p, q):
    R = p.R
    A, S, N = R.add, R.mul, R.zero
    return U6({
        "a": A(p.a, q.a),
        "b": A(p.b, q.b),
        "c": A(p.c, q.c),
        "d": A(p.d, q.d),
        "e": A(p.e, q.e),
        "f": A(A(p.f, q.f), S(p.a, q.b)),
        "g": A(A(p.g, q.g), S(p.b, q.c)),
        "h": A(A(p.h, q.h), S(p.c, q.d)),
        "i": A(A(p.i, q.i), S(p.d, q.e)),
        "j": A(A(A(p.j, q.j), S(p.a, q.g)), S(p.f, q.c)),
        "k": A(A(A(p.k, q.k), S(p.b, q.h)), S(p.g, q.d)),
        "l": A(A(A(p.l, q.l), S(p.c, q.i)), S(p.h, q.e)),
        "m": A(A(A(A(p.m, q.m), S(p.a, q.k)), S(p.f, q.h)), S(p.j, q.d)),
        "n": A(A(A(A(p.n, q.n), S(p.b, q.l)), S(p.g, q.i)), S(p.k, q.e)),
        "o": A(A(A(A(A(p.o, q.o), S(p.a, q.n)), S(p.f, q.l)), S(p.j, q.i)), S(p.m, q.e)),
    }, R)


def inv(p):
    R = p.R
    A, S, G, K = R.add, R.mul, R.neg, R.scal

    def prod(*fs):
        out = fs[0]
        for f in fs[1:]:
            out = S(out, f)
        return out

    def summ(*fs):
        out = fs[0]
        for f in fs[1:]:
            out = A(out, f)
        return out

    return U6({
        "a": G(p.a), "b": G(p.b), "c": G(p.c), "d": G(p.d), "e": G(p.e),
        "f": R.sub(prod(p.a, p.b), p.f),
        "g": R.sub(prod(p.b, p.c), p.g),
        "h": R.sub(prod(p.c, p.d), p.h),
        "i": R.sub(prod(p.d, p.e), p.i),
        "j": summ(G(prod(p.a, p.b, p.c)), prod(p.a, p.g), prod(p.c, p.f), G(p.j)),
        "k": summ(G(prod(p.b, p.c, p.d)), prod(p.b, p.h), prod(p.d, p.g), G(p.k)),
        "l": summ(G(prod(p.c, p.d, p.e)), prod(p.c, p.i), prod(p.e, p.h), G(p.l)),
        "m": summ(prod(p.a, p.b, p.c, p.d), G(prod(p.a, p.b, p.h)), G(prod(p.a, p.d, p.g)),
                  prod(p.a, p.k), G(prod(p.c, p.d, p.f)), prod(p.d, p.j), prod(p.f, p.h),
                  G(p.m)),
        "n": summ(prod(p.b, p.c, p.d, p.e), G(prod(p.b, p.c, p.i)), G(prod(p.b, p.e, p.h)),
                  prod(p.b, p.l), G(prod(p.d, p.e, p.g)), prod(p.e, p.k), prod(p.g, p.i),
                  G(p.n)),
        "o": summ(G(prod(p.a, p.b, p.c, p.d, p.e)), prod(p.a, p.b, p.c, p.i),
                  prod(p.a, p.b, p.e, p.h), G(prod(p.a, p.b, p.l)), prod(p.a, p.d, p.e, p.g),
                  G(prod(p.a, p.e, p.k)), G(prod(p.a, p.g, p.i)), prod(p.a, p.n),
                  prod(p.c, p.d, p.e, p.f), G(prod(p.c, p.f, p.i)), G(prod(p.d, p.e, p.j)),
                  G(prod(p.e, p.f, p.h)), prod(p.e, p.m), prod(p.f, p.l), prod(p.i, p.j),
                  G(p.o)),
    }, R)


def pw(p, n):
    r = one(p.R)
    for _ in range(n):
        r = mul(r, p)
    return r


def conjP(x, g):
    return mul(mul(inv(g), x), g)


def commP(x, y):
    return mul(mul(mul(inv(x), inv(y)), x), y)


def sqWord(s, x, y):
    """`sqWord s x y = (conjP x s)⁻¹ * (x ^ 3)⁻¹ * y ^ 2 * commP y (conjP y s)`."""
    return mul(mul(mul(inv(conjP(x, s)), inv(pw(x, 3))), pw(y, 2)), commP(y, conjP(y, s)))


def red(p, n=M):
    return U6({k: p.co[k] % n for k in NAMES}, IntRing)


def rmul(p, q):
    return red(mul(p, q))


def rsqWord(s, x, y):
    return red(sqWord(s, x, y))


def is_one(p):
    return all(p.co[k] % M == 0 for k in NAMES)


def is_central(p):
    return all(p.co[k] % M == 0 for k in NAMES if k != "o")


def par(z):
    return z % 2


def symU6(prefix):
    return U6({k: s_var(prefix + k) for k in NAMES}, PolyRing)


# ------------------------------------------------------------------------------------------
# Independent certification: honest integer 6 x 6 matrices, written from scratch.


def mat_of(p):
    m = [[1 if r == c else 0 for c in range(6)] for r in range(6)]
    for k, (r, c) in CELL.items():
        m[r][c] = p.co[k]
    return m


def mat_mul(a, b):
    return [[sum(a[r][t] * b[t][c] for t in range(6)) for c in range(6)] for r in range(6)]


def mat_inv(a):
    """Inverse of a unitriangular integer matrix, by back substitution (exact over Z)."""
    n = 6
    out = [[1 if r == c else 0 for c in range(n)] for r in range(n)]
    for d in range(1, n):
        for r in range(n - d):
            c = r + d
            out[r][c] = -sum(a[r][t] * out[t][c] for t in range(r + 1, c + 1))
    return out


def u6_of_mat(m):
    return U6({k: m[r][c] for k, (r, c) in CELL.items()}, IntRing)


def check_against_matrices(rng, trials=400):
    """Compare the transcribed coordinate law against honest integer `6 x 6` arithmetic."""
    ok = bad = 0
    for _ in range(trials):
        p = U6({k: rng.randrange(-6, 7) for k in NAMES})
        q = U6({k: rng.randrange(-6, 7) for k in NAMES})
        pm, qm = mat_of(p), mat_of(q)
        cases = [
            (u6_of_mat(mat_mul(pm, qm)), mul(p, q)),
            (u6_of_mat(mat_inv(pm)), inv(p)),
            (u6_of_mat(mat_mul(mat_mul(pm, pm), pm)), pw(p, 3)),
            (u6_of_mat(mat_mul(mat_mul(mat_inv(qm), pm), qm)), conjP(p, q)),
            (u6_of_mat(mat_mul(mat_mul(mat_mul(mat_inv(pm), mat_inv(qm)), pm), qm)),
             commP(p, q)),
        ]
        sm, xm, ym = mat_of(p), mat_of(q), mat_of(U6({k: rng.randrange(-4, 5) for k in NAMES}))
        yy = u6_of_mat(ym)
        cxs = mat_mul(mat_mul(mat_inv(sm), xm), sm)
        cys = mat_mul(mat_mul(mat_inv(sm), ym), sm)
        w = mat_mul(mat_mul(mat_mul(mat_inv(cxs), mat_inv(mat_mul(mat_mul(xm, xm), xm))),
                            mat_mul(ym, ym)),
                    mat_mul(mat_mul(mat_mul(mat_inv(ym), mat_inv(cys)), ym), cys))
        cases.append((u6_of_mat(w), sqWord(p, q, yy)))
        for lhs, rhs in cases:
            if all(lhs.co[k] == rhs.co[k] for k in NAMES):
                ok += 1
            else:
                bad += 1
    return ok, bad


def rand(rng, keys=NAMES):
    return U6({k: rng.randrange(M) for k in keys})


LAYERS = [["a", "b", "c", "d", "e"], ["f", "g", "h", "i"], ["j", "k", "l"], ["m", "n"], ["o"]]


def solve_x1(s, x, target, rng, branch=None):
    """The layered solve of `scripts/w61_block/blocklib.py`, retranscribed with no parity input."""
    y = U6()
    picks = iter(branch) if branch is not None else None
    for layer in LAYERS:
        for row in layer:
            w = rsqWord(s, x, y)
            resid = (target.co[row] - w.co[row]) % M
            if resid % 2 != 0:
                return None, row
            half = (resid // 2) % 4
            bit = next(picks) if picks is not None else rng.randrange(2)
            y.co[row] = (y.co[row] + half + 4 * bit) % M
    if any((rsqWord(s, x, y).co[k] - target.co[k]) % M for k in NAMES):
        return None, "VERIFY"
    return y, None
