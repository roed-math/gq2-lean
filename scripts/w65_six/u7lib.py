"""W65-SIX: honest unitriangular `n x n` arithmetic in PLAIN Python, generic in `n`.

The class-`N` test group of the campaign is `U_{N+1}`: `SqHeis = U_3` (class two),
`SqU4` (class three), `SqU5` (class four), `SqU6` (class five, top entry `(1,6)`).
So the **class-six** test group is `U_7`, whose top entry is `(1,7)`, and the tree
has no such group.  This module supplies it off-Lean.

Design decision, deliberately different from `scripts/w64_sep0h/seplib.py`: nothing here
transcribes a coordinate law.  Elements are honest `n x n` unitriangular matrices and the
product is matrix multiplication; the inverse is back substitution, which is exact over any
commutative ring because the diagonal is `1`.  So there is no transcription to certify, and
`check_against_seplib` in `derive_six.py` uses the `n = 6` instance to certify the OTHER
direction: that the campaign's committed `SqU6` coordinate law agrees with this one.

Four scalar rings, all exact:

* `IntRing`   - the integers;
* `ModRing(m)`- `Z/m`, used with `m = 8 = gr3R`;
* `PolyRing`  - `Z[vars]`, monomials as sorted tuples, coefficients plain `int`;
* `F2Ring`    - `F_2[vars]`, a polynomial is a `frozenset` of monomials (XOR arithmetic).

No `sympy`, no floating point.
"""

import itertools

# ------------------------------------------------------------------------------------------
# Scalar rings.


class IntRing:
    zero = 0
    one = 1

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
    def is_zero(p):
        return p == 0


class ModRing:
    """`Z/m` for a fixed modulus."""

    def __init__(self, m):
        self.m = m
        self.zero = 0
        self.one = 1 % m

    def add(self, p, q):
        return (p + q) % self.m

    def sub(self, p, q):
        return (p - q) % self.m

    def mul(self, p, q):
        return (p * q) % self.m

    def neg(self, p):
        return (-p) % self.m

    def is_zero(self, p):
        return p % self.m == 0


def p_add(p, q):
    out = dict(p)
    for m, c in q.items():
        n = out.get(m, 0) + c
        if n:
            out[m] = n
        else:
            out.pop(m, None)
    return out


def p_neg(p):
    return {m: -c for m, c in p.items()}


def p_sub(p, q):
    return p_add(p, p_neg(q))


def p_mul(p, q):
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


def p_var(v):
    return {(v,): 1}


def p_const(c):
    return {(): c} if c else {}


def p_mod(p, n):
    return {m: c % n for m, c in p.items() if c % n}


def p_str(p):
    if not p:
        return "0"
    parts = []
    for m in sorted(p, key=lambda t: (len(t), t)):
        c = p[m]
        mono = "*".join(m) if m else "1"
        parts.append(f"{c}*{mono}" if c != 1 or not m else mono)
    return " + ".join(parts)


class PolyRing:
    zero = {}
    one = {(): 1}
    add = staticmethod(p_add)
    sub = staticmethod(p_sub)
    mul = staticmethod(p_mul)
    neg = staticmethod(p_neg)

    @staticmethod
    def is_zero(p):
        return not p


def f2_var(v):
    return frozenset([(v,)])


F2_ONE = frozenset([()])
F2_ZERO = frozenset()


class F2Ring:
    """`F_2`-valued polynomial FUNCTIONS on `F_2^k`, i.e. multilinear representatives.

    ⚠ `mul` reduces `v * v` to `v`.  That is the ring of functions `F_2^k -> F_2`, NOT the
    polynomial ring, and it is used here for exactly one purpose: deciding whether a matrix
    entry vanishes at EVERY `F_2` point.  Multilinear representatives are unique, so
    `is_zero` on this ring is a decision procedure for that question - which is the question,
    since a word in `s, x, y` reduces modulo `2` to the same word in the reductions.
    Statements meant to hold over an arbitrary commutative ring are computed in `PolyRing`.
    """
    zero = F2_ZERO
    one = F2_ONE

    @staticmethod
    def add(p, q):
        return p ^ q

    sub = add

    @staticmethod
    def mul(p, q):
        if not p or not q:
            return F2_ZERO
        out = set()
        for m1 in p:
            for m2 in q:
                m = tuple(sorted(set(m1) | set(m2)))
                if m in out:
                    out.discard(m)
                else:
                    out.add(m)
        return frozenset(out)

    @staticmethod
    def neg(p):
        return p

    @staticmethod
    def is_zero(p):
        return not p


def f2_str(p):
    if not p:
        return "0"
    return " + ".join("*".join(m) if m else "1"
                      for m in sorted(p, key=lambda t: (len(t), t)))


# ------------------------------------------------------------------------------------------
# The unitriangular group `U_n(R)`, as honest matrices.


def eye(n, R):
    return [[R.one if r == c else R.zero for c in range(n)] for r in range(n)]


def mmul(a, b, R):
    n = len(a)
    out = [[R.zero] * n for _ in range(n)]
    for r in range(n):
        ar = a[r]
        for c in range(r, n):
            acc = R.zero
            for t in range(r, c + 1):
                if R.is_zero(ar[t]) or R.is_zero(b[t][c]):
                    continue
                acc = R.add(acc, R.mul(ar[t], b[t][c]))
            out[r][c] = acc
    return out


def minv(a, R):
    """Inverse of a unitriangular matrix, by back substitution; exact over any commutative ring."""
    n = len(a)
    out = eye(n, R)
    for d in range(1, n):
        for r in range(n - d):
            c = r + d
            acc = R.zero
            for t in range(r + 1, c + 1):
                if R.is_zero(a[r][t]) or R.is_zero(out[t][c]):
                    continue
                acc = R.add(acc, R.mul(a[r][t], out[t][c]))
            out[r][c] = R.neg(acc)
    return out


def mpw(a, k, R):
    out = eye(len(a), R)
    for _ in range(k):
        out = mmul(out, a, R)
    return out


def conjP(x, g, R):
    """`conjP x g = g⁻¹ * x * g`, the campaign's `GQ2/Words.lean` convention."""
    return mmul(mmul(minv(g, R), x, R), g, R)


def commP(x, y, R):
    """`commP x y = x⁻¹ * y⁻¹ * x * y`."""
    return mmul(mmul(mmul(minv(x, R), minv(y, R), R), x, R), y, R)


def sqWord(s, x, y, R):
    """`sqWord s x y = (conjP x s)⁻¹ * (x ^ 3)⁻¹ * y ^ 2 * commP y (conjP y s)`.

    Transcribed from `GQ2/Dyadic/SqCore/Cores.lean` line 118.
    """
    return mmul(mmul(mmul(minv(conjP(x, s, R), R), minv(mpw(x, 3, R), R), R),
                     mpw(y, 2, R), R),
                commP(y, conjP(y, s, R), R), R)


def is_one(a, R):
    n = len(a)
    return all(R.is_zero(a[r][c]) for r in range(n) for c in range(r + 1, n))


def msub_entries(a, b, R):
    n = len(a)
    return [[R.sub(a[r][c], b[r][c]) for c in range(n)] for r in range(n)]


def cells(n):
    """`(r, c)` with `r < c`, in class order: class `1` first, then `2`, ..."""
    return [(r, r + d) for d in range(1, n) for r in range(n - d)]


def label(r, c):
    return f"({r + 1},{c + 1})"


def sym_mat(n, prefix, R=PolyRing, skip=()):
    """A symbolic element of `U_n`, with entry `(r, c)` named `<prefix>_<r+1><c+1>`.

    Cells listed in `skip` are set to zero (used for "the abelian columns of `y` vanish
    modulo 2").
    """
    var = p_var if R is PolyRing else f2_var
    a = eye(n, R)
    for (r, c) in cells(n):
        a[r][c] = R.zero if (r, c) in skip else var(f"{prefix}{r + 1}{c + 1}")
    return a


def sym_mat_halved(n, prefix, halves, R=PolyRing):
    """Symbolic element with the cells in `halves` replaced by `2 * <prefix>H_<rc>`."""
    a = eye(n, R)
    for (r, c) in cells(n):
        if (r, c) in halves:
            a[r][c] = p_mul(p_const(2), p_var(f"{prefix}H{r + 1}{c + 1}"))
        else:
            a[r][c] = p_var(f"{prefix}{r + 1}{c + 1}")
    return a


def abelian_cells(n):
    return [(r, r + 1) for r in range(n - 1)]


def rand_mat(n, rng, m=8, skip=()):
    a = eye(n, ModRing(m))
    for (r, c) in cells(n):
        a[r][c] = 0 if (r, c) in skip else rng.randrange(m)
    return a


def layers(n):
    return [[(r, r + d) for r in range(n - d)] for d in range(1, n)]


def solve_x1(s, x, n, rng, m=8, branch=None):
    """Solve `sqWord s x y = 1` for `y`, layer by layer, over `Z/m`.

    The same layered solve as `seplib.solve_x1`, retranscribed for general `n`: bumping the
    class-`c` entry of `y` by `t` moves the class-`c` entry of `sqWord s x y` by exactly `2 t`
    and moves no earlier entry, so each layer is a parity test followed by a free choice of
    the top bit.  Returns `(y, None)` or `(None, blocking_cell)`.
    """
    R = ModRing(m)
    y = eye(n, R)
    picks = iter(branch) if branch is not None else None
    for layer in layers(n):
        for (r, c) in layer:
            w = sqWord(s, x, y, R)
            resid = (-w[r][c]) % m
            if resid % 2 != 0:
                return None, (r, c)
            half = (resid // 2) % (m // 2)
            bit = next(picks) if picks is not None else rng.randrange(2)
            y[r][c] = (y[r][c] + half + (m // 2) * bit) % m
    if not is_one(sqWord(s, x, y, R), R):
        return None, "VERIFY"
    return y, None
