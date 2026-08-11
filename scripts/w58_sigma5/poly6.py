"""Exact symbolic U_6 arithmetic over Z: the minimal multivariate polynomial ring of
`scripts/w57_cleared/poly.py` (verbatim `P`), plus the class-five group operations.

Monomials are frozen sorted tuples of variable names; a polynomial is a dict
{monomial: coefficient} with zero coefficients pruned.  Plain Python integers throughout, no
external packages.  Enough to run the fifteen-row `sqWord` / `commP` closed forms symbolically
over Z and read off the halves that `exists k, ... = 2 * k` statements need.

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""


class P:
    __slots__ = ("d",)

    def __init__(self, d=None):
        self.d = {} if d is None else {m: c for m, c in d.items() if c}

    @staticmethod
    def var(name):
        return P({(name,): 1})

    @staticmethod
    def const(c):
        return P({(): c}) if c else P()

    def __add__(self, o):
        o = o if isinstance(o, P) else P.const(o)
        r = dict(self.d)
        for m, c in o.d.items():
            r[m] = r.get(m, 0) + c
        return P(r)

    __radd__ = __add__

    def __neg__(self):
        return P({m: -c for m, c in self.d.items()})

    def __sub__(self, o):
        return self + (-(o if isinstance(o, P) else P.const(o)))

    def __rsub__(self, o):
        return (-self) + o

    def __mul__(self, o):
        o = o if isinstance(o, P) else P.const(o)
        r = {}
        for m1, c1 in self.d.items():
            for m2, c2 in o.d.items():
                m = tuple(sorted(m1 + m2))
                r[m] = r.get(m, 0) + c1 * c2
        return P(r)

    __rmul__ = __mul__

    def __eq__(self, o):
        return self.d == (o if isinstance(o, P) else P.const(o)).d

    def __hash__(self):
        return hash(tuple(sorted(self.d.items())))

    def is_zero(self):
        return not self.d

    def subs(self, env):
        """Substitute {name: P or int} into every variable, leaving unlisted ones alone."""
        out = P()
        for m, c in self.d.items():
            term = P.const(c)
            for v in m:
                term = term * (env[v] if v in env else P.var(v))
            out = out + term
        return out

    def half(self):
        """Divide every coefficient by 2; raises if any coefficient is odd."""
        for m, c in self.d.items():
            if c % 2:
                raise ValueError("odd coefficient %d on %s" % (c, m))
        return P({m: c // 2 for m, c in self.d.items()})

    def mod(self, n):
        return P({m: c % n for m, c in self.d.items()})

    def coeff_in(self, name):
        """Split self = name * A + B and return (A, B); requires degree <= 1 in `name`."""
        A, B = {}, {}
        for m, c in self.d.items():
            k = m.count(name)
            if k == 0:
                B[m] = c
            elif k == 1:
                rest = list(m)
                rest.remove(name)
                A[tuple(rest)] = c
            else:
                raise ValueError("degree %d in %s" % (k, name))
        return P(A), P(B)

    def __repr__(self):
        if not self.d:
            return "0"
        parts = []
        for m in sorted(self.d, key=lambda t: (len(t), t)):
            c = self.d[m]
            s = "*".join(m) if m else "1"
            parts.append(("+ " if c > 0 else "- ") + (("%d*" % abs(c)) if abs(c) != 1 or not m
                                                      else "") + (s if m else "%d" % abs(c)))
        out = " ".join(parts)
        return out[2:] if out.startswith("+ ") else out


from u6lib import POS, IDX, COORDS  # noqa: E402

PONE = tuple(P() for _ in range(15))


def sym(tag):
    """A symbolic U_6 element with coordinates tag+'a' ... tag+'o'."""
    return tuple(P.var(tag + c) for c in COORDS)


def pmul(p, q):
    out = []
    for (i, k) in POS:
        s = p[IDX[(i, k)]] + q[IDX[(i, k)]]
        for m in range(i + 1, k):
            s = s + p[IDX[(i, m)]] * q[IDX[(m, k)]]
        out.append(s)
    return tuple(out)


def _pmat(p):
    M = [[P.const(1) if r == c else P() for c in range(6)] for r in range(6)]
    for k, (i, j) in enumerate(POS):
        M[i - 1][j - 1] = p[k]
    return M


def _ptup(M):
    return tuple(M[i - 1][j - 1] for (i, j) in POS)


def _pmatmul(A, B):
    out = []
    for i in range(6):
        row = []
        for j in range(6):
            s = P()
            for k in range(6):
                s = s + A[i][k] * B[k][j]
            row.append(s)
        out.append(row)
    return out


def pinv(p):
    """Neumann series I - N + N^2 - N^3 + N^4 - N^5 on the symbolic matrix."""
    A = _pmat(p)
    Nm = [[A[i][j] - (P.const(1) if i == j else P()) for j in range(6)] for i in range(6)]
    R = [[P.const(1) if i == j else P() for j in range(6)] for i in range(6)]
    Q = [[P.const(1) if i == j else P() for j in range(6)] for i in range(6)]
    sign = 1
    for _ in range(5):
        Q = _pmatmul(Q, Nm)
        sign = -sign
        R = [[R[i][j] + (Q[i][j] if sign > 0 else -Q[i][j]) for j in range(6)] for i in range(6)]
    return _ptup(R)


def ppow(p, k):
    r = PONE
    for _ in range(k):
        r = pmul(r, p)
    return r


def pconj(p, g):
    return pmul(pmul(pinv(g), p), g)


def pcomm(p, q):
    return pmul(pmul(pinv(p), pinv(q)), pmul(p, q))


def psqWord(s, x, y):
    return pmul(pmul(pmul(pinv(pconj(x, s)), pinv(ppow(x, 3))), ppow(y, 2)),
                pcomm(y, pconj(y, s)))


def pconst(t):
    """Lift an integer tuple to a constant symbolic tuple."""
    return tuple(P.const(c) for c in t)
