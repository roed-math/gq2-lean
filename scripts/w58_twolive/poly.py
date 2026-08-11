"""A minimal exact multivariate polynomial ring over the integers.

Monomials are frozen sorted tuples of variable names (with repetition); a polynomial is a
dict {monomial: coefficient} with zero coefficients pruned.  Plain Python integers throughout,
no external packages.  Enough to run the ten-row `sqWord` / `commP` closed forms symbolically
and read off the halves the Lean `∃ k, … = 2 * k` statements need.

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


COORDS = "abcdefghij"


def sym(tag):
    """A symbolic SqU5 element with coordinates tag+'a' ... tag+'j'."""
    return tuple(P.var(tag + c) for c in COORDS)


def pmul(p, q):
    (pa, pb, pc, pd, pe, pf, pg, ph, pi, pj) = p
    (qa, qb, qc, qd, qe, qf, qg, qh, qi, qj) = q
    return (pa + qa, pb + qb, pc + qc, pd + qd,
            pe + qe + pa * qb, pf + qf + pb * qc, pg + qg + pc * qd,
            ph + qh + pa * qf + pe * qc, pi + qi + pb * qg + pf * qd,
            pj + qj + pa * qi + pe * qg + ph * qd)


def pinv(p):
    (pa, pb, pc, pd, pe, pf, pg, ph, pi, pj) = p
    return (-pa, -pb, -pc, -pd,
            pa * pb - pe, pb * pc - pf, pc * pd - pg,
            -(pa * pb * pc) + pa * pf + pc * pe - ph,
            -(pb * pc * pd) + pb * pg + pd * pf - pi,
            pa * pb * pc * pd - pa * pb * pg - pa * pd * pf + pa * pi
            - pc * pd * pe + pd * ph + pe * pg - pj)


PONE = tuple(P() for _ in range(10))


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
