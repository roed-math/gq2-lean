"""Exact SqU5 = U_5(Z/8) arithmetic, transcribed from GQ2/Dyadic/SqCore/GradedFour.lean.

Coordinates (a, b, c, d, e, f, g, h, i, j) = (x12, x23, x34, x45, x13, x24, x35, x14, x25, x15).
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

ONE = (0,) * 10


def red(p, n=N):
    return tuple(x % n for x in p)


def mul(p, q, n=N):
    (pa, pb, pc, pd, pe, pf, pg, ph, pi, pj) = p
    (qa, qb, qc, qd, qe, qf, qg, qh, qi, qj) = q
    return red((
        pa + qa,
        pb + qb,
        pc + qc,
        pd + qd,
        pe + qe + pa * qb,
        pf + qf + pb * qc,
        pg + qg + pc * qd,
        ph + qh + pa * qf + pe * qc,
        pi + qi + pb * qg + pf * qd,
        pj + qj + pa * qi + pe * qg + ph * qd,
    ), n)


def inv(p, n=N):
    (pa, pb, pc, pd, pe, pf, pg, ph, pi, pj) = p
    return red((
        -pa, -pb, -pc, -pd,
        pa * pb - pe,
        pb * pc - pf,
        pc * pd - pg,
        -(pa * pb * pc) + pa * pf + pc * pe - ph,
        -(pb * pc * pd) + pb * pg + pd * pf - pi,
        pa * pb * pc * pd - pa * pb * pg - pa * pd * pf + pa * pi
        - pc * pd * pe + pd * ph + pe * pg - pj,
    ), n)


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
    """(x^s)^{-1} * (x^3)^{-1} * y^2 * [y, y^s]."""
    return mul(mul(mul(inv(conjP(x, s, n), n), inv(power(x, 3, n), n), n),
                   power(y, 2, n), n),
               commP(y, conjP(y, s, n), n), n)


def handleWord(us, vs, n=N):
    r = ONE
    for u, v in zip(us, vs):
        r = mul(r, commP(u, v, n), n)
    return r


def sqRelWord(m, n=N):
    """m is the tuple (slot0=sigma, slot1=x0, slot2=x1, then handle pairs u_0, v_0, ...)."""
    h = (len(m) - 3) // 2
    us = [m[3 + 2 * k] for k in range(h)]
    vs = [m[4 + 2 * k] for k in range(h)]
    return mul(sqWord(m[0], m[1], m[2], n), handleWord(us, vs, n), n)


def liftC(w, n=N):
    return red((0, 0, 0, 0, 0, 0, 0, 0, 0, w), n)


def is_ga_two(p):
    return p[0] == 0 and p[1] == 0 and p[2] == 0 and p[3] == 0


def is_ga_three(p):
    return is_ga_two(p) and p[4] == 0 and p[5] == 0 and p[6] == 0


def is_ga_four(p):
    return is_ga_three(p) and p[7] == 0 and p[8] == 0


def selPar(x):
    return x % 2


# ---- committed objects, transcribed from GradedSigmaFour.lean -------------------

sigFourMark = (0, 1, 0, 0, 0, 0, 0, 0, 0, 0)
sigFourU = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
sigFourV = (2, 0, 0, 0, 0, 0, 0, 0, 0, 0)
sigFourX = (2, 0, 0, 0, 0, 0, 0, 0, 1, 0)
sigFourY = (0, 0, 0, 0, 1, 0, 4, 0, 2, 0)


def sigFourWit(v, n=N):
    return [mul(sigFourMark, v, n), sigFourX, sigFourY, sigFourU, sigFourV]


def sigFourRead(v, x, y, n=N):
    return (
        v[0] * (4 * (x[2] * x[3]) - 2 * (x[2] * y[3]) - 4 * (x[3] * x[5])
                + 2 * (x[5] * y[3]) - x[6] + x[8] - y[2] * y[3] + y[3] * y[5])
        + v[2] * (3 * (x[0] * x[3]) - 2 * (x[0] * y[3]) + 3 * (x[3] * x[4])
                  - 2 * (x[4] * y[3]) - y[0] * y[3] - 2 * (y[3] * y[4]))
        + v[3] * (x[0] * x[5] + x[2] * x[4] - x[7] - y[0] * y[2] + y[0] * y[5] + y[2] * y[4])
        + v[4] * (-4 * (x[2] * x[3]) + 2 * (x[2] * y[3]) + x[6] + y[2] * y[3])
        + v[5] * (3 * (x[0] * x[3]) - 2 * (x[0] * y[3]) - 2 * (y[0] * y[3]))
        + v[6] * (-x[0] - x[4])
        + v[7] * x[3] - v[8] * x[0]
        + (v[0] * v[3] * (x[5] - x[2]) - v[0] * v[5] * x[3]
           - v[2] * v[4] * x[3] + v[3] * v[4] * x[2])
    ) % n


def sigFourG(v, x, n=N):
    return (v[2] * x[3] - v[3] * x[2]) % n


def sigFourH(v, x, n=N):
    return (v[0] * (x[5] - x[2]) - v[2] * (x[0] + x[4]) + v[4] * x[2] - v[5] * x[0]) % n


def sigFourI(v, x, n=N):
    return (v[3] * (x[2] - x[5]) + v[5] * x[3]) % n


def sigLift(m, z0, w1, w2, z3, z4, n=N):
    """Five-slot class-four refinement at handle j = 0, h = 1."""
    return [mul(m[0], z0, n), mul(m[1], w1, n), mul(m[2], w2, n),
            mul(m[3], z3, n), mul(m[4], z4, n)]
