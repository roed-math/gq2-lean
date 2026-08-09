#!/usr/bin/env python3
"""W53-SIGMA shared library: U5(Z/8) arithmetic and the relator word.

Coordinate order 0..9 = a b c d e f g h i j, matching GQ2/Dyadic/SqCore/GradedFour.lean:
  a=(1,2) b=(2,3) c=(3,4) d=(4,5)  e=(1,3) f=(2,4) g=(3,5)  h=(1,4) i=(2,5)  j=(1,5).
Repo conventions: conjP x g = g^-1 x g, commP x y = x^-1 y^-1 x y,
  sqWord s x y = (conjP x s)^-1 * (x^3)^-1 * y^2 * commP y (conjP y s),
  sqRelWord m   = sqWord (m 0) (m 1) (m 2) * prod_j commP (m U_j) (m V_j).
Slot layout of a rank-(3+2h) marking: 0 = sigma, 1 = x0, 2 = x1, 3+2j = U_j, 4+2j = V_j.
"""

M = 8
ONE = (0,) * 10
NAMES = "abcdefghij"


def mul(x, y):
    a = (x[0] + y[0]) % M
    b = (x[1] + y[1]) % M
    c = (x[2] + y[2]) % M
    d = (x[3] + y[3]) % M
    e = (x[4] + y[4] + x[0] * y[1]) % M
    f = (x[5] + y[5] + x[1] * y[2]) % M
    g = (x[6] + y[6] + x[2] * y[3]) % M
    h = (x[7] + y[7] + x[0] * y[5] + x[4] * y[2]) % M
    i = (x[8] + y[8] + x[1] * y[6] + x[5] * y[3]) % M
    j = (x[9] + y[9] + x[0] * y[8] + x[4] * y[6] + x[7] * y[3]) % M
    return (a, b, c, d, e, f, g, h, i, j)


def inv(p):
    a, b, c, d, e, f, g, h, i, j = p
    return (
        (-a) % M, (-b) % M, (-c) % M, (-d) % M,
        (a * b - e) % M, (b * c - f) % M, (c * d - g) % M,
        (-(a * b * c) + a * f + c * e - h) % M,
        (-(b * c * d) + b * g + d * f - i) % M,
        (a * b * c * d - a * b * g - a * d * f + a * i - c * d * e + d * h + e * g - j) % M,
    )


def conjP(p, g):
    return mul(mul(inv(g), p), g)


def commP(p, q):
    return mul(mul(mul(inv(p), inv(q)), p), q)


def power(p, n):
    r = ONE
    for _ in range(n):
        r = mul(r, p)
    return r


def sqWord(s, x, y):
    return mul(mul(mul(inv(conjP(x, s)), inv(power(x, 3))), power(y, 2)),
               commP(y, conjP(y, s)))


def handleWord(us, vs):
    r = ONE
    for u, v in zip(us, vs):
        r = mul(r, commP(u, v))
    return r


def sqRelWord(m, h):
    us = [m[3 + 2 * k] for k in range(h)]
    vs = [m[4 + 2 * k] for k in range(h)]
    return mul(sqWord(m[0], m[1], m[2]), handleWord(us, vs))


def liftC(w):
    return (0, 0, 0, 0, 0, 0, 0, 0, 0, w % M)


def show(p):
    return "<" + ", ".join(str(v) for v in p) + ">"
