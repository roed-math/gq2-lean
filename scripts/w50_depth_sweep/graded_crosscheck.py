"""W50 cross-validations (b) and (c): the committed class-two and class-three closed forms.

(b) GradedTwo.lean, SqHeis.sqWord_c :

      (sqWord s x y).c = -4 x.c + 2 y.c + (s.a*x.b - x.a*s.b)
                         + 10 (x.a*x.b) + y.a*y.b - 8 (x.a*y.b)

    and sqHeisDefect / SqHeis.sqRelWord_c at h = 1.

(c) GradedThree.lean, SqU4.sqRelWord_f with sqU4Core / u4Comm3 / sqU4Defect, plus
    sqU4_top_range (the adjustable set of the class-three coordinate is 2R) and the
    two class-two rows of U_4 being GradedTwo's defect pulled back through the
    Heisenberg quotients toHeisAB, toHeisBC.

Each closed form is checked against a DIRECT evaluation of the relator word in the group,
over Z/2^k, on pseudo-random markings with a fixed seed.
"""

import random

MODBITS = 6                       # work over Z/64; every claimed identity is over any CommRing
M = 1 << MODBITS


# ------------------------------------------------------------------ SqHeis R
def h_mul(p, q):
    return ((p[0] + q[0]) % M, (p[1] + q[1]) % M, (p[2] + q[2] + p[0] * q[1]) % M)


def h_inv(p):
    a, b, c = p
    return ((-a) % M, (-b) % M, (-c + a * b) % M)


H1 = (0, 0, 0)


def gmul(mulf, *xs):
    z = None
    for x in xs:
        z = x if z is None else mulf(z, x)
    return z


def gpow(mulf, invf, one, x, k):
    if k < 0:
        x, k = invf(x), -k
    z = one
    for _ in range(k):
        z = mulf(z, x)
    return z


def gconj(mulf, invf, x, g):
    return mulf(mulf(invf(g), x), g)


def gcomm(mulf, invf, x, y):
    return mulf(mulf(invf(x), invf(y)), mulf(x, y))


def sqword(mulf, invf, one, s, x, y):
    return gmul(mulf, invf(gconj(mulf, invf, x, s)), invf(gpow(mulf, invf, one, x, 3)),
                gpow(mulf, invf, one, y, 2), gcomm(mulf, invf, y, gconj(mulf, invf, y, s)))


def relword1(mulf, invf, one, m):
    """sqRelWord at h = 1: sqWord(m0,m1,m2) * [m3,m4]."""
    return mulf(sqword(mulf, invf, one, m[0], m[1], m[2]), gcomm(mulf, invf, m[3], m[4]))


# ------------------------------------------------------------------ SqU4 R
def u_mul(p, q):
    a, b, c, d, e, f = p
    A, B, C, D, E, F = q
    return ((a + A) % M, (b + B) % M, (c + C) % M,
            (d + D + a * B) % M, (e + E + b * C) % M, (f + F + a * E + d * C) % M)


def u_inv(p):
    a, b, c, d, e, f = p
    return ((-a) % M, (-b) % M, (-c) % M, (-d + a * b) % M, (-e + b * c) % M,
            (-f + a * e - a * b * c + c * d) % M)


U1 = (0, 0, 0, 0, 0, 0)


def u4comm3(p, q):
    return (p[0] * q[4] - p[4] * q[0] + p[3] * q[2] - p[2] * q[3]
            + p[0] * p[2] * q[1] - p[0] * p[1] * q[2]
            + p[2] * q[0] * q[1] - p[1] * q[0] * q[2]) % M


def sqU4core(s, x, y):
    return (-(s[0] * s[1] * x[2]) + s[0] * s[2] * x[1]
            + s[0] * x[4] - s[2] * x[3] + s[3] * x[2] - s[4] * x[0]
            - 4 * (s[0] * x[1] * x[2]) + 3 * (s[1] * x[0] * x[2]) + s[2] * x[0] * x[1]
            + 2 * (s[0] * x[1] * y[2]) - 2 * (s[1] * x[0] * y[2])
            + s[0] * y[1] * y[2] - 2 * (s[1] * y[0] * y[2]) + s[2] * y[0] * y[1]
            - 20 * (x[0] * x[1] * x[2]) + 20 * (x[0] * x[1] * y[2]) - 4 * (x[0] * y[1] * y[2])
            + 10 * (x[0] * x[4]) - 8 * (x[0] * y[4]) + 10 * (x[2] * x[3]) - 8 * (x[3] * y[2])
            + y[0] * y[4] + y[2] * y[3]) % M


def heisAB(p):
    return (p[0], p[1], p[3])


def heisBC(p):
    return (p[1], p[2], p[4])


def heisdefect1(m):
    """sqHeisDefect at h = 1 (GradedTwo.lean)."""
    return (m[0][0] * m[1][1] - m[1][0] * m[0][1]
            + 10 * (m[1][0] * m[1][1]) + m[2][0] * m[2][1] - 8 * (m[1][0] * m[2][1])
            + m[3][0] * m[4][1] - m[4][0] * m[3][1]) % M


def sqU4defect1(m):
    return (sqU4core(m[0], m[1], m[2])
            + (-4 * m[1][0] + 2 * m[2][0]) * (m[3][1] * m[4][2] - m[4][1] * m[3][2])
            + u4comm3(m[3], m[4])) % M


if __name__ == "__main__":
    rnd = random.Random(20260807)
    NT = 4000

    # ---- (b) SqHeis.sqWord_c and SqHeis.sqRelWord_c ------------------------
    bad = 0
    for _ in range(NT):
        s, x, y = [tuple(rnd.randrange(M) for _ in range(3)) for _ in range(3)]
        lhs = sqword(h_mul, h_inv, H1, s, x, y)[2]
        rhs = (-4 * x[2] + 2 * y[2] + (s[0] * x[1] - x[0] * s[1])
               + 10 * (x[0] * x[1]) + y[0] * y[1] - 8 * (x[0] * y[1])) % M
        bad += (lhs != rhs)
    print(f"(b) SqHeis.sqWord_c over Z/{M}, {NT} random triples : mismatches {bad}")

    bad = 0
    for _ in range(NT):
        m = [tuple(rnd.randrange(M) for _ in range(3)) for _ in range(5)]
        lhs = relword1(h_mul, h_inv, H1, m)[2]
        rhs = (-4 * m[1][2] + 2 * m[2][2] + heisdefect1(m)) % M
        bad += (lhs != rhs)
    print(f"(b) SqHeis.sqRelWord_c (h=1) with sqHeisDefect, {NT} markings : mismatches {bad}")

    # ---- (c) SqU4.sqRelWord_f and the two pulled-back class-two rows -------
    badf = badd = bade = 0
    for _ in range(NT):
        m = [tuple(rnd.randrange(M) for _ in range(6)) for _ in range(5)]
        r = relword1(u_mul, u_inv, U1, m)
        if r[5] != (-4 * m[1][5] + 2 * m[2][5] + sqU4defect1(m)) % M:
            badf += 1
        if r[3] != (-4 * m[1][3] + 2 * m[2][3] + heisdefect1([heisAB(p) for p in m])) % M:
            badd += 1
        if r[4] != (-4 * m[1][4] + 2 * m[2][4] + heisdefect1([heisBC(p) for p in m])) % M:
            bade += 1
    print(f"(c) SqU4.sqRelWord_f with sqU4Core/u4Comm3/sqU4Defect, {NT} markings"
          f" : mismatches {badf}")
    print(f"(c) SqU4 class-two rows = GradedTwo's defect through toHeisAB / toHeisBC"
          f" : mismatches {badd} / {bade}")

    # ---- (c) sqU4_top_range: the adjustable set of the top coordinate is 2R
    m0 = [tuple(rnd.randrange(M) for _ in range(6)) for _ in range(5)]
    reach = set()
    for g in range(M):
        for d in range(M):
            m = [list(p) for p in m0]
            m[1][5] = g
            m[2][5] = d
            reach.add(relword1(u_mul, u_inv, U1, [tuple(p) for p in m])[5])
    base = relword1(u_mul, u_inv, U1, m0)[5]
    shifted = {(x - base) % M for x in reach}
    print(f"(c) sqU4_top_range: moving only the class-three coordinates of slots 1,2 reaches"
          f" {len(shifted)} values; = 2R? {shifted == {2 * k % M for k in range(M)}}")

    # ---- and the sigma / handle slots' class-three coordinates cancel outright
    ok = True
    for slot in (0, 3, 4):
        for _ in range(200):
            m = [list(p) for p in m0]
            m[slot][5] = rnd.randrange(M)
            if relword1(u_mul, u_inv, U1, [tuple(p) for p in m])[5] != base:
                ok = False
    print(f"(c) the sigma-slot and both handle slots' class-three coordinates cancel: {ok}")
