#!/usr/bin/env python3
"""validate_u6.py.

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

"""validate_u6.py.
"""

"""validate_u6.py.
"""

"""validate_u6.py.
"""

"""validate_u6.py.
"""

"""W58-FIVE step 3: validate every SqU6 closed form against honest group collection.

The "closed form" side is the fifteen-coordinate formula that goes into
GQ2/Dyadic/SqCore/GradedFive.lean; the "collection" side is genuine 6x6 unitriangular
matrix arithmetic over Z/N (products, inverses by back-substitution, powers by repeated
multiplication, and the words spelled letter by letter).  Any disagreement is a mismatch.

Also checked here:
  * the two U5-quotients are homomorphisms and agree with the committed SqU5 formulas;
  * the flat/even power hypotheses really do kill the C(n,3), C(n,4), C(n,5) layers of the
    top coordinate, as exact ring identities;
  * the relator's top-row split and the sigma-dressing response formula;
  * the class-five non-blindness witness.
"""
import random
import sys

NAMES = "abcdefghijklmno"
POS = dict(a=(0, 1), b=(1, 2), c=(2, 3), d=(3, 4), e=(4, 5),
           f=(0, 2), g=(1, 3), h=(2, 4), i=(3, 5),
           j=(0, 3), k=(1, 4), l=(2, 5),
           m=(0, 4), n=(1, 5),
           o=(0, 5))

MISMATCH = 0
COMPARISONS = 0
CHECKS = 0


def fail(tag, extra=""):
    global MISMATCH
    MISMATCH += 1
    print(f"  !! MISMATCH {tag} {extra}")


def eq(tag, u, v):
    global COMPARISONS
    COMPARISONS += 1
    if u != v:
        fail(tag, f"{u} != {v}")


# ---------------------------------------------------------------- honest collection

def to_mat(t, N):
    M = [[1 if r == c else 0 for c in range(6)] for r in range(6)]
    for idx, nm in enumerate(NAMES):
        r, c = POS[nm]
        M[r][c] = t[idx] % N
    return M


def of_mat(M, N):
    return tuple(M[POS[nm][0]][POS[nm][1]] % N for nm in NAMES)


def mmul(A, B, N):
    return [[sum(A[r][s] * B[s][c] for s in range(6)) % N for c in range(6)]
            for r in range(6)]


def minv(A, N):
    """Inverse of a unitriangular matrix by back-substitution (honest, no formula)."""
    X = [[1 if r == c else 0 for c in range(6)] for r in range(6)]
    for d in range(1, 6):
        for r in range(6 - d):
            c = r + d
            X[r][c] = (-A[r][c] - sum(X[r][s] * A[s][c] for s in range(r + 1, c))) % N
    return X


def mpow(A, k, N):
    R = [[1 if r == c else 0 for c in range(6)] for r in range(6)]
    for _ in range(k):
        R = mmul(R, A, N)
    return R


def mconj(P, G, N):
    return mmul(mmul(minv(G, N), P, N), G, N)


def mcomm(P, Q, N):
    return mmul(mmul(mmul(minv(P, N), minv(Q, N), N), P, N), Q, N)


# ---------------------------------------------------------------- closed forms

def T(t):
    return dict(zip(NAMES, t))


def cf_mul(p, q, N):
    p, q = T(p), T(q)
    r = {}
    r["a"] = p["a"] + q["a"]
    r["b"] = p["b"] + q["b"]
    r["c"] = p["c"] + q["c"]
    r["d"] = p["d"] + q["d"]
    r["e"] = p["e"] + q["e"]
    r["f"] = p["f"] + q["f"] + p["a"] * q["b"]
    r["g"] = p["g"] + q["g"] + p["b"] * q["c"]
    r["h"] = p["h"] + q["h"] + p["c"] * q["d"]
    r["i"] = p["i"] + q["i"] + p["d"] * q["e"]
    r["j"] = p["j"] + q["j"] + p["a"] * q["g"] + p["f"] * q["c"]
    r["k"] = p["k"] + q["k"] + p["b"] * q["h"] + p["g"] * q["d"]
    r["l"] = p["l"] + q["l"] + p["c"] * q["i"] + p["h"] * q["e"]
    r["m"] = p["m"] + q["m"] + p["a"] * q["k"] + p["f"] * q["h"] + p["j"] * q["d"]
    r["n"] = p["n"] + q["n"] + p["b"] * q["l"] + p["g"] * q["i"] + p["k"] * q["e"]
    r["o"] = (p["o"] + q["o"] + p["a"] * q["n"] + p["f"] * q["l"] + p["j"] * q["i"]
              + p["m"] * q["e"])
    return tuple(r[nm] % N for nm in NAMES)


def cf_inv(p, N):
    p = T(p)
    a, b, c, d, e = p["a"], p["b"], p["c"], p["d"], p["e"]
    f, g, h, i = p["f"], p["g"], p["h"], p["i"]
    j, k, l = p["j"], p["k"], p["l"]
    m, n, o = p["m"], p["n"], p["o"]
    r = {}
    r["a"], r["b"], r["c"], r["d"], r["e"] = -a, -b, -c, -d, -e
    r["f"] = a * b - f
    r["g"] = b * c - g
    r["h"] = c * d - h
    r["i"] = d * e - i
    r["j"] = -a * b * c + a * g + c * f - j
    r["k"] = -b * c * d + b * h + d * g - k
    r["l"] = -c * d * e + c * i + e * h - l
    r["m"] = a * b * c * d - a * b * h - a * d * g + a * k - c * d * f + d * j + f * h - m
    r["n"] = b * c * d * e - b * c * i - b * e * h + b * l - d * e * g + e * k + g * i - n
    r["o"] = (-a * b * c * d * e + a * b * c * i + a * b * e * h - a * b * l + a * d * e * g
              - a * e * k - a * g * i + a * n + c * d * e * f - c * f * i - d * e * j
              - e * f * h + e * m + f * l + i * j - o)
    return tuple(r[nm] % N for nm in NAMES)


def binom(n, k):
    r = 1
    for t in range(k):
        r = r * (n - t) // (t + 1)
    return r


def cf_pow(p, n, N):
    p = T(p)
    a, b, c, d, e = p["a"], p["b"], p["c"], p["d"], p["e"]
    f, g, h, i = p["f"], p["g"], p["h"], p["i"]
    j, k, l = p["j"], p["k"], p["l"]
    m, nn, o = p["m"], p["n"], p["o"]
    c2, c3, c4, c5 = binom(n, 2), binom(n, 3), binom(n, 4), binom(n, 5)
    r = {}
    for nm, v in zip("abcde", (a, b, c, d, e)):
        r[nm] = n * v
    r["f"] = n * f + c2 * (a * b)
    r["g"] = n * g + c2 * (b * c)
    r["h"] = n * h + c2 * (c * d)
    r["i"] = n * i + c2 * (d * e)
    r["j"] = n * j + c2 * (a * g + c * f) + c3 * (a * b * c)
    r["k"] = n * k + c2 * (b * h + d * g) + c3 * (b * c * d)
    r["l"] = n * l + c2 * (c * i + e * h) + c3 * (c * d * e)
    r["m"] = (n * m + c2 * (a * k + d * j + f * h)
              + c3 * (a * b * h + a * d * g + c * d * f) + c4 * (a * b * c * d))
    r["n"] = (n * nn + c2 * (b * l + e * k + g * i)
              + c3 * (b * c * i + b * e * h + d * e * g) + c4 * (b * c * d * e))
    r["o"] = (n * o + c2 * (a * nn + e * m + f * l + i * j)
              + c3 * (a * b * l + a * e * k + a * g * i + c * f * i + d * e * j + e * f * h)
              + c4 * (a * b * c * i + a * b * e * h + a * d * e * g + c * d * e * f)
              + c5 * (a * b * c * d * e))
    return tuple(r[nm] % N for nm in NAMES)


def cf_comm(p, q, N):
    """commP p q = p^-1 q^-1 p q, via the closed forms only."""
    return cf_mul(cf_mul(cf_mul(cf_inv(p, N), cf_inv(q, N), N), p, N), q, N)


# ---------------------------------------------------------------- word layer

def w_conj(p, g, N):
    return cf_mul(cf_mul(cf_inv(g, N), p, N), g, N)


def w_comm(p, q, N):
    return cf_comm(p, q, N)


ONE = tuple(0 for _ in NAMES)


def w_pow(p, k, N):
    r = ONE
    for _ in range(k):
        r = cf_mul(r, p, N)
    return r


def sqWord(s, x, y, N):
    """(conjP x s)^-1 * (x^3)^-1 * y^2 * commP y (conjP y s)"""
    A = cf_inv(w_conj(x, s, N), N)
    B = cf_inv(w_pow(x, 3, N), N)
    C = w_pow(y, 2, N)
    D = w_comm(y, w_conj(y, s, N), N)
    return cf_mul(cf_mul(cf_mul(A, B, N), C, N), D, N)


def handleWord(us, vs, N):
    r = ONE
    for u, v in zip(us, vs):
        r = cf_mul(r, w_comm(u, v, N), N)
    return r


def sqRelWord(mk, h, N):
    us = [mk[3 + 2 * jj] for jj in range(h)]
    vs = [mk[4 + 2 * jj] for jj in range(h)]
    return cf_mul(sqWord(mk[0], mk[1], mk[2], N), handleWord(us, vs, N), N)


# honest matrix versions of the words
def M_sqWord(s, x, y, N):
    S, X, Y = to_mat(s, N), to_mat(x, N), to_mat(y, N)
    A = minv(mconj(X, S, N), N)
    B = minv(mpow(X, 3, N), N)
    C = mpow(Y, 2, N)
    D = mcomm(Y, mconj(Y, S, N), N)
    return of_mat(mmul(mmul(mmul(A, B, N), C, N), D, N), N)


def M_sqRelWord(mk, h, N):
    S, X, Y = to_mat(mk[0], N), to_mat(mk[1], N), to_mat(mk[2], N)
    A = minv(mconj(X, S, N), N)
    B = minv(mpow(X, 3, N), N)
    C = mpow(Y, 2, N)
    D = mcomm(Y, mconj(Y, S, N), N)
    W = mmul(mmul(mmul(A, B, N), C, N), D, N)
    for jj in range(h):
        U, V = to_mat(mk[3 + 2 * jj], N), to_mat(mk[4 + 2 * jj], N)
        W = mmul(W, mcomm(U, V, N), N)
    return of_mat(W, N)


def rnd(rng, N):
    return tuple(rng.randrange(N) for _ in NAMES)


# ---------------------------------------------------------------- checks

def check_group_laws(rng, Ns, reps):
    print("## 1. closed forms vs honest 6x6 collection")
    for N in Ns:
        for _ in range(reps):
            p, q, r = rnd(rng, N), rnd(rng, N), rnd(rng, N)
            P, Q, R = to_mat(p, N), to_mat(q, N), to_mat(r, N)
            eq(f"mul N={N}", cf_mul(p, q, N), of_mat(mmul(P, Q, N), N))
            eq(f"inv N={N}", cf_inv(p, N), of_mat(minv(P, N), N))
            eq(f"comm N={N}", cf_comm(p, q, N), of_mat(mcomm(P, Q, N), N))
            eq(f"conj N={N}", w_conj(p, q, N), of_mat(mconj(P, Q, N), N))
            eq(f"assoc N={N}", cf_mul(cf_mul(p, q, N), r, N), cf_mul(p, cf_mul(q, r, N), N))
            eq(f"invcancel N={N}", cf_mul(cf_inv(p, N), p, N), ONE)
            eq(f"one N={N}", cf_mul(p, ONE, N), p)
            for k in range(0, 9):
                eq(f"pow{k} N={N}", cf_pow(p, k, N), of_mat(mpow(P, k, N), N))
    print(f"   ok ({COMPARISONS} comparisons so far)")


def check_quotients(rng, Ns, reps):
    """toU5L and toU5R are homs onto the committed SqU5 multiplication."""
    global CHECKS
    print("## 2. the two U5-quotients")
    L = ["a", "b", "c", "d", "f", "g", "h", "j", "k", "m"]
    R = ["b", "c", "d", "e", "g", "h", "i", "k", "l", "n"]

    def u5mul(p, q, N):
        (pa, pb, pc, pd, pe, pf, pg, ph, pi, pj) = p
        (qa, qb, qc, qd, qe, qf, qg, qh, qi, qj) = q
        return tuple(v % N for v in (
            pa + qa, pb + qb, pc + qc, pd + qd,
            pe + qe + pa * qb, pf + qf + pb * qc, pg + qg + pc * qd,
            ph + qh + pa * qf + pe * qc, pi + qi + pb * qg + pf * qd,
            pj + qj + pa * qi + pe * qg + ph * qd))

    for N in Ns:
        for _ in range(reps):
            p, q = rnd(rng, N), rnd(rng, N)
            pq = cf_mul(p, q, N)
            for tag, sel in (("toU5L", L), ("toU5R", R)):
                ip = tuple(T(p)[c] for c in sel)
                iq = tuple(T(q)[c] for c in sel)
                ipq = tuple(T(pq)[c] for c in sel)
                eq(f"{tag} N={N}", ipq, u5mul(ip, iq, N))
    CHECKS += 1
    print("   ok")


def check_flat_identities():
    """The exact ring identities that make the class-five powering lemma work."""
    global CHECKS
    import sympy as sp
    print("## 3. the power-layer identities (exact, over Z)")
    syms = {nm: sp.Symbol(nm) for nm in NAMES}
    a, b, c, d, e = (syms[x] for x in "abcde")
    f, g, h, i = (syms[x] for x in "fghi")
    j, k, l = (syms[x] for x in "jkl")
    m, n, o = (syms[x] for x in "mno")
    X3 = a * b * l + a * e * k + a * g * i + c * f * i + d * e * j + e * f * h
    X4 = a * b * c * i + a * b * e * h + a * d * e * g + c * d * e * f
    X5 = a * b * c * d * e
    ob_j = a * g + c * f
    ob_m = a * k + d * j + f * h
    id3 = sp.expand(X3 - (l * (a * b) + i * ob_j + e * ob_m))
    id4 = sp.expand(X4 - ((a * b) * (c * i + e * h) + d * e * ob_j))
    id5 = sp.expand(X5 - (a * b) * c * d * e)
    for tag, v in (("X3", id3), ("X4", id4), ("X5", id5)):
        CHECKS += 1
        if v != 0:
            fail(f"layer identity {tag}", str(v))
        else:
            print(f"   {tag} identity holds")
    # the C(n,3)/C(n,4) layers of m and n
    Y3m = a * b * h + a * d * g + c * d * f
    id3m = sp.expand(Y3m - ((a * b) * h + d * ob_j))
    Y3n = b * c * i + b * e * h + d * e * g
    ob_k = b * h + d * g
    id3n = sp.expand(Y3n - ((b * c) * i + e * ob_k))
    for tag, v in (("Y3m", id3m), ("Y3n", id3n)):
        CHECKS += 1
        if v != 0:
            fail(f"layer identity {tag}", str(v))
        else:
            print(f"   {tag} identity holds")


def check_pow_polynomial(rng, Ns, reps):
    """With the seven lower obstructions flat and the class-four ones even, the top
    coordinate of g^n is the polynomial the Lean lemma claims.  Random tuples essentially
    never meet the hypotheses, so the family is constructed: b = c = d = g = h = 0 makes all
    seven lower obstructions vanish identically, and the rest is sampled."""
    global CHECKS
    print("## 4. the powering polynomial at flat / even-class-four bases")
    found_flat = found_even = skipped = 0
    for N in Ns:
        for _ in range(reps * 60):
            vals = {nm: 0 for nm in NAMES}
            for nm in ("a", "e", "f", "i", "j", "k", "l", "m", "n", "o"):
                vals[nm] = rng.randrange(N)
            t = tuple(vals[nm] for nm in NAMES)
            p = T(t)
            for key, val in (("ab", p["a"] * p["b"]), ("bc", p["b"] * p["c"]),
                             ("cd", p["c"] * p["d"]), ("de", p["d"] * p["e"]),
                             ("j", p["a"] * p["g"] + p["c"] * p["f"]),
                             ("k", p["b"] * p["h"] + p["d"] * p["g"]),
                             ("l", p["c"] * p["i"] + p["e"] * p["h"])):
                eq(f"lower flat {key} N={N}", val % N, 0)
            obm = (p["a"] * p["k"] + p["d"] * p["j"] + p["f"] * p["h"]) % N
            obn = (p["b"] * p["l"] + p["e"] * p["k"] + p["g"] * p["i"]) % N
            obo = (p["a"] * p["n"] + p["e"] * p["m"] + p["f"] * p["l"] + p["i"] * p["j"]) % N
            if obm % 2 or obn % 2 or obo % 2:
                skipped += 1
                continue
            wm, wn, w2 = obm // 2 % N, obn // 2 % N, obo // 2 % N
            tgt = {(p["e"] * wm) % N, (p["a"] * wn) % N}
            if len(tgt) != 1:
                skipped += 1
                continue
            tgt = tgt.pop()
            w3 = next((cd for cd in range(N) if 3 * cd % N == tgt), None)
            if w3 is None:
                skipped += 1
                continue
            for nexp in range(0, 12):
                got = cf_pow(t, nexp, N)
                want = {nm: nexp * p[nm] % N for nm in NAMES}
                want["m"] = (nexp * p["m"] + (nexp * nexp - nexp) * wm) % N
                want["n"] = (nexp * p["n"] + (nexp * nexp - nexp) * wn) % N
                want["o"] = (nexp * p["o"] + (nexp * nexp - nexp) * w2
                             + (nexp ** 3 - 3 * nexp ** 2 + 2 * nexp) * w3) % N
                eq(f"powpoly N={N} n={nexp}", got, tuple(want[nm] % N for nm in NAMES))
            if obm == 0 and obn == 0:
                found_flat += 1
            else:
                found_even += 1
    CHECKS += 1
    print(f"   bases meeting the flat hypotheses: {found_flat}")
    print(f"   bases meeting the even-class-four hypotheses but NOT flat: {found_even}")
    print(f"   bases outside both (hypotheses genuinely bite): {skipped}")


def check_relator_split(rng, Ns, reps, hs):
    """(sqRelWord m).o splits as core.o + H.o + core.a*H.n + core.f*H.l + core.j*H.i."""
    global CHECKS
    print("## 5. the relator's top-row split and the sigma response")
    for N in Ns:
        for h in hs:
            for _ in range(reps):
                mk = [rnd(rng, N) for _ in range(3 + 2 * h)]
                eq(f"relword N={N} h={h}", sqRelWord(mk, h, N), M_sqRelWord(mk, h, N))
                core = sqWord(mk[0], mk[1], mk[2], N)
                H = handleWord([mk[3 + 2 * jj] for jj in range(h)],
                               [mk[4 + 2 * jj] for jj in range(h)], N)
                cT, HT = T(core), T(H)
                eq(f"handle gamma2 N={N} h={h}", tuple(HT[x] for x in "abcde"), (0,) * 5)
                lhs = T(sqRelWord(mk, h, N))["o"]
                rhs = (cT["o"] + HT["o"] + cT["a"] * HT["n"] + cT["f"] * HT["l"]
                       + cT["j"] * HT["i"]) % N
                eq(f"o-split N={N} h={h}", lhs, rhs)
    CHECKS += 1
    print("   ok")


def check_nonblindness(rng, Ns, reps, hs):
    """The class-five sigma response DOES depend on the handle block."""
    global CHECKS
    print("## 6. class-five non-blindness of the sigma reading")
    witnesses = 0
    blind_four = 0
    for N in Ns:
        for h in hs:
            if h == 0:
                continue
            for _ in range(reps * 4):
                # two markings with the SAME core slots, DIFFERENT handle blocks
                s, x, y = rnd(rng, N), rnd(rng, N), rnd(rng, N)
                # impose the wave-57 gauge: b-columns of x, y and of the dressing vanish
                x = tuple(0 if nm == "b" else v for nm, v in zip(NAMES, x))
                y = tuple(0 if nm == "b" else v for nm, v in zip(NAMES, y))
                v = rnd(rng, N)
                v = tuple(0 if nm == "b" else vv for nm, vv in zip(NAMES, v))
                mk1 = [s, x, y] + [rnd(rng, N) for _ in range(2 * h)]
                mk2 = [s, x, y] + [rnd(rng, N) for _ in range(2 * h)]
                d1 = [cf_mul(s, v, N), x, y] + mk1[3:]
                d2 = [cf_mul(s, v, N), x, y] + mk2[3:]
                r1 = (T(M_sqRelWord(d1, h, N))["o"] - T(M_sqRelWord(mk1, h, N))["o"]) % N
                r2 = (T(M_sqRelWord(d2, h, N))["o"] - T(M_sqRelWord(mk2, h, N))["o"]) % N
                if r1 != r2:
                    witnesses += 1
                # the class-four rows must still be blind (wave 57), through toU5L
                q1 = (T(M_sqRelWord(d1, h, N))["m"] - T(M_sqRelWord(mk1, h, N))["m"]) % N
                q2 = (T(M_sqRelWord(d2, h, N))["m"] - T(M_sqRelWord(mk2, h, N))["m"]) % N
                if q1 == q2:
                    blind_four += 1
                else:
                    fail(f"class-four row NOT blind N={N} h={h}", f"{q1} != {q2}")
    CHECKS += 1
    print(f"   class-five o-row responses that DIFFER between handle blocks: {witnesses}")
    print(f"   class-four m-row responses that agree (wave-57 blindness): {blind_four}")


def main():
    rng = random.Random(20260810)
    Ns = [8, 16, 32]
    check_group_laws(rng, Ns, 40)
    check_quotients(rng, Ns, 60)
    check_flat_identities()
    check_pow_polynomial(rng, [8, 16], 30)
    check_relator_split(rng, Ns, 25, [0, 1, 2, 3])
    check_nonblindness(rng, [8, 16], 25, [1, 2])
    print()
    print(f"TOTAL comparisons: {COMPARISONS}")
    print(f"TOTAL named checks: {CHECKS}")
    print(f"TOTAL mismatches: {MISMATCH}")
    return 0 if MISMATCH == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
