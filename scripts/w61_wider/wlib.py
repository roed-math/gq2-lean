"""W61-WIDER shared library: the closed forms of the `gamma_2` transport at class five.

Every form here is a CONJECTURE until `derive_assemble.py` certifies it against the honest
group law of `u6poly.py`, and `validate_wider.py` certifies it against honest 6 x 6 matrix
collection over four rings.  Nothing in this file is transcribed from Lean; the Lean file is
emitted from it (`emit_lean.py`).

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""
import sys
import os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_defect5"))

import u6poly as P                                            # noqa: E402
from u6poly import U6, padd, psub, pmul, pneg, pscale, pzero, pvar  # noqa: E402

COORDS = P.COORDS
GA2 = ["f", "g", "h", "i", "j", "k", "l", "m", "n", "o"]
GA3 = ["j", "k", "l", "m", "n", "o"]


def ga2(prefix):
    return U6(**{co: pvar(prefix + "_" + co) for co in GA2})


def shift(before, after):
    return before.inv() * after


def shape(z, live):
    dead = [co for co in COORDS if co not in live and getattr(z, co)]
    return dead, {co: getattr(z, co) for co in live}


# ------------------------------------------------------- the six pairing forms
# `pairX z L` is the X-coordinate of `[z, L]` for `z` a gamma_2 element: the graded Fox
# pairing of a dressing against a letter.  Certified in derive_blocks.py section A.


def pairJ(z, L):
    return psub(pmul(z.f, L.c), pmul(z.g, L.a))


def pairK(z, L):
    return psub(pmul(z.g, L.d), pmul(z.h, L.b))


def pairL(z, L):
    return psub(pmul(z.h, L.e), pmul(z.i, L.c))


def pairM(z, L):
    return padd(pmul(z.j, L.d), pneg(pmul(z.k, L.a)),
                pmul(z.f, L.h), pneg(pmul(z.h, L.f)),
                pmul(z.h, pmul(L.a, L.b)), pneg(pmul(z.g, pmul(L.a, L.d))))


def pairN(z, L):
    return padd(pmul(z.k, L.e), pneg(pmul(z.l, L.b)),
                pmul(z.g, L.i), pneg(pmul(z.i, L.g)),
                pmul(z.i, pmul(L.b, L.c)), pneg(pmul(z.h, pmul(L.b, L.e))))


def pairO(z, L):
    return padd(pmul(z.m, L.e), pneg(pmul(z.n, L.a)),
                pmul(z.j, L.i), pneg(pmul(z.i, L.j)),
                pmul(z.f, L.l), pneg(pmul(z.l, L.f)),
                pmul(z.l, pmul(L.a, L.b)), pneg(pmul(z.k, pmul(L.a, L.e))),
                pmul(z.i, pmul(L.a, L.g)), pneg(pmul(z.g, pmul(L.a, L.i))),
                pmul(z.i, pmul(L.c, L.f)), pneg(pmul(z.h, pmul(L.e, L.f))),
                pmul(pmul(z.f, z.i), L.c), pneg(pmul(pmul(z.f, z.h), L.e)),
                pneg(pmul(z.i, pmul(pmul(L.a, L.b), L.c))),
                pmul(z.h, pmul(pmul(L.a, L.b), L.e)))


PAIRS = {"j": pairJ, "k": pairK, "l": pairL, "m": pairM, "n": pairN, "o": pairO}


# ------------------------------------------------ the commutator's class-two rows


def cF(p, q):
    return psub(pmul(p.a, q.b), pmul(p.b, q.a))


def cG(p, q):
    return psub(pmul(p.b, q.c), pmul(p.c, q.b))


def cH(p, q):
    return psub(pmul(p.c, q.d), pmul(p.d, q.c))


def cI(p, q):
    return psub(pmul(p.d, q.e), pmul(p.e, q.d))


# ------------------------------------------------------------- the handle shift


def handleX(p, q, z, w):
    """The 16-term collection artefact of the handle shift's class-five row."""
    return padd(
        pmul(w.f, padd(pmul(psub(q.c, p.c), z.i), pneg(pmul(q.e, z.h)),
                       pneg(pmul(p.c, cI(p, q))))),
        pmul(w.g, pmul(p.a, padd(z.i, cI(p, q)))),
        pmul(w.h, pmul(p.e, padd(z.f, cF(p, q)))),
        pmul(w.i, padd(pmul(psub(q.c, p.c), z.f), pneg(pmul(q.a, z.g)),
                       pneg(pmul(p.c, cF(p, q))))))


def handleShift(p, q, z, w):
    cj = P.commP(p, q).j
    cl = P.commP(p, q).l
    return U6(
        j=psub(pairJ(z, q), pairJ(w, p)),
        k=psub(pairK(z, q), pairK(w, p)),
        l=psub(pairL(z, q), pairL(w, p)),
        m=padd(psub(pairM(z, q), pairM(w, p)),
               psub(pmul(z.f, w.h), pmul(z.h, w.f)),
               pmul(cF(p, q), padd(z.h, w.h)), pneg(pmul(cH(p, q), padd(z.f, w.f)))),
        n=padd(psub(pairN(z, q), pairN(w, p)),
               psub(pmul(z.g, w.i), pmul(z.i, w.g)),
               pmul(cG(p, q), padd(z.i, w.i)), pneg(pmul(cI(p, q), padd(z.g, w.g)))),
        o=padd(psub(pairO(z, q), pairO(w, p)),
               psub(pmul(z.f, w.l), pmul(z.l, w.f)),
               psub(pmul(z.j, w.i), pmul(z.i, w.j)),
               pmul(cF(p, q), padd(z.l, w.l)), pneg(pmul(cl, padd(z.f, w.f))),
               pmul(cj, padd(z.i, w.i)), pneg(pmul(cI(p, q), padd(z.j, w.j))),
               handleX(p, q, z, w)))


# --------------------------------------------------------------- the core shift


def foxletter(s, x, y):
    """`10 x - s - 8 y` columnwise: the x0-slot's Fox letter (`sqFoxX6`)."""
    return U6(**{co: padd(pscale(10, getattr(x, co)), pneg(getattr(s, co)),
                          pscale(-8, getattr(y, co))) for co in COORDS})


def coreShift(s, x, y, z0, z1, z2):
    """The honest core shift, computed, not conjectured."""
    return shift(P.sqWord(s, x, y), P.sqWord(s * z0, x * z1, y * z2))


def coreBlocks(s, x, y, z0, z1, z2):
    """Split the core shift's m, n, o rows into (correction, quadratic) blocks."""
    cs = coreShift(s, x, y, z0, z1, z2)
    fx = foxletter(s, x, y)
    out = {}
    for co in ("m", "n", "o"):
        want = padd(pscale(-4, pvar("z1_" + co)), pscale(2, pvar("z2_" + co)),
                    PAIRS[co](z0, x), PAIRS[co](z1, fx), PAIRS[co](z2, y))
        rem = psub(getattr(cs, co), want)
        quad, corr = {}, {}
        for mon, c in rem.items():
            d = sum(1 for v in mon if v.startswith("z"))
            (quad if d >= 2 else corr)[mon] = c
        out[co] = (corr, quad)
    return out


# -------------------------------------------------- the handle word and the total


def handleWordShift(us, vs, zus, zvs):
    """The gamma_3-element by which the handle word moves under an all-pair dressing.
    The cross-handle term is the price of moving each handle's gamma_3 shift past the LATER
    handle commutators: at class four that price is zero, here it is not."""
    n = len(us)
    Ds = [handleShift(us[k], vs[k], zus[k], zvs[k]) for k in range(n)]
    out = U6()
    for co in GA3:
        setattr(out, co, padd(*[getattr(D, co) for D in Ds]) if n else pzero())
    cross = pzero()
    for s_ in range(n):
        for t in range(s_ + 1, n):
            cross = padd(cross, pmul(Ds[s_].j, cI(us[t], vs[t])),
                         pneg(pmul(Ds[s_].l, cF(us[t], vs[t]))))
    out.o = padd(out.o, cross)
    return out


def relShift(m, h):
    """The gamma_2-element by which the relator moves under a five-slot gamma_2 dressing.
    `m` is a list of (frame slot, dressing) pairs of length `3 + 2h`."""
    s, x, y = m[0][0], m[1][0], m[2][0]
    z0, z1, z2 = m[0][1], m[1][1], m[2][1]
    us = [m[3 + 2 * k][0] for k in range(h)]
    vs = [m[4 + 2 * k][0] for k in range(h)]
    zus = [m[3 + 2 * k][1] for k in range(h)]
    zvs = [m[4 + 2 * k][1] for k in range(h)]
    C = coreShift(s, x, y, z0, z1, z2)
    HWs = handleWordShift(us, vs, zus, zvs)
    HW = P.handleWord(us, vs)
    K = U6(m=psub(pmul(C.f, HW.h), pmul(C.h, HW.f)),
           n=psub(pmul(C.g, HW.i), pmul(C.i, HW.g)),
           o=padd(psub(pmul(C.f, HW.l), pmul(C.l, HW.f)),
                  psub(pmul(C.j, HW.i), pmul(C.i, HW.j))))
    T = U6(**{co: padd(getattr(HWs, co), getattr(K, co)) for co in GA3})
    return C * T
