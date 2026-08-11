"""W61-WIDER step 2: the PURE class-two half of the `gamma_2` transport.

Every `gamma_2` element factors uniquely as `w * v` with `w` carrying only the four class-two
coordinates `(f, g, h, i)` and `v` a `gamma_3`-element, so

    conFiveDress m z = conFiveDress (conFiveDress m w) v ,

and the `gamma_2` transport is the composite of a PURE CLASS-TWO transport with wave 60's
committed stage-four transport `sqRelWord_gaThreeDress`.  This file measures the pure
class-two half: how big it is, and how its blocks decompose.

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
from u6poly import U6, padd, psub, pmul, pneg, pscale, pzero, pvar, poly_str  # noqa: E402

COORDS = P.COORDS
PURE = ["f", "g", "h", "i"]
GA2 = ["f", "g", "h", "i", "j", "k", "l", "m", "n", "o"]
GA3 = ["j", "k", "l", "m", "n", "o"]
GA4 = ["m", "n", "o"]


def pure(prefix):
    return U6(**{co: pvar(prefix + "_" + co) for co in PURE})


def ga2(prefix):
    return U6(**{co: pvar(prefix + "_" + co) for co in GA2})


def ga3(prefix):
    return U6(**{co: pvar(prefix + "_" + co) for co in GA3})


def shift(before, after):
    return before.inv() * after


def shape(z, live):
    dead = [co for co in COORDS if co not in live and getattr(z, co)]
    return dead, {co: getattr(z, co) for co in live}


def show(name, p):
    print("   %s = %s" % (name, poly_str(p)))


def is_dress(v):
    return v.split("_")[0] in ("z0", "z1", "z2", "z", "w", "v")


def bydeg(p):
    out = {}
    for mon, c in p.items():
        d = sum(1 for x in mon if is_dress(x))
        out.setdefault(d, {})[mon] = c
    return out


print("=" * 92)
print("== 0. the factorisation gamma_2 = (pure class two) . gamma_3 ==")
zz = ga2("z")
w = U6(**{co: getattr(zz, co) for co in PURE})
v = U6(j=zz.j, k=zz.k, l=zz.l, m=zz.m, n=zz.n,
       o=psub(zz.o, pmul(zz.f, zz.l)))
prod = w * v
bad = [co for co in COORDS if psub(getattr(prod, co), getattr(zz, co))]
print("   z = w * v with w pure class two and v gamma_3, v.o = z.o - z.f z.l : %s"
      % ("EXACT" if not bad else "fails at %s" % bad))
print()

print("=" * 92)
print("== 1. the core word under a three-slot PURE CLASS-TWO dressing ==")
s, x, y = U6.gen("s"), U6.gen("x"), U6.gen("y")
z0, z1, z2 = pure("z0"), pure("z1"), pure("z2")
cs = shift(P.sqWord(s, x, y), P.sqWord(s * z0, x * z1, y * z2))
dead, live = shape(cs, GA2)
print("   shape: gamma_2 (%s)" % ("yes" if not dead else "NO: " + str(dead)))
for co in GA2:
    d = bydeg(live[co])
    print("   [%s] %3d terms (deg-1 %3d, deg-2 %3d), poly degree %d"
          % (co, len(live[co]), len(d.get(1, {})), len(d.get(2, {})), P.pdeg(live[co])))
print()


def foxletter(a, b, c):
    return U6(**{co: padd(pscale(10, getattr(b, co)), pneg(getattr(a, co)),
                          pscale(-8, getattr(c, co))) for co in COORDS})


fx = foxletter(s, x, y)

# pairing forms of a PURE class-two dressing against a letter, from the commutator
zg, L = pure("z"), U6.gen("L")
cz = P.commP(zg, L)
_, pv = shape(cz, GA3)
print("   the pairing forms [pure class-two z, letter L]:")
for co in GA3:
    show("     pair_" + co, pv[co])
print()


def pair(zz_, LL, co):
    sub = {}
    for c in PURE:
        sub["z_" + c] = getattr(zz_, c)
    for c in COORDS:
        sub["L_" + c] = getattr(LL, c)
    out = {}
    for mon, coef in pv[co].items():
        term = {(): coef}
        for var in mon:
            term = pmul(term, sub[var])
        out = padd(out, term)
    return out


print("   --- residuals after Frobenius + the three Fox pairings ---")
for co in GA2:
    if co in PURE:
        want = padd(pscale(-4, pvar("z1_" + co)), pscale(2, pvar("z2_" + co)))
    else:
        want = padd(pscale(-4, pvar("z1_" + co)), pscale(2, pvar("z2_" + co)),
                    pair(z0, x, co), pair(z1, fx, co), pair(z2, y, co))
    rem = psub(live[co], want)
    d = bydeg(rem)
    print("   [%s] residual %3d terms (deg-1 %3d, deg-2 %3d)"
          % (co, len(rem), len(d.get(1, {})), len(d.get(2, {}))))
print()

print("=" * 92)
print("== 2. the handle commutator under a two-sided PURE class-two dressing ==")
p, q = U6.gen("p"), U6.gen("q")
zh, wh = pure("z"), pure("w")
hs = shift(P.commP(p, q), P.commP(p * zh, q * wh))
dead, hlive = shape(hs, GA3)
print("   shape: gamma_3 (%s)" % ("yes" if not dead else "NO: " + str(dead)))
for co in GA3:
    d = bydeg(hlive[co])
    print("   [%s] %3d terms (deg-1 %3d, deg-2 %3d)"
          % (co, len(hlive[co]), len(d.get(1, {})), len(d.get(2, {}))))
print()
