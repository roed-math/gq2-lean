"""W61-WIDER step 3: the named blocks of the `gamma_2` transport at class five.

Takes the raw shifts of `derive_wider.py` and splits every row into blocks that can be
transcribed as Lean definitions:

  * the three class-three rows   Frobenius + Fox pairings, exactly (affine);
  * the two class-four rows      Frobenius + Fox pairings + correction + quadratic, and both
                                 are `GradedGammaTwo` verbatim through the two U_5-quotients;
  * the class-five row           Frobenius + Fox pairings + correction + quadratic, the last
                                 block NOT frame-free, which is the genuinely new feature;
  * the handle shift             pairings + commutator-of-dressings + block corrections;
  * the collection term.

Nothing is guessed: each candidate block is subtracted and the residual printed, so a claim of
"EXACT" is a certificate that the two polynomials are equal as exact integer polynomials.

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
GA2 = ["f", "g", "h", "i", "j", "k", "l", "m", "n", "o"]
GA3 = ["j", "k", "l", "m", "n", "o"]
GA4 = ["m", "n", "o"]


def ga2(prefix):
    return U6(**{co: pvar(prefix + "_" + co) for co in GA2})


def shift(before, after):
    return before.inv() * after


def shape(z, live):
    dead = [co for co in COORDS if co not in live and getattr(z, co)]
    return dead, {co: getattr(z, co) for co in live}


def is_dress(v):
    return v.split("_")[0] in ("z0", "z1", "z2", "z", "w")


def bydeg(p):
    out = {}
    for mon, c in p.items():
        d = sum(1 for x in mon if is_dress(x))
        out.setdefault(d, {})[mon] = c
    return out


def show(name, p):
    print("   %s = %s" % (name, poly_str(p)))


# ------------------------------------------------------------------ the pairings


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


def foxletter(s, x, y):
    return U6(**{co: padd(pscale(10, getattr(x, co)), pneg(getattr(s, co)),
                          pscale(-8, getattr(y, co))) for co in COORDS})


print("=" * 92)
print("== A. the pairing forms are the honest commutator forms on gamma_2 ==")
zg, Lg = ga2("z"), U6.gen("L")
cz = P.commP(zg, Lg)
dead, livep = shape(cz, GA3)
ok = True
for co in GA3:
    d = psub(livep[co], PAIRS[co](zg, Lg))
    ok = ok and not d
    print("   pair_%s = [z, L].%s : %s" % (co, co, "EXACT" if not d else poly_str(d)))
print("   all six pairing forms are exact commutator forms: %s" % ok)
print()

print("=" * 92)
print("== B. the core shift, block by block ==")
s, x, y = U6.gen("s"), U6.gen("x"), U6.gen("y")
z0, z1, z2 = ga2("z0"), ga2("z1"), ga2("z2")
cs = shift(P.sqWord(s, x, y), P.sqWord(s * z0, x * z1, y * z2))
_, live = shape(cs, GA2)
fx = foxletter(s, x, y)

CORE_RES = {}
for co in GA2:
    want = padd(pscale(-4, pvar("z1_" + co)), pscale(2, pvar("z2_" + co)))
    if co in PAIRS:
        want = padd(want, PAIRS[co](z0, x), PAIRS[co](z1, fx), PAIRS[co](z2, y))
    CORE_RES[co] = psub(live[co], want)
    print("   [%s] residual after Frobenius + pairings: %d terms" % (co, len(CORE_RES[co])))
print()

print("   --- the class-four rows against GradedGammaTwo, transposed ---")
# gaTwoCorr with (e,f,g)->(f,g,h) and letter columns (a,b,c,d)->(a,b,c,d)   [the toU5L route]
# gaTwoCorr with (e,f,g)->(g,h,i) and letter columns (a,b,c,d)->(b,c,d,e)  [the toU5R route]
W54 = {  # slot -> dressing coordinate (SqU5 naming e,f,g) -> list of (coeff, (v1, v2))
    0: {"e": [(-1, ("s.c", "x.d")), (1, ("s.d", "x.c")), (-4, ("x.c", "x.d")),
              (2, ("x.c", "y.d")), (1, ("y.c", "y.d"))],
        "f": [(8, ("x.a", "x.d")), (-2, ("x.a", "y.d")), (-2, ("x.d", "y.a")),
              (-2, ("y.a", "y.d"))],
        "g": [(1, ("s.a", "x.b")), (-1, ("s.b", "x.a")), (-4, ("x.a", "x.b")),
              (2, ("x.b", "y.a")), (1, ("y.a", "y.b"))]},
    1: {"e": [(3, ("s.c", "x.d")), (-2, ("s.c", "y.d")), (1, ("s.d", "x.c")),
              (-20, ("x.c", "x.d")), (20, ("x.c", "y.d")), (-4, ("y.c", "y.d"))],
        "f": [(2, ("s.a", "s.d")), (-14, ("s.a", "x.d")), (10, ("s.a", "y.d")),
              (-14, ("s.d", "x.a")), (10, ("s.d", "y.a")), (130, ("x.a", "x.d")),
              (-100, ("x.a", "y.d")), (-100, ("x.d", "y.a")), (80, ("y.a", "y.d"))],
        "g": [(-2, ("s.a", "s.b")), (11, ("s.a", "x.b")), (-8, ("s.a", "y.b")),
              (13, ("s.b", "x.a")), (-10, ("s.b", "y.a")), (-110, ("x.a", "x.b")),
              (80, ("x.a", "y.b")), (100, ("x.b", "y.a")), (-76, ("y.a", "y.b"))]},
    2: {"e": [(-2, ("s.c", "y.d")), (1, ("s.d", "y.c"))],
        "f": [(1, ("s.a", "y.d")), (1, ("s.d", "y.a"))],
        "g": [(1, ("s.a", "y.b")), (-2, ("s.b", "y.a"))]},
}
LEFT = {"a": "a", "b": "b", "c": "c", "d": "d", "e": "f", "f": "g", "g": "h"}
RIGHT = {"a": "b", "b": "c", "c": "d", "d": "e", "e": "g", "f": "h", "g": "i"}


def transposed_corr(dic):
    out = {}
    for slot, tab in W54.items():
        for u5co, block in tab.items():
            key = "z%d_%s" % (slot, dic[u5co])
            for c, mon in block:
                m = tuple(sorted(v[0] + "_" + dic[v[2]] for v in mon))
                out.setdefault(key, {})
                out[key][m] = out[key].get(m, 0) + c
    return out


def flatten(byvar):
    out = {}
    for v, blk in byvar.items():
        for mon, c in blk.items():
            key = tuple(sorted(mon + (v,)))
            out[key] = out.get(key, 0) + c
    return {k: v for k, v in out.items() if v}


QUAD_U5 = [(1, ("z0.e", "z1.g")), (-1, ("z0.g", "z1.e")), (10, ("z1.e", "z1.g")),
           (-8, ("z1.e", "z2.g")), (1, ("z2.e", "z2.g"))]


def transposed_quad(dic):
    out = {}
    for c, mon in QUAD_U5:
        m = tuple(sorted(v[0:2] + "_" + dic[v[3]] for v in mon))
        out[m] = out.get(m, 0) + c
    return out


for co, dic in (("m", LEFT), ("n", RIGHT)):
    want = padd(flatten(transposed_corr(dic)), transposed_quad(dic))
    d = psub(CORE_RES[co], want)
    print("   [%s] = gaTwoCorr + gaTwoQuad transposed (%s route): %s"
          % (co, "toU5L" if co == "m" else "toU5R", "VERBATIM" if not d else poly_str(d)))
print()

print("   --- the class-five row: correction and quadratic blocks ---")
d = bydeg(CORE_RES["o"])
QUAD_O = d.get(2, {})
CORR_O = d.get(1, {})
print("   quadratic block: %d terms; correction block: %d terms"
      % (len(QUAD_O), len(CORR_O)))
byvar = {}
for mon, c in CORR_O.items():
    zs = [v for v in mon if is_dress(v)]
    assert len(zs) == 1
    rest = tuple(v for v in mon if not is_dress(v))
    byvar.setdefault(zs[0], {})[rest] = c
print("   correction block, by dressing coordinate: %s"
      % ", ".join("%s:%d" % (v, len(byvar[v])) for v in sorted(byvar)))
qbyvar = {}
for mon, c in QUAD_O.items():
    zs = tuple(sorted(v for v in mon if is_dress(v)))
    rest = tuple(v for v in mon if not is_dress(v))
    qbyvar.setdefault(rest, {})[zs] = c
print("   quadratic block, by FRAME factor:")
for rest in sorted(qbyvar, key=lambda t: (len(t), t)):
    print("     %-12s %d terms" % ("(frame-free)" if not rest else " ".join(rest),
                                   len(qbyvar[rest])))
print()

print("=" * 92)
print("== C. the handle shift, block by block ==")
p, q = U6.gen("p"), U6.gen("q")
zh, wh = ga2("z"), ga2("w")
hs = shift(P.commP(p, q), P.commP(p * zh, q * wh))
_, hlive = shape(hs, GA3)
cc = P.commP(p, q)
HAND_RES = {}
for co in GA3:
    want = psub(PAIRS[co](zh, q), PAIRS[co](wh, p))
    HAND_RES[co] = psub(hlive[co], want)
    print("   [%s] residual after the two pairings: %d terms" % (co, len(HAND_RES[co])))
print()
# candidate: the commutator's own rows against the dressings, plus [z, w]
cand_m = padd(psub(pmul(zh.f, wh.h), pmul(zh.h, wh.f)),
              pmul(cc.f, padd(zh.h, wh.h)), pneg(pmul(cc.h, padd(zh.f, wh.f))))
cand_n = padd(psub(pmul(zh.g, wh.i), pmul(zh.i, wh.g)),
              pmul(cc.g, padd(zh.i, wh.i)), pneg(pmul(cc.i, padd(zh.g, wh.g))))
cand_o = padd(psub(pmul(zh.f, wh.l), pmul(zh.l, wh.f)),
              psub(pmul(zh.j, wh.i), pmul(zh.i, wh.j)),
              pmul(cc.f, padd(zh.l, wh.l)), pneg(pmul(cc.l, padd(zh.f, wh.f))),
              pmul(cc.j, padd(zh.i, wh.i)), pneg(pmul(cc.i, padd(zh.j, wh.j))))
for co, cand in (("m", cand_m), ("n", cand_n), ("o", cand_o)):
    d = psub(HAND_RES[co], cand)
    print("   [%s] residual after [z,w] + commutator-row blocks: %d terms" % (co, len(d)))
    if d:
        show("        left over", d)
print()

print("=" * 92)
print("== D. the collection term ==")
core = ga2("C")
hw = U6.gen("H")
for co in ("a", "b", "c", "d", "e"):
    setattr(hw, co, pzero())
coll = shift(hw * core, core * hw)
dead, live4 = shape(coll, GA4)
print("   gamma_4-shaped: %s" % (not dead))
for co in GA4:
    show("   collection . " + co, live4[co])
