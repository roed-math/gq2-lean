"""W61-WIDER step 1: the `gamma_2`-level translation identity at class five, derived.

One filtration step wider than `GradedFiveStageFour`'s stage-four identity.  A `gamma_2`
dressing disturbs the class-two rows as well, and - unlike the stage-four case - the
commutator subgroup `[gamma_2, gamma_2] = gamma_4` does NOT vanish in the class-five carrier,
so the shift carries a genuinely quadratic block.  This is the wave-54 problem
(`GradedGammaTwo.gaTwoQuad`) one class up.

Everything is derived with the exact integer polynomial engine of `scripts/w59_defect5/`
(`u6poly.py`), never transcribed from Lean; `validate_wider.py` re-checks every emitted form
against honest 6 x 6 collection over four rings at handle counts 0..4 before transcription.

Sections
  0. the shape of `gamma_2` and its commutator subgroup;
  1. the pairing forms: the class-3/4/5 commutator forms of a `gamma_2` element vs a letter;
  2. the handle commutator under a two-sided `gamma_2`-dressing;
  3. the core word under a three-slot `gamma_2`-dressing, split into blocks;
  4. the collection term (core shift past handle word) and the assembled relator shift;
  5. sanity: the `gamma_3` specialisation reproduces `GradedFiveStageFour`.
"""
import sys
import os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_defect5"))

import u6poly as P                                            # noqa: E402
from u6poly import U6, padd, psub, pmul, pneg, pscale, pzero, pvar, poly_str  # noqa: E402

COORDS = P.COORDS
GA2 = ["f", "g", "h", "i", "j", "k", "l", "m", "n", "o"]      # live coords of gamma_2
GA3 = ["j", "k", "l", "m", "n", "o"]
GA4 = ["m", "n", "o"]
ABEL = ["a", "b", "c", "d", "e"]


def ga2(prefix):
    """A generic `gamma_2`-shaped element: ten live coordinates."""
    return U6(**{co: pvar(prefix + "_" + co) for co in GA2})


def ga3(prefix):
    return U6(**{co: pvar(prefix + "_" + co) for co in GA3})


def shift(before, after):
    """`before^{-1} * after`, the element by which a dressing moves a word."""
    return before.inv() * after


def shape(z, live):
    dead = [co for co in COORDS if co not in live and getattr(z, co)]
    return dead, {co: getattr(z, co) for co in live}


def show(name, p):
    print("   %s = %s" % (name, poly_str(p)))


def nterms(p):
    return len(p)


def is_dress(v):
    return v.split("_")[0] in ("z0", "z1", "z2", "z", "w", "zu", "zv")


def split_by_dress_degree(p):
    """Split a polynomial by how many dressing variables each monomial carries."""
    out = {}
    for mon, c in p.items():
        d = sum(1 for v in mon if is_dress(v))
        out.setdefault(d, {})[mon] = c
    return out


print("=" * 92)
print("== 0. the shape of gamma_2 and of [gamma_2, gamma_2] ==")
p2, q2 = ga2("z"), ga2("w")
prod = p2 * q2
dead, _ = shape(prod, GA2)
print("   gamma_2 is a subgroup (product stays gamma_2-shaped): %s" % (not dead))
cc = P.commP(p2, q2)
dead, live = shape(cc, GA4)
print("   [gamma_2, gamma_2] is gamma_4-shaped: %s" % (not dead))
for co in GA4:
    show("   [z, w] . " + co, live[co])
ccc = P.commP(cc, ga2("v"))
print("   [[gamma_2, gamma_2], gamma_2] = 1 (so the shift is at most QUADRATIC): %s"
      % ccc.is_zero())
cl = P.commP(cc, U6.gen("L"))
dead, live = shape(cl, ["o"])
print("   [[gamma_2, gamma_2], letter] is central (gamma_5-shaped): %s" % (not dead))
show("   [[z, w], L] . o", live["o"])
print()

print("=" * 92)
print("== 1. the pairing forms: [gamma_2-element, letter] coordinate by coordinate ==")
z = ga2("z")
L = U6.gen("L")
cz = P.commP(z, L)
deadp, livep = shape(cz, GA3)
print("   [gamma_2, letter] is gamma_3-shaped: %s" % (not deadp))
PAIR = {}
for co in GA3:
    PAIR[co] = livep[co]
    print("   [%s] %d terms" % (co, nterms(livep[co])))
    show("     pair_" + co, livep[co])
print()


def pair(zz, LL, co):
    """The class-`co` pairing form of a gamma_2 dressing `zz` against a letter `LL`,
    obtained by substituting into the generic form PAIR[co]."""
    sub = {}
    for c in GA2:
        sub["z_" + c] = getattr(zz, c)
    for c in COORDS:
        sub["L_" + c] = getattr(LL, c)
    out = {}
    for mon, coef in PAIR[co].items():
        term = {(): coef}
        for v in mon:
            term = pmul(term, sub[v])
        out = padd(out, term)
    return out


def foxletter(s, x, y):
    """`10 x - s - 8 y` columnwise."""
    return U6(**{co: padd(pscale(10, getattr(x, co)), pneg(getattr(s, co)),
                          pscale(-8, getattr(y, co))) for co in COORDS})


print("=" * 92)
print("== 2. the handle commutator under a two-sided gamma_2-dressing ==")
p, q = U6.gen("p"), U6.gen("q")
zh, wh = ga2("z"), ga2("w")
hs = shift(P.commP(p, q), P.commP(p * zh, q * wh))
dead, live = shape(hs, GA3)
print("   dead coordinates outside gamma_3: %s" % (dead if dead else "NONE (gamma_3-shaped)"))
HANDLE = {}
for co in GA3:
    HANDLE[co] = live[co]
    byd = split_by_dress_degree(live[co])
    print("   [%s] %d terms; degree-1 in dressings: %d, degree-2: %d"
          % (co, nterms(live[co]), nterms(byd.get(1, {})), nterms(byd.get(2, {}))))
print()
for co in GA3:
    # try: pair(z, q) - pair(w, p) + remainder
    want = psub(pair(zh, q, co), pair(wh, p, co))
    rem = psub(live[co], want)
    print("   [%s] handle shift  -  ( pair(z,q) - pair(w,p) ) :  %d terms" % (co, nterms(rem)))
    if rem:
        show("        remainder", rem)
print()

print("=" * 92)
print("== 3. the core word under a three-slot gamma_2-dressing ==")
s, x, y = U6.gen("s"), U6.gen("x"), U6.gen("y")
z0, z1, z2 = ga2("z0"), ga2("z1"), ga2("z2")
cs = shift(P.sqWord(s, x, y), P.sqWord(s * z0, x * z1, y * z2))
dead, live = shape(cs, GA2)
print("   dead coordinates outside gamma_2: %s" % (dead if dead else "NONE (gamma_2-shaped)"))
for co in GA2:
    byd = split_by_dress_degree(live[co])
    print("   [%s] %d terms, degree %d; dressing-degree 1: %d, 2: %d"
          % (co, nterms(live[co]), P.pdeg(live[co]), nterms(byd.get(1, {})),
             nterms(byd.get(2, {}))))
print()

fx = foxletter(s, x, y)
CORE = {}
print("   --- class-two rows: pure Frobenius? ---")
for co in ("f", "g", "h", "i"):
    want = padd(pscale(-4, pvar("z1_" + co)), pscale(2, pvar("z2_" + co)))
    rem = psub(live[co], want)
    print("   [%s] -4 z1.%s + 2 z2.%s : %s" % (co, co, co, "EXACT" if not rem
                                               else "residual " + poly_str(rem)))
print()
print("   --- class-three rows: Frobenius + three Fox pairings? ---")
for co in ("j", "k", "l"):
    want = padd(pscale(-4, pvar("z1_" + co)), pscale(2, pvar("z2_" + co)),
                pair(z0, x, co), pair(z1, fx, co), pair(z2, y, co))
    rem = psub(live[co], want)
    CORE[co] = rem
    print("   [%s] residual after Frobenius + pairings: %d terms" % (co, nterms(rem)))
    if rem:
        show("        residual", rem)
print()
print("   --- class-four and class-five rows ---")
for co in ("m", "n", "o"):
    want = padd(pscale(-4, pvar("z1_" + co)), pscale(2, pvar("z2_" + co)),
                pair(z0, x, co), pair(z1, fx, co), pair(z2, y, co))
    rem = psub(live[co], want)
    CORE[co] = rem
    byd = split_by_dress_degree(rem)
    print("   [%s] residual after Frobenius + pairings: %d terms  (deg-1 %d, deg-2 %d)"
          % (co, nterms(rem), nterms(byd.get(1, {})), nterms(byd.get(2, {}))))
    print("        QUADRATIC part (%d terms):" % nterms(byd.get(2, {})))
    show("          ", byd.get(2, {}))
    corr = byd.get(1, {})
    print("        CORRECTION part (%d terms), grouped by dressing coordinate:"
          % nterms(corr))
    byvar = {}
    for mon, c in corr.items():
        zs = [v for v in mon if is_dress(v)]
        assert len(zs) == 1, (mon, c)
        rest = tuple(v for v in mon if not is_dress(v))
        byvar.setdefault(zs[0], {})[rest] = c
    for v in sorted(byvar):
        show("          %s *" % v, byvar[v])
    assert not byd.get(0, {}) and not byd.get(3, {}), "unexpected dressing degree"
    print()

print("=" * 92)
print("== 4. the collection term: the core shift past the handle word ==")
core = ga2("C")
hw = U6.gen("H")
for co in ABEL:
    setattr(hw, co, pzero())
coll = shift(hw * core, core * hw)
dead, live4 = shape(coll, GA4)
print("   collection term is gamma_4-shaped: %s" % (not dead))
for co in GA4:
    show("   collection . " + co, live4[co])
print()

print("=" * 92)
print("== 5. sanity: the gamma_3 specialisation reproduces GradedFiveStageFour ==")
z0f, z1f, z2f = ga2("z0"), ga2("z1"), ga2("z2")
for zz in (z0f, z1f, z2f):
    for co in ("f", "g", "h", "i"):
        setattr(zz, co, pzero())
cs3 = shift(P.sqWord(s, x, y), P.sqWord(s * z0f, x * z1f, y * z2f))
dead, live3 = shape(cs3, GA3)
print("   gamma_3 dressing gives a gamma_3-shaped core shift: %s" % (not dead))


def foxpairL3(zz, LL):
    return psub(pmul(zz.j, LL.d), pmul(zz.k, LL.a))


def foxpairR3(zz, LL):
    return psub(pmul(zz.k, LL.e), pmul(zz.l, LL.b))


def foxpair3(zz, LL):
    return padd(pmul(zz.m, LL.e), pneg(pmul(zz.n, LL.a)),
                pmul(zz.j, LL.i), pneg(pmul(zz.l, LL.f)),
                pmul(zz.l, pmul(LL.a, LL.b)), pneg(pmul(zz.k, pmul(LL.a, LL.e))))


for co, pr in (("m", foxpairL3), ("n", foxpairR3)):
    want = padd(pscale(-4, pvar("z1_" + co)), pscale(2, pvar("z2_" + co)),
                pr(z0f, x), pr(z1f, fx), pr(z2f, y))
    print("   [%s] matches gaThreeCore: %s" % (co, not psub(live3[co], want)))
print("   [j,k,l] pure Frobenius: %s"
      % all(not psub(live3[co], padd(pscale(-4, pvar("z1_" + co)), pscale(2, pvar("z2_" + co))))
            for co in ("j", "k", "l")))
