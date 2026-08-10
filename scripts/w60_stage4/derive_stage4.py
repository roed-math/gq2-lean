"""W60-STAGE4 step 2 (route a): the STAGE-FOUR translation identity at class five, derived.

Wave 59's class-five translation identity dresses every slot by a `gamma_4`-shaped element and
moves the relator centrally.  One filtration step wider - `gamma_3`-shaped dressings, the moves
that already disturb the class-four rows - the motion is no longer central and no longer
affine: the class-five row picks up terms quadratic in the dressings.  This is exactly the
step wave 54 took at class four (`GradedGammaTwo`, `gaTwoCorr` and `gaTwoQuad`), one class up.

Everything is derived with the exact integer polynomial engine of `scripts/w59_defect5/`
(`u6poly.py`), never transcribed from Lean, and `validate_stage4.py` re-checks every emitted
form against honest 6 x 6 collection over several rings before anything is written down.

Sections
  1. the commutator under a two-sided `gamma_3`-dressing: the handle shift;
  2. the core word under a three-slot `gamma_3`-dressing: the core shift;
  3. the split of the core shift's class-five row into Fox pairing, correction and quadratic
     blocks, matched against the class-four precedent;
  4. the collection term, and the five-slot relator shift;
  5. the Lean transcription.
"""
import sys
import os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_defect5"))

import u6poly as P                                            # noqa: E402
from u6poly import U6, padd, psub, pmul, pneg, pscale, pzero, pvar, poly_str  # noqa: E402

COORDS = P.COORDS
GA3 = ["j", "k", "l", "m", "n", "o"]                          # the live coordinates of gamma_3
GA4 = ["m", "n", "o"]


def ga3(prefix):
    """A generic `gamma_3`-shaped element."""
    return U6(**{co: pvar(prefix + "_" + co) for co in GA3})


def shift(before, after):
    """`before^{-1} * after`, the element by which a dressing moves a word."""
    return before.inv() * after


def shape(z, live):
    """Check that only `live` coordinates are non-zero; return the live ones."""
    dead = [co for co in COORDS if co not in live and getattr(z, co)]
    return dead, {co: getattr(z, co) for co in live}


def show(name, p, namer=lambda v: v):
    print("   %s = %s" % (name, poly_str(p, namer)))


def nterms(p):
    return len(p)


print("=" * 88)
print("== 1. the handle commutator under a two-sided gamma_3-dressing ==")
p, q = U6.gen("p"), U6.gen("q")
z, w = ga3("z"), ga3("w")
hs = shift(P.commP(p, q), P.commP(p * z, q * w))
dead, live = shape(hs, GA4)
print("   dead coordinates outside gamma_4: %s" % (dead if dead else "NONE (gamma_4-shaped)"))
for co in GA4:
    print("   [%s] %d terms" % (co, nterms(live[co])))
    show("     ", live[co])
print()

print("=" * 88)
print("== 2. the core word under a three-slot gamma_3-dressing ==")
s, x, y = U6.gen("s"), U6.gen("x"), U6.gen("y")
z0, z1, z2 = ga3("z0"), ga3("z1"), ga3("z2")
cs = shift(P.sqWord(s, x, y), P.sqWord(s * z0, x * z1, y * z2))
dead, live = shape(cs, GA3)
print("   dead coordinates outside gamma_3: %s" % (dead if dead else "NONE (gamma_3-shaped)"))
for co in GA3:
    print("   [%s] %d terms, degree %d" % (co, nterms(live[co]), P.pdeg(live[co])))
print()
for co in ("j", "k", "l"):
    show("   core shift . " + co, live[co])
print()
for co in ("m", "n"):
    show("   core shift . " + co, live[co])
print()

print("=" * 88)
print("== 3. the class-five row of the core shift, split into blocks ==")
o = live["o"]
print("   total: %d terms, degree %d" % (nterms(o), P.pdeg(o)))

# --- block A: the Frobenius weights on the exponent slots
frob = padd(pscale(-4, pvar("z1_o")), pscale(2, pvar("z2_o")))


def foxpair(zz, L):
    """The class-five graded Fox pairing of a `gamma_3`-element against a letter: the exact
    transposition of `GradedGammaTwo.gaTwoPair` under the dictionary

        class-four (SqU5)   e  f  g  |  h  i  |  j        letter columns  a  b  c  d  |  e  g
        class-five (SqU6)   j  k  l  |  m  n  |  o                        a  b  .  e  |  f  i

    i.e. the dressing's class-`c` data one class deeper and the letter's outermost columns one
    further out.  The last two terms are the ones wave 54 folded into its pairing rather than
    into its correction; keeping the same convention is what makes the correction blocks below
    match `gaTwoCorr` verbatim. """
    return padd(pmul(zz.m, L.e), pneg(pmul(zz.n, L.a)),
                pmul(zz.j, L.i), pneg(pmul(zz.l, L.f)),
                pmul(zz.l, pmul(L.a, L.b)), pneg(pmul(zz.k, pmul(L.a, L.e))))


def foxpairL(zz, L):
    """The class-four LEFT pairing: `GradedGammaTwo.gaTwoPairL` one class up."""
    return psub(pmul(zz.j, L.d), pmul(zz.k, L.a))


def foxpairR(zz, L):
    """…and the RIGHT one, `gaTwoPairR` one class up."""
    return psub(pmul(zz.k, L.e), pmul(zz.l, L.b))


def foxletter(s, x, y):
    """`10 x - s - 8 y` columnwise: the `x0`-slot's Fox letter, as in the committed
    `conFiveShift` and `GradedGammaTwo.sqFoxX`."""
    return U6(**{co: padd(pscale(10, getattr(x, co)), pneg(getattr(s, co)),
                          pscale(-8, getattr(y, co))) for co in COORDS})


fx = foxletter(s, x, y)
fox = padd(foxpair(z0, x), foxpair(z1, fx), foxpair(z2, y))
rem = psub(o, padd(frob, fox))
print("   after removing the Frobenius part and the three Fox pairings: %d terms, degree %d"
      % (nterms(rem), P.pdeg(rem)))

# --- block C: the part quadratic in the dressings (no frame variable at all)
quad = {mon: c for mon, c in rem.items()
        if all(v.startswith("z0_") or v.startswith("z1_") or v.startswith("z2_") for v in mon)}
corr = {mon: c for mon, c in rem.items() if mon not in quad}
print()
print("   QUADRATIC block (dressings only): %d terms" % nterms(quad))
show("     quad", quad)
print()
print("   CORRECTION block (dressings against the frame): %d terms, degree %d"
      % (nterms(corr), P.pdeg(corr)))
# group the correction by which dressing coordinate it multiplies
byvar = {}
for mon, c in corr.items():
    zs = [v for v in mon if v.startswith("z")]
    assert len(zs) == 1, (mon, c)
    rest = tuple(v for v in mon if not v.startswith("z"))
    byvar.setdefault(zs[0], {})[rest] = c
for v in sorted(byvar):
    show("     %s *" % v, byvar[v])
print()

print("=" * 88)
print("== 3b. the class-four rows of the core shift, as Fox pairings ==")
for co, pr in (("m", foxpairL), ("n", foxpairR)):
    want = padd(pscale(-4, pvar("z1_" + co)), pscale(2, pvar("z2_" + co)),
                pr(z0, x), pr(z1, fx), pr(z2, y))
    print("   [%s] Frobenius + the three pairings against (x0, foxletter, x1): %s"
          % (co, "EXACT" if not psub(live[co], want) else
             "residual " + poly_str(psub(live[co], want))))
print()

print("=" * 88)
print("== 3c. the correction, against the class-four precedent gaTwoCorr, transposed ==")
DICT = {"c": "d", "d": "e", "e": "f", "g": "i", "a": "a", "b": "b"}
W54 = {
    "e": [(-1, ("s.c", "x.d")), (1, ("s.d", "x.c")), (-4, ("x.c", "x.d")),
          (2, ("x.c", "y.d")), (1, ("y.c", "y.d"))],
    "f": [(8, ("x.a", "x.d")), (-2, ("x.a", "y.d")), (-2, ("x.d", "y.a")),
          (-2, ("y.a", "y.d"))],
    "g": [(1, ("s.a", "x.b")), (-1, ("s.b", "x.a")), (-4, ("x.a", "x.b")),
          (2, ("x.b", "y.a")), (1, ("y.a", "y.b"))],
}
W54_1 = {
    "e": [(3, ("s.c", "x.d")), (-2, ("s.c", "y.d")), (1, ("s.d", "x.c")),
          (-20, ("x.c", "x.d")), (20, ("x.c", "y.d")), (-4, ("y.c", "y.d"))],
    "f": [(2, ("s.a", "s.d")), (-14, ("s.a", "x.d")), (10, ("s.a", "y.d")),
          (-14, ("s.d", "x.a")), (10, ("s.d", "y.a")), (130, ("x.a", "x.d")),
          (-100, ("x.a", "y.d")), (-100, ("x.d", "y.a")), (80, ("y.a", "y.d"))],
    "g": [(-2, ("s.a", "s.b")), (11, ("s.a", "x.b")), (-8, ("s.a", "y.b")),
          (13, ("s.b", "x.a")), (-10, ("s.b", "y.a")), (-110, ("x.a", "x.b")),
          (80, ("x.a", "y.b")), (100, ("x.b", "y.a")), (-76, ("y.a", "y.b"))],
}
W54_2 = {
    "e": [(-2, ("s.c", "y.d")), (1, ("s.d", "y.c"))],
    "f": [(1, ("s.a", "y.d")), (1, ("s.d", "y.a"))],
    "g": [(1, ("s.a", "y.b")), (-2, ("s.b", "y.a"))],
}
MAP = {"e": "j", "f": "k", "g": "l"}


def transpose(block):
    out = {}
    for c, mon in block:
        key = tuple(sorted(v[0] + "_" + DICT[v[2]] for v in mon))
        out[key] = out.get(key, 0) + c
    return {k: v for k, v in out.items() if v}


ok = True
for slot, tab in ((0, W54), (1, W54_1), (2, W54_2)):
    for u5co, u6co in MAP.items():
        want = transpose(tab[u5co])
        got = byvar.get("z%d_%s" % (slot, u6co), {})
        same = (want == got)
        ok = ok and same
        print("   z%d block on %s : %s" % (slot, u6co, "VERBATIM" if same else "DIFFERS"))
        if not same:
            print("        want %s" % poly_str(want))
            print("        got  %s" % poly_str(got))
print("   => the class-five stage-four correction is `gaTwoCorr` transposed: %s" % ok)
print()

print("=" * 88)
print("== 4. the five-slot relator shift ==")
# The core shift is gamma_3-shaped and the handle word has zero abelian columns, so moving the
# core shift past the handle word costs one central collection term.
core = cs
hw = U6.gen("H")
for co in ("a", "b", "c", "d", "e"):
    setattr(hw, co, pzero())
coll = shift(hw * core, core * hw)
dead, live5 = shape(coll, ["o"])
print("   the collection term core-shift-past-handle-word is central: %s"
      % ("yes" if not dead else "NO, live at %s" % dead))
show("   collection", live5["o"])
print()

print("=" * 88)
print("== 5. sanity: the gamma_4 specialisation reproduces the committed class-five identity ==")
z0f, z1f, z2f = ga3("z0"), ga3("z1"), ga3("z2")
for zz in (z0f, z1f, z2f):
    zz.j = zz.k = zz.l = pzero()
cs4 = shift(P.sqWord(s, x, y), P.sqWord(s * z0f, x * z1f, y * z2f))
want_m = padd(pscale(-4, pvar("z1_m")), pscale(2, pvar("z2_m")))
want_n = padd(pscale(-4, pvar("z1_n")), pscale(2, pvar("z2_n")))
want_o = padd(pscale(-4, pvar("z1_o")), pscale(2, pvar("z2_o")),
              psub(pmul(x.e, pvar("z0_m")), pmul(x.a, pvar("z0_n"))),
              psub(pmul(padd(pscale(10, x.e), pneg(s.e), pscale(-8, y.e)), pvar("z1_m")),
                   pmul(padd(pscale(10, x.a), pneg(s.a), pscale(-8, y.a)), pvar("z1_n"))),
              psub(pmul(y.e, pvar("z2_m")), pmul(y.a, pvar("z2_n"))))
print("   m row matches GradedFiveDefect.SqU6.sqWord_mul_gaFour : %s"
      % (not psub(cs4.m, want_m)))
print("   n row matches                                        : %s"
      % (not psub(cs4.n, want_n)))
print("   o row matches                                        : %s"
      % (not psub(cs4.o, want_o)))
print("   j, k, l rows vanish                                  : %s"
      % (not cs4.j and not cs4.k and not cs4.l))
