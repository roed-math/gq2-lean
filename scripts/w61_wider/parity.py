"""W61-WIDER step 5: is the quadratic block EVEN on the achievable lattice?

The class-four precedent (`GradedGammaTwo`, wave 54) found that its quadratic block `gaTwoQuad`
is even at every point of the achievable lattice, because every generator of `gamma_2(im Phi)`
has an even `g`-column; so the class-four `gamma_2` transport is affine mod two.  This file asks
the same question one class up, with the class-five lattice wave 60 proved:

    frame letters in  M_1 = { 2 | z.a  and  2 | z.c }                    (`stageN1`)
    dressings     in  M_2 = { gamma_2, 2 | z.f, 2 | z.h, 2 | z.j }       (`stageN2`)

and `GradedFiveStageFour.stageN2_of_commutator` proves `[M_1, M_1] <= M_2`, i.e. M_2 really is
the honest achievable `gamma_2` lattice at such a point, not a declared one.

Method: substitute `frame.a = 2 A`, `frame.c = 2 C`, `dress.f = 2 F`, `dress.h = 2 H`,
`dress.j = 2 J` into the class-five row of the shift, reduce the coefficients mod 2, and read
off what survives.  Exact integer arithmetic throughout; nothing is sampled.
"""
import sys
import os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_defect5"))

import u6poly as P                                            # noqa: E402
from u6poly import U6, padd, psub, pmul, pneg, pscale, pzero, pvar, poly_str  # noqa: E402
import wlib as A                                              # noqa: E402

COORDS = P.COORDS
GA2 = ["f", "g", "h", "i", "j", "k", "l", "m", "n", "o"]

DRESS_PREFIX = ("z",)


def is_dress(v):
    return v.startswith("z")


def subst(p, rules):
    """Substitute variable -> polynomial."""
    out = {}
    for mon, c in p.items():
        term = {(): c}
        for v in mon:
            term = pmul(term, rules.get(v, pvar(v)))
        out = padd(out, term)
    return out


def mod2(p):
    return {mon: c % 2 for mon, c in p.items() if c % 2}


def rules_for(rank):
    r = {}
    for i in range(rank):
        r["m%d_a" % i] = pscale(2, pvar("A%d" % i))
        r["m%d_c" % i] = pscale(2, pvar("C%d" % i))
        r["z%d_f" % i] = pscale(2, pvar("F%d" % i))
        r["z%d_h" % i] = pscale(2, pvar("H%d" % i))
        r["z%d_j" % i] = pscale(2, pvar("J%d" % i))
    return r


print("=" * 92)
print("== the class-five row of the gamma_2 shift, on the achievable lattice ==")
print()
for h in (0, 1, 2):
    rank = 3 + 2 * h
    m = [(U6.gen("m%d" % i), U6(**{co: pvar("z%d_%s" % (i, co)) for co in GA2}))
         for i in range(rank)]
    G = A.relShift(m, h)
    o = G.o
    r = rules_for(rank)
    red = mod2(subst(o, r))
    deg2 = {mon: c for mon, c in red.items() if sum(1 for v in mon if is_dress(v)) >= 2}
    deg1 = {mon: c for mon, c in red.items() if sum(1 for v in mon if is_dress(v)) == 1}
    deg0 = {mon: c for mon, c in red.items() if sum(1 for v in mon if is_dress(v)) == 0}
    print("   h = %d :  shift.o has %d terms; mod 2 on the lattice %d terms remain"
          % (h, len(o), len(red)))
    print("            dressing-degree 0: %d,  1: %d,  >= 2: %d"
          % (len(deg0), len(deg1), len(deg2)))
    print("            *** QUADRATIC BLOCK EVEN ON THE LATTICE: %s ***"
          % ("YES" if not deg2 else "NO, %d terms survive" % len(deg2)))
    if deg2:
        print("            survivors: %s" % poly_str(deg2))
    print("            surviving AFFINE channels (%d):" % len(deg1))
    # group the affine survivors by dressing coordinate
    by = {}
    for mon, c in deg1.items():
        zs = [v for v in mon if is_dress(v)]
        rest = tuple(v for v in mon if not is_dress(v))
        by.setdefault(zs[0], {})[rest] = c
    for v in sorted(by):
        print("              %-8s * ( %s )" % (v, poly_str(by[v])))
    print()

print("=" * 92)
print("== the same question for the two class-four rows ==")
for h in (1,):
    rank = 3 + 2 * h
    m = [(U6.gen("m%d" % i), U6(**{co: pvar("z%d_%s" % (i, co)) for co in GA2}))
         for i in range(rank)]
    G = A.relShift(m, h)
    r = rules_for(rank)
    for co in ("m", "n"):
        red = mod2(subst(getattr(G, co), r))
        deg2 = {mon: c for mon, c in red.items()
                if sum(1 for v in mon if is_dress(v)) >= 2}
        print("   [%s] mod 2 on the lattice: %d terms, of which quadratic %d"
              % (co, len(red), len(deg2)))
        if deg2:
            print("        quadratic survivors: %s" % poly_str(deg2))
print()

print("=" * 92)
print("== what the surviving affine channels are, structurally ==")
print("""   Every surviving term of the class-five row is one dressing coordinate against one
   frame quantity, and there are exactly THREE channels, the three terms of the class-five
   pairing form the frame does not already close:

       z.m * L.e        class-four dressing coordinate against the letter's fifth column
       z.i * L.j        class-two  dressing coordinate against the letter's class-three row
       z.l * L.f        class-three dressing coordinate against the letter's class-two row

   plus, from the handle block, the same three channels with the opposite handle letter, and
   the cross term  C.j * H.i  (killed: C.j is even on the lattice).  The class-four rows have
   the single channel  z.j * L.d  /  z.k * L.e  respectively.""")
