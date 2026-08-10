"""W60-STAGE4 step 1b: the wave-59 point, perturbed one column at a time.

The wave-59 hole has an exact mechanism.  Its killing dressing is `[[sigma, U], x1]`, whose
class-three part vanishes because the gauge forces `x1.a = x1.c = x1.d = 0`, and whose
class-four coordinate is

    [sigma, U].f * x1.h = (sigma.a * U.b - sigma.b * U.a) * x1.h = -U.a * x1.h,

odd because `U.a` and `x1.h` are both odd.  `x1.h` cannot be made even: the residue's measured
parity is `x0.a * x1.g * x1.i + x0.e * x1.f * x1.h`, and on the gauge (`x0.a` even, `x0.e` odd)
an odd residue FORCES `x1.f` and `x1.h` odd.  So the lever is `U.a`.  This script varies it,
and the `x0` slot's own columns, re-solving the `x1` slot each time with the two-sided cascade.
"""
import sys
import os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))

import u6mat as M                                             # noqa: E402
import gam3lib as G                                           # noqa: E402
import pointlib as P                                          # noqa: E402
from search_point import ga4_kill_slots                       # noqa: E402

SIG = M.sigFiveMark
X0, U0, V0 = M.sepX, M.sepU, M.sepV


def weight(p):
    return sum(1 for x in p if x)


def verdict(X, U, V, ylimit=48):
    """The sparsest `x1` among the first `ylimit` two-sided solutions, and its hole."""
    best = None
    for Y in P.solve_y_central(SIG, X, U, V, limit=ylimit):
        if any(z[2] % 2 for z in (SIG, X, Y, U, V)):
            continue
        res = P.residue(SIG, X, Y, U, V)[14]
        b3 = G.gamma3_module([SIG, X, Y, U, V])
        shaped = G.ga4_shaped_elements(b3)
        hits = ga4_kill_slots(M.mul(SIG, X), X, Y, U, V, res, shaped)
        cand = (len(hits), weight(Y), Y, res, len(shaped),
                sorted({(m % 2, n % 2) for (m, n, o) in shaped}))
        if best is None or cand[:2] < best[:2]:
            best = cand
    return best


def line(tag, b):
    if b is None:
        print("   %-12s : no live point" % tag)
    else:
        nh, w, Y, res, ns, par = b
        print("   %-12s : ga4-shaped kills %2d, |shaped|=%4d, parities %s, residue %d"
              % (tag, nh, ns, par, res))
        print("   %-12s   x1 = %s" % ("", M.show(Y)))


print("== baseline: the wave-59 point ==")
line("wave 59", verdict(X0, U0, V0))
print()

print("== U with its a-column changed (everything else as wave 59) ==")
for a in range(8):
    line("U.a=%d" % a, verdict(X0, M.named(a=a, c=2, d=3, f=3, g=2, h=2, i=2), V0))
print()

print("== V with its a-column changed ==")
for a in range(8):
    line("V.a=%d" % a, verdict(X0, U0, M.named(a=a, d=1, e=2, f=3, g=2, h=3, i=3)))
print()

print("== both handle letters with even a-columns ==")
for ua in (0, 2, 4, 6):
    for va in (0, 2):
        line("U.a=%d V.a=%d" % (ua, va),
             verdict(X0, M.named(a=ua, c=2, d=3, f=3, g=2, h=2, i=2),
                     M.named(a=va, d=1, e=2, f=3, g=2, h=3, i=3)))
