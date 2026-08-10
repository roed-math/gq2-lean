"""W60-STAGE4: the FULL honest census at a candidate class-five sigma point.

The module route of `gam3lib` is fast but indirect.  This script does the load-bearing check
element by element: it enumerates the whole of `gamma_3` of the image by honest closure and
tries EVERY single-slot dressing against the honest relator, at several handle counts.  A point
that passes here has no stage-four hole in the sense wave 59's `scope_probe.py` measured one.
"""
import sys
import os
import random

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))

import u6mat as M                                             # noqa: E402
import modlib as MD                                           # noqa: E402
import gam3lib as G                                           # noqa: E402
import pointlib as P                                          # noqa: E402

SIG = M.sigFiveMark

POINT = os.environ.get("W60_POINT", "cand")
if POINT == "cand":
    X = M.named(a=2, e=5)
    U = M.named(a=6, b=7, c=4, d=1, e=3, g=5, h=5)
    V = M.named(a=6, b=7, c=6, d=1, e=3, f=5, g=3, h=3, i=4)
    Y = M.named(e=2, f=1, g=1, h=1, m=3, n=3)
else:
    vals = [eval(t) for t in POINT.split(";")]
    X, U, V, Y = [tuple(v) for v in vals]

letters = [SIG, X, Y, U, V]
print("== the candidate point ==")
for nm, z in (("sigma", SIG), ("x0", X), ("x1", Y), ("U", U), ("V", V)):
    print("   %-5s = %s" % (nm, M.show(z)))
print()

print("== 1. the two verdicts, at several handle counts ==")
ok = True
for h, jj in ((1, 0), (2, 0), (2, 1), (3, 2), (4, 3)):
    r0 = M.sqRelWord(P.mirTuple(h, jj, SIG, X, Y, U, V))
    r1 = P.residue(SIG, X, Y, U, V, h, jj)
    good = (r0 == M.ONE) and all(r1[k] == 0 for k in range(14)) and (r1[14] % 2 == 1)
    ok = ok and good
    print("   h=%d j=%d : undressed %-6s  dressed %-8s  %s"
          % (h, jj, M.show(r0), M.show(r1), "OK" if good else "BAD"))
print()

print("== 2. the frame hypotheses ==")
print("   every letter has an even (1,2)-column: %s" % all(z[0] % 2 == 0 for z in letters))
print("   every letter has an even (3,4)-column: %s" % all(z[2] % 2 == 0 for z in letters))
blk = M.commP(U, V)
print("   the handle block is live: %s, class-four row %d (odd: %s)"
      % (blk != M.ONE, blk[12], blk[12] % 2 == 1))
print("   the gauge columns x0.b, x0.c, x0.d, x0.f, x0.g = %s"
      % [X[k] for k in (1, 2, 3, 5, 6)])
print("   x1.a, x1.c, x1.d = %s" % [Y[k] for k in (0, 2, 3)])
print("   x0.a even and x0.e odd: %s, %s" % (X[0] % 2 == 0, X[4] % 2 == 1))
print()

print("== 3. the achievable lattices ==")
b3 = G.gamma3_module(letters)
b4 = G.gamma4_module(letters)
g3, g4, g5 = P.gamma_series(letters)
print("   Howell   |gamma_3| = %6d  |gamma_4| = %4d" % (MD.card(b3, 6), MD.card(b4, 6)))
print("   closure  |gamma_3| = %6d  |gamma_4| = %4d  |gamma_5| = %d"
      % (len(g3), len(g4), len(g5)))
print("   the two agree elementwise: %s" % (MD.members(b3, 6) == {G.vec(z) for z in g3}))
odd = [z for z in g3 if z[9] % 2 or z[11] % 2 or z[12] % 2]
print("   members of gamma_3(im) with j, l or m ODD: %d of %d" % (len(odd), len(g3)))
sh = P.gaFour_shaped(g3)
print("   gamma_4-SHAPED members of gamma_3(im): %d (wave 59's point had 512)" % len(sh))
print("   of those, with odd m: %d" % len([z for z in sh if z[12] % 2]))
print()

print("== 4. THE CENSUS: every achievable gamma_3-dressing, every slot, honestly ==")
base = [M.mul(SIG, X), X, Y, U, V]
tot = 0
for i in range(5):
    k = [z for z in sorted(g3) if P.kills(base, i, z)]
    tot += len(k)
    print("   slot %-5s : %5d of %5d achievable gamma_3-dressings kill the dressed frame"
          % (P.SLOT[i], len(k), len(g3)))
    if k:
        print("               e.g. %s" % ", ".join(M.show(z) for z in k[:3]))
print("   TOTAL single-slot stage-four kills: %d of %d   (wave 59: 1280 of 81920)"
      % (tot, 5 * len(g3)))
print()

print("== 5. random five-slot achievable refinements ==")
random.seed(60041)
g3l = sorted(g3)
bad = 0
for _ in range(4000):
    m = [M.mul(base[i], random.choice(g3l)) for i in range(5)]
    if M.sqRelWord(m) == M.ONE:
        bad += 1
print("   4000 random five-slot achievable gamma_3-refinements: %d kills" % bad)
print()

print("== 6. UNRESTRICTED gamma_3-dressings do kill, so achievability is load-bearing ==")
hits = 0
ex = []
for mm in range(8):
    for nn in range(8):
        z = M.named(m=mm, n=nn)
        for i in range(5):
            if P.kills(base, i, z):
                hits += 1
                if len(ex) < 4:
                    ex.append((P.SLOT[i], M.show(z)))
print("   %d of the 320 unrestricted gamma_4-shaped single-slot moves kill: %s" % (hits, ex))
print()
print("VERDICT: the point is %s" % ("CLEAN" if ok and tot == 0 and bad == 0 else "NOT clean"))
