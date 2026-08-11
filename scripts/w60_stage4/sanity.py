"""W60-STAGE4 step 0: reproduce the wave-59 point and its hole with this lane's machinery.

If the cascade solve and the censuses here cannot re-derive wave 59's own numbers, nothing
downstream is worth reading.

BRACKET CONVENTION.  [NONE]
This script computes no commutators, so the convention does not arise.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""
import sys
import os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))

import u6mat as M                                             # noqa: E402
import pointlib as P                                          # noqa: E402

sigma, X, Y, U, V = M.sigFiveMark, M.sepX, M.sepY, M.sepU, M.sepV

print("== the wave-59 point ==")
print("   sigma = %s" % M.show(sigma))
print("   x0    = %s" % M.show(X))
print("   x1    = %s" % M.show(Y))
print("   U     = %s" % M.show(U))
print("   V     = %s" % M.show(V))
print()
for h, jj in ((1, 0), (2, 0), (2, 1), (3, 2)):
    r0 = M.sqRelWord(P.mirTuple(h, jj, sigma, X, Y, U, V))
    r1 = P.residue(sigma, X, Y, U, V, h, jj)
    print("   h=%d j=%d : undressed %s   dressed %s" % (h, jj, M.show(r0), M.show(r1)))
print()

print("== the cascade solve finds this Y among its solutions ==")
sols = P.solve_y(sigma, X, U, V)
print("   %d solutions Y for the undressed frame at h=1" % len(sols))
print("   the committed forceY is among them: %s" % (Y in sols))
odd = [y for y in sols if P.residue(sigma, X, y, U, V)[14] % 2]
print("   %d of them leave an ODD class-five residue under the a0=a1 dressing" % len(odd))
print("   every solution's dressed relator is central: %s"
      % all(all(P.residue(sigma, X, y, U, V)[k] == 0 for k in range(14)) for y in sols))
print()

print("== the hole, re-measured ==")
g3, g4, g5 = P.gamma_series([sigma, X, Y, U, V])
print("   |gamma_3| = %d  |gamma_4| = %d  |gamma_5| = %d" % (len(g3), len(g4), len(g5)))
c3, c4, ex, _ = P.hole_report(sigma, X, Y, U, V, g3, g4)
for i in range(5):
    print("   slot %-5s : %5d of %5d gamma_3-dressings kill,  %3d of %3d gamma_4-dressings kill"
          % (P.SLOT[i], c3[i], len(g3), c4[i], len(g4)))
    if ex[i]:
        print("               e.g. %s" % ", ".join(M.show(z) for z in ex[i]))
print("   TOTAL gamma_3-level single-slot kills: %d of %d" % (sum(c3), 5 * len(g3)))
print()
sh = P.gaFour_shaped(g3)
print("   gamma_4-SHAPED members of gamma_3(im): %d" % len(sh))
print("   of which class-four coordinate m is odd: %d"
      % len([z for z in sh if z[12] % 2]))
print("   of which n is odd: %d" % len([z for z in sh if z[13] % 2]))
print("   gamma_4-shaped members of gamma_4(im) with odd m or n: %d"
      % len([z for z in P.gaFour_shaped(g4) if z[12] % 2 or z[13] % 2]))
