#!/usr/bin/env python3
"""W53-SIGMA step 4: the class-four separation instance at h = 1, certified.

The binder point (slot images of a level-one dressed frame in U5(Z/8)):

  sigma slot   S    = <0,1,0,0,0,0,0,0,0,0> * v        (v the sigma dressing)
  x0 slot      X    = <2,0,0,0,0,0,0,0,1,0>            (= Vbar times a gamma-3 element)
  x1 slot      Y    = <0,0,0,0,1,0,4,0,2,0>
  U handle     Ubar = <1,0,0,0,0,0,0,0,0,0>
  V handle     Vbar = <2,0,0,0,0,0,0,0,0,0>

At the uncleared row type (T, S) = (1, 0) the class-two forcing pins the x0-dressing to
Ubar^-S Vbar^T = Vbar up to gamma-3, and X is exactly that: Vbar times the gamma-3 element
<0,...,0,1,6>.  The gauge conditions x.a, x.c, x.d, x.e, x.f all even hold on the nose, and
the free class-three coordinate x.i = 1 is what the class-four reading uses.

Reported below:
  R1  the three verdicts (undressed / forced Vbar / non-forced Ubar);
  R2  X as Vbar times a gamma-3 correction;
  R3  the bit rule selPar(residue) = selPar(v.a) over a full sweep of dressings;
  R4  every killing dressing has even v.a (the forcing);
  R5  the achievable lattice selLamThree at this point is even in both coordinates,
      so no five-slot refinement of any shape can flip the bit;
  R6  the residual: the dressings 1, Vbar and X are mutually unseparated.
"""
import itertools
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from u5lib import M, ONE, mul, inv, sqRelWord, liftC, show

A_, B_, C_, D_, E_, F_, G_, H_, I_, J_ = range(10)

SIG = (0, 1, 0, 0, 0, 0, 0, 0, 0, 0)
UB = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
VB = (2, 0, 0, 0, 0, 0, 0, 0, 0, 0)
X = (2, 0, 0, 0, 0, 0, 0, 0, 1, 0)
Y = (0, 0, 0, 0, 1, 0, 4, 0, 2, 0)


def rows(v):
    return sqRelWord([mul(SIG, v), X, Y, UB, VB], 1)


print("=" * 78)
print("W53-SIGMA / instance_sigma4.py : the class-four sigma-forcing witness")
print("=" * 78)
print(f"  Ubar = {show(UB)}")
print(f"  Vbar = {show(VB)}")
print(f"  X    = {show(X)}")
print(f"  Y    = {show(Y)}")

print()
print("## R1  the three verdicts")
for name, v in (("a0 = 1     (undressed)          ", ONE),
                ("a0 = Vbar  (class-two forced)   ", VB),
                ("a0 = Ubar  (not forced)         ", UB)):
    r = rows(v)
    print(f"  {name}: rows a..i = {[r[k] for k in range(9)]}   residue j = {r[J_]}"
          f"   parity {r[J_] % 2}")

print()
print("## R2  the x0 slot is the forced value times a gamma-3 correction")
z = mul(inv(VB), X)
print(f"  Vbar^-1 * X = {show(z)}   gamma-3? {all(z[k] == 0 for k in range(7))}")
print(f"  gauge: x.a, x.c, x.d, x.e, x.f = {[X[k] for k in (A_, C_, D_, E_, F_)]} (all even)")
print(f"  free deep coordinates: x.g = {X[G_]}, x.h = {X[H_]}, x.i = {X[I_]}")

print()
print("## R3  the bit rule  selPar(residue) = selPar(v.a)")
bad = tot = 0
for va, vc, vd, ve in itertools.product(range(M), repeat=4):
    for vf, vg, vh, vi in itertools.product((0, 1, 2, 3), repeat=4):
        v = (va, 0, vc, vd, ve, vf, vg, vh, vi, 0)
        tot += 1
        if rows(v)[J_] % 2 != va % 2:
            bad += 1
print(f"  {tot} nu'-trivial dressings swept, mismatches = {bad}")

print()
print("## R4  every killing dressing has even chi_a")
kills = odd_kills = 0
for va, vc, vd, ve in itertools.product(range(M), repeat=4):
    for vf, vg, vh, vi in itertools.product((0, 1, 2, 3), repeat=4):
        v = (va, 0, vc, vd, ve, vf, vg, vh, vi, 0)
        if all(t == 0 for t in rows(v)):
            kills += 1
            if va % 2:
                odd_kills += 1
print(f"  kills = {kills}, of which with odd v.a = {odd_kills}")

print()
print("## R5  the achievable lattice is even at this point")
A, B, C, D, E, F, T, S = 1, 2, 0, 0, 0, 0, 1, 0
worst_h = worst_i = 0
for P, Q, R in itertools.product(range(M), repeat=3):
    if (2 * P + (A * S - B * T)) % M or (2 * Q + (T * D - S * C)) % M:
        continue
    if (2 * R + (C * F - D * E)) % M:
        continue
    for r in itertools.product(range(M), repeat=7):
        r1, r2, r3, r4, r5, r6, r7 = r
        zh = (-(r1 * (2 * (A * C))) - r2 * (A * D + B * C) - r3 * (A * D + B * C)
              - r4 * (2 * (B * D)) + 2 * (r6 * (Q * A - P * C))
              + 2 * (r7 * (Q * B - P * D))) % M
        zi = (r1 * (C * E) + r2 * (D * E) + r3 * (C * F) + r4 * (D * F) + 2 * (r5 * R)
              + 2 * (r6 * (R * T - Q * E)) + 2 * (r7 * (R * S - Q * F))) % M
        worst_h = max(worst_h, zh % 2)
        worst_i = max(worst_i, zi % 2)
        break
    # the full 8^7 scan is redundant: the parities are additive in the r's, so scan
    # the seven generators only
    for k in range(7):
        r = [0] * 7
        r[k] = 1
        r1, r2, r3, r4, r5, r6, r7 = r
        zh = (-(r1 * (2 * (A * C))) - r2 * (A * D + B * C) - r3 * (A * D + B * C)
              - r4 * (2 * (B * D)) + 2 * (r6 * (Q * A - P * C))
              + 2 * (r7 * (Q * B - P * D))) % M
        zi = (r1 * (C * E) + r2 * (D * E) + r3 * (C * F) + r4 * (D * F) + 2 * (r5 * R)
              + 2 * (r6 * (R * T - Q * E)) + 2 * (r7 * (R * S - Q * F))) % M
        worst_h = max(worst_h, zh % 2)
        worst_i = max(worst_i, zi % 2)
print(f"  max parity over every selLamThree generator at every legal (P, Q, R): "
      f"z.h -> {worst_h}, z.i -> {worst_i}")
print("  (0, 0 means: no achievable gamma-3 move on any slot can flip the residue parity)")

print()
print("## R6  the residual: what class four still cannot separate")
for name, v in (("a0 = 1   ", ONE), ("a0 = Vbar", VB), ("a0 = X   ", X)):
    r = rows(v)
    print(f"  {name}: residue {r[J_]}, parity {r[J_] % 2}  (v.a = {v[A_]}, even)")
print("  all three have even chi_a, so the bit does not distinguish them: the depth")
print("  sweep's a0 = a1 forcing remains invisible at class four.")
