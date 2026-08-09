#!/usr/bin/env python3
"""W53-SIGMA step 2: numerical validation of the class-four sigma reading, and the hunt
for a separation instance on the class-two-forced x0 gauge.

Claims validated (all over Z/8, h = 1 unless said otherwise):

 V1  conjP p z = p * liftC (z.i*p.a - z.h*p.d) for gamma-3 z.
 V2  sqWord (s*z) x y = sqWord s x y * liftC (z.h*x.d - z.i*x.a) for gamma-3 z, any s,x,y.
 V3  the five-slot translation identity (sigma gamma-3 + selLift's four dressings).
 V4  the sigma-dressing row shifts at a nu'-trivial exponent pair (x.b = y.b = 0):
       rows a..f unchanged,
       row g  += v.c*x.d - v.d*x.c
       row h  += v.a*(x.f - x.c) + v.c*(-x.a - x.e) + v.e*x.c - v.f*x.a
       row i  += v.d*(x.c - x.f) + v.f*x.d
       row j  += sigFourRead (closed form below, at the sigma marking <0,1,0,0,0,...>).
 V5  the gauge collapse: if x.a, x.c, x.d, x.e, x.f and y.a, y.c, y.d are all even then
       row-j shift == v.a*(x.g + x.i) + v.d*x.h + v.e*x.g  (mod 2).
 V6  a separation instance: two h = 1 tuples differing only in the sigma slot, both with
       rows a..i identically zero, whose class-four residues differ by an odd amount, at a
       point where every achievable increment is even.
"""
import itertools
import random
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from u5lib import (M, ONE, mul, inv, conjP, commP, power, sqWord, handleWord,
                   sqRelWord, liftC, show)

random.seed(20260809)


def rnd(**fixed):
    p = [random.randrange(M) for _ in range(10)]
    for k, n in enumerate("abcdefghij"):
        if n in fixed:
            p[k] = fixed[n] % M
    return tuple(p)


A, B, C, D, E, F, G, H, I, J = range(10)


def ok(cond, name):
    print(f"  [{'ok ' if cond else 'FAIL'}] {name}")
    return cond


allok = True
print("=" * 78)
print("W53-SIGMA / sweep_sigma4.py")
print("=" * 78)

# ------------------------------------------------------------------ V1, V2
print()
print("## V1  conjugation by a gamma-3 element is central")
bad = 0
for _ in range(4000):
    p = rnd()
    z = rnd(a=0, b=0, c=0, d=0, e=0, f=0, g=0)
    if conjP(p, z) != mul(p, liftC(z[I] * p[A] - z[H] * p[D])):
        bad += 1
allok &= ok(bad == 0, f"4000 random pairs, mismatches = {bad}")

print()
print("## V2  the sigma-slot gamma-3 move on the core word")
bad = 0
for _ in range(4000):
    s, x, y = rnd(), rnd(), rnd()
    z = rnd(a=0, b=0, c=0, d=0, e=0, f=0, g=0)
    if sqWord(mul(s, z), x, y) != mul(sqWord(s, x, y), liftC(z[H] * x[D] - z[I] * x[A])):
        bad += 1
allok &= ok(bad == 0, f"4000 random triples, mismatches = {bad}")

# ---------------------------------------------------------------------- V3
print()
print("## V3  the five-slot class-four translation identity")


def sigLift(m, h, jj, z0, w1, w2, z3, z4):
    m = list(m)
    m[0] = mul(m[0], z0)
    m[1] = mul(m[1], w1)
    m[2] = mul(m[2], w2)
    m[3 + 2 * jj] = mul(m[3 + 2 * jj], z3)
    m[4 + 2 * jj] = mul(m[4 + 2 * jj], z4)
    return m


bad = 0
for h in (1, 2, 3):
    for _ in range(1500):
        m = [rnd() for _ in range(3 + 2 * h)]
        jj = random.randrange(h)
        z0 = rnd(a=0, b=0, c=0, d=0, e=0, f=0, g=0)
        z3 = rnd(a=0, b=0, c=0, d=0, e=0, f=0, g=0)
        z4 = rnd(a=0, b=0, c=0, d=0, e=0, f=0, g=0)
        w1 = rnd(a=0, b=0, c=0, d=0, e=0, f=0, g=0, h=0, i=0)
        w2 = rnd(a=0, b=0, c=0, d=0, e=0, f=0, g=0, h=0, i=0)
        mU, mV = m[3 + 2 * jj], m[4 + 2 * jj]
        delta = (z0[H] * m[1][D] - z0[I] * m[1][A]
                 + (-4 * w1[J] + 2 * w2[J])
                 + (z3[H] * mV[D] - z3[I] * mV[A])
                 + (mU[A] * z4[I] - mU[D] * z4[H]))
        lhs = sqRelWord(sigLift(m, h, jj, z0, w1, w2, z3, z4), h)
        if lhs != mul(sqRelWord(m, h), liftC(delta)):
            bad += 1
allok &= ok(bad == 0, f"h = 1,2,3, 1500 each, mismatches = {bad}")

# ---------------------------------------------------------------------- V4
print()
print("## V4  the sigma-dressing row shifts at a nu'-trivial exponent pair")


def sigRowShift(v, x, y):
    """The predicted shifts of rows g, h, i when the sigma slot <0,1,0,0,...> is dressed
    by v (with v.b = 0), at x0-slot x and x1-slot y both with b = 0."""
    dg = v[C] * x[D] - v[D] * x[C]
    dh = v[A] * (x[F] - x[C]) + v[C] * (-x[A] - x[E]) + v[E] * x[C] - v[F] * x[A]
    di = v[D] * (x[C] - x[F]) + v[F] * x[D]
    return dg % M, dh % M, di % M


def sigFourRead(v, x, y):
    """The row-j shift, at the sigma marking <0,1,0,0,0,0,0,0,0,0> with x.b = y.b = 0.
    Derived in derive_sigma4.py; the four linear blocks plus the two quadratic terms."""
    va, vc, vd, ve, vf, vg, vh, vi = (v[A], v[C], v[D], v[E], v[F], v[G], v[H], v[I])
    xa, xc, xd, xe, xf, xg, xh, xi = (x[A], x[C], x[D], x[E], x[F], x[G], x[H], x[I])
    ya, yc, yd, ye, yf, yg = y[A], y[C], y[D], y[E], y[F], y[G]
    Ka = (4 * xc * xd - 2 * xc * yd + 4 * xd * xf + 2 * xf * yd - xg + xi
          - yc * yd + yd * yf)
    Kc = 3 * xa * xd - 2 * xa * yd + 3 * xd * xe - 2 * xe * yd - ya * yd - 2 * yd * ye
    Kd = xa * xf + xc * xe - xh - ya * yc + ya * yf + yc * ye
    Ke = 4 * xc * xd + 2 * xc * yd + xg + yc * yd
    Kf = 3 * xa * xd - 2 * xa * yd - 2 * ya * yd
    Kg = -xa - xe
    quad = (-va * vc * 0 + va * vd * (xf - xc) - va * vf * xd
            - vc * ve * xd + vd * ve * xc)
    return (va * Ka + vc * Kc + vd * Kd + ve * Ke + vf * Kf + vg * Kg
            + vh * xd - vi * xa + quad) % M


SIGMARK = (0, 1, 0, 0, 0, 0, 0, 0, 0, 0)

bad = 0
for h in (1, 2):
    for _ in range(3000):
        x = rnd(b=0)
        y = rnd(b=0)
        v = rnd(b=0)
        m = [SIGMARK, x, y] + [rnd() for _ in range(2 * h)]
        m2 = [mul(SIGMARK, v)] + m[1:]
        r1, r2 = sqRelWord(m, h), sqRelWord(m2, h)
        dg, dh, di = sigRowShift(v, x, y)
        pred = [0, 0, 0, 0, 0, 0, dg, dh, di, sigFourRead(v, x, y)]
        got = [(r2[k] - r1[k]) % M for k in range(10)]
        if got != [p % M for p in pred]:
            bad += 1
            if bad < 3:
                print("    got ", got)
                print("    pred", [p % M for p in pred])
allok &= ok(bad == 0, f"h = 1,2, 3000 each, mismatches = {bad}")

# ---------------------------------------------------------------------- V5
print()
print("## V5  the gauge collapse of the reading mod 2")
bad = 0
tot = 0
for _ in range(20000):
    x = rnd(b=0)
    y = rnd(b=0)
    for k in (A, C, D, E, F):
        x = x[:k] + ((x[k] // 2 * 2) % M,) + x[k + 1:]
    for k in (A, C, D):
        y = y[:k] + ((y[k] // 2 * 2) % M,) + y[k + 1:]
    v = rnd(b=0)
    lhs = sigFourRead(v, x, y) % 2
    rhs = (v[A] * (x[G] + x[I]) + v[D] * x[H] + v[E] * x[G]) % 2
    tot += 1
    if lhs != rhs:
        bad += 1
allok &= ok(bad == 0, f"{tot} gauge points, mismatches = {bad}")

# ---------------------------------------------------------------------- V5b
print()
print("## V5b the class-three reading on the same gauge is even (the committed blindness)")
print("     (class three = the toU4L quotient: coordinates a,b,c,e,f,h of SqU5)")
bad = 0
for _ in range(20000):
    x = rnd(b=0)
    y = rnd(b=0)
    for k in (A, C, D, E, F):
        x = x[:k] + ((x[k] // 2 * 2) % M,) + x[k + 1:]
    for k in (A, C, D):
        y = y[:k] + ((y[k] // 2 * 2) % M,) + y[k + 1:]
    v = rnd(b=0)
    m = [SIGMARK, x, y, rnd(), rnd()]
    m2 = [mul(SIGMARK, v)] + m[1:]
    r1, r2 = sqRelWord(m, 1), sqRelWord(m2, 1)
    if ((r2[H] - r1[H]) % M) % 2 != 0:
        bad += 1
allok &= ok(bad == 0, f"class-three (h-row) shift always even on the gauge: bad = {bad}")

print()
print("=" * 78)
print("ALL CLAIMS OK" if allok else "SOME CLAIM FAILED")
print("=" * 78)
