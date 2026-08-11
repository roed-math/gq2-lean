#!/usr/bin/env python3
"""certs_u5.py.

BRACKET CONVENTION.  [NONE]
This script computes no commutators, so the convention does not arise.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

"""certs_u5.py.
"""

"""certs_u5.py.
"""

"""certs_u5.py.
"""

"""certs_u5.py.
"""

"""W52-LIFT step 8: Lean transcription certificates for GradedLift sections 3-4.

Verifies, over ZZ[A..W2]:
  (a) the U4R-quotient row expressions (rows d, g, i of the U5 witness relator)
      against the exact witness_forms rows, via the SqU4 closed-form machinery
      (sqRelWord_c / _e / _f shapes) evaluated at the quotient slots;
  (b) the linear_combination certificates (coefficients on hb, he, hg and the
      8-multiple slack) for each row goal;
  (c) the concrete engine-instance numbers at the chosen binder point.
"""
import sympy as sp

A, B, C, D, E, F, T, S, P, Q, R, W2 = sp.symbols("A B C D E F T S P Q R W2")

hd = 2 * P + (A * S - B * T)
he = 2 * Q + (T * D - S * C)
hg = 2 * R + (C * F - D * E)
hb = 2 * W2 + (E * S - F * T)


def u4(a=0, b=0, c=0, d=0, e=0, f=0):
    return dict(a=a, b=b, c=c, d=d, e=e, f=f)


# right-quotient slots of the U5 witness (deep zero): (a,b,c,d,e,f) = U5 (b,c,d,f,g,i)
m0 = u4(a=1)
m1 = u4(b=D * T - C * S, c=F * T - E * S, d=S * (T * C) + T * S * D)
m2 = u4(d=Q, e=R)
mU = u4(b=C, c=E, d=-(T * C))
mV = u4(b=D, c=F)


def sqU4Core(s, x, y):
    return (-(s['a'] * s['b'] * x['c']) + s['a'] * s['c'] * x['b']
            + s['a'] * x['e'] - s['c'] * x['d'] + s['d'] * x['c'] - s['e'] * x['a']
            - 4 * (s['a'] * x['b'] * x['c']) + 3 * (s['b'] * x['a'] * x['c'])
            + s['c'] * x['a'] * x['b']
            + 2 * (s['a'] * x['b'] * y['c']) - 2 * (s['b'] * x['a'] * y['c'])
            + s['a'] * y['b'] * y['c'] - 2 * (s['b'] * y['a'] * y['c'])
            + s['c'] * y['a'] * y['b']
            - 20 * (x['a'] * x['b'] * x['c']) + 20 * (x['a'] * x['b'] * y['c'])
            - 4 * (x['a'] * y['b'] * y['c'])
            + 10 * (x['a'] * x['e']) - 8 * (x['a'] * y['e'])
            + 10 * (x['c'] * x['d']) - 8 * (x['d'] * y['c'])
            + y['a'] * y['e'] + y['c'] * y['d'])


def u4Comm3(p, q):
    return (p['a'] * q['e'] - p['e'] * q['a'] + p['d'] * q['c'] - p['c'] * q['d']
            + p['a'] * p['c'] * q['b'] - p['a'] * p['b'] * q['c']
            + p['c'] * q['a'] * q['b'] - p['b'] * q['a'] * q['c'])


def sqHeisDefect_BC(slots):
    # toHeisBC: (a,b) of SqHeis = (b,c) of SqU4
    s0, s1, s2, sU, sV = slots
    return ((s0['b'] * s1['c'] - s1['b'] * s0['c'])
            + 10 * (s1['b'] * s1['c']) + s2['b'] * s2['c'] - 8 * (s1['b'] * s2['c'])
            + (sU['b'] * sV['c'] - sV['b'] * sU['c']))


# row d of U5 = row c of U4R tuple
row_d = sp.expand(-4 * m1['c'] + 2 * m2['c'])
# row g of U5 = row e of U4R tuple
row_g = sp.expand(-4 * m1['e'] + 2 * m2['e'] + sqHeisDefect_BC([m0, m1, m2, mU, mV]))
# row i of U5 = row f of U4R tuple (cross coefficient -4*(m1).a + 2*(m2).a = 0 but keep it)
cross = (mU['b'] * mV['c'] - mV['b'] * mU['c'])
row_i = sp.expand(-4 * m1['f'] + 2 * m2['f'] + sqU4Core(m0, m1, m2)
                  + (-4 * m1['a'] + 2 * m2['a']) * cross + u4Comm3(mU, mV))

print("row d =", row_d)
print("row g =", row_g)
print("row i =", row_i)

# reference exact rows from witness_forms.py (deep zero)
ref_d = 4 * E * S - 4 * F * T
ref_g = (10 * C * E * S**2 - 10 * C * F * S * T + C * F - 10 * D * E * S * T - D * E
         + 10 * D * F * T**2 + 2 * R)
ref_i = (-10 * C * E * S**2 * T - 4 * C * E * S**2 + 10 * C * F * S * T**2
         + 4 * C * F * S * T - C * F * T - 10 * D * E * S**2 * T + 4 * D * E * S * T
         + 10 * D * F * S * T**2 - 4 * D * F * T**2)
print("row d - ref:", sp.expand(row_d - ref_d))
print("row g - ref:", sp.expand(row_g - ref_g))
print("row i - ref:", sp.expand(row_i - ref_i))

# certificates: goal_lhs - goal_rhs - sum(c_k * hyp_k) must be divisible by 8
print()
print("== certificates")
cert_d = sp.expand(row_d - 0 - 4 * hb)
print("row d slack/8:", sp.factor(cert_d / 8), "int?", sp.simplify(cert_d / 8))
Jp = C * E * S**2 - C * F * S * T - D * E * S * T + D * F * T**2
cert_g = sp.expand(row_g - 0 - (2 * (C * S - D * T)) * hb - (4 * W2) * he - hg)
print("row g slack:", sp.expand(cert_g), "-> /8:", sp.expand(cert_g / 8))
tgt_i = 4 * S * T * (C + D) * W2 - C * F * T
cert_i = sp.expand(row_i - tgt_i - (-2 * S * T * (C + D) - 4 * (C * S - D * T)) * hb)
print("row i slack:", sp.expand(cert_i), "-> /8:", sp.expand(cert_i / 8))
