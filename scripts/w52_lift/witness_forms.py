#!/usr/bin/env python3
"""W52-LIFT step 7: symbolic closed forms of the relator rows at the U5 witness.

Witness tuple (h = 1):
  slot0 = sigma = <b=1>
  slot1 = <a=BT-AS, b=0, c=DT-CS, d=FT-ES, e=-2TSB, f=STC+TSD, g=GW, h=HW, i=IW, j=JW>
  slot2 = X1 = <e=P, f=Q, g=R, h=-((A+B)Q), i=IT, j=JT>
  slot3 = Ubar = <a=A, c=C, d=E, f=-(T*C)>
  slot4 = Vbar = <a=B, c=D, d=F, e=-(B*S)>
Print each relator row as a polynomial; the parity substitutions are NOT imposed,
so these are ring identities transcribable to Lean (proved by ring/linear_combination).
"""
import sympy as sp

A, B, C, D, E, F, T, S, P, Q, R, W2 = sp.symbols("A B C D E F T S P Q R W2")
GW, HW, IW, JW, IT, JT = sp.symbols("GW HW IW JW IT JT")

NAMES = "abcdefghij"


def mat(cs):
    a, b, c, d, e, f, g, h, i, j = [cs.get(n, 0) for n in NAMES]
    return sp.Matrix([
        [1, a, e, h, j],
        [0, 1, b, f, i],
        [0, 0, 1, c, g],
        [0, 0, 0, 1, d],
        [0, 0, 0, 0, 1]])


def coords(m):
    return dict(a=m[0, 1], b=m[1, 2], c=m[2, 3], d=m[3, 4], e=m[0, 2],
                f=m[1, 3], g=m[2, 4], h=m[0, 3], i=m[1, 4], j=m[0, 4])


inv = lambda m: m.inv()
conjP = lambda p, g: inv(g) * p * g
commP = lambda p, q: inv(p) * inv(q) * p * q

s0 = mat(dict(b=1))
s1 = mat(dict(a=B * T - A * S, c=D * T - C * S, d=F * T - E * S,
              e=-2 * T * S * B, f=S * T * C + T * S * D, g=GW, h=HW, i=IW, j=JW))
s2 = mat(dict(e=P, f=Q, g=R, h=-(A + B) * Q, i=IT, j=JT))
s3 = mat(dict(a=A, c=C, d=E, f=-(T * C)))
s4 = mat(dict(a=B, c=D, d=F, e=-(B * S)))

w = inv(conjP(s1, s0)) * inv(s1 ** 3) * (s2 ** 2) * commP(s2, conjP(s2, s0))
rel = w * commP(s3, s4)
cs = coords(rel)
for n in NAMES:
    print(f"row {n}: {sp.expand(cs[n])}")
print()
print("# after substituting the four parity halves (checks evenness claims):")
subs = {P: sp.Symbol('P'), }
# substitute BT-AS = 2P, DT-CS = 2Q ... i.e. express residues mod the relations:
# use a Groebner-free trick: replace S -> S, and reduce each row by the ideal
gens = [2 * P + A * S - B * T, 2 * Q + T * D - S * C, 2 * R + C * F - D * E,
        2 * W2 + E * S - F * T]
ord_syms = [P, Q, R, W2, A, B, C, D, E, F, T, S, GW, HW, IW, JW, IT, JT]
for n in "defghij":
    red = sp.reduced(sp.expand(cs[n]), gens, ord_syms)[1]
    print(f"row {n} mod parities: {sp.expand(red)}")
