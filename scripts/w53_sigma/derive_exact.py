#!/usr/bin/env python3
"""W53-SIGMA step 3: the EXACT integer closed forms (valid over any commutative ring),
printed in Lean syntax, for the sigma-dressing row shifts at the plain class-four
sigma marking <0,1,0,0,0,0,0,0,0,0> with nu'-trivial exponent slots (x.b = y.b = 0).

No mod-8 reduction anywhere: everything below is a polynomial identity over Z.
"""
import sympy as sp

NAMES = "abcdefghij"


def mat(a, b, c, d, e, f, g, h, i, j):
    return sp.Matrix([
        [1, a, e, h, j],
        [0, 1, b, f, i],
        [0, 0, 1, c, g],
        [0, 0, 0, 1, d],
        [0, 0, 0, 0, 1]])


def M(pref, **fixed):
    vs = []
    for n in NAMES:
        vs.append(fixed[n] if n in fixed else sp.Symbol(f"{pref}{n}"))
    return mat(*vs), vs


def coords(m):
    return dict(a=m[0, 1], b=m[1, 2], c=m[2, 3], d=m[3, 4], e=m[0, 2],
                f=m[1, 3], g=m[2, 4], h=m[0, 3], i=m[1, 4], j=m[0, 4])


conjP = lambda p, g: g.inv() * p * g
commP = lambda p, q: p.inv() * q.inv() * p * q
sqWord = lambda s, x, y: (conjP(x, s).inv() * (x ** 3).inv() * (y ** 2)
                          * commP(y, conjP(y, s)))


def lean(ex):
    """Render a sympy polynomial as Lean source (coordinates as v.a, x.b, ...)."""
    s = str(sp.expand(ex))
    for pref, tag in (("v", "v"), ("x", "x"), ("y", "y")):
        for n in NAMES:
            s = s.replace(f"{pref}{n}", f"{tag}.{n}")
    return s.replace("**", " ^ ")


x, _ = M("x", b=0)
y, _ = M("y", b=0)
v, _ = M("v", b=0)
sM = mat(0, 1, 0, 0, 0, 0, 0, 0, 0, 0)

w0 = coords(sqWord(sM, x, y))
wv = coords(sqWord(sM * v, x, y))

print("-- W53-SIGMA exact row shifts, sigma marking <0,1,0,0,0,0,0,0,0,0>, x.b = y.b = 0")
for n in NAMES:
    d = sp.expand(wv[n] - w0[n])
    print(f"\n-- row {n}:")
    print(f"   {lean(d)}")

print()
print("=" * 78)
print("-- row j collected by the dressing coordinate (exact integer coefficients)")
dj = sp.expand(wv["j"] - w0["j"])
fields = {n: sp.Symbol(f"v{n}") for n in NAMES}
lin = {}
for n in "acdefghij":
    co = sp.expand(sp.diff(dj, fields[n]).subs({fields[m]: 0 for m in NAMES}))
    lin[n] = co
    print(f"\n-- K_{n} (coefficient of v.{n} at v = 0):")
    print(f"   {lean(co)}")
rem = sp.expand(dj - sum(lin[n] * fields[n] for n in "acdefghij"))
print("\n-- quadratic remainder:")
print(f"   {lean(rem)}")

print()
print("=" * 78)
print("-- sanity: the reassembled form equals the shift")
re_assembled = sum(lin[n] * fields[n] for n in "acdefghij") + rem
print("   ", sp.simplify(sp.expand(dj - re_assembled)) == 0)

print()
print("=" * 78)
print("-- the gamma-3 special case (v.a = v.c = v.d = v.e = v.f = v.g = 0):")
sub0 = {fields[n]: 0 for n in "acdefg"}
print("   row j shift =", lean(sp.expand(dj.subs(sub0))))
for n in "efghi":
    print(f"   row {n} shift =", lean(sp.expand((wv[n] - w0[n]).subs(sub0))))
