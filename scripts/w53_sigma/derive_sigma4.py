#!/usr/bin/env python3
"""W53-SIGMA step 1: the exact sigma-slot reading at class four, symbolically.

The sigma slot enters `sqRelWord` only through `sqWord s x y`; the handle block never
sees it.  So the whole sigma-dependence of the class-four residue is

    sigFourDelta(s, v, x, y) := (sqWord (s*v) x y).j - (sqWord s x y).j ,

with `s` the sigma-slot marking value, `v` its dressing, `x` the x0-slot value and `y`
the x1-slot value.  This script derives that polynomial over Z (then mod 8), in the two
regimes that matter:

  A. `v` a general gamma-3 element (only h, i, j nonzero)  -> the pure junk move;
  B. `v` a general element with `v.b = 0` (the nu'-trivial dressings) -> the full reading.

It also checks the conjugation lemma `conjP p g = p * liftC (g.i*p.a - g.h*p.d)` for
gamma-3 `g`, which is what makes regime A a central translation.
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
        if n in fixed:
            vs.append(fixed[n])
        else:
            vs.append(sp.Symbol(f"{pref}{n}"))
    return mat(*vs), vs


def coords(m):
    return dict(a=m[0, 1], b=m[1, 2], c=m[2, 3], d=m[3, 4], e=m[0, 2],
                f=m[1, 3], g=m[2, 4], h=m[0, 3], i=m[1, 4], j=m[0, 4])


inv = lambda m: sp.simplify(m.inv())
conjP = lambda p, g: g.inv() * p * g
commP = lambda p, q: p.inv() * q.inv() * p * q


def sqWord(s, x, y):
    return conjP(x, s).inv() * (x ** 3).inv() * (y ** 2) * commP(y, conjP(y, s))


def red8(ex):
    """Reduce a polynomial's integer coefficients mod 8, into [-4, 3]."""
    ex = sp.expand(ex)
    p = sp.Poly(ex, *sorted(ex.free_symbols, key=str)) if ex.free_symbols else None
    if p is None:
        return sp.Integer(int(ex) % 8)
    out = 0
    for mono, co in zip(p.monoms(), p.coeffs()):
        c = int(co) % 8
        if c > 4:
            c -= 8
        if c:
            term = sp.Integer(c)
            for v, e in zip(p.gens, mono):
                term *= v ** e
            out += term
    return sp.expand(out)


print("=" * 78)
print("W53-SIGMA / derive_sigma4.py : the class-four sigma reading")
print("=" * 78)

# ---------------------------------------------------------------- lemma check
print()
print("## 0.  conjugation by a gamma-3 element is a central liftC translation")
p, pv = M("p")
g3, g3v = M("z", a=0, b=0, c=0, d=0, e=0, f=0, g=0)
cj = coords(conjP(p, g3))
pc = coords(p)
zh, zi, zj = sp.Symbol("zh"), sp.Symbol("zi"), sp.Symbol("zj")
for n in NAMES:
    diff = sp.expand(cj[n] - pc[n])
    print(f"  (conjP p z).{n} - p.{n} = {diff}")
print("  claim: only the j-coordinate moves, by  z.i*p.a - z.h*p.d .")
print("  check:", sp.simplify(sp.expand(cj["j"] - pc["j"] - (zi * pc["a"] - zh * pc["d"]))) == 0)

# ------------------------------------------------------- regime A: gamma-3 v
print()
print("## 1.  regime A: the sigma-slot gamma-3 move")
s, sv = M("s")
x, xv = M("x")
y, yv = M("y")
v3, v3v = M("v", a=0, b=0, c=0, d=0, e=0, f=0, g=0)
w0 = coords(sqWord(s, x, y))
wv = coords(sqWord(s * v3, x, y))
for n in NAMES:
    d = sp.expand(wv[n] - w0[n])
    print(f"  Delta.{n} = {d}")
vh, vi = sp.Symbol("vh"), sp.Symbol("vi")
claim = vh * coords(x)["d"] - vi * coords(x)["a"]
print("  claim Delta.j =  v.h*x.d - v.i*x.a :",
      sp.simplify(sp.expand(wv["j"] - w0["j"] - claim)) == 0)

# ------------------------------------------------- regime B: general b=0 v
print()
print("## 2.  regime B: a general nu'-trivial dressing (v.b = 0)")
vB, vBv = M("v", b=0)
wB = coords(sqWord(s * vB, x, y))
for n in NAMES[:9]:
    d = red8(wB[n] - w0[n])
    print(f"  Delta.{n} = {d}")
dj = red8(wB["j"] - w0["j"])
print()
print("  Delta.j (mod 8) =")
print("   ", dj)
print()
print("  ... number of monomials:", len(sp.Add.make_args(dj)))

# ------------------------------------- regime B specialised: sigma marking b=1
print()
print("## 3.  regime B at the sigma marking shape s = <A0, 1, C0, D0, 0,...,0>")
A0, C0, D0 = sp.symbols("A0 C0 D0")
sMark = mat(A0, 1, C0, D0, 0, 0, 0, 0, 0, 0)
w0m = coords(sqWord(sMark, x, y))
wBm = coords(sqWord(sMark * vB, x, y))
djm = red8(wBm["j"] - w0m["j"])
print("  Delta.j (mod 8) =")
print("   ", djm)
print()
for n in NAMES[:9]:
    d = red8(wBm[n] - w0m[n])
    print(f"  Delta.{n} = {d}")

# ------------------------------------------------- collect by dressing field
print()
print("## 4.  Delta.j at the sigma marking, collected by the dressing's fields")
fields = {n: sp.Symbol(f"v{n}") for n in NAMES}
poly = sp.Poly(djm, *[fields[n] for n in "acdefghij"])
print("  (linear part in each dressing coordinate; the constant term is 0)")
for n in "acdefghij":
    lin = red8(sp.diff(djm, fields[n]).subs({fields[m]: 0 for m in NAMES}))
    print(f"  d(Delta.j)/d(v.{n}) at v = 0 :  {lin}")
print()
print("  full remainder (Delta.j minus its linear part at v = 0):")
linsum = sum(sp.diff(djm, fields[n]).subs({fields[m]: 0 for m in NAMES}) * fields[n]
             for n in "acdefghij")
print("   ", red8(djm - linsum))
