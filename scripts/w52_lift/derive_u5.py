#!/usr/bin/env python3
"""W52-LIFT step 1: derive the SqU5 closed forms symbolically (sympy).

U5(R) carried on ten strictly-upper coords of a 5x5 unitriangular matrix:
  a=(1,2) b=(2,3) c=(3,4) d=(4,5)  e=(1,3) f=(2,4) g=(3,5)  h=(1,4) i=(2,5)  j=(1,5).
Repo conventions: conjP x g = g^-1 x g, commP x y = x^-1 y^-1 x y,
  sqWord s x y = (conjP x s)^-1 * (x^3)^-1 * y^2 * commP y (conjP y s).
Outputs Lean-ready polynomial closed forms.
"""
import sympy as sp

NAMES = "abcdefghij"


def M(pref):
    v = sp.symbols(" ".join(f"{pref}{n}" for n in NAMES))
    return mat(*v), v


def mat(a, b, c, d, e, f, g, h, i, j):
    return sp.Matrix([
        [1, a, e, h, j],
        [0, 1, b, f, i],
        [0, 0, 1, c, g],
        [0, 0, 0, 1, d],
        [0, 0, 0, 0, 1]])


def coords(m):
    return dict(a=m[0, 1], b=m[1, 2], c=m[2, 3], d=m[3, 4], e=m[0, 2],
                f=m[1, 3], g=m[2, 4], h=m[0, 3], i=m[1, 4], j=m[0, 4])


def pr(title, m, ref=None):
    print(f"== {title}")
    cs = coords(m)
    for n in NAMES:
        ex = sp.expand(cs[n])
        if ref is not None:
            ex = sp.expand(ex - ref[n])
            tag = f".{n} - ref"
        else:
            tag = f".{n}"
        print(f"  {tag} = {ex}")
    print()


x, xv = M("x")
y, yv = M("y")
s, sv = M("s")

inv = lambda m: m.inv()
conjP = lambda p, g: inv(g) * p * g
commP = lambda p, q: inv(p) * inv(q) * p * q

print("# mul components")
pr("x * y", x * y)
print("# inv components")
pr("x^-1", inv(x))
print("# commP components (j-row = u5Comm4)")
pr("commP x y", commP(x, y))
print("# conjP components")
pr("conjP x s  (s^-1 x s)", conjP(x, s))
print("# pow 2, 3")
pr("x^2", x * x)
pr("x^3", x * x * x)

print("# sqWord rows; j-row minus linear part = sqU5Core")
w = inv(conjP(x, s)) * inv(x * x * x) * (y * y) * commP(y, conjP(y, s))
cs = coords(w)
for n in "abcd":
    print(f"  (sqWord).{n} = {sp.expand(cs[n])}")
lin = {"e": -4 * xv[4] + 2 * yv[4], "f": -4 * xv[5] + 2 * yv[5],
       "g": -4 * xv[6] + 2 * yv[6], "h": -4 * xv[7] + 2 * yv[7],
       "i": -4 * xv[8] + 2 * yv[8], "j": -4 * xv[9] + 2 * yv[9]}
core = {}
for n in "efghij":
    core[n] = sp.expand(cs[n] - lin[n])
    print(f"  (sqWord).{n} - ({lin[n]}) = sqU5Core_{n} = {core[n]}")

print()
print("# handleWord for h = 2: [u1,v1]*[u2,v2], j-row cross-handle check")
u1, _ = M("p")
v1, _ = M("q")
u2, _ = M("r")
v2, _ = M("t")
hw = commP(u1, v1) * commP(u2, v2)
c1, c2 = coords(commP(u1, v1)), coords(commP(u2, v2))
crossj = sp.expand(coords(hw)["j"] - c1["j"] - c2["j"])
print(f"  hw.j - comm1.j - comm2.j = {crossj}")
print(f"  check e1*g2: {sp.expand(crossj - c1['e'] * c2['g'])}  (0 = confirmed)")
for n in "efghi":
    dd = sp.expand(coords(hw)[n] - c1[n] - c2[n])
    print(f"  hw.{n} additive? residue = {dd}")
