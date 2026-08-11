"""W61-WIDER step 4: the handle-word product law and the assembled five-slot relator shift.

At class four a `gamma_3`-shaped per-handle shift commutes with everything of vanishing outer
abelian columns, so the per-handle shifts of `GradedGammaTwo` collect with no correction.  One
class up they do NOT: `[gamma_3, gamma_2] <= gamma_5 <> 1`, so moving each handle shift past
the LATER handle commutators costs a strictly triangular cross-handle term.  That term is
derived and checked here, symbolically at handle counts 0..3, and the five-slot relator shift
is assembled and checked symbolically at handle counts 0..2 over `Z[frame, dressings]`.

Every check is an exact polynomial identity over the integers: "EXACT" means the difference of
the two sides is the zero polynomial, not that it vanished at sample points.

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
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
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_defect5"))

import u6poly as P                                            # noqa: E402
from u6poly import U6, padd, psub, pmul, pneg, pzero, poly_str  # noqa: E402
import wlib as W                                              # noqa: E402

COORDS = P.COORDS

print("=" * 92)
print("== 1. the handle shift, as a closed form ==")
p, q = U6.gen("p"), U6.gen("q")
zh, wh = W.ga2("z"), W.ga2("w")
got = W.shift(P.commP(p, q), P.commP(p * zh, q * wh))
want = W.handleShift(p, q, zh, wh)
bad = [co for co in COORDS if psub(getattr(got, co), getattr(want, co))]
print("   commP(p z, q w) = commP(p, q) * handleShift : %s"
      % ("EXACT, all fifteen rows" if not bad else "FAILS at %s" % bad))
print()

print("=" * 92)
print("== 2. the handle WORD under an all-pair gamma_2-dressing ==")
for n in range(0, 4):
    us = [U6.gen("u%d" % k) for k in range(n)]
    vs = [U6.gen("v%d" % k) for k in range(n)]
    zus = [W.ga2("zu%d" % k) for k in range(n)]
    zvs = [W.ga2("zv%d" % k) for k in range(n)]
    lhs = P.handleWord([us[k] * zus[k] for k in range(n)],
                       [vs[k] * zvs[k] for k in range(n)])
    rhs = P.handleWord(us, vs) * W.handleWordShift(us, vs, zus, zvs)
    bad = [co for co in COORDS if psub(getattr(lhs, co), getattr(rhs, co))]
    print("   h = %d : %s" % (n, "EXACT" if not bad else "FAILS at %s" % bad))
print()

print("=" * 92)
print("== 3. the collection of the core shift past the handle word ==")
C = W.ga2("C")
H = U6.gen("H")
for co in ("a", "b", "c", "d", "e"):
    setattr(H, co, pzero())
coll = W.shift(H * C, C * H)
_, cl = W.shape(coll, ["m", "n", "o"])
want_m = psub(pmul(C.f, H.h), pmul(C.h, H.f))
want_n = psub(pmul(C.g, H.i), pmul(C.i, H.g))
want_o = padd(psub(pmul(C.f, H.l), pmul(C.l, H.f)), psub(pmul(C.j, H.i), pmul(C.i, H.j)))
print("   K.m = C.f H.h - C.h H.f                     : %s" % (not psub(cl["m"], want_m)))
print("   K.n = C.g H.i - C.i H.g                     : %s" % (not psub(cl["n"], want_n)))
print("   K.o = C.f H.l - C.l H.f + C.j H.i - C.i H.j : %s" % (not psub(cl["o"], want_o)))
print()

print("=" * 92)
print("== 4. THE ASSEMBLED FIVE-SLOT RELATOR IDENTITY, symbolically ==")
for h in range(0, 3):
    rank = 3 + 2 * h
    m = [(U6.gen("m%d" % i), W.ga2("z%d" % i)) for i in range(rank)]
    frame = [m[i][0] for i in range(rank)]
    dressed = [m[i][0] * m[i][1] for i in range(rank)]
    lhs = P.sqRelWord(dressed, h)
    rhs = P.sqRelWord(frame, h) * W.relShift(m, h)
    bad = [co for co in COORDS if psub(getattr(lhs, co), getattr(rhs, co))]
    print("   h = %d : sqRelWord(m . z) = sqRelWord(m) * shift : %s"
          % (h, "EXACT, all fifteen rows" if not bad else "FAILS at %s" % bad))
print()

print("=" * 92)
print("== 5. the core shift's blocks, and their sizes ==")
s, x, y = U6.gen("s"), U6.gen("x"), U6.gen("y")
z0, z1, z2 = W.ga2("z0"), W.ga2("z1"), W.ga2("z2")
blocks = W.coreBlocks(s, x, y, z0, z1, z2)
for co in ("m", "n", "o"):
    corr, quad = blocks[co]
    print("   [%s] correction %3d terms, quadratic %3d terms" % (co, len(corr), len(quad)))
print()
print("   the class-five quadratic block, grouped by its frame factor:")
by = {}
for mon, c in blocks["o"][1].items():
    rest = tuple(v for v in mon if not v.startswith("z"))
    by.setdefault(rest, {})[tuple(v for v in mon if v.startswith("z"))] = c
for rest in sorted(by, key=lambda t: (len(t), t)):
    lbl = "(frame-free)" if not rest else " ".join(rest)
    print("     %-12s : %s" % (lbl, poly_str(by[rest])))
