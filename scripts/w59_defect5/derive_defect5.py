"""W59-DEFECT5, step 1: derive the class-five defect closed form symbolically.

Everything is exact integer arithmetic on `scripts/w59_defect5/u6poly.py`
polynomials.  The script derives, and writes to `results/derive.txt`:

* the fifteen coordinates of the core word `sqWord s x y`, and in particular
  the class-four content `sqU6Core4` and the class-five content `sqU6Core`
  (the coordinate minus the Frobenius head `-4 x + 2 y`);
* the structural facts the closed form needs: which coordinates of a product of
  gamma_2 elements are additive, and which carry cross-handle terms;
* the handle block's class-four and class-five coordinates, as the sum of the
  per-handle commutator forms plus a STRICTLY TRIANGULAR cross-handle pairing;
* the assembled class-five defect, checked against the raw relator at h = 0..3
  with generic (fully symbolic) markings.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from u6poly import (COORDS, U6, commP, conjP, handleWord, padd, pdeg, pmul,
                    pneg, poly_terms, psub, pscale, pvar, pvars, pzero,
                    sqRelWord, sqWord)

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(OUT, exist_ok=True)
LOG = []


def say(msg=""):
    print(msg)
    LOG.append(msg)


def check(name, cond):
    say("  [%s] %s" % ("PASS" if cond else "FAIL", name))
    if not cond:
        raise SystemExit("FAILED: " + name)


# ============================================================ 1 the core word

say("=" * 78)
say("W59-DEFECT5 derivation: the class-five defect of a general marking")
say("=" * 78)
say()
say("## 1 The core word `sqWord s x y`")

s, x, y = U6.gen("s"), U6.gen("x"), U6.gen("y")
W = sqWord(s, x, y)

frob = {co: padd(pscale(-4, pvar("x_" + co)), pscale(2, pvar("y_" + co)))
        for co in COORDS}

core = {co: psub(getattr(W, co), frob[co]) for co in COORDS}

for co in COORDS:
    say("  sqWord.%s : %d terms beyond the Frobenius head -4x+2y, degree %d"
        % (co, len(core[co]), pdeg(core[co])))

say()
say("### the five abelian rows are exactly the relator vector")
for co in "abcde":
    check("sqWord.%s = -4 x.%s + 2 y.%s" % (co, co, co), not core[co])

say()
say("### the top coordinate does not read any slot's own top coordinate")
check("sqU6Core has no s.o, x.o, y.o", not ({"s_o", "x_o", "y_o"} & pvars(core["o"])))
check("sqU6Core4 has no s.m, x.m, y.m", not ({"s_m", "x_m", "y_m"} & pvars(core["m"])))
say("  NOTE the class-five core reads the slots' coordinates up to class FOUR, the")
say("  sigma slot's s.m and s.n included (conjugation moves the top row by")
say("  g.n * p.a - g.m * p.e).  That is the exact analogue of the class-three core,")
say("  which reads the class-TWO coordinates s.d, s.e and no class-three one: at every")
say("  class the core reads everything strictly below the top row and nothing at it.")
check("sqU6Core reads s.n", "s_n" in pvars(core["o"]))
check("sqU6Core reads s.m", "s_m" in pvars(core["o"]))

say()
say("### which lower coordinates the class-five core reads")
say("  variables in sqU6Core : " + ", ".join(sorted(pvars(core["o"]))))
say("  variables in sqU6Core4: " + ", ".join(sorted(pvars(core["m"]))))

# Cross-check the two committed core rows: class two and class three.
f_committed = padd(
    pmul(pvar("s_a"), pvar("x_b")), pneg(pmul(pvar("s_b"), pvar("x_a"))),
    pscale(10, pmul(pvar("x_a"), pvar("x_b"))),
    pscale(-8, pmul(pvar("x_a"), pvar("y_b"))),
    pmul(pvar("y_a"), pvar("y_b")))
check("sqWord.f matches the committed SqU6.sqWord_f", not psub(core["f"], f_committed))


def sqU4Core(sp, xp, yp):
    """`GradedThree`'s committed class-three core, in (a, b, c, d, e, f) names."""
    def V(pref, co):
        return pvar(pref + "_" + co)
    S, X, Y = sp, xp, yp
    t = []
    t.append(pneg(pmul(pmul(V(S, "a"), V(S, "b")), V(X, "c"))))
    t.append(pmul(pmul(V(S, "a"), V(S, "c")), V(X, "b")))
    t.append(pmul(V(S, "a"), V(X, "e")))
    t.append(pneg(pmul(V(S, "c"), V(X, "d"))))
    t.append(pmul(V(S, "d"), V(X, "c")))
    t.append(pneg(pmul(V(S, "e"), V(X, "a"))))
    t.append(pscale(-4, pmul(pmul(V(S, "a"), V(X, "b")), V(X, "c"))))
    t.append(pscale(3, pmul(pmul(V(S, "b"), V(X, "a")), V(X, "c"))))
    t.append(pmul(pmul(V(S, "c"), V(X, "a")), V(X, "b")))
    t.append(pscale(2, pmul(pmul(V(S, "a"), V(X, "b")), V(Y, "c"))))
    t.append(pscale(-2, pmul(pmul(V(S, "b"), V(X, "a")), V(Y, "c"))))
    t.append(pmul(pmul(V(S, "a"), V(Y, "b")), V(Y, "c")))
    t.append(pscale(-2, pmul(pmul(V(S, "b"), V(Y, "a")), V(Y, "c"))))
    t.append(pmul(pmul(V(S, "c"), V(Y, "a")), V(Y, "b")))
    t.append(pscale(-20, pmul(pmul(V(X, "a"), V(X, "b")), V(X, "c"))))
    t.append(pscale(20, pmul(pmul(V(X, "a"), V(X, "b")), V(Y, "c"))))
    t.append(pscale(-4, pmul(pmul(V(X, "a"), V(Y, "b")), V(Y, "c"))))
    t.append(pscale(10, pmul(V(X, "a"), V(X, "e"))))
    t.append(pscale(-8, pmul(V(X, "a"), V(Y, "e"))))
    t.append(pscale(10, pmul(V(X, "c"), V(X, "d"))))
    t.append(pscale(-8, pmul(V(X, "d"), V(Y, "c"))))
    t.append(pmul(V(Y, "a"), V(Y, "e")))
    t.append(pmul(V(Y, "c"), V(Y, "d")))
    return padd(*t)


# toU4LL sends (a, b, c, f, g, j) of SqU6 to (a, b, c, d, e, f) of SqU4.
RENAME_LL = {"a": "a", "b": "b", "c": "c", "d": "f", "e": "g", "f": "j"}


def sqU4Core_LL():
    raw = sqU4Core("s", "x", "y")
    out = {}
    for mon, c in raw.items():
        newmon = tuple(sorted(v.split("_")[0] + "_" + RENAME_LL[v.split("_")[1]]
                              for v in mon))
        out[newmon] = out.get(newmon, 0) + c
    return {m: c for m, c in out.items() if c}


check("sqWord.j matches the committed sqU4Core through toU4LL",
      not psub(core["j"], sqU4Core_LL()))

say()
say("### sizes of the two genuinely new core rows")
say("  sqU6Core4 (class four, the (1,5) row): %d terms, degree %d"
    % (len(core["m"]), pdeg(core["m"])))
say("  sqU6Core  (class five, the (1,6) row): %d terms, degree %d"
    % (len(core["o"]), pdeg(core["o"])))

# ==================================================== 2 the gamma_2 structure

say()
say("## 2 Products of gamma_2 elements: what is additive and what is not")

p2 = U6.gen("p")
q2 = U6.gen("q")
for z in (p2, q2):
    for co in "abcde":
        setattr(z, co, pzero())
pq = p2 * q2
for co in COORDS:
    diff = psub(getattr(pq, co), padd(getattr(p2, co), getattr(q2, co)))
    tag = "additive" if not diff else "CROSS " + " + ".join(
        "%s" % ("*".join(m)) for m, c in poly_terms(diff))
    say("  (p*q).%s : %s" % (co, tag))

# ====================================================== 3 the handle block

say()
say("## 3 The handle block at class five")
say("  the handle commutators are gamma_2, so the additive coordinates are plain")
say("  sums and the class-four and class-five coordinates carry a STRICTLY")
say("  TRIANGULAR cross-handle pairing (vanishing at h <= 1).")


def handle_block_check(h):
    us = [U6.gen("u%d" % j) for j in range(h)]
    vs = [U6.gen("v%d" % j) for j in range(h)]
    H = handleWord(us, vs)
    C = [commP(us[j], vs[j]) for j in range(h)]

    def total(co):
        return padd(*[getattr(c, co) for c in C]) if C else pzero()

    def tri(co1, co2):
        acc = pzero()
        for t in range(h):
            pre = padd(*[getattr(C[ss], co1) for ss in range(t)]) if t else pzero()
            acc = padd(acc, pmul(pre, getattr(C[t], co2)))
        return acc

    ok = True
    for co in ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l"]:
        ok &= not psub(getattr(H, co), total(co))
    ok &= not psub(getattr(H, "m"), padd(total("m"), tri("f", "h")))
    ok &= not psub(getattr(H, "n"), padd(total("n"), tri("g", "i")))
    ok &= not psub(getattr(H, "o"), padd(total("o"), tri("f", "l"), tri("j", "i")))
    return ok


for h in range(0, 5):
    check("handle block closed form at h = %d" % h, handle_block_check(h))

# ================================================== 4 the assembled defect

say()
say("## 4 The assembled class-five defect")
say("  (sqRelWord m).o = -4 (m 1).o + 2 (m 2).o + sqU6Defect h m,")
say("  sqU6Defect h m = sqU6Core (m 0) (m 1) (m 2)")
say("                 + W.a * H.n + W.f * H.l + W.j * H.i + H.o")
say("  with W = sqWord (m 0) (m 1) (m 2) and H the handle block.")


def defect_check(h):
    m = [U6.gen("m%d" % i) for i in range(3 + 2 * h)]
    R = sqRelWord(m, h)
    Wm = sqWord(m[0], m[1], m[2])
    us = [m[3 + 2 * j] for j in range(h)]
    vs = [m[4 + 2 * j] for j in range(h)]
    H = handleWord(us, vs)
    head = padd(pscale(-4, pvar("m1_o")), pscale(2, pvar("m2_o")))
    defect = padd(
        psub(Wm.o, padd(pscale(-4, pvar("m1_o")), pscale(2, pvar("m2_o")))),
        pmul(Wm.a, H.n), pmul(Wm.f, H.l), pmul(Wm.j, H.i), H.o)
    return not psub(R.o, padd(head, defect))


for h in range(0, 4):
    check("assembled defect at h = %d (generic marking)" % h, defect_check(h))

# ==================================================== 5 the class-four row

say()
say("## 5 The class-four row, for the same reason")
say("  (sqRelWord m).m = -4 (m 1).m + 2 (m 2).m + sqU6Defect4 h m,")
say("  sqU6Defect4 h m = sqU6Core4 (m 0) (m 1) (m 2) + W.a * H.k + W.f * H.h + H.m")


def defect4_check(h):
    m = [U6.gen("m%d" % i) for i in range(3 + 2 * h)]
    R = sqRelWord(m, h)
    Wm = sqWord(m[0], m[1], m[2])
    us = [m[3 + 2 * j] for j in range(h)]
    vs = [m[4 + 2 * j] for j in range(h)]
    H = handleWord(us, vs)
    head = padd(pscale(-4, pvar("m1_m")), pscale(2, pvar("m2_m")))
    defect = padd(psub(Wm.m, head), pmul(Wm.a, H.k), pmul(Wm.f, H.h), H.m)
    return not psub(R.m, padd(head, defect))


for h in range(0, 4):
    check("assembled class-four defect at h = %d (generic marking)" % h,
          defect4_check(h))

# ============================================================ 6 the printout

say()
say("## 6 The two new core polynomials, term by term")


def show(name, p):
    say()
    say("### %s (%d terms, degree %d)" % (name, len(p), pdeg(p)))
    for mon, c in poly_terms(p):
        say("  %+d  %s" % (c, " * ".join(mon) if mon else "1"))


show("sqU6Core4  =  (sqWord s x y).m  -  (-4 x.m + 2 y.m)", core["m"])
show("sqU6Core   =  (sqWord s x y).o  -  (-4 x.o + 2 y.o)", core["o"])

with open(os.path.join(OUT, "derive.txt"), "w") as fh:
    fh.write("\n".join(LOG) + "\n")

print()
print("wrote %s" % os.path.join(OUT, "derive.txt"))
