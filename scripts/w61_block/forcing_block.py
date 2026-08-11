"""W61-BLOCK, part 3: the forcing, and the soundness that comes with it.

Sections
--------
A  ⭐⭐ which sigma slots admit a relator-killing completion, exactly;
B  the forcing in the campaign's shape, and its exact scope;
C  ⭐⭐⭐ the handle-count separation at wave 59's counterexample core slots, EXHAUSTIVELY;
D  ⭐⭐ the block channel against the honest lower central series of the image subgroup.

Run: `python3 scripts/w61_block/forcing_block.py > scripts/w61_block/results/forcing_block.txt`

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from blocklib import (  # noqa: E402
    LAYERS, NAMES, U6, block_read, eq, handle_word, is_one, par, rand, red, rel_of, rinv,
    rmul, rsqWord, sig_dress, solve_x1,
)
from u6lib import commP  # noqa: E402

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok)))
    print(f"[{'ok ' if ok else 'FAIL'}] {name}{('  ' + detail) if detail else ''}")


rng = random.Random(6106100)

print("=" * 88)
print("W61-BLOCK  forcing_block.py   the forcing, its scope, and its soundness")
print("=" * 88)

# ---------------------------------------------------------------------------------------
print("\n## A  ⭐⭐ which sigma slots admit a relator-killing completion\n")
print("    Fix the handle letters and the x0 slot.  A sigma slot admits a relator-killing")
print("    x1 slot IFF selPar blockRead(s, x) = selPar H_46.  The block equation is not just")
print("    a consequence of relator-killing: it CHARACTERISES the admissible sigma slots.")

agree = dis = adm = 0
for _ in range(2500):
    h = rng.randrange(1, 4)
    us = [rand(rng) for _ in range(h)]
    vs = [rand(rng) for _ in range(h)]
    hw = handle_word(us, vs)
    x = rand(rng)
    for _ in range(12):
        s = rand(rng)
        # only rows a..e and i can obstruct the (4,6) datum; run the two relevant layers
        y = U6()
        ok = True
        tgt = rinv(hw)
        for row in LAYERS[0] + ["i"]:
            resid = (tgt.co[row] - rsqWord(s, x, y).co[row]) % 8
            if resid % 2:
                ok = False
                break
            y.co[row] = (y.co[row] + (resid // 2) % 4 + 4 * rng.randrange(2)) % 8
        predicted = par(hw.i) == par(block_read(s, x))
        if ok == predicted:
            agree += 1
        else:
            dis += 1
        adm += 1 if ok else 0
check("⭐⭐ admissible sigma slots = { selPar blockRead = selPar H_46 }", dis == 0,
      f"{agree} agreements, {dis} disagreements, {adm} admissible")

# ---------------------------------------------------------------------------------------
print("\n## B  the forcing in the campaign's shape, and its exact scope\n")
print("    `a sigma dressing that keeps the relator killed must have an even bit`:")
print("      selPar( v_45 * x_56 - v_56 * x_45 ) = 0.")

# genuine relator-preserving sigma dressings, found by solving rather than by rejection
found = viol = 0
for _ in range(1200):
    h = rng.randrange(1, 3)
    us = [rand(rng) for _ in range(h)]
    vs = [rand(rng) for _ in range(h)]
    hw = handle_word(us, vs)
    s, x = rand(rng), rand(rng)
    y, badrow = solve_x1(s, x, rinv(hw), rng)
    if y is None:
        continue
    mk = dict(s=s, x=x, y=y, us=us, vs=vs, h=h)
    for _ in range(240):
        v = rand(rng, rng.sample(NAMES, rng.randrange(1, 4)))
        if is_one(rel_of(sig_dress(mk, v))):
            found += 1
            if par((v.d * x.e - v.e * x.d) % 8) != 0:
                viol += 1
check("⭐⭐ relator-preserving sigma dressings pair EVENLY against the x0 slot", viol == 0,
      f"{found} relator-preserving dressings, {viol} odd pairings")

print("\n    …and the scope, stated because it decides what the forcing is worth:")
dg = sum(1 for _ in range(2000)
         if (lambda x: par((x.d * x.e - x.e * x.d) % 8) == 0)(rand(rng)))
check("the DIAGONAL dressing v = x0 always pairs evenly (a minor of a slot against itself)",
      dg == 2000, "2000 of 2000")
g2 = 0
for _ in range(2000):
    v = rand(rng, [k for k in NAMES if k not in "abcde"])
    x = rand(rng)
    if par((v.d * x.e - v.e * x.d) % 8) == 0:
        g2 += 1
check("every gamma_2-dressing pairs evenly", g2 == 2000, "2000 of 2000")
ab = 0
for _ in range(2000):
    v, x = rand(rng, ["d", "e"]), rand(rng)
    if par((v.d * x.e - v.e * x.d) % 8) == 1:
        ab += 1
check("…so the forcing bites exactly on ABELIAN dressings, and there it is not vacuous",
      ab > 0, f"{ab} of 2000 abelian dressings pair oddly")

# ---------------------------------------------------------------------------------------
print("\n## C  ⭐⭐⭐ the handle-count separation, exhaustively\n")

cexS, cexX = U6({"b": 1, "e": 1}), U6({"d": 1, "g": 1, "l": 1})
cexY = U6({"d": 2, "g": 2, "k": 1, "l": 2, "n": 1})
cex = dict(s=cexS, x=cexX, y=cexY, us=[U6({"d": 1})], vs=[U6({"e": 1})], h=1)
check("h = 1: the committed marking kills the relator (GradedFiveBlind)", is_one(rel_of(cex)))
print(f"    blockRead(sigma, x0) = {block_read(cexS, cexX)}  (odd)")

print("\n    h = 0: EVERY x1 slot, exhaustively.  W_46 depends on the x1 slot only through")
print("    y_45, y_56 and y_46, so 8^3 = 512 values decide it; the other twelve coordinates")
print("    cannot enter.  The relator's own (4,5)-row `-4*x_45 + 2*y_45 = 0` is imposed,")
print("    because a marking that kills the relator kills that row too.")
alive = free = tested = 0
for yd in range(8):
    for ye in range(8):
        for yi in range(8):
            tested += 1
            y = U6({"d": yd, "e": ye, "i": yi})
            if rsqWord(cexS, cexX, y).i != 0:
                continue
            free += 1
            if (-4 * cexX.d + 2 * yd) % 8 == 0:
                alive += 1
check("⭐⭐⭐ no x1 slot kills the (4,6) row at h = 0", alive == 0,
      f"{tested} values of (y_45, y_56, y_46), {alive} kills")
check("…and the (4,5)-row is load-bearing: without it there ARE kills", free > 0,
      f"{free} of {tested} kill the (4,6) row when the (4,5)-row is dropped")

print("\n    a wider sweep, all fifteen x1 coordinates random, for the whole relator:")
bad = 0
for _ in range(300000):
    y = rand(rng)
    if is_one(rsqWord(cexS, cexX, y)):
        bad += 1
check("…and none of 300000 random x1 slots kills the relator at h = 0", bad == 0)

# ---------------------------------------------------------------------------------------
print("\n## D  ⭐⭐ the block channel against the honest image subgroup\n")
print("    The campaign's achievable refinements are gamma_3- and gamma_4-dressings of the")
print("    IMAGE subgroup <sigma, x0, x1, u_j, v_j>.  Every element of gamma_2 of the CARRIER")
print("    already has vanishing abelian columns, so no achievable dressing at any stage from")
print("    two upwards can move the block reading.  Measured on the honest lower central")
print("    series of the image at wave 59's counterexample point:")


def closure(gens, cap=400000):
    seen = {tuple(U6().co[k] for k in NAMES)}
    frontier = [U6()]
    gl = list(gens)
    while frontier:
        nxt = []
        for p in frontier:
            for g in gl:
                q = rmul(p, g)
                key = tuple(q.co[k] % 8 for k in NAMES)
                if key not in seen:
                    seen.add(key)
                    nxt.append(q)
                    if len(seen) > cap:
                        return None
        frontier = nxt
    return seen


gens = [cexS, cexX, cexY, cex["us"][0], cex["vs"][0]]
lower = [gens]
for _ in range(5):
    nxt = [red(commP(a, g)) for a in lower[-1] for g in gens]
    nxt = [p for p in nxt if not is_one(p)]
    lower.append(nxt)
for k in range(2, 6):
    cl = closure(lower[k - 1] + [p for lvl in lower[k:] for p in lvl])
    if cl is None:
        print(f"    gamma_{k}(im): larger than the cap")
        continue
    bad_de = sum(1 for t in cl if t[3] % 8 or t[4] % 8)
    print(f"    |gamma_{k}(im)| = {len(cl):>6}   elements with a nonzero (4,5) or (5,6) "
          f"column: {bad_de}")
    check(f"gamma_{k}(im) cannot move the block reading", bad_de == 0)

# ---------------------------------------------------------------------------------------
print("\n" + "=" * 88)
okc = sum(1 for _, o in CHECKS if o)
print(f"{okc} of {len(CHECKS)} checks passed, {len(CHECKS) - okc} failures")
print("=" * 88)
sys.exit(0 if okc == len(CHECKS) else 1)
