"""W61-BLOCK, part 2: the block reading against honest group collection.

Every marking used here is produced by the layered solve of `blocklib.solve_x1`, which knows
nothing about the block equation: it asks only whether each row's residual is even.  So the
census is a test and not a restatement.

Sections
--------
A  relator-killing markings at handle counts 0..4: the block equation, honest;
B  row `i` of the layered solve is solvable IFF the block equation holds, both directions;
C  ⭐⭐ the `h = 0` forcing: no handles, no odd block reading;
D  the class-five bit collapse at relator-killing markings and arbitrary `nu'`-trivial
   dressings, against honestly collected relators;
E  the block ELEMENT is pinned outright, and what freedom the handle letters keep;
F  what an odd block reading costs the handle letters;
G  ⭐⭐⭐ the block channel sits BELOW the achievable lattice: invariance under
   `gamma_2`- and `gamma_3`-dressings of every slot;
H  the committed points of waves 58 and 59, re-measured.

Run: `python3 scripts/w61_block/census_block.py > scripts/w61_block/results/census_block.txt`
"""

import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from blocklib import (  # noqa: E402
    LAYERS, NAMES, U6, block_read, coupling, eq, handle_minor, handle_word, is_one, par, rand,
    random_relator_marking, red, rel_of, rinv, rmul, rsqWord, sig_dress, solve_x1,
)
from u6lib import sqWord_matrix  # noqa: E402

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok)))
    print(f"[{'ok ' if ok else 'FAIL'}] {name}{('  ' + detail) if detail else ''}")


rng = random.Random(610610)
NOB = [k for k in NAMES if k != "b"]

print("=" * 88)
print("W61-BLOCK  census_block.py   the block reading against honest group collection")
print("=" * 88)

# ---------------------------------------------------------------------------------------
print("\n## A  relator-killing markings at handle counts 0..4\n")

pool = {}
for h in range(5):
    marks = []
    for _ in range(900):
        mk = random_relator_marking(rng, h, tries=40)
        if mk is not None:
            marks.append(mk)
    pool[h] = marks
    print(f"    h = {h}:  {len(marks)} relator-killing markings found")

allm = [mk for h in pool for mk in pool[h]]
check("every marking really kills all fifteen rows", all(is_one(rel_of(mk)) for mk in allm),
      f"{len(allm)} markings")

mis = 0
for mk in allm[:80]:
    acc = red(sqWord_matrix(mk["s"], mk["x"], mk["y"]))
    for u, v in zip(mk["us"], mk["vs"]):
        um, vm = u.matrix(), v.matrix()
        acc = rmul(acc, red(U6.of_matrix(um.inv() * vm.inv() * um * vm)))
    if not is_one(acc):
        mis += 1
check("…by honest 6 x 6 matrix collection too", mis == 0, f"80 markings, {mis} mismatches")

bad = [mk for mk in allm
       if par(handle_word(mk["us"], mk["vs"]).i) != par(block_read(mk["s"], mk["x"]))]
check("⭐⭐ THE BLOCK EQUATION  selPar H_46 = selPar (s_45 x_56 - s_56 x_45)",
      not bad, f"{len(allm)} markings, {len(bad)} mismatches")

odd = [mk for mk in allm if par(block_read(mk["s"], mk["x"])) == 1]
print(f"    of which {len(odd)} have an ODD block reading "
      f"({100.0 * len(odd) / max(1, len(allm)):.1f} %)")

badx = [mk for mk in allm
        if (handle_word(mk["us"], mk["vs"]).i + rsqWord(mk["s"], mk["x"], mk["y"]).i) % 8 != 0]
check("…and the exact pinning  H_46 = -W_46  (Lean `handleWord_i_of_relator`)", not badx)

# ---------------------------------------------------------------------------------------
print("\n## B  row `i` of the layered solve, in isolation\n")
print("    W_46 depends on the x1 slot only through y_45, y_56 (the abelian layer) and y_46")
print("    itself, so row `i` can be tested on its own once the abelian layer is fixed - and")
print("    that layer always solves, because a handle block has vanishing abelian rows.")
print("    Row `i` is solvable IFF the block equation holds.  The solver assumes neither.")

agree = dis = 0
for _ in range(20000):
    h = rng.randrange(1, 4)
    us = [rand(rng) for _ in range(h)]
    vs = [rand(rng) for _ in range(h)]
    hw = handle_word(us, vs)
    tgt = rinv(hw)
    s, x = rand(rng), rand(rng)
    y = U6()
    ok_layer1 = True
    for row in LAYERS[0]:
        resid = (tgt.co[row] - rsqWord(s, x, y).co[row]) % 8
        if resid % 2:
            ok_layer1 = False
            break
        y.co[row] = (y.co[row] + (resid // 2) % 4 + 4 * rng.randrange(2)) % 8
    if not ok_layer1:
        continue
    resid_i = (tgt.i - rsqWord(s, x, y).i) % 8
    row_i_solvable = resid_i % 2 == 0
    predicted = par(hw.i) == par(block_read(s, x))
    if row_i_solvable == predicted:
        agree += 1
    else:
        dis += 1
check("row `i` solvable  <=>  block equation holds, BOTH directions", dis == 0,
      f"{agree} agreements, {dis} disagreements")

# ---------------------------------------------------------------------------------------
print("\n## C  ⭐⭐ the h = 0 forcing\n")
print("    At h = 0 the relator IS the core word, so H_46 = 0 and the block equation reads")
print("    `s_45 x_56 - s_56 x_45` EVEN.  Contrapositive: a relator-killing marking with an")
print("    ODD block reading forces h >= 1.")

zero = pool[0]
check("h = 0: every relator-killing marking has EVEN block reading",
      all(par(block_read(mk["s"], mk["x"])) == 0 for mk in zero), f"{len(zero)} markings")

hits = miss = 0
for _ in range(8000):
    s, x = rand(rng), rand(rng)
    if par(block_read(s, x)) != 1:
        continue
    y, badrow = solve_x1(s, x, U6(), rng)
    if y is None:
        hits += 1
    else:
        miss += 1
check("h = 0: an ODD block reading is never completable to a relator-killing marking",
      miss == 0, f"{hits} odd (s,x) pairs, all rejected; {miss} completions")

print("\n    …and at h >= 1 an odd block reading IS realizable:")
for h in range(1, 5):
    o = [mk for mk in pool[h] if par(block_read(mk["s"], mk["x"])) == 1]
    print(f"    h = {h}:  {len(o)} of {len(pool[h])} relator-killing markings have odd block")
check("odd block readings exist at every h >= 1",
      all(any(par(block_read(mk["s"], mk["x"])) == 1 for mk in pool[h]) for h in range(1, 5)))

# ---------------------------------------------------------------------------------------
print("\n## D  the class-five bit collapse, against honestly collected relators\n")
print("    claim:  selPar[ Delta_v relator.o ]  =  selPar[ Delta_v coreword.o ]")
print("                                          + selPar[coupling] * selPar[blockRead]")
print("    at EVERY relator-killing marking, EVERY sigma slot, EVERY nu'-trivial dressing.")

gauged = [mk for mk in allm if mk["x"].b % 8 == 0 and mk["y"].b % 8 == 0]
print(f"    markings on the nu'-gauge (x.b = y.b = 0): {len(gauged)} of {len(allm)}")
cmp_n = mism = live = 0
for mk in gauged:
    for _ in range(40):
        v = rand(rng, NOB)
        dm = sig_dress(mk, v)
        lhs = par((rel_of(dm).o - rel_of(mk).o) % 8)
        core = par((rsqWord(rmul(mk["s"], v), mk["x"], mk["y"]).o
                    - rsqWord(mk["s"], mk["x"], mk["y"]).o) % 8)
        chan = par(coupling(v, mk["s"], mk["x"])) * par(block_read(mk["s"], mk["x"]))
        cmp_n += 1
        if lhs != (core + chan) % 2:
            mism += 1
        live += chan
check("⭐⭐⭐ the bit collapse", mism == 0, f"{cmp_n} comparisons, {mism} mismatches")
print(f"    the block channel is LIVE (odd contribution) at {live} of {cmp_n} "
      f"({100.0 * live / max(1, cmp_n):.1f} %)")

mis2 = 0
for mk in gauged[:300]:
    for _ in range(8):
        v = rand(rng, NOB)
        lhs = (rel_of(sig_dress(mk, v)).o - rel_of(mk).o) % 8
        rhs = ((rsqWord(rmul(mk["s"], v), mk["x"], mk["y"]).o
                - rsqWord(mk["s"], mk["x"], mk["y"]).o)
               + coupling(v, mk["s"], mk["x"]) * handle_word(mk["us"], mk["vs"]).i) % 8
        if lhs != rhs:
            mis2 += 1
check("the wave-58 coupling identity, integrally", mis2 == 0)

# ---------------------------------------------------------------------------------------
print("\n## E  the block ELEMENT is pinned outright\n")
print("    `sqRelWord m = 1` says handleWord = sqWord^{-1}: the WHOLE block element, not")
print("    just its (4,6) coordinate, is a function of the three core slots.  So the")
print("    class-five bit is core-determined for a trivial reason, and the content of the")
print("    block equation is the CLOSED FORM of the pinned coordinate's parity - four core")
print("    entries out of thirty, and no evaluation of sqWord at all.")

bad = [mk for mk in allm
       if not eq(handle_word(mk["us"], mk["vs"]), rinv(rsqWord(mk["s"], mk["x"], mk["y"])))]
check("handleWord = sqWord^{-1} at every relator-killing marking, all fifteen rows", not bad)

print("\n    the freedom that remains: same core slots, different handle letters and counts.")
fam = 0
bitdiff = 0
tot = 0
for mk in allm:
    if mk["h"] == 0:
        continue
    # (i) shift a handle letter by a central element: the commutator is unchanged
    us2 = list(mk["us"])
    us2[0] = rmul(us2[0], U6({"o": rng.randrange(8)}))
    alt1 = dict(mk, us=us2)
    # (ii) append a dead handle pair: a different HANDLE COUNT, same block
    alt2 = dict(mk, us=list(mk["us"]) + [rand(rng)], vs=list(mk["vs"]) + [U6()],
                h=mk["h"] + 1)
    for alt in (alt1, alt2):
        if not is_one(rel_of(alt)):
            continue
        fam += 1
        for _ in range(6):
            v = rand(rng, NOB)
            b0 = par((rel_of(sig_dress(mk, v)).o - rel_of(mk).o) % 8)
            b1 = par((rel_of(sig_dress(alt, v)).o - rel_of(alt).o) % 8)
            tot += 1
            if b0 != b1:
                bitdiff += 1
check("alternative handle configurations still kill the relator", fam > 0,
      f"{fam} alternatives built")
check("…and every one has the SAME class-five selection bit", bitdiff == 0,
      f"{tot} comparisons, {bitdiff} separations")

# ---------------------------------------------------------------------------------------
print("\n## F  what an odd block reading costs the handle letters\n")
print("    H_46 = sum_j (u_j,45 v_j,56 - u_j,56 v_j,45): a sum of 2x2 minors in the")
print("    (4,5)/(5,6) columns.  Odd block reading => at least one handle's minor is odd.")

bad = 0
for mk in allm:
    if par(block_read(mk["s"], mk["x"])) == 1:
        if not any(par(handle_minor(u, v)) == 1 for u, v in zip(mk["us"], mk["vs"])):
            bad += 1
check("odd block reading => some handle pair has an ODD minor", bad == 0)

bad = 0
for mk in allm:
    tot = sum(handle_minor(u, v) for u, v in zip(mk["us"], mk["vs"]))
    if par(tot) != par(block_read(mk["s"], mk["x"])):
        bad += 1
check("…and the minors sum to the block reading, mod 2", bad == 0)

print("\n    the two handle letters of that pair must be INDEPENDENT mod 2 in the two")
print("    columns (4,5) and (5,6): an odd 2x2 minor is exactly independence over F_2.")

# ---------------------------------------------------------------------------------------
print("\n## G  ⭐⭐⭐ the block channel sits BELOW the achievable lattice\n")
print("    Every element of gamma_2 has vanishing abelian columns, so a gamma_2-dressing of")
print("    ANY slot leaves the (4,5)- and (5,6)-columns alone and cannot move blockRead.")
print("    Every element of gamma_3 has vanishing class-two columns too, so a gamma_3-")
print("    dressing cannot move the COUPLING either.  The campaign's achievable refinements")
print("    live in gamma_4 at class five and in gamma_3 at the one filtration step wider")
print("    that produced wave 59's hole; both are inside gamma_3.")

GA2 = [k for k in NAMES if k not in "abcde"]
GA3 = [k for k in NAMES if k not in "abcdefghi"]
moved_blk = moved_cpl = trials = 0
for mk in allm[:400]:
    s, x = mk["s"], mk["x"]
    b0 = par(block_read(s, x))
    for _ in range(25):
        z0, z1 = rand(rng, GA2), rand(rng, GA2)
        s2, x2 = rmul(s, z0), rmul(x, z1)
        trials += 1
        if par(block_read(s2, x2)) != b0:
            moved_blk += 1
        v = rand(rng, NOB)
        w0, w1 = rand(rng, GA3), rand(rng, GA3)
        if par(coupling(v, rmul(s, w0), rmul(x, w1))) != par(coupling(v, s, x)):
            moved_cpl += 1
check("⭐⭐⭐ no gamma_2-dressing of any slot moves the block reading", moved_blk == 0,
      f"{trials} dressings")
check("⭐⭐⭐ no gamma_3-dressing of any slot moves the coupling parity", moved_cpl == 0,
      f"{trials} dressings")

print("\n    the CONTROL: gamma_2-dressings DO move the coupling, and gamma_1-dressings do")
print("    move the block reading, so neither invariance is vacuous.")
mv_c = mv_b = 0
for mk in allm[:400]:
    s, x = mk["s"], mk["x"]
    for _ in range(25):
        v = rand(rng, NOB)
        if par(coupling(v, s, rmul(x, rand(rng, GA2)))) != par(coupling(v, s, x)):
            mv_c += 1
        if par(block_read(rmul(s, rand(rng)), x)) != par(block_read(s, x)):
            mv_b += 1
check("gamma_2-dressings move the coupling parity", mv_c > 0, f"{mv_c} of {trials}")
check("full dressings move the block reading", mv_b > 0, f"{mv_b} of {trials}")

# ---------------------------------------------------------------------------------------
print("\n## H  the committed points, re-measured\n")

fiveX = U6({"g": 1})
fiveY = U6({"g": 2, "i": 3, "n": 1})
live = dict(s=U6(), x=fiveX, y=fiveY, us=[U6({"d": 1})], vs=[U6({"e": 2})], h=1)
check("GradedFive.liveFiveMark kills the relator", is_one(rel_of(live)))
print(f"    blockRead = {block_read(live['s'], live['x'])},  H_46 = "
      f"{handle_word(live['us'], live['vs']).i}   -> both EVEN, as the theorem says")
check("liveFiveMark: block equation",
      par(handle_word(live["us"], live["vs"]).i) == par(block_read(live["s"], live["x"])))
print("    ⭐ and GradedFive.deadFiveMark - the marking wave 58 compares it against - does")
print("      NOT kill the relator, which is the whole reason the block looked visible:")
dead = dict(live, us=[U6()], vs=[U6()])
check("deadFiveMark does NOT kill the relator", not is_one(rel_of(dead)))

cexS, cexX = U6({"b": 1, "e": 1}), U6({"d": 1, "g": 1, "l": 1})
cex = dict(s=cexS, x=cexX, y=U6({"d": 2, "g": 2, "k": 1, "l": 2, "n": 1}),
           us=[U6({"d": 1})], vs=[U6({"e": 1})], h=1)
check("GradedFiveBlind.blindCexMark kills the relator", is_one(rel_of(cex)))
print(f"    blockRead = {block_read(cex['s'], cex['x'])},  H_46 = "
      f"{handle_word(cex['us'], cex['vs']).i}   -> both ODD")
check("blindCexMark: block equation",
      par(handle_word(cex["us"], cex["vs"]).i) == par(block_read(cex["s"], cex["x"])))
print("    ⭐ so wave 59's counterexample is not a free odd block: its own core slots")
print("      predict the odd block coordinate, and that is what the bit reads.")

dressed = rel_of(sig_dress(cex, U6({"a": 1})))
print("    the a0-dressed relator at blindCex: "
      + ", ".join(f"{k}={dressed.co[k] % 8}" for k in NAMES if dressed.co[k] % 8))
check("⚠ it is NOT a central translation, so blindCex is not itself a forcing witness",
      any(dressed.co[k] % 8 for k in NAMES if k != "o"))

# ---------------------------------------------------------------------------------------
print("\n" + "=" * 88)
okc = sum(1 for _, o in CHECKS if o)
print(f"{okc} of {len(CHECKS)} checks passed, {len(CHECKS) - okc} failures")
print("=" * 88)
sys.exit(0 if okc == len(CHECKS) else 1)
