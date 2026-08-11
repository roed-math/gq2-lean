"""W63-SECOND, part 2: the second block reading against honestly collected relators.

Everything here is measured against relator-killing markings produced by the wave-61 layered
solve, which is written WITHOUT any parity fact: at each of the fifteen rows it computes
`sqWord` honestly and only asks whether the residual is even.  Row `h` failing IS the second
block equation failing, and section B turns that into a two-directional characterisation.

Sections
--------
A  the block equation and the symplectic identity, at all four class-two rows, against
   honestly collected relator-killing markings at handle counts `0..4`;
B  ⭐ the layered solve's class-two rows characterise the four block equations, in both
   directions;
C  ⭐⭐ the `h = 0` forcing for the SECOND reading, and a core pair that requires a handle;
D  the second pairing is an ALTERNATING BI-ADDITIVE form mod `2`, with controls;
E  the torsion letter's `(3,4)`- and `(4,5)`-columns are even at every relator-killing
   marking, exhaustively;
F  ⭐⭐ the `h = 0` vanishing of the second form on EVERY pair, exhaustively over the mod-2
   generator data, with both hypotheses dropped in turn as controls;
G  the second channel sits below the achievable lattice, exactly as the first does.

Run: `python3 scripts/w63_second/census_second.py > scripts/w63_second/results/census_second.txt`
"""

import itertools
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import secondlib  # noqa: E402
from secondlib import (  # noqa: E402
    FIRST, M, ROWS, ROW_ENTRY, SECOND, U6, collect, commP, handle_block, handle_word,
    minor_sum, par, rand, red, rel_of, rel_word, rinv, rmul, show, solve_x1, wedge, wedge_par,
)
from u6lib import NAMES  # noqa: E402

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok)))
    print(f"[{'ok ' if ok else 'FAIL'}] {name}{('  ' + detail) if detail else ''}")


def head(s):
    print()
    print("## " + s)
    print()


rng = random.Random(6363063)

print("=" * 86)
print("W63-SECOND  census_second.py   the (3,5) reading against honest relators")
print("=" * 86)

# --------------------------------------------------------------------------------------
head("A  the block equation at all four class-two rows, at honest relator-killing markings")

print("    Markings are built the honest way round: random handle letters first, then the")
print("    layered solve for the x1 slot against the target handleWord^{-1}.  Every one is")
print("    re-verified by recomputing all fifteen rows of sqRelWord from the letters.")
print()

marks = []
for h in range(5):
    for _ in range(140):
        m = collect(rng, h, 1, tries=200)
        if m:
            marks.append(m[0])
per_h = {}
for m in marks:
    per_h[m["h"]] = per_h.get(m["h"], 0) + 1
print("    collected: " + ", ".join(f"h = {h}: {per_h.get(h, 0)}" for h in range(5))
      + f"   (total {len(marks)})")
print()

bad = 0
for m in marks:
    w = rel_word(m["s"], m["x"], m["y"], m["us"], m["vs"])
    if any(w.co[k] % M != 0 for k in NAMES):
        bad += 1
check("control: every collected marking really kills the relator, all fifteen rows",
      bad == 0, f"{len(marks)} markings, {bad} live rows")

bad_neg = 0
for m in marks:
    core = secondlib.rsqWord(m["s"], m["x"], m["y"])
    for r in ROWS:
        if (handle_block(m, r) + core.co[r]) % M != 0:
            bad_neg += 1
check("handleWord.row = -sqWord.row at all four class-two rows", bad_neg == 0,
      f"{4 * len(marks)} comparisons, {bad_neg} mismatches")

bad_sum = 0
for m in marks:
    for r in ROWS:
        if (handle_block(m, r) - minor_sum(m, r)) % M != 0:
            bad_sum += 1
check("handleWord.row = sum of the handles' wedges, integrally", bad_sum == 0,
      f"{4 * len(marks)} comparisons, {bad_sum} mismatches")

live = {r: 0 for r in ROWS}
bad_eq = {r: 0 for r in ROWS}
for m in marks:
    for r in ROWS:
        if (handle_block(m, r) - wedge(m["s"], m["x"], r)) % 2 != 0:
            bad_eq[r] += 1
        live[r] += wedge_par(m["s"], m["x"], r)
for r in ROWS:
    check(f"⭐⭐ the block equation at row {ROW_ENTRY[r]}", bad_eq[r] == 0,
          f"{len(marks)} markings, {bad_eq[r]} mismatches, "
          f"{live[r]} live ({100.0 * live[r] / max(1, len(marks)):.1f} %)")

bad_sym = {r: 0 for r in ROWS}
for m in marks:
    for r in ROWS:
        if wedge_par(m["s"], m["x"], r) != minor_sum(m, r) % 2:
            bad_sym[r] += 1
check("⭐⭐ the symplectic identity at all four rows", sum(bad_sym.values()) == 0,
      f"{4 * len(marks)} comparisons, {sum(bad_sym.values())} mismatches")

# --------------------------------------------------------------------------------------
head("B  the layered solve's class-two rows CHARACTERISE the four block equations")

print("    For random handle letters, a random sigma slot and a random x0 slot, run the solve")
print("    and record the first row at which the residual came out ODD.  The claim is that")
print("    the first failing row among f, g, h, i is exactly the first of the four block")
print("    equations that fails, and that the solve gets past row i exactly when all four")
print("    hold.  Neither direction is assumed anywhere in the solve.")
print()

order = ["f", "g", "h", "i"]
bad_fwd = 0
bad_bwd = 0
trials = 30000
reached = {r: 0 for r in order}
past = 0
for _ in range(trials):
    hh = rng.randrange(0, 3)
    us = [rand(rng) for _ in range(hh)]
    vs = [rand(rng) for _ in range(hh)]
    hw = handle_word(us, vs)
    s, x = rand(rng), rand(rng)
    y, badrow = solve_x1(s, x, rinv(hw), rng)
    mk = dict(s=s, x=x, y=y, us=us, vs=vs, h=hh)
    predicted = None
    for r in order:
        if (hw.co[r] - wedge(s, x, r)) % 2 != 0:
            predicted = r
            break
    if predicted is not None:
        reached[predicted] += 1
        if badrow != predicted:
            bad_fwd += 1
    else:
        past += 1
        if badrow in order:
            bad_bwd += 1
check("⭐ the first failing class-two row IS the first failing block equation",
      bad_fwd == 0, f"{trials - past} trials with a predicted failure, {bad_fwd} disagreements")
check("⭐ …and the solve gets past all four exactly when all four equations hold",
      bad_bwd == 0, f"{past} trials with no predicted failure, {bad_bwd} disagreements")
print("    first failing row, by row:  "
      + ", ".join(f"{ROW_ENTRY[r]} {reached[r]}" for r in order)
      + f",  none {past}")

# --------------------------------------------------------------------------------------
head("C  the h = 0 forcing for the SECOND reading, and a core pair that requires a handle")

zeros = [m for m in marks if m["h"] == 0]
bad = sum(1 for m in zeros if wedge_par(m["s"], m["x"], SECOND) != 0)
check("at h = 0 the second reading is EVEN, at every collected marking", bad == 0,
      f"{len(zeros)} handle-free markings, {bad} odd")

print()
print("    The sharp form: a core pair whose second reading is ODD admits no relator-killing")
print("    completion at h = 0, whatever the x1 slot.  The pair used here is the mirror of")
print("    wave 59's counterexample core pair one column in:")
CD_S = U6({"c": 1})
CD_X = U6({"d": 1})
print(f"      sigma = {show(CD_S)},  x0 = {show(CD_X)}")
print(f"      second reading  s_34 x_45 - s_45 x_34 = {secondlib.block_read_cd(CD_S, CD_X)}  (ODD)")
print(f"      first reading   s_45 x_56 - s_56 x_45 = "
      f"{wedge(CD_S, CD_X, FIRST)}  (EVEN), so the two disagree here")
print()

# exhaustive over the three x1 coordinates that can enter the (3,5) row
badk = 0
tot = 0
for yc, yd, yh in itertools.product(range(M), repeat=3):
    if (-4 * CD_X.c + 2 * yc) % M != 0:
        continue
    tot += 1
    y = U6({"c": yc, "d": yd, "h": yh})
    if secondlib.rsqWord(CD_S, CD_X, y).co["h"] % M == 0:
        badk += 1
check("no h = 0 completion: the (3,5) row cannot be killed, EXHAUSTIVE on the three "
      "x1 coordinates", badk == 0, f"{tot} admissible values, {badk} kills")

badk0 = 0
tot0 = 0
for yc, yd, yh in itertools.product(range(M), repeat=3):
    tot0 += 1
    y = U6({"c": yc, "d": yd, "h": yh})
    if secondlib.rsqWord(CD_S, CD_X, y).co["h"] % M == 0:
        badk0 += 1
check("…and WITHOUT the relator's (3,4)-row some values do kill it, so the row is needed",
      badk0 > 0, f"{badk0} of {tot0} values kill the (3,5) row")

badr = 0
for _ in range(200000):
    y = rand(rng)
    if secondlib.rsqWord(CD_S, CD_X, y).co["h"] % M == 0 and (-4 * CD_X.c + 2 * y.c) % M == 0:
        badr += 1
check("…and a random sweep of the WHOLE x1 slot finds nothing either",
      badr == 0, f"200000 x1 slots, {badr} kills")

# and it IS realizable at every positive handle count
print()
print("    …and the same core pair IS realized at every h >= 1, with the handle letters")
print("      U = <c=1>, V = <d=1>, whose (3,5) minor is 1:")
CD_U = U6({"c": 1})
CD_V = U6({"d": 1})
found = {}
for hh in range(1, 5):
    us = [CD_U] + [U6() for _ in range(hh - 1)]
    vs = [CD_V] + [U6() for _ in range(hh - 1)]
    hw = handle_word(us, vs)
    for _ in range(4000):
        y, _b = solve_x1(CD_S, CD_X, rinv(hw), rng)
        if y is not None:
            found[hh] = dict(s=CD_S, x=CD_X, y=y, us=us, vs=vs, h=hh)
            break
check("⭐⭐ the CD core pair is relator-killing at every h = 1..4",
      all(hh in found for hh in range(1, 5)),
      f"{len(found)} of 4 handle counts realized")
bad = 0
for hh, mk in found.items():
    if any(rel_of(mk).co[k] % M != 0 for k in NAMES):
        bad += 1
check("control: those markings really kill all fifteen rows", bad == 0,
      f"{len(found)} markings, {bad} live rows")
if 1 in found:
    y1 = found[1]["y"]
    print(f"      at h = 1 the solve returns  x1 = {show(y1)}")
    print(f"      as a fifteen-tuple for Lean:  {secondlib.tuple15(y1)}")
    print(f"      readings there:  (3,5) {wedge_par(CD_S, CD_X, SECOND)},  "
          f"(4,6) {wedge_par(CD_S, CD_X, FIRST)}")

# --------------------------------------------------------------------------------------
head("D  the second pairing is an ALTERNATING BI-ADDITIVE form mod 2")

print("    omegaCD(p, q) = par(p_34 q_45 - p_45 q_34),  p, q in U_6(Z/8).")
print("    It is a form on the group because the (3,4)- and (4,5)-columns are CHARACTERS:")
print("    both are abelian coordinates of U_6, so `SqU6.mul_c` and `SqU6.mul_d` are additive.")
print()


def cd(p, q):
    return par(wedge(p, q, SECOND))


badadd_l = badadd_r = balt = bsym = binv = bcom = 0
for _ in range(20000):
    p, q, r = rand(rng), rand(rng), rand(rng)
    if cd(rmul(p, q), r) != (cd(p, r) + cd(q, r)) % 2:
        badadd_l += 1
    if cd(p, rmul(q, r)) != (cd(p, q) + cd(p, r)) % 2:
        badadd_r += 1
    if cd(p, p) != 0:
        balt += 1
    if cd(p, q) != cd(q, p):
        bsym += 1
    if cd(rinv(p), q) != cd(p, q):
        binv += 1
    if cd(red(commP(p, q)), r) != 0:
        bcom += 1
check("bi-additive on the left", badadd_l == 0, f"20000 triples, {badadd_l} failures")
check("bi-additive on the right", badadd_r == 0, f"20000 triples, {badadd_r} failures")
check("alternating", balt == 0, f"20000 elements, {balt} failures")
check("symmetric mod 2", bsym == 0, f"20000 pairs, {bsym} failures")
check("inverse-invariant mod 2", binv == 0, f"20000 pairs, {binv} failures")
check("kills commutators, so it is a form on the abelianisation", bcom == 0,
      f"20000 triples, {bcom} failures")

bad = 0
tot = 0
for pc, pd, qc, qd, rc, rd in itertools.product(range(M), repeat=6):
    p, q, r = U6({"c": pc, "d": pd}), U6({"c": qc, "d": qd}), U6({"c": rc, "d": rd})
    tot += 1
    if cd(rmul(p, q), r) != (cd(p, r) + cd(q, r)) % 2:
        bad += 1
check("bi-additivity, EXHAUSTIVE on the four live columns", bad == 0,
      f"{tot} points, {bad} failures")

moved = 0
for _ in range(10000):
    p, q, r = rand(rng), rand(rng), rand(rng)
    if wedge(rmul(p, q), r, SECOND) != (wedge(p, r, SECOND) + wedge(q, r, SECOND)) % M:
        moved += 1
check("the INTEGRAL second reading is already additive, so the parity is not doing the work",
      moved == 0, f"10000 triples, {moved} disagreements")

# --------------------------------------------------------------------------------------
head("E  the torsion letter's (3,4)- and (4,5)-columns are EVEN")

bad = 0
tot = 0
for xc, yc in itertools.product(range(M), repeat=2):
    if (-4 * xc + 2 * yc) % M != 0:
        continue
    tot += 1
    if yc % 2 != 0:
        bad += 1
check("(3,4)-row forces y_34 even, EXHAUSTIVE", bad == 0, f"{tot} admissible pairs, {bad} odd")

bad = 0
tot = 0
for xd, yd in itertools.product(range(M), repeat=2):
    if (-4 * xd + 2 * yd) % M != 0:
        continue
    tot += 1
    if yd % 2 != 0:
        bad += 1
check("(4,5)-row forces y_45 even, EXHAUSTIVE", bad == 0, f"{tot} admissible pairs, {bad} odd")

bad = sum(1 for m in marks if m["y"].c % 2 != 0 or m["y"].d % 2 != 0)
check("…and at honestly collected relator-killing markings", bad == 0,
      f"{len(marks)} markings, {bad} odd columns")

bad = 0
for m in marks:
    for _ in range(4):
        g = rand(rng)
        if cd(g, m["y"]) != 0 or cd(m["y"], g) != 0:
            bad += 1
check("hence the x1 slot pairs evenly against EVERYTHING, for the second form too",
      bad == 0, f"{4 * len(marks)} pairings, {bad} odd")

# --------------------------------------------------------------------------------------
head("F  the h = 0 vanishing of the second form on EVERY pair")

print("    At h = 0 the group is generated by sigma, x0, x1.  The form is bi-additive, kills")
print("    commutators, and kills x1 by section E, so it is determined by the mod-2 data")
print("    (sigma_34, sigma_45, x0_34, x0_45), and the relator forces its value on the core")
print("    pair to be 0.  Claim: it then vanishes on every pair of the subgroup.")
print()


def spanned(vecs):
    """Every F_2-combination of the given (c, d) column vectors."""
    out = {(0, 0)}
    for v in vecs:
        out |= {((a + v[0]) % 2, (b + v[1]) % 2) for a, b in out}
    return out


bad = 0
tot = 0
for sc, sd, xc, xd in itertools.product(range(2), repeat=4):
    if (sc * xd - sd * xc) % 2 != 0:
        continue
    tot += 1
    pts = spanned([(sc, sd), (xc, xd), (0, 0)])
    for (ac, ad) in pts:
        for (bc, bd) in pts:
            if (ac * bd - ad * bc) % 2 != 0:
                bad += 1
check("⭐⭐ at h = 0 the second form dies on EVERY pair, EXHAUSTIVE on the mod-2 data",
      bad == 0, f"{tot} admissible data, {bad} live pairs")

live0 = 0
tot0 = 0
for sc, sd, xc, xd in itertools.product(range(2), repeat=4):
    tot0 += 1
    if (sc * xd - sd * xc) % 2 != 0:
        live0 += 1
check("control: DROPPING the relator condition, the form is live", live0 > 0,
      f"{live0} of {tot0} data have a live core pair")

live1 = 0
tot1 = 0
for sc, sd, xc, xd, yc, yd in itertools.product(range(2), repeat=6):
    if (sc * xd - sd * xc) % 2 != 0:
        continue
    tot1 += 1
    pts = spanned([(sc, sd), (xc, xd), (yc, yd)])
    if any((a[0] * b[1] - a[1] * b[0]) % 2 != 0 for a in pts for b in pts):
        live1 += 1
check("control: DROPPING the x1 evenness, the form is live", live1 > 0,
      f"{live1} of {tot1} data have a live pair somewhere")

# --------------------------------------------------------------------------------------
head("G  the second channel sits below the achievable lattice, exactly as the first does")

print("    Every element of gamma_2 has vanishing abelian columns, so no gamma_2-dressing of")
print("    either core slot can move a reading built from two of them.  Measured for both")
print("    readings, with the control that FULL dressings do move them.")
print()

for row, name in [(SECOND, "second (3,5)"), (FIRST, "first (4,6)")]:
    bad = 0
    for _ in range(10000):
        s, x = rand(rng), rand(rng)
        z = rand(rng)
        w = rand(rng)
        for k in "abcde":
            z.co[k] = 0
            w.co[k] = 0
        if wedge(rmul(s, z), rmul(x, w), row) != wedge(s, x, row):
            bad += 1
    check(f"gamma_2-dressings cannot move the {name} reading", bad == 0,
          f"10000 dressings, {bad} moves")
    moved = 0
    for _ in range(10000):
        s, x = rand(rng), rand(rng)
        z, w = rand(rng), rand(rng)
        if wedge(rmul(s, z), rmul(x, w), row) != wedge(s, x, row):
            moved += 1
    check(f"control: FULL dressings do move the {name} reading", moved > 0,
          f"{moved} of 10000 dressings move it")

# --------------------------------------------------------------------------------------
print()
print("=" * 86)
okc = sum(1 for _, o in CHECKS if o)
print(f"{okc} of {len(CHECKS)} checks passed, {len(CHECKS) - okc} failures")
print("=" * 86)
sys.exit(0 if okc == len(CHECKS) else 1)
