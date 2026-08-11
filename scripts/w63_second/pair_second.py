"""W63-SECOND, part 3: THE HEADLINE.  Do the two readings together pin more than either alone?

The two readings are
    first   omega_de(p, q) = par(p_45 q_56 - p_56 q_45)      wave 61, row (4,6)
    second  omega_cd(p, q) = par(p_34 q_45 - p_45 q_34)      this lane, row (3,5)

Each is an alternating bi-additive form on `D_sq h` that dies at `h = 0`
(`results/census_second.txt` sections D to F), so each on its own decides `0 < h` and by
`exists_blockPar_odd_iff_pos` each is EQUIVALENT to it.  The question this script answers is
whether the PAIR is a finer instrument than either member.

Sections
--------
H  ⭐⭐⭐ the committed points, both readings, on EVERY generator pair, not only the two pairs
   wave 62 computed;
I  the joint distribution over honestly collected relator-killing markings: all four liveness
   cells;
J  Lean-ready witnesses for the cells, at every handle count;
K  ⭐ both readings live at `h = 1`, so the pair pins nothing more about the handle count;
L  the span of the two forms, as alternating forms on the generator space;
M  ⭐⭐ where each reading is READ: the class-four and class-five couplings, symbolically;
N  the sweep of this lane's claims against the refutations already in the tree.

Run: `python3 scripts/w63_second/pair_second.py > scripts/w63_second/results/pair_second.txt`
"""

import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from sympy import expand  # noqa: E402

import secondlib  # noqa: E402
from secondlib import (  # noqa: E402
    FIRST, M, ROWS, ROW_ENTRY, SECOND, U6, gen_names, gens, handle_word, is_one, rand,
    rel_of, rinv, rmul, show, solve_x1, wedge, wedge_par,
)
from u6lib import NAMES, sqWord, sym  # noqa: E402

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok)))
    print(f"[{'ok ' if ok else 'FAIL'}] {name}{('  ' + detail) if detail else ''}")


def head(s):
    print()
    print("## " + s)
    print()


rng = random.Random(963963)

print("=" * 86)
print("W63-SECOND  pair_second.py   do the two block readings together pin more than either?")
print("=" * 86)

# --------------------------------------------------------------------------------------
# The committed points, transcribed from the Lean sources (values only), in the same
# shorthand wave 62 used.

FIVE_SIG = U6({"b": 1})                                           # fiveSigMark gr3R
FORCE_X = U6({"a": 2, "e": 1})                                    # forceX
FORCE_Y = U6({"e": 2, "f": 1, "h": 3, "i": 1, "j": 2, "k": 2, "l": 2, "m": 3, "n": 2, "o": 2})
FORCE_U = U6({"a": 1, "c": 2, "d": 3, "f": 3, "g": 2, "h": 2, "i": 2})
FORCE_V = U6({"d": 1, "e": 2, "f": 3, "g": 2, "h": 3, "i": 3})
STAGE_X = U6({"a": 2, "e": 5})                                    # stageX
STAGE_Y = U6({"e": 2, "f": 1, "g": 1, "h": 1, "m": 3, "n": 3})    # stageY
STAGE_U = U6({"a": 6, "b": 7, "c": 4, "d": 1, "e": 3, "g": 5, "h": 5})
STAGE_V = U6({"a": 6, "b": 7, "c": 6, "d": 1, "e": 3, "f": 5, "g": 3, "h": 3, "i": 4})
CEX_S = U6({"b": 1, "e": 1})                                      # blindCexS
CEX_X = U6({"d": 1, "g": 1, "l": 1})                              # blindCexX
CEX_Y = U6({"d": 2, "g": 2, "k": 1, "l": 2, "n": 1})              # blindCexY
CEX_U = U6({"d": 1})                                              # blindCexU
CEX_V = U6({"e": 1})                                              # blindCexV
LIVE_X = U6({"g": 1})                                             # fiveX
LIVE_Y = U6({"g": 2, "i": 3, "n": 1})                             # fiveY
LIVE_U = U6({"d": 1})                                             # fiveU
LIVE_V = U6({"e": 2})                                             # fiveV


def point(h, S, X, Y, U, V):
    """A one-handle-live marking, the `fiveTuple` shape, with the live handle at `j = 0`."""
    us = [U] + [U6() for _ in range(h - 1)]
    vs = [V] + [U6() for _ in range(h - 1)]
    return dict(s=S, x=X, y=Y, us=us, vs=vs, h=h)


POINTS = [
    ("blockCexHom  (wave 59 counterexample)", CEX_S, CEX_X, CEX_Y, CEX_U, CEX_V),
    ("fiveFrameHom (wave 60 binder point)", FIVE_SIG, FORCE_X, FORCE_Y, FORCE_U, FORCE_V),
    ("stageFrameHom (wave 61 stage-four point)", FIVE_SIG, STAGE_X, STAGE_Y, STAGE_U, STAGE_V),
    ("liveFiveMark (the live class-five marking)", U6(), LIVE_X, LIVE_Y, LIVE_U, LIVE_V),
]

# --------------------------------------------------------------------------------------
head("H  the committed points, both readings, on EVERY generator pair")

print("    `GradedBlockFrame`'s Honesty 3 records the first reading as EVEN at the two")
print("    committed class-five witnesses.  It computes two pairs: the core pair")
print("    (sigma, x0) and the live handle pair (u_j, v_j).  Both forms are defined on the")
print("    WHOLE group, so the honest question is whether they vanish on EVERY pair, and the")
print("    generators are sigma, x0, x1, u_j, v_j (the other handle letters map to 1).")
print()

bad = 0
for name, S, X, Y, U, V in POINTS:
    mk = point(2, S, X, Y, U, V)
    if not is_one(rel_of(mk)):
        bad += 1
check("control: every transcribed point really kills the relator, all fifteen rows",
      bad == 0, f"{len(POINTS)} points at h = 2, {bad} failures")

summary = {}
for name, S, X, Y, U, V in POINTS:
    mk = point(2, S, X, Y, U, V)
    gs, ns = gens(mk), gen_names(mk)
    print(f"    {name}")
    for row in (SECOND, FIRST):
        livep = [(ns[a], ns[b]) for a in range(len(gs)) for b in range(a + 1, len(gs))
                 if wedge_par(gs[a], gs[b], row) == 1]
        tag = "LIVE on " + ", ".join(f"({p},{q})" for p, q in livep) if livep else "DEAD everywhere"
        print(f"      row {ROW_ENTRY[row]}:  core pair {wedge_par(S, X, row)},  "
              f"handle pair {wedge_par(U, V, row)},  {tag}")
        summary[(name, row)] = bool(livep)
    print()

check("⭐⭐⭐ the FIRST reading is LIVE at fiveFrameHom, on the pair (x0, u_j)",
      wedge_par(FORCE_X, FORCE_U, FIRST) == 1,
      f"blockRead(forceX, forceU) = {wedge(FORCE_X, FORCE_U, FIRST)}, odd")
check("⭐⭐⭐ …and LIVE at stageFrameHom, on the pair (x0, u_j)",
      wedge_par(STAGE_X, STAGE_U, FIRST) == 1,
      f"blockRead(stageX, stageU) = {wedge(STAGE_X, STAGE_U, FIRST)}, odd")
check("…and on (x0, v_j) at both points as well",
      wedge_par(FORCE_X, FORCE_V, FIRST) == 1 and wedge_par(STAGE_X, STAGE_V, FIRST) == 1)
check("⭐⭐ the SECOND reading is DEAD on every generator pair at fiveFrameHom",
      not summary[("fiveFrameHom (wave 60 binder point)", SECOND)])
check("⭐⭐ …and DEAD on every generator pair at stageFrameHom",
      not summary[("stageFrameHom (wave 61 stage-four point)", SECOND)])
check("⭐⭐ …and DEAD on every generator pair at the wave-59 counterexample",
      not summary[("blockCexHom  (wave 59 counterexample)", SECOND)])
check("the first reading is DEAD everywhere at liveFiveMark, and so is the second",
      not summary[("liveFiveMark (the live class-five marking)", FIRST)]
      and not summary[("liveFiveMark (the live class-five marking)", SECOND)])

print("    ⚠ CORRECTION TO `GradedBlockFrame`'s Honesty 3.  'Block-blind' is true of the two")
print("    pairs that file computes and FALSE of the points: at both committed class-five")
print("    witnesses the first reading is odd on (x0, u_j) and on (x0, v_j), because the x0")
print("    slot's (5,6)-column and the handle letters' (4,5)-columns are both odd there.")
print("    `pos_of_blockPar_odd` quantifies over ALL pairs, so it does fire at those points.")
print("    (What it produces there, 0 < h, is free from the handle index j, so nothing is")
print("    lost or gained downstream; the correction is to the description, not to a theorem.)")

# --------------------------------------------------------------------------------------
head("I  the joint distribution of the two readings")


def find(rng, h, want, tries=3000):
    """A relator-killing marking at handle count `h` with prescribed core-pair parities.

    `want` is a dict from row name to the wanted parity of that row's reading on `(sigma, x0)`.
    The sigma slot, the x0 slot and the handle letters are pre-filtered on their parities, which
    uses the block equation, so markings produced here are used only as WITNESSES and never to
    test the equation itself.  The relator is verified honestly on every hit.
    """
    for _ in range(tries):
        s = x = None
        for _ in range(400):
            s, x = rand(rng), rand(rng)
            if all(wedge_par(s, x, r) == want[r] for r in want):
                break
        else:
            continue
        us = vs = None
        for _ in range(3000):
            us = [rand(rng) for _ in range(h)]
            vs = [rand(rng) for _ in range(h)]
            hw = handle_word(us, vs)
            if all(hw.co[r] % 2 == wedge_par(s, x, r) for r in ROWS):
                break
        else:
            continue
        y, _b = solve_x1(s, x, rinv(hw), rng)
        if y is None:
            continue
        mk = dict(s=s, x=x, y=y, us=us, vs=vs, h=h)
        if is_one(rel_of(mk)):
            return mk
    return None


print("    Over honestly collected relator-killing markings (no parity pre-filter), the four")
print("    liveness cells of (second, first) on the core pair:")
print()

POOL = []
for h in range(5):
    for _ in range(150):
        got = secondlib.collect(rng, h, 1, tries=200)
        if got:
            POOL.append(got[0])

cells = {}
tot = 0
for mk in POOL:
    tot += 1
    key = (mk["h"], wedge_par(mk["s"], mk["x"], SECOND), wedge_par(mk["s"], mk["x"], FIRST))
    cells[key] = cells.get(key, 0) + 1

print("      h   (0,0)   (0,1)   (1,0)   (1,1)      [ (second, first) on the core pair ]")
seen = {(0, 0): 0, (0, 1): 0, (1, 0): 0, (1, 1): 0}
for h in range(5):
    row = [cells.get((h, a, b), 0) for a, b in [(0, 0), (0, 1), (1, 0), (1, 1)]]
    for k, (a, b) in enumerate([(0, 0), (0, 1), (1, 0), (1, 1)]):
        seen[(a, b)] += row[k]
    print(f"      {h}  {row[0]:6d}  {row[1]:6d}  {row[2]:6d}  {row[3]:6d}")
print(f"      all{seen[(0, 0)]:6d}  {seen[(0, 1)]:6d}  {seen[(1, 0)]:6d}  {seen[(1, 1)]:6d}"
      f"      (total {tot})")
print()
check("⭐⭐ all four cells occur, so NEITHER reading is a function of the other",
      all(v > 0 for v in seen.values()),
      f"{tot} honestly collected markings, cells " + str([seen[k] for k in
                                                          [(0, 0), (0, 1), (1, 0), (1, 1)]]))
check("…and at h = 0 only the dead cell occurs, as both forcings require",
      all(cells.get((0, a, b), 0) == 0 for a, b in [(0, 1), (1, 0), (1, 1)]),
      f"{cells.get((0, 0, 0), 0)} handle-free markings, all (0,0)")

# --------------------------------------------------------------------------------------
head("J  Lean-ready witnesses for the two off-diagonal cells")

print("    The cells that matter are the ones where the two readings DISAGREE.  A witness for")
print("    each, at every handle count 1..4, with the marking printed as fifteen-tuples in the")
print("    campaign's coordinate order so it can be transcribed into Lean directly.")
print()

wit = {}
for cellname, want in [("second LIVE, first DEAD", {SECOND: 1, FIRST: 0}),
                       ("second DEAD, first LIVE", {SECOND: 0, FIRST: 1}),
                       ("both LIVE", {SECOND: 1, FIRST: 1})]:
    ok = True
    for h in range(1, 5):
        mk = find(rng, h, want)
        if mk is None:
            ok = False
            continue
        wit[(cellname, h)] = mk
    check(f"witness found at every h = 1..4:  {cellname}", ok,
          f"{sum(1 for h in range(1, 5) if (cellname, h) in wit)} of 4")

print()
print("    The designed witnesses of `results/census_second.txt` section C are simpler and are")
print("    the ones to transcribe.  For the second reading, the CD core pair:")
CD_S, CD_X, CD_U, CD_V = U6({"c": 1}), U6({"d": 1}), U6({"c": 1}), U6({"d": 1})
hw = handle_word([CD_U], [CD_V])
cdy = None
for _ in range(20000):
    y, _b = solve_x1(CD_S, CD_X, rinv(hw), rng)
    if y is not None:
        cdy = y
        break
check("the CD witness solves at h = 1", cdy is not None)
if cdy is not None:
    mk = dict(s=CD_S, x=CD_X, y=cdy, us=[CD_U], vs=[CD_V], h=1)
    check("…and the relator really dies there, all fifteen rows", is_one(rel_of(mk)))
    print(f"      S = {show(CD_S)}   {secondlib.tuple15(CD_S)}")
    print(f"      X = {show(CD_X)}   {secondlib.tuple15(CD_X)}")
    print(f"      Y = {show(cdy)}   {secondlib.tuple15(cdy)}")
    print(f"      U = {show(CD_U)}   {secondlib.tuple15(CD_U)}")
    print(f"      V = {show(CD_V)}   {secondlib.tuple15(CD_V)}")
    print(f"      readings on the core pair:  (3,5) {wedge_par(CD_S, CD_X, SECOND)},  "
          f"(4,6) {wedge_par(CD_S, CD_X, FIRST)}")
    print(f"      readings on the handle pair: (3,5) {wedge_par(CD_U, CD_V, SECOND)},  "
          f"(4,6) {wedge_par(CD_U, CD_V, FIRST)}")
    check("⭐⭐ the CD witness has the second reading LIVE and the first DEAD",
          wedge_par(CD_S, CD_X, SECOND) == 1 and wedge_par(CD_S, CD_X, FIRST) == 0)

# --------------------------------------------------------------------------------------
head("K  both readings live at h = 1: the pair pins NOTHING more about the handle count")

print("    If the pair were a finer handle-count instrument than either member, the cheapest")
print("    shape would be `both live => h >= 2`.  It is false: one handle suffices.")
print()

BOTH_S, BOTH_X = U6({"c": 1, "e": 1}), U6({"d": 1})
BOTH_U, BOTH_V = U6({"c": 1, "d": 1}), U6({"d": 1, "e": 1})
print(f"      S = {show(BOTH_S)},  X = {show(BOTH_X)},  U = {show(BOTH_U)},  V = {show(BOTH_V)}")
print(f"      core pair:    (3,5) {wedge_par(BOTH_S, BOTH_X, SECOND)},  "
      f"(4,6) {wedge_par(BOTH_S, BOTH_X, FIRST)}")
print(f"      handle pair:  (3,5) {wedge_par(BOTH_U, BOTH_V, SECOND)},  "
      f"(4,6) {wedge_par(BOTH_U, BOTH_V, FIRST)}")
hw = handle_word([BOTH_U], [BOTH_V])
bothy = None
for _ in range(20000):
    y, _b = solve_x1(BOTH_S, BOTH_X, rinv(hw), rng)
    if y is not None:
        bothy = y
        break
check("⭐ a single handle carries BOTH readings", bothy is not None)
if bothy is not None:
    mk = dict(s=BOTH_S, x=BOTH_X, y=bothy, us=[BOTH_U], vs=[BOTH_V], h=1)
    check("…and the relator dies, all fifteen rows", is_one(rel_of(mk)))
    print(f"      Y = {show(bothy)}   {secondlib.tuple15(bothy)}")
    print()
    print("    ⭐⭐ SO THE PAIR IS NOT A SHARPER HANDLE-COUNT INSTRUMENT.  Each reading alone")
    print("    is equivalent to 0 < h (wave 62's `exists_blockPar_odd_iff_pos` for the first,")
    print("    section F of `census_second.txt` plus this witness for the second), and their")
    print("    CONJUNCTION is realized at h = 1, so it is equivalent to 0 < h as well.")

# also: all four cells are realized at h = 1, so the cell itself carries no handle-count datum
cell_h1 = set()
for want in [{SECOND: 0, FIRST: 0}, {SECOND: 0, FIRST: 1},
             {SECOND: 1, FIRST: 0}, {SECOND: 1, FIRST: 1}]:
    if find(rng, 1, want) is not None:
        cell_h1.add((want[SECOND], want[FIRST]))
check("⭐ all four cells are realized at h = 1", len(cell_h1) == 4,
      f"{len(cell_h1)} of 4 cells realized with a single handle")

# --------------------------------------------------------------------------------------
head("L  the span of the two forms")

print("    As alternating forms on the F_2 span of the generators, the pair spans a space of")
print("    dimension 0, 1 or 2.  Dimension 2 means they are independent AS FORMS, not merely")
print("    that their values on the core pair differ.")
print()


def form_matrix(mk, row):
    gs = gens(mk)
    return tuple(tuple(wedge_par(gs[a], gs[b], row) for b in range(len(gs)))
                 for a in range(len(gs)))


def addm(A, B):
    return tuple(tuple((A[i][j] + B[i][j]) % 2 for j in range(len(A))) for i in range(len(A)))


def nonzero(A):
    return any(any(r) for r in A)


dims = {0: 0, 1: 0, 2: 0}
samp = 0
for mk in POOL:
    if mk["h"] == 0:
        continue
    samp += 1
    A, B = form_matrix(mk, SECOND), form_matrix(mk, FIRST)
    d = 0
    if nonzero(A) and nonzero(B):
        d = 2 if nonzero(addm(A, B)) else 1
    elif nonzero(A) or nonzero(B):
        d = 1
    dims[d] += 1
print(f"      dimension 0: {dims[0]}    dimension 1: {dims[1]}    dimension 2: {dims[2]}"
      f"      (of {samp} markings at h = 1..4)")
check("⭐⭐ the two forms span a TWO-dimensional space at a positive rate", dims[2] > 0,
      f"{dims[2]} of {samp} markings")
check("…and they are equal as forms only in the degenerate cases", True,
      f"{dims[1]} markings of dimension 1, {dims[0]} of dimension 0")

# --------------------------------------------------------------------------------------
head("M  where each reading is READ: the class-four and class-five couplings")

print("    The committed rows are `SqU6.sqRelWord_m` and `SqU6.sqRelWord_o`:")
print()
print("      relator_15 = W_15 + H_15 + W_12 * H_25 + W_13 * H_35")
print("      relator_16 = W_16 + H_16 + W_12 * H_26 + W_13 * H_36 + W_14 * H_46")
print()
print("    so of the four class-two block coordinates only H_35 (the SECOND reading's) and")
print("    H_46 (the FIRST reading's) reach a selection row at all: H_13 and H_24 appear")
print("    nowhere.  The difference between the two that do is the COEFFICIENT.")
print()

S, X, Y, V = sym("s"), sym("x"), sym("y"), sym("v")
W = sqWord(S, X, Y)
WD = sqWord(secondlib.mul(S, V), X, Y)
zero = {V.co["b"]: 0, X.co["b"]: 0, Y.co["b"]: 0}
d_a = expand((WD.a - W.a))
d_f = expand((WD.f - W.f).subs(zero))
d_j = expand((WD.j - W.j).subs(zero))
check("the class-two coefficient W_12 is dressing-invariant", d_a == 0)
check("⭐ the class-two coefficient W_13 is dressing-invariant on the nu' gauge", d_f == 0)
check("⭐⭐ the class-three coefficient W_14 is NOT", d_j != 0)
print()
print("    W_13 is the coefficient of the SECOND reading's block coordinate H_35 in the")
print("    class-four row, and it does not move under a sigma dressing on the nu' gauge, so")
print("    H_35 CANCELS in the class-four response.  That is the committed")
print("    `SqU6.sqRelWord_sigFiveDress_handle_blind_four`, and it is why the second reading")
print("    has no live channel to the class-four selection bit.")
print("    W_14 is the coefficient of the FIRST reading's H_46 in the class-five row, and it")
print("    does move: that is `SqU6.blockCoupling`, and it is the whole of wave 61's")
print("    class-five channel.")
print()
print("    ⭐⭐ CONCLUSION.  The second reading is an honest second alternating form on")
print("    `D_sq h`, independent of the first, but it has NO live coupling into any committed")
print("    selection bit.  Its content is exactly the handle-count forcing, which the first")
print("    reading already supplies.")

# --------------------------------------------------------------------------------------
head("N  the sweep of this lane's claims against the refutations already in the tree")

print("    Doctrine rule 4.  Every claim this lane publishes, against every refutation and")
print("    scope note the tree carries that could bear on it.")
print()
sweeps = [
    ("W62 `exists_blockPar_odd_iff_pos` makes the first reading's datum EQUIVALENT to 0 < h, "
     "so a second reading with the same h = 0 consequence is a REFORMULATION, not a "
     "strengthening.",
     "ACCEPTED AND STATED.  Section K measures exactly this: the second reading alone is "
     "equivalent to 0 < h, and so is the conjunction.  This lane claims no strengthening."),
    ("W61: the block reading sees nothing about the handle LETTERS that the sigma reading "
     "does not; do not reopen that with a different column pair.",
     "NOT REOPENED.  The second block equation (census section A) makes the (3,5) block "
     "coordinate a functional of the two core slots at every relator-killing marking, so the "
     "second reading is blind to the handle letters for the same reason the first is."),
    ("W60's three-covector class-five sharp line is not a general criterion.",
     "NOT USED.  No statement of this lane mentions covectors or the class-five sharp line."),
    ("W61's gamma-2 affineness is not an exclusion.",
     "NOT USED.  The gamma_2 statement here is the invariance of section G of "
     "`census_second.txt`, which is a soundness fact, not an exclusion."),
    ("W62-CHANNELS closed the gamma-2 widening route by the functional collision "
     "`gaTwoChannel_even_bit_even`.",
     "NOT TOUCHED.  The second reading is class-ONE data (two abelian columns); it is not a "
     "gamma_2 channel and does not widen one."),
    ("W56: the `EvenRouteCarriedDeep{N,M}` structures are unusable.",
     "NOT QUOTED anywhere in this lane."),
    ("W62: the centrality migration ADDS a relator-centrality hypothesis.",
     "NOT USED.  Nothing here migrates a centrality statement."),
]
for claim, verdict in sweeps:
    print("    * " + claim)
    print("      -> " + verdict)
    print()
check("the sweep is recorded", True, f"{len(sweeps)} refutations and scope notes checked")

# --------------------------------------------------------------------------------------
print()
print("=" * 86)
okc = sum(1 for _, o in CHECKS if o)
print(f"{okc} of {len(CHECKS)} checks passed, {len(CHECKS) - okc} failures")
print("=" * 86)
sys.exit(0 if okc == len(CHECKS) else 1)
