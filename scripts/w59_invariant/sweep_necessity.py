"""W59-INVARIANT stage 2: the kill sweeps and the CENSUS that decides the question.

For a marking `m` over the committed `x0`-gauge whose relator vanishes, `sqRelWord_sigLift`
makes every five-slot refinement translate the relator by a central `liftC(increment)`, and
over the gauge the increment's parity is the HANDLE PAIRING's:

    pair(z3, z4) = z3.h * V.d - z3.i * V.a + U.a * z4.i - U.d * z4.h        (mod 2)

with `U`, `V` the two handle slots at the lifted handle.  The claim under test is that this
pairing, and NOT `liveFrameSub`, is the sharp line:

    the class-four sigma forcing holds at (m, j)
      <=>  both mod-2 covectors (V.d, V.a) and (U.d, U.a) annihilate the class-three parity
           image of gamma_2 of the marking's image.

The census below computes both sides independently at every marking of four families and
compares them.  Run:  python3 sweep_necessity.py     (writes results/sweep_necessity.txt)

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

import os
import random
import sys
import time
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import u5lib as L

CHECKS = 0
FAILS = []
OUT = []
T0 = time.time()


def emit(s=""):
    OUT.append(s)
    print(s, flush=True)


def check(name, got, want):
    global CHECKS
    CHECKS += 1
    if got != want:
        FAILS.append((name, got, want))
        emit(f"  MISMATCH {name}: got {got}, want {want}")


# ------------------------------------------------------------------------------------------
# The refinement space, and exact kill counts over the whole of it.
#
#   z0 : gamma_3-shaped, FREE               512 elements, read only through z0.i
#   w1, w2 : gamma_4-shaped, FREE           8 each, read through their j
#   z3, z4 : gamma_3-shaped and ACHIEVABLE  |A3| each, read through (h, i)
#
# so the space has 512 * 8 * 8 * |A3|^2 refinements, exactly the W58 convention.
# ------------------------------------------------------------------------------------------

ALL_G3 = [(0,) * 7 + (a, b, c) for a in range(8) for b in range(8) for c in range(8)]

# the z0- and (w1, w2)-fibres of the increment, over the committed x0-gauge m 1 = sigFourX
ZERO_FIBRE = Counter()
for _zh in range(8):
    for _zi in range(8):
        ZERO_FIBRE[(_zh * L.sigFourX[3] - _zi * L.sigFourX[0]) % 8] += 8
EXP_FIBRE = Counter((-4 * _a + 2 * _b) % 8 for _a in range(8) for _b in range(8))


def kill_counts(res, mU, mV, A3):
    """(space size, number of refinements killing the relator at a dressing of residue `res`).

    Exact, by counting the increment's fibres rather than enumerating the space."""
    space = 512 * 8 * 8 * len(A3) * len(A3)
    if not L.is_ga_four(res):        # a non-central residue can never be killed centrally
        return space, 0
    pairs = Counter(L.sigIncrPair(mU, mV, z3, z4) for z3 in A3 for z4 in A3)
    tot = 0
    for p, cp in pairs.items():
        for z, cz in ZERO_FIBRE.items():
            for e, ce in EXP_FIBRE.items():
                if (res[9] + p + z + e) % 8 == 0:
                    tot += cp * cz * ce
    return space, tot


def orth_from(A3, mU, mV):
    """The sharp criterion, evaluated from the marking's own subgroup data."""
    for z in A3:
        if (z[7] * mV[3] - z[8] * mV[0]) % 2 != 0:
            return False
        if (mU[0] * z[8] - mU[3] * z[7]) % 2 != 0:
            return False
    return True


def point_data(U, V, unrestricted=False):
    """Everything the census needs about the two-live swap marking with letters (U, V)."""
    m = L.twoSwapMark(2, 0, 1, U, V)
    A3 = L.derived_gaThree(m)
    mU, mV = m[3], m[4]
    res_odd = L.sqRelWord(L.sigFourDress_at(m, L.sigFourU))
    res_even = L.sqRelWord(L.sigFourDress_at(m, L.mul(L.sigFourU, L.sigFourU)))
    space, ko = kill_counts(res_odd, mU, mV, A3)
    _, ke = kill_counts(res_even, mU, mV, A3)
    out = {"m": m, "A3": A3, "space": space, "killOdd": ko, "killEven": ke,
           "orth": orth_from(A3, mU, mV), "rel": L.sqRelWord(m),
           "live": L.in_live_frame(U) and L.in_live_frame(V),
           "even_moves": all(z[7] % 2 == 0 and z[8] % 2 == 0 for z in A3),
           "even_cols": U[0] % 2 == 0 and U[3] % 2 == 0 and V[0] % 2 == 0 and V[3] % 2 == 0,
           "block": L.commP(U, V)}
    if unrestricted:
        out["uspace"], out["ukillOdd"] = kill_counts(res_odd, mU, mV, ALL_G3)
    return out


def sample_kill_direct(m, A3, v, trials, rng):
    """Full-fidelity spot check of `kill_counts`: draw refinements uniformly from the same
    space and evaluate `sqRelWord` on the lifted marking directly."""
    hit = 0
    md = L.sigFourDress_at(m, v)
    for _ in range(trials):
        z0 = (0,) * 7 + (rng.randrange(8), rng.randrange(8), rng.randrange(8))
        w1 = L.liftC(rng.randrange(8))
        w2 = L.liftC(rng.randrange(8))
        z3 = A3[rng.randrange(len(A3))]
        z4 = A3[rng.randrange(len(A3))]
        if L.sqRelWord(L.sigLift_at(2, 0, md, z0, w1, w2, z3, z4)) == L.ONE:
            hit += 1
    return hit


emit("=" * 92)
emit("W59-INVARIANT stage 2: kill sweeps and the census deciding necessity vs sufficiency")
emit("=" * 92)

# ------------------------------------------------------------------------------------------
emit()
emit("-- 0. The subgroup engine, validated against the honest orbit BFS ------------------")
emit()
emit("  The census needs gamma_2 of each marking's image, cut to its gamma_3-shaped part.")
emit("  It is computed by an induced polycyclic generating sequence; here that engine is")
emit("  checked against a full orbit enumeration of the same subgroup wherever the latter")
emit("  is affordable, on order AND on the gamma_3 part element by element.")
_rng0 = random.Random(590000)
_BITS0 = [(a, 0, c, d, e, f, g, 0, 0, 0) for a in (0, 1) for c in (0, 1) for d in (0, 1)
          for e in (0, 1) for f in (0, 1) for g in (0, 1)]
_val = 0
for _ in range(60):
    _U = _BITS0[_rng0.randrange(64)]
    _V = _BITS0[_rng0.randrange(64)]
    _m = L.twoSwapMark(2, 0, 1, _U, _V)
    _bc = L.basic_commutators(_m, 4)
    try:
        _A = L.subgroup_closure(_bc, cap=1 << 15)
    except RuntimeError:
        continue
    _val += 1
    _piv = L.pc_closure(_bc)
    check("pc order = BFS order", L.pc_order(_piv), len(_A))
    check("pc gamma_3 part = BFS gamma_3 part", L.pc_gaThree(_piv), L.gaThree_part(_A))
for _nm, _U, _V in (("twoLive", L.twoLiveU, L.twoLiveV), ("oddLive", L.sigFourU, L.oddLiveV),
                    ("orth", L.orthU, L.orthV), ("mix", L.mixU, L.mixV)):
    _m = L.twoSwapMark(2, 0, 1, _U, _V)
    _bc = L.basic_commutators(_m, 4)
    check(f"pc order = BFS order [{_nm}]", L.pc_order(L.pc_closure(_bc)),
          len(L.subgroup_closure(_bc)))
    _val += 1
emit(f"  {_val} markings validated element by element against the BFS closure")
emit(f"  (W58 census: |[K,K]| = 512 at the two-live point; here "
     f"{L.pc_order(L.pc_closure(L.basic_commutators(L.twoSwapMark(2, 0, 1, L.twoLiveU, L.twoLiveV), 4)))})")

# ------------------------------------------------------------------------------------------
emit()
emit("-- 1. Kill sweeps at the catalogue points and the new ones -------------------------")
emit()
emit("  `odd` = the committed odd-character dressing sigFourU;  `even` = its square.")
emit("  A refinement kills when the lifted relator is trivial.  ORTH is the sharp criterion.")
emit()

POINTS = [
    ("W57/58 twoLive  (both letters inside liveFrameSub)", L.twoLiveU, L.twoLiveV),
    ("W58  oddLive    (V.f odd AND V.d odd)  <- the W58 KILL", L.sigFourU, L.oddLiveV),
    ("W59  orth       (V.c = 1; both covectors vanish)", L.orthU, L.orthV),
    ("W59  mix        (V.f odd, V.d even; u-covector (0,1))", L.mixU, L.mixV),
    ("W59  ctrl-d     (V.f even, V.d odd)", L.mixU, (0, 0, 0, 1, 0, 0, 0, 0, 0, 0)),
    ("W59  ctrl-ad    (V.f odd, V.d odd, U even columns)", L.orthU,
     (0, 0, 0, 1, 0, 1, 0, 0, 0, 0)),
]

rng = random.Random(591591)
emit(f"  {'point':54s} {'|A3|':>5s} {'space':>12s} {'killOdd':>12s} {'killEven':>10s}"
     f" {'ORTH':>6s}")
DATA = {}
for nm, U, V in POINTS:
    d = point_data(U, V, unrestricted=True)
    DATA[nm] = d
    check(f"relator killed at {nm}", d["rel"], L.ONE)
    emit(f"  {nm:54s} {len(d['A3']):5d} {d['space']:12d} {d['killOdd']:12d}"
         f" {d['killEven']:10d} {str(d['orth']):>6s}")
    check(f"criterion predicts the odd kill at {nm}", d["killOdd"] > 0, not d["orth"])
    trials = 200000
    hit = sample_kill_direct(d["m"], d["A3"], L.sigFourU, trials, rng)
    check(f"exact counter matches direct sqRelWord at {nm}",
          abs(hit / trials - d["killOdd"] / d["space"]) < 0.01, True)

emit()
emit("  W58 reproduction: at the oddLive point the lane reported 67108864 of 536870912")
emit("  achievable refinements killing the odd dressing.")
d = DATA["W58  oddLive    (V.f odd AND V.d odd)  <- the W58 KILL"]
check("W58 space size 536870912", d["space"], 536870912)
check("W58 odd-kill count 67108864", d["killOdd"], 67108864)
emit(f"    reproduced: {d['killOdd']} of {d['space']}")

# ------------------------------------------------------------------------------------------
emit()
emit("-- 2. Unrestricted gamma_3 moves: where achievability is load-bearing and where not --")
emit()
emit("  Same sweep with z3, z4 over ALL 512 gamma_3-shaped elements rather than the achievable")
emit("  ones.  At the ORTH point even this cannot kill the odd dressing: the pairing is")
emit("  identically zero, so the forcing there needs no achievability convention at all.")
emit()
emit(f"  {'point':54s} {'space':>14s} {'killOdd(unrestricted)':>23s}")
for nm, U, V in POINTS:
    d = DATA[nm]
    emit(f"  {nm:54s} {d['uspace']:14d} {d['ukillOdd']:23d}")
check("orth point: unrestricted moves cannot kill the odd dressing",
      DATA["W59  orth       (V.c = 1; both covectors vanish)"]["ukillOdd"], 0)
check("mix point: unrestricted moves DO kill, so achievability is load-bearing",
      DATA["W59  mix        (V.f odd, V.d even; u-covector (0,1))"]["ukillOdd"] > 0, True)
check("twoLive: W58's 1073741824 of 8589934592 unrestricted moves",
      (DATA["W57/58 twoLive  (both letters inside liveFrameSub)"]["uspace"],
       DATA["W57/58 twoLive  (both letters inside liveFrameSub)"]["ukillOdd"]),
      (8589934592, 1073741824))

# ------------------------------------------------------------------------------------------
emit()
emit("-- 3. THE CENSUS: predicted (pairing) versus actual (kill search) -------------------")
emit()
emit("  For each marking of each family: `predicted` is the sharp criterion evaluated from")
emit("  the marking's own subgroup data; `actual` is whether some achievable five-slot")
emit("  refinement kills the relator at the committed odd dressing.  Any disagreement")
emit("  refutes the characterisation.  The cross-tabulations below decide the question.")
emit()

TOTALS = Counter()


def census(name, pairs, spot_every=0):
    agree = disagree = broken = 0
    outside_live = outside_live_safe = inside_live_broken = 0
    k = 0
    for (U, V) in pairs:
        d = point_data(U, V)
        if d["rel"] != L.ONE:
            FAILS.append((f"{name}: swap marking does not kill the relator", (U, V), None))
            continue
        actual = d["killOdd"] > 0
        predicted = not d["orth"]
        if predicted == actual:
            agree += 1
        else:
            disagree += 1
            FAILS.append((f"{name} census disagreement", (U, V), (predicted, actual)))
        if actual:
            broken += 1
        if not d["live"]:
            outside_live += 1
            if not actual:
                outside_live_safe += 1
        elif actual:
            inside_live_broken += 1
        blk = d["block"]
        TOTALS[("oddblock", blk[7] % 2 == 1 or blk[8] % 2 == 1, actual)] += 1
        TOTALS[("live", d["live"], actual)] += 1
        TOTALS[("evenmoves", d["even_moves"], actual)] += 1
        TOTALS[("evencols", d["even_cols"], actual)] += 1
        TOTALS[("outside-both", (not d["even_moves"]) and (not d["even_cols"]), actual)] += 1
        k += 1
        if spot_every and k % spot_every == 0:
            hit = sample_kill_direct(d["m"], d["A3"], L.sigFourU, 20000, rng)
            check(f"{name} spot check {k}",
                  abs(hit / 20000 - d["killOdd"] / d["space"]) < 0.02, True)
    emit(f"  {name}")
    emit(f"    markings                                  {k}")
    emit(f"    forcing BREAKS (some achievable kill)     {broken}")
    emit(f"    predicted = actual                        {agree}")
    emit(f"    DISAGREEMENTS                             {disagree}")
    emit(f"    outside liveFrameSub                      {outside_live}")
    emit(f"      ...of which the forcing still HOLDS     {outside_live_safe}")
    emit(f"    inside liveFrameSub and broken            {inside_live_broken}")
    emit(f"    [{time.time() - T0:.0f}s]")
    check(f"{name}: zero census disagreements", disagree, 0)
    check(f"{name}: liveFrameSub is sufficient", inside_live_broken, 0)


# Family A, exhaustive: letters with b = h = i = j = 0 and (a, c, d, e, f, g) in {0, 1}.
BITS = [(a, 0, c, d, e, f, g, 0, 0, 0) for a in (0, 1) for c in (0, 1) for d in (0, 1)
        for e in (0, 1) for f in (0, 1) for g in (0, 1)]
famA = [(U, V) for U in BITS for V in BITS]
census(f"family A (exhaustive 0/1 letters, {len(famA)} markings)", famA, spot_every=997)

# Family B, random: uniform nu'-trivial letters over the whole of Z/8.
rngB = random.Random(592592)


def rnd_nu_trivial():
    p = [rngB.randrange(8) for _ in range(10)]
    p[1] = 0
    return tuple(p)


famB = [(rnd_nu_trivial(), rnd_nu_trivial()) for _ in range(2000)]
census(f"family B (random nu'-trivial letters, {len(famB)} markings)", famB, spot_every=499)

# Family C: the campaign's own catalogue letters, crossed.
CATALOGUE = [L.sigFourU, L.sigFourV, L.liveFourV, L.mirFourU, L.mirFourV, L.mirLiveV,
             L.rowFourU, L.rowFourV, L.rowLiveU, L.dblLiveV, L.hiLiveV, L.oddLiveV,
             L.twoLiveU, L.twoLiveV, L.orthU, L.orthV, L.mixU, L.mixV]
famC = [(U, V) for U in CATALOGUE for V in CATALOGUE]
census(f"family C (catalogue letters crossed, {len(famC)} markings)", famC)

# Family D: the pairing's own coordinates swept exhaustively, everything else fixed.
famD = [(L.sigFourU, (va, 0, 0, vd, 0, vf, 0, 0, 0, 0))
        for va in range(8) for vd in range(8) for vf in range(8)]
census(f"family D (V.a, V.d, V.f swept, {len(famD)} markings)", famD, spot_every=127)

# ------------------------------------------------------------------------------------------
emit()
emit("-- 4. What separates the safe markings from the dangerous ones ----------------------")
emit()
emit("  Cross-tabulations over all four families together.  Rows read:")
emit("  'property holds / property fails' against 'the forcing breaks / holds'.")
emit()


def tab(key, label):
    emit(f"    {label}")
    emit(f"      holds & breaks {TOTALS[(key, True, True)]:6d}      "
         f"holds & HOLDS {TOTALS[(key, True, False)]:6d}")
    emit(f"      fails & breaks {TOTALS[(key, False, True)]:6d}      "
         f"fails & HOLDS {TOTALS[(key, False, False)]:6d}")


tab("live", "marking inside liveFrameSub (the CARRIED hypothesis)")
tab("evenmoves", "every achievable move even in class three (its CONSEQUENCE)")
tab("evencols", "handle slots have even outer columns (the DUAL sufficient condition)")
tab("oddblock", "the handle block is ODD in a class-three coordinate")
tab("outside-both", "OUTSIDE both sufficient conditions")
emit()
check("liveFrameSub never breaks", TOTALS[("live", True, True)], 0)
check("achievable evenness never breaks", TOTALS[("evenmoves", True, True)], 0)
check("even handle columns never break", TOTALS[("evencols", True, True)], 0)
check("markings outside liveFrameSub at which the forcing HOLDS are common",
      TOTALS[("live", False, False)] > 0, True)
check("markings whose achievable set is ODD and the forcing still HOLDS are common",
      TOTALS[("evenmoves", False, False)] > 0, True)
check("markings outside BOTH sufficient conditions at which the forcing HOLDS exist",
      TOTALS[("outside-both", True, False)] > 0, True)
check("an ODD block with the forcing still holding is common",
      TOTALS[("oddblock", True, False)] > 0, True)

# ------------------------------------------------------------------------------------------
emit()
emit("-- 5. Every nu'-trivial dressing at the headline points -----------------------------")
emit()
emit("  The forcing quantifies over ALL nu'-trivial sigma dressings, not just the committed")
emit("  one.  Sample v uniformly with v.b = 0 and check that no kill ever has odd character")
emit("  where the criterion says the forcing holds.")
emit()
rngE = random.Random(593593)
for nm, U, V in POINTS:
    d = DATA[nm]
    A3 = d["A3"]
    kills = oddkills = 0
    trials = 200000
    for _ in range(trials):
        v = [rngE.randrange(8) for _ in range(10)]
        v[1] = 0
        md = L.sigFourDress_at(d["m"], tuple(v))
        z0 = (0,) * 7 + (rngE.randrange(8), rngE.randrange(8), rngE.randrange(8))
        w1 = L.liftC(rngE.randrange(8))
        w2 = L.liftC(rngE.randrange(8))
        z3 = A3[rngE.randrange(len(A3))]
        z4 = A3[rngE.randrange(len(A3))]
        if L.sqRelWord(L.sigLift_at(2, 0, md, z0, w1, w2, z3, z4)) == L.ONE:
            kills += 1
            if v[0] % 2 == 1:
                oddkills += 1
    emit(f"  {nm:54s} kills {kills:7d} of {trials}   odd-character kills {oddkills:7d}"
         f"   ORTH {d['orth']}")
    if d["orth"]:
        check(f"no odd-character kill at {nm}", oddkills, 0)
    else:
        check(f"odd-character kills exist at {nm}", oddkills > 0, True)

emit()
emit("=" * 92)
emit(f"named checks: {CHECKS}    MISMATCHES: {len(FAILS)}    [{time.time() - T0:.0f}s]")
if FAILS:
    for f in FAILS[:20]:
        emit(f"  {f}")
emit("=" * 92)

here = os.path.dirname(os.path.abspath(__file__))
os.makedirs(os.path.join(here, "results"), exist_ok=True)
with open(os.path.join(here, "results", "sweep_necessity.txt"), "w") as fh:
    fh.write("\n".join(OUT) + "\n")
sys.exit(1 if FAILS else 0)
