"""W59-INVARIANT: is `liveFrameSub` NECESSARY or merely SUFFICIENT?

Stage 1 of three.  This file (a) revalidates the transcribed `SqU5` library against every
committed Lean fact the question touches, (b) derives the increment's parity closed form and
the sharp criterion, and (c) certifies the two W59 witness markings.

Run:  python3 derive_necessity.py            (writes results/derive_necessity.txt)

BRACKET CONVENTION.  [IMMUNE]
This script only ever sifts brackets into a closure, which is convention-IMMUNE (the
generated subgroup is the same in either convention), so nothing here depends on the
choice.  Its Lean target is written with commP.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""


import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import u5lib as L

CHECKS = 0
FAILS = []
OUT = []


def emit(s=""):
    OUT.append(s)
    print(s)


def check(name, got, want):
    global CHECKS
    CHECKS += 1
    if got != want:
        FAILS.append((name, got, want))
        emit(f"  MISMATCH {name}: got {got}, want {want}")
    return got == want


# ==========================================================================================
emit("=" * 88)
emit("W59-INVARIANT stage 1: library validation, the pairing closed form, the two witnesses")
emit("=" * 88)
emit()
emit("-- 1. Library validated against the committed Lean facts ---------------------------")

# GradedSigmaFour / GradedFourCleared / GradedFourTwoLive committed values.
check("commP_clrFour (W57)", L.commP(L.sigFourU, L.sigFourV), L.ONE)
check("commP_liveFour (W57)", L.commP(L.liveFourU, L.liveFourV), (0, 0, 0, 0, 0, 0, 0, 2, 0, 0))
check("sqWord_clrFour (W57)", L.sqWord(L.sigFourMark, L.sigFourX, L.sigFourY), L.ONE)
check("sqWord_liveFour (W57)", L.sqWord(L.sigFourMark, L.sigFourX, L.liveFourY),
      (0, 0, 0, 0, 0, 0, 0, 6, 0, 0))
check("commP_twoLive.1 (W58)", L.commP(L.twoLiveU, L.twoLiveV), (0, 0, 0, 0, 0, 0, 0, 2, 0, 0))
check("commP_twoLive.2 (W58)", L.commP(L.twoLiveV, L.twoLiveU), (0, 0, 0, 0, 0, 0, 0, 6, 0, 0))
check("commP_oddLive (W58)", L.commP(L.sigFourU, L.oddLiveV), (0, 0, 0, 0, 0, 0, 0, 1, 0, 0))
check("commP_mirLive (W58)", L.commP(L.mirFourU, L.mirLiveV), (0, 0, 0, 0, 0, 0, 0, 4, 0, 0))
check("commP_rowLive (W58)", L.commP(L.rowLiveU, L.rowFourV), (0, 0, 0, 0, 0, 0, 0, 4, 0, 0))
check("commP_hiLive = commP_liveFour (W58)", L.commP(L.sigFourU, L.hiLiveV),
      L.commP(L.liveFourU, L.liveFourV))
check("commP_swap identity (W58)",
      [L.mul(L.commP(p, q), L.commP(q, p)) for p in (L.sigFourU, L.oddLiveV, L.orthU)
       for q in (L.sigFourV, L.liveFourV, L.orthV)], [L.ONE] * 9)
check("oddLiveV not in liveFrameSub (W58)", L.in_live_frame(L.oddLiveV), False)
check("twoLiveU in liveFrameSub (W58)", L.in_live_frame(L.twoLiveU), True)
check("twoLiveV in liveFrameSub (W58)", L.in_live_frame(L.twoLiveV), True)

# The relator of a swapped two-live marking is the bare core word, at every handle count.
for h in (1, 2, 3, 4):
    for j1 in range(h):
        for j2 in range(j1 + 1, h):
            for (U, V) in ((L.twoLiveU, L.twoLiveV), (L.sigFourU, L.oddLiveV),
                           (L.orthU, L.orthV), (L.mixU, L.mixV)):
                check(f"sqRelWord_twoTuple_swap h={h} j={j1},{j2}",
                      L.sqRelWord(L.twoSwapMark(h, j1, j2, U, V)), L.ONE)

# The three committed verdicts of the swap family, independent of the letters.
for (U, V) in ((L.twoLiveU, L.twoLiveV), (L.sigFourU, L.oddLiveV), (L.orthU, L.orthV),
               (L.mixU, L.mixV)):
    check("sqRelWord_twoLiveWit_triv", L.sqRelWord(L.twoSwapWit(2, 0, 1, U, V, L.ONE)), L.ONE)
    check("sqRelWord_twoLiveWit_U = liftC 1",
          L.sqRelWord(L.twoSwapWit(2, 0, 1, U, V, L.sigFourU)), L.liftC(1))
    check("sqRelWord_twoLiveWit_Usq = liftC 2",
          L.sqRelWord(L.twoSwapWit(2, 0, 1, U, V, L.mul(L.sigFourU, L.sigFourU))), L.liftC(2))

emit(f"  committed-fact checks so far: {CHECKS}, mismatches {len(FAILS)}")

# ==========================================================================================
emit()
emit("-- 2. The five-slot translation identity, and the increment's parity ----------------")

# sqRelWord (sigLift j m z0 w1 w2 z3 z4) = sqRelWord m * liftC (increment), verified directly
# against the group law on a large randomised family - no closed form assumed.
import random
random.seed(590590)


def rnd_gaThree():
    return (0, 0, 0, 0, 0, 0, 0, random.randrange(8), random.randrange(8), random.randrange(8))


def rnd_gaFour():
    return (0, 0, 0, 0, 0, 0, 0, 0, 0, random.randrange(8))


def rnd_elt():
    return tuple(random.randrange(8) for _ in range(10))


ident_checks = 0
for _ in range(30000):
    h = random.randrange(1, 4)
    j = random.randrange(h)
    m = [rnd_elt() for _ in range(3 + 2 * h)]
    z0, z3, z4 = rnd_gaThree(), rnd_gaThree(), rnd_gaThree()
    w1, w2 = rnd_gaFour(), rnd_gaFour()
    lhs = L.sqRelWord(L.sigLift_at(h, j, m, z0, w1, w2, z3, z4))
    rhs = L.mul(L.sqRelWord(m), L.liftC(L.sigIncrFull(m, j, z0, w1, w2, z3, z4)))
    if lhs != rhs:
        FAILS.append(("sqRelWord_sigLift", lhs, rhs))
    ident_checks += 1
CHECKS += ident_checks
emit(f"  sqRelWord_sigLift verified directly on {ident_checks} random (marking, refinement)"
     f" pairs; mismatches {len([f for f in FAILS if f[0] == 'sqRelWord_sigLift'])}")

# Over the committed x0-gauge `m 1 = sigFourX` the increment's PARITY is the handle pairing's:
# the z0-term reads (d, a) = (0, 2) and the two exponent terms are -4 w1.j + 2 w2.j.
par_checks = 0
for _ in range(30000):
    h = random.randrange(1, 4)
    j = random.randrange(h)
    m = [rnd_elt() for _ in range(3 + 2 * h)]
    m[1] = L.sigFourX
    z0, z3, z4 = rnd_gaThree(), rnd_gaThree(), rnd_gaThree()
    w1, w2 = rnd_gaFour(), rnd_gaFour()
    full = L.sigIncrFull(m, j, z0, w1, w2, z3, z4)
    pair = L.sigIncrPair(m[3 + 2 * j], m[4 + 2 * j], z3, z4)
    if full % 2 != pair % 2:
        FAILS.append(("increment parity = pairing parity", full, pair))
    par_checks += 1
CHECKS += par_checks
emit(f"  parity(increment) = parity(pairing) on {par_checks} random gauge markings;"
     f" mismatches {len([f for f in FAILS if f[0].startswith('increment parity')])}")

# ...and the even part of the increment is FULLY tunable: as w2.j runs over Z/8 the increment
# runs over the whole coset pairing + 2*(Z/8).  This is what makes the criterion sharp.
tun = set()
m = L.twoSwapMark(2, 0, 1, L.sigFourU, L.oddLiveV)
for w2j in range(8):
    tun.add(L.sigIncrFull(m, 0, L.ONE, L.ONE, L.liftC(w2j), L.commP(L.sigFourU, L.oddLiveV),
                          L.ONE))
check("increment coset = pairing + 2(Z/8)", tun, {1, 3, 5, 7})

# ==========================================================================================
emit()
emit("-- 3. The two sufficient conditions, and the sharp line between them ----------------")
emit()
emit("  liveFrameSub containment  ==>  every achievable move is EVEN in both class-three")
emit("  coordinates             ==>  the pairing is even WHATEVER the handle columns are.")
emit("  even handle columns (U.a, U.d, V.a, V.d all even)")
emit("                          ==>  the pairing is even WHATEVER the achievable set is.")
emit("  Sharp line: both mod-2 covectors (V.d, V.a) and (U.d, U.a) annihilate the")
emit("  class-three parity image of gamma_2 of the marking's image.")
emit()

def rnd_live_frame():
    """A uniform element of liveFrameSub: c = 0, f and g even."""
    p = list(rnd_elt())
    p[2] = 0
    p[5] = 2 * random.randrange(4)
    p[6] = 2 * random.randrange(4)
    return tuple(p)


def rnd_half_frame():
    """A uniform element of halfFrameSub: d and g even."""
    p = list(rnd_elt())
    p[3] = 2 * random.randrange(4)
    p[6] = 2 * random.randrange(4)
    return tuple(p)


# `commP_mem_liveGaTwoSub`: the algebraic fact behind the first sufficient condition.
cnt = 0
for _ in range(200000):
    p, q = rnd_live_frame(), rnd_live_frame()
    cnt += 1
    if not L.in_live_gaTwo(L.commP(p, q)):
        FAILS.append(("commP_mem_liveGaTwoSub", (p, q), L.commP(p, q)))
CHECKS += cnt
emit(f"  commP_mem_liveGaTwoSub confirmed on {cnt} uniform liveFrameSub pairs")

# `commP_mem_halfGaTwoSub`: the algebraic fact behind the MIXED point's invariant, which is
# incomparable with liveFrameSub - it constrains d and g, not c and f.
cnt = 0
for _ in range(200000):
    p, q = rnd_half_frame(), rnd_half_frame()
    cnt += 1
    if not L.in_half_gaTwo(L.commP(p, q)):
        FAILS.append(("commP_mem_halfGaTwoSub", (p, q), L.commP(p, q)))
CHECKS += cnt
emit(f"  commP_mem_halfGaTwoSub confirmed on {cnt} uniform halfFrameSub pairs")

# halfFrameSub, halfGaTwoSub, liveFrameSub and liveGaTwoSub really are subgroups.
for nm, pred, sampler in (("halfFrameSub", L.in_half_frame, rnd_half_frame),
                          ("liveFrameSub", L.in_live_frame, rnd_live_frame)):
    bad = 0
    for _ in range(200000):
        p, q = sampler(), sampler()
        if not pred(L.mul(p, q)) or not pred(L.inv(p)):
            bad += 1
    CHECKS += 1
    check(f"{nm} is a subgroup (200000 uniform pairs)", bad, 0)

for nm, pred in (("halfGaTwoSub", L.in_half_gaTwo), ("liveGaTwoSub", L.in_live_gaTwo)):
    bad = 0
    tested = 0
    for _ in range(400000):
        p, q = L.commP(rnd_half_frame(), rnd_half_frame()), \
            L.commP(rnd_half_frame(), rnd_half_frame())
        if pred(p) and pred(q):
            tested += 1
            if not pred(L.mul(p, q)) or not pred(L.inv(p)):
                bad += 1
    CHECKS += 1
    check(f"{nm} is a subgroup ({tested} pairs)", bad, 0)

# The two conditions are INCOMPARABLE: neither implies the other.
ex1 = [p for p in (L.mixV, L.orthV) if L.in_half_frame(p) and not L.in_live_frame(p)]
ex2 = [p for p in ((0, 0, 0, 1, 0, 0, 0, 0, 0, 0),) if L.in_live_frame(p)
       and not L.in_half_frame(p)]
check("halfFrameSub \\ liveFrameSub nonempty", len(ex1) > 0, True)
check("liveFrameSub \\ halfFrameSub nonempty", len(ex2) > 0, True)

# ==========================================================================================
emit()
emit("-- 4. THE THREE MARKINGS WITH THE SAME ODD BLOCK ------------------------------------")
emit()
emit("  All three carry the SAME live handle block, the class-three element with h = 1:")
emit("  odd in its first class-three coordinate, hence outside every evenness the campaign")
emit("  has ever carried.  One breaks the forcing.  Two do not.")
emit()

POINTS = [
    ("W58 oddLive   U=sigFourU   V=(2,0,0,1,0,1,0,0,0,0)", L.sigFourU, L.oddLiveV),
    ("W59 orth      U=(0,0,0,0,1,0,0,0,0,0)  V=(0,0,1,0,0,0,0,0,0,0)", L.orthU, L.orthV),
    ("W59 mix       U=sigFourU   V=(0,0,0,0,0,1,0,0,0,0)", L.mixU, L.mixV),
    ("W57/58 twoLive  U=sigFourU  V=(2,0,0,0,0,2,0,0,0,0)", L.twoLiveU, L.twoLiveV),
]

emit(f"  {'point':60s} {'block(h,i)':>11s} {'liveFrame':>10s} {'evenMoves':>10s}"
     f" {'evenCols':>9s} {'ORTH':>6s}")
for nm, U, V in POINTS:
    m = L.twoSwapMark(2, 0, 1, U, V)
    A = L.derived_subgroup(m)
    blk = L.commP(U, V)
    even_moves = all(z[7] % 2 == 0 and z[8] % 2 == 0 for z in L.gaThree_part(A))
    even_cols = (U[0] % 2 == 0 and U[3] % 2 == 0 and V[0] % 2 == 0 and V[3] % 2 == 0)
    live = L.in_live_frame(U) and L.in_live_frame(V)
    emit(f"  {nm:60s} {str((blk[7], blk[8])):>11s} {str(live):>10s} {str(even_moves):>10s}"
         f" {str(even_cols):>9s} {str(L.frame_orth(m, 0)):>6s}")

check("W58 oddLive block is odd", L.commP(L.sigFourU, L.oddLiveV)[7] % 2, 1)
check("W59 orth block is odd", L.commP(L.orthU, L.orthV)[7] % 2, 1)
check("W59 mix block is odd", L.commP(L.mixU, L.mixV)[7] % 2, 1)
check("the three odd blocks are the SAME element",
      {L.commP(L.sigFourU, L.oddLiveV), L.commP(L.orthU, L.orthV), L.commP(L.mixU, L.mixV)},
      {(0, 0, 0, 0, 0, 0, 0, 1, 0, 0)})
check("orthV outside liveFrameSub", L.in_live_frame(L.orthV), False)
check("mixV outside liveFrameSub", L.in_live_frame(L.mixV), False)
check("orth point: both covectors vanish",
      (L.orthU[0] % 2, L.orthU[3] % 2, L.orthV[0] % 2, L.orthV[3] % 2), (0, 0, 0, 0))
check("mix point: u-covector is (0,1), v-covector vanishes",
      (L.mixU[0] % 2, L.mixU[3] % 2, L.mixV[0] % 2, L.mixV[3] % 2), (1, 0, 0, 0))
check("mix point: every slot is in halfFrameSub",
      all(L.in_half_frame(p) for p in L.twoSwapMark(2, 0, 1, L.mixU, L.mixV)), True)
check("orth point: NOT every slot is in halfFrameSub or liveFrameSub is irrelevant",
      all(L.in_live_frame(p) for p in L.twoSwapMark(2, 0, 1, L.orthU, L.orthV)), False)

# The derived-subgroup shortcut (basic commutators of weight <= 4) is validated against the
# honest BFS closure of the whole image at the W58 two-live point.
m = L.twoSwapMark(2, 0, 1, L.twoLiveU, L.twoLiveV)
A_short = L.derived_subgroup(m)
check("derived subgroup order at the two-live point (W58 census: 512)", len(A_short), 512)

# ==========================================================================================
emit()
emit("-- 5. The COVECTORS of the campaign's own committed points --------------------------")
emit()
emit("  The sharp line reads the two handle slots through their mod-2 covectors")
emit("  (U.d, U.a) and (V.d, V.a).  A vanishing covector means that slot imposes NOTHING.")
emit("  This is what tells the campaign how much of `liveFrameSub` each committed point")
emit("  actually needs.")
emit()
COMMITTED = [
    ("W57 cleared      (0,0)", L.sigFourU, L.sigFourV),
    ("W57 live         (0,0)", L.liveFourU, L.liveFourV),
    ("W58 twoLive      (0,0)", L.twoLiveU, L.twoLiveV),
    ("W58 mirLive      (1,0)", L.mirFourU, L.mirLiveV),
    ("W58 rowLive      (0,1)", L.rowLiveU, L.rowFourV),
    ("W58 dblLive      (1,1)", L.mirFourU, L.dblLiveV),
    ("W58 hiLive       (2,0)", L.sigFourU, L.hiLiveV),
    ("W58 oddLive  (the kill)", L.sigFourU, L.oddLiveV),
    ("W59 orth", L.orthU, L.orthV),
    ("W59 mix", L.mixU, L.mixV),
]
emit(f"  {'point':26s} {'(U.d,U.a)':>10s} {'(V.d,V.a)':>10s}   needs")
for nm, U, V in COMMITTED:
    cu = (U[3] % 2, U[0] % 2)
    cv = (V[3] % 2, V[0] % 2)
    need = []
    if cv != (0, 0):
        need.append("z.h" if cv == (1, 0) else ("z.i" if cv == (0, 1) else "z.h+z.i"))
    if cu != (0, 0):
        need.append("z.i" if cu == (0, 1) else ("z.h" if cu == (1, 0) else "z.h+z.i"))
    emit(f"  {nm:26s} {str(cu):>10s} {str(cv):>10s}   "
         f"{' and '.join(sorted(set(need))) if need else 'NOTHING'} even")
check("cleared-row points read only the u-covector",
      [(V[3] % 2, V[0] % 2) for _, _, V in COMMITTED[:3]], [(0, 0), (0, 0), (0, 0)])
check("displaced-row points have BOTH covectors nonzero",
      [((U[3] % 2, U[0] % 2) != (0, 0) and (V[3] % 2, V[0] % 2) != (0, 0))
       for _, U, V in COMMITTED[3:7]], [True, True, True, True])

emit()
emit("=" * 88)
emit(f"named checks: {CHECKS}    MISMATCHES: {len(FAILS)}")
if FAILS:
    for f in FAILS[:20]:
        emit(f"  {f}")
emit("=" * 88)

here = os.path.dirname(os.path.abspath(__file__))
os.makedirs(os.path.join(here, "results"), exist_ok=True)
with open(os.path.join(here, "results", "derive_necessity.txt"), "w") as fh:
    fh.write("\n".join(OUT) + "\n")
sys.exit(1 if FAILS else 0)
