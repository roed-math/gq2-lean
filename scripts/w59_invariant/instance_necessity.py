"""W59-INVARIANT stage 3: every explicit claim of GradedFrameNecessity.lean, mirrored
numerically at h = 1, 2, 3, 4, every handle j < h and every ordered handle pair.

Run:  python3 instance_necessity.py       (writes results/instance_necessity.txt)

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

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import u5lib as L

CHECKS = 0
FAILS = []
OUT = []


def emit(s=""):
    OUT.append(s)
    print(s, flush=True)


def check(name, got, want):
    global CHECKS
    CHECKS += 1
    if got != want:
        FAILS.append((name, got, want))
        emit(f"  MISMATCH {name}: got {got}, want {want}")


HJ = [(h, j1, j2) for h in (1, 2, 3, 4) for j1 in range(h) for j2 in range(h) if j1 < j2]
HJ1 = [(h, j) for h in (1, 2, 3, 4) for j in range(h)]

rng = random.Random(594594)


def rnd_gaThree():
    return (0,) * 7 + (rng.randrange(8), rng.randrange(8), rng.randrange(8))


def rnd_gaFour():
    return L.liftC(rng.randrange(8))


def rnd_elt():
    return tuple(rng.randrange(8) for _ in range(10))


def rnd_marking(h):
    return [rnd_elt() for _ in range(3 + 2 * h)]


emit("=" * 88)
emit("W59-INVARIANT stage 3: numerical mirror of every claim in GradedFrameNecessity.lean")
emit("=" * 88)

# ---- section 1: the pairing --------------------------------------------------------------
emit()
emit("-- 1 sigIncrPair, sigIncrPair_eq_add, and the two sufficient conditions ------------")
for h, j in HJ1:
    for _ in range(400):
        m = rnd_marking(h)
        z3, z4 = rnd_gaThree(), rnd_gaThree()
        mU, mV = m[3 + 2 * j], m[4 + 2 * j]
        # sigIncrPair_eq_add
        check("sigIncrPair_eq_add",
              L.sigIncrPair(mU, mV, z3, z4),
              (L.sigIncrPair(mU, mV, z3, L.ONE) + L.sigIncrPair(mU, mV, L.ONE, z4)) % 8)
        # sigIncrPair_even_of_gaThree_even
        ze3 = (0,) * 7 + (2 * rng.randrange(4), 2 * rng.randrange(4), rng.randrange(8))
        ze4 = (0,) * 7 + (2 * rng.randrange(4), 2 * rng.randrange(4), rng.randrange(8))
        check("sigIncrPair_even_of_gaThree_even", L.sigIncrPair(mU, mV, ze3, ze4) % 2, 0)
        # sigIncrPair_even_of_handle_even
        mUe = list(mU); mUe[0] = 2 * rng.randrange(4); mUe[3] = 2 * rng.randrange(4)
        mVe = list(mV); mVe[0] = 2 * rng.randrange(4); mVe[3] = 2 * rng.randrange(4)
        check("sigIncrPair_even_of_handle_even",
              L.sigIncrPair(tuple(mUe), tuple(mVe), z3, z4) % 2, 0)
emit(f"  {CHECKS} checks")

# ---- section 2: the increment and the forcing ---------------------------------------------
emit()
emit("-- 2 gaugeX_increment_even_of_pair, gaugeX_sigma_forced_pair -----------------------")
n2 = CHECKS
for h, j in HJ1:
    for _ in range(400):
        m = rnd_marking(h)
        m[1] = L.sigFourX
        z0, z3, z4 = rnd_gaThree(), rnd_gaThree(), rnd_gaThree()
        w1, w2 = rnd_gaFour(), rnd_gaFour()
        mU, mV = m[3 + 2 * j], m[4 + 2 * j]
        full = L.sigIncrFull(m, j, z0, w1, w2, z3, z4)
        pair = L.sigIncrPair(mU, mV, z3, z4)
        # gaugeX_increment_even_of_pair: pair even ==> full even
        if pair % 2 == 0:
            check("gaugeX_increment_even_of_pair", full % 2, 0)
        # the forcing itself, on the swap family where the relator is known to vanish
for h, j1, j2 in HJ:
    for (U, V) in ((L.twoLiveU, L.twoLiveV), (L.orthU, L.orthV), (L.mixU, L.mixV),
                   (L.sigFourU, L.oddLiveV)):
        m = L.twoSwapMark(h, j1, j2, U, V)
        check("swap marking kills the relator", L.sqRelWord(m), L.ONE)
        A3 = L.derived_gaThree(m)
        for _ in range(600):
            v = list(rnd_elt()); v[1] = 0; v = tuple(v)
            z0, w1, w2 = rnd_gaThree(), rnd_gaFour(), rnd_gaFour()
            z3, z4 = A3[rng.randrange(len(A3))], A3[rng.randrange(len(A3))]
            md = L.sigFourDress_at(m, v)
            killed = L.sqRelWord(L.sigLift_at(h, j1, md, z0, w1, w2, z3, z4)) == L.ONE
            pair = L.sigIncrPair(m[3 + 2 * j1], m[4 + 2 * j1], z3, z4)
            if killed and pair % 2 == 0:
                # gaugeX_sigma_forced_pair
                check("gaugeX_sigma_forced_pair", v[0] % 2, 0)
emit(f"  {CHECKS - n2} checks")

# ---- section 3: the converse ---------------------------------------------------------------
emit()
emit("-- 3 gaugeX_kill_of_pair, selPar_res_of_odd, gaugeX_kill_of_pair_odd ---------------")
n3 = CHECKS
for h, j1, j2 in HJ:
    for (U, V) in ((L.twoLiveU, L.twoLiveV), (L.orthU, L.orthV), (L.mixU, L.mixV),
                   (L.sigFourU, L.oddLiveV)):
        m = L.twoSwapMark(h, j1, j2, U, V)
        mU, mV = m[3 + 2 * j1], m[4 + 2 * j1]
        for v in (L.sigFourU, L.mul(L.sigFourU, L.sigFourU), L.ONE):
            res = L.sqRelWord(L.sigFourDress_at(m, v))
            check("residue is central", L.is_ga_four(res), True)
            # selPar_res_of_odd
            check("selPar_res_of_odd", res[9] % 2, v[0] % 2)
            for _ in range(200):
                z3, z4 = rnd_gaThree(), rnd_gaThree()
                pair = L.sigIncrPair(mU, mV, z3, z4)
                if (res[9] + pair) % 2 == 0:
                    # solve c + pair = 2 t over Z/8
                    ts = [t0 for t0 in range(8) if (2 * t0) % 8 == (res[9] + pair) % 8]
                    check("a t exists", len(ts) > 0, True)
                    t0 = ts[0]
                    w2 = L.liftC((-t0) % 8)
                    # gaugeX_kill_of_pair
                    check("gaugeX_kill_of_pair",
                          L.sqRelWord(L.sigLift_at(h, j1, L.sigFourDress_at(m, v), L.ONE,
                                                   L.ONE, w2, z3, z4)), L.ONE)
emit(f"  {CHECKS - n3} checks")

# ---- section 4: the characterisation --------------------------------------------------------
emit()
emit("-- 4 sigmaForces_iff_frameOrth, on every point of the catalogue --------------------")
n4 = CHECKS
CAT = [("twoLive", L.twoLiveU, L.twoLiveV), ("oddLive", L.sigFourU, L.oddLiveV),
       ("orth", L.orthU, L.orthV), ("mix", L.mixU, L.mixV),
       ("cleared", L.sigFourU, L.sigFourV), ("live", L.liveFourU, L.liveFourV),
       ("mirLive", L.mirFourU, L.mirLiveV), ("rowLive", L.rowLiveU, L.rowFourV),
       ("hiLive", L.sigFourU, L.hiLiveV)]
for h, j1, j2 in HJ:
    for nm, U, V in CAT:
        m = L.twoSwapMark(h, j1, j2, U, V)
        A3 = L.derived_gaThree(m)
        mU, mV = m[3 + 2 * j1], m[4 + 2 * j1]
        orth = all((z[7] * mV[3] - z[8] * mV[0]) % 2 == 0
                   and (mU[0] * z[8] - mU[3] * z[7]) % 2 == 0 for z in A3)
        # SigmaForces, evaluated exactly: it fails iff some achievable pair has odd pairing
        # (the odd dressing sigFourU has central residue liftC 1 on the whole swap family)
        res = L.sqRelWord(L.sigFourDress_at(m, L.sigFourU))
        check("odd dressing residue is liftC 1", res, L.liftC(1))
        breaks = any(L.sigIncrPair(mU, mV, z3, z4) % 2 == 1 for z3 in A3 for z4 in A3)
        check(f"sigmaForces_iff_frameOrth [{nm}]", (not breaks), orth)
        # frameOrth_of_le_liveFrameSub
        if all(L.in_live_frame(p) for p in m):
            check(f"frameOrth_of_le_liveFrameSub [{nm}]", orth, True)
        # frameOrth_of_handle_even
        if mU[0] % 2 == 0 and mU[3] % 2 == 0 and mV[0] % 2 == 0 and mV[3] % 2 == 0:
            check(f"frameOrth_of_handle_even [{nm}]", orth, True)
emit(f"  {CHECKS - n4} checks")

# ---- section 5: the orthogonal point -----------------------------------------------------
emit()
emit("-- 5 the orthogonal point, end to end ---------------------------------------------")
n5 = CHECKS
check("commP_orth", L.commP(L.orthU, L.orthV), (0, 0, 0, 0, 0, 0, 0, 1, 0, 0))
check("commP_orth_eq_oddLive", L.commP(L.orthU, L.orthV), L.commP(L.sigFourU, L.oddLiveV))
check("commP_orth_ne_one", L.commP(L.orthU, L.orthV) != L.ONE, True)
check("commP_orth_isGaThree", L.is_ga_three(L.commP(L.orthU, L.orthV)), True)
check("commP_orth_g", L.commP(L.orthV, L.orthU)[6], 0)
check("orthV_not_mem_liveFrameSub", L.in_live_frame(L.orthV), False)
check("orth_block_odd", L.commP(L.orthU, L.orthV)[7] % 2, 1)
check("orth_handle_even", (L.orthU[0] % 2, L.orthU[3] % 2, L.orthV[0] % 2, L.orthV[3] % 2),
      (0, 0, 0, 0))
for h, j1, j2 in HJ:
    m = L.twoSwapMark(h, j1, j2, L.orthU, L.orthV)
    check("sqRelWord_orthMark", L.sqRelWord(m), L.ONE)
    check("orth: both blocks live",
          (L.commP(m[3 + 2 * j1], m[4 + 2 * j1]) != L.ONE,
           L.commP(m[3 + 2 * j2], m[4 + 2 * j2]) != L.ONE), (True, True))
    for _ in range(400):
        z3, z4 = rnd_gaThree(), rnd_gaThree()
        # orth_pair_eq_zero: for ARBITRARY gamma_3 moves, achievable or not
        check("orth_pair_eq_zero",
              L.sigIncrPair(m[3 + 2 * j1], m[4 + 2 * j1], z3, z4), 0)
        v = list(rnd_elt()); v[1] = 0; v = tuple(v)
        z0, w1, w2 = rnd_gaThree(), rnd_gaFour(), rnd_gaFour()
        md = L.sigFourDress_at(m, v)
        if L.sqRelWord(L.sigLift_at(h, j1, md, z0, w1, w2, z3, z4)) == L.ONE:
            # orth_sigma_forced, with NO achievability hypothesis
            check("orth_sigma_forced", v[0] % 2, 0)
    # orth_forcing_nonvacuous
    check("orth_forcing_nonvacuous residue",
          L.sqRelWord(L.sigFourDress_at(m, L.sigFourU)), L.liftC(1))
    # orth_not_gaTwo_even
    A3 = L.derived_gaThree(m)
    check("orth_not_gaTwo_even", any(z[7] % 2 for z in A3), True)
emit(f"  {CHECKS - n5} checks")

# ---- section 6: the mixed point ------------------------------------------------------------
emit()
emit("-- 6 the mixed point, end to end ---------------------------------------------------")
n6 = CHECKS
check("commP_mix", L.commP(L.mixU, L.mixV), (0, 0, 0, 0, 0, 0, 0, 1, 0, 0))
check("commP_mix_eq_oddLive", L.commP(L.mixU, L.mixV), L.commP(L.sigFourU, L.oddLiveV))
check("mixV_not_mem_liveFrameSub", L.in_live_frame(L.mixV), False)
check("mixU_chiA", L.mixU[0] % 2, 1)
check("mixV_covector_vs_oddLiveV",
      (L.mixV[5], L.oddLiveV[5], L.mixV[0] % 2, L.oddLiveV[0] % 2, L.mixV[3] % 2,
       L.oddLiveV[3] % 2), (1, 1, 0, 0, 0, 1))
# commP_mem_halfGaTwoSub, on a uniform sample of the half frame
for _ in range(200000):
    p = list(rnd_elt()); p[3] = 2 * rng.randrange(4); p[6] = 2 * rng.randrange(4)
    q = list(rnd_elt()); q[3] = 2 * rng.randrange(4); q[6] = 2 * rng.randrange(4)
    if not L.in_half_gaTwo(L.commP(tuple(p), tuple(q))):
        FAILS.append(("commP_mem_halfGaTwoSub", (p, q), None))
CHECKS += 200000
for h, j1, j2 in HJ:
    m = L.twoSwapMark(h, j1, j2, L.mixU, L.mixV)
    check("mixMark_le_halfFrameSub", all(L.in_half_frame(p) for p in m), True)
    A3 = L.derived_gaThree(m)
    check("mix_gaTwo_i_even", all(z[8] % 2 == 0 for z in A3), True)
    check("mix_not_gaTwo_even", any(z[7] % 2 for z in A3), True)
    check("mixMove_not_mem_gaTwoOf", (0, 0, 0, 0, 0, 0, 0, 0, 1, 0) in A3, False)
    check("sqRelWord_mixWit_U", L.sqRelWord(L.sigFourDress_at(m, L.sigFourU)), L.liftC(1))
    # mix_unrestricted_kill
    check("mix_unrestricted_kill",
          L.sqRelWord(L.sigLift_at(h, j1, L.sigFourDress_at(m, L.sigFourU), L.ONE, L.ONE,
                                   L.liftC(7), L.ONE, (0, 0, 0, 0, 0, 0, 0, 0, 1, 0))), L.ONE)
    # mix_sigmaForces: no ACHIEVABLE refinement kills at an odd character
    for _ in range(400):
        v = list(rnd_elt()); v[1] = 0; v = tuple(v)
        z0, w1, w2 = rnd_gaThree(), rnd_gaFour(), rnd_gaFour()
        z3, z4 = A3[rng.randrange(len(A3))], A3[rng.randrange(len(A3))]
        md = L.sigFourDress_at(m, v)
        if L.sqRelWord(L.sigLift_at(h, j1, md, z0, w1, w2, z3, z4)) == L.ONE:
            check("mix_sigmaForces", v[0] % 2, 0)
emit(f"  {CHECKS - n6} checks")

# ---- section 7: the corrected headline -------------------------------------------------------
emit()
emit("-- 7 twoLiveOdd_block_not_the_criterion -------------------------------------------")
n7 = CHECKS
check("the three blocks coincide",
      {L.commP(L.sigFourU, L.oddLiveV), L.commP(L.orthU, L.orthV), L.commP(L.mixU, L.mixV)},
      {(0, 0, 0, 0, 0, 0, 0, 1, 0, 0)})
check("all three v-letters are outside liveFrameSub",
      (L.in_live_frame(L.oddLiveV), L.in_live_frame(L.orthV), L.in_live_frame(L.mixV)),
      (False, False, False))
for h, j1, j2 in HJ:
    for nm, U, V, want in (("oddLive", L.sigFourU, L.oddLiveV, False),
                           ("orth", L.orthU, L.orthV, True),
                           ("mix", L.mixU, L.mixV, True)):
        m = L.twoSwapMark(h, j1, j2, U, V)
        A3 = L.derived_gaThree(m)
        mU, mV = m[3 + 2 * j1], m[4 + 2 * j1]
        forces = not any(L.sigIncrPair(mU, mV, z3, z4) % 2 == 1 for z3 in A3 for z4 in A3)
        check(f"SigmaForces [{nm}] h={h} j={j1},{j2}", forces, want)
# the wave-58 kill itself
for h, j1, j2 in HJ:
    m = L.twoSwapMark(h, j1, j2, L.sigFourU, L.oddLiveV)
    check("twoLiveOdd_kill",
          L.sqRelWord(L.sigLift_at(h, j1, L.sigFourDress_at(m, L.sigFourU), L.ONE, L.ONE,
                                   L.liftC(3), L.commP(L.sigFourU, L.oddLiveV), L.ONE)), L.ONE)
emit(f"  {CHECKS - n7} checks")

emit()
emit("=" * 88)
emit(f"named checks: {CHECKS}    MISMATCHES: {len(FAILS)}")
if FAILS:
    for f in FAILS[:20]:
        emit(f"  {f}")
emit("=" * 88)

here = os.path.dirname(os.path.abspath(__file__))
os.makedirs(os.path.join(here, "results"), exist_ok=True)
with open(os.path.join(here, "results", "instance_necessity.txt"), "w") as fh:
    fh.write("\n".join(OUT) + "\n")
sys.exit(1 if FAILS else 0)
