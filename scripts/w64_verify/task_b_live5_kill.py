"""W64-VERIFY task B: does W63-CENTRAL2's gamma_2 kill apply at W63-LIVE5's point?

W63-CENTRAL2 killed the DIAGONALLY dressed frame at wave 60's binder point with an achievable
gamma_2-dressing of the sigma slot, and recorded the mechanism: the sigma slot's class-four
coordinate pairs against `x0.e`, a unit there.  W63-LIVE5 built a fresh point and REUSED the
same `x0` slot.  Neither lane resolved whether the kill transports; an orchestrator spot-check
mis-modelled the dressing, sweeping the BARE witness (which already kills the relator, so the
sweep only recovers the trivial dressing).  The object to sweep is the `a0 = a1` dressing
`liveBlkWit h j stageX`, whose relator is the central translation `<o=1>`.

Everything is computed on the honest `6 x 6` matrices of `scripts/w59_force5/u6mat.py` with the
gamma_2 shift read off the relator (`scripts/w63_central2/centrallib.py`), and the achievable
lattices by exact polycyclic sift.  Nothing is transcribed from an emitted closed form.

Run: `python3 scripts/w64_verify/task_b_live5_kill.py`
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w63_central2"))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))

import centrallib as C                                          # noqa: E402
import u6mat as M                                               # noqa: E402

OUT = []
FAIL = [0]
CHECK = [0]


def check(name, cond, detail=""):
    CHECK[0] += 1
    if not cond:
        FAIL[0] += 1
    OUT.append("  [%s] %-64s %s" % ("ok " if cond else "FAIL", name, detail))


def say(s=""):
    OUT.append(s)


# ---- 0 the live point ---------------------------------------------------------------------

liveSig = M.named(b=1, d=1)                       # liveBlkSig = E_23 E_45
liveY = M.named(e=2, f=5, h=5, l=5, n=7, o=3)     # liveBlkY
liveU = M.named(c=2, d=1)                         # liveBlkU
liveV = M.named(c=2, e=3, j=5)                    # liveBlkV
KILL = M.named(m=3)                               # GradedGammaTwoCentral.gaTwoCenKill


def live_wit(v, h=1, jj=0):
    """`liveBlkWit h j v`: the sigma slot is `liveBlkSig * v`, the x0 slot is `stageX`."""
    return M.mirTuple(h, jj, M.mul(liveSig, v), C.stageX, liveY, liveU, liveV)


say("=" * 100)
say("W64-VERIFY  task B: W63-CENTRAL2's gamma_2 kill at W63-LIVE5's point")
say("=" * 100)
say()
say("0  The live point, and the two frames it names")
say()
mk = live_wit(C.stageX)
S, X, Y, U, V = mk[0], mk[1], mk[2], mk[3], mk[4]
for nm, g in [("sigma  liveBlkSig * stageX", S), ("x0     stageX", X), ("x1     liveBlkY", Y),
              ("U      liveBlkU", U), ("V      liveBlkV", V)]:
    say("   %-26s %s" % (nm, M.show(g)))
say()
check("the BARE witness kills the relator outright (sqRelWord_liveBlkWit_triv)",
      M.sqRelWord(live_wit(M.ONE)) == M.ONE,
      "-> a naive kill sweep here is vacuous; the diagonal frame is the object")
check("the DIAGONAL dressing leaves <o=1> (sqRelWord_liveBlkWit_diag)",
      M.sqRelWord(mk) == M.liftC(1), M.show(M.sqRelWord(mk)))
check("the residue is ODD, so the separation is genuinely class five",
      M.sqRelWord(mk)[14] % 2 == 1)
check("the x0 slot is the SAME letter as wave 60's point", X == C.stageX,
      "stageX = %s, and stageX.e = 5 is a unit" % M.show(C.stageX))

# ---- 1 the achievable gamma_2 lattice at the live point ------------------------------------

say()
say("1  The achievable gamma_2 lattice at the live point,  forceLcs H 1")
say()
gens = [g for g in mk if g != M.ONE]
H = C.subgroup(gens)
A1 = C.derived_of(gens)
say("   log2 |H| = %d,   log2 |forceLcs H 1| = %d" % (H.order_log2(), A1.order_log2()))
check("|forceLcs H 1| = 2^26, the same count wave 63 measured at ITS point",
      A1.order_log2() == 26)
BOXEVEN, BOXFREE = "fghj", "iklmno"
box = (4 ** len(BOXEVEN)) * (8 ** len(BOXFREE))
check("the lattice is the SAME box {gamma_2-shaped : f, g, h, j even}", box == 2 ** 26,
      "box = %d" % box)
random.seed(6401)
bad = 0
for _ in range(4000):
    t = [0] * 15
    for c in BOXEVEN:
        t[C.IDX[c]] = 2 * random.randrange(4)
    for c in BOXFREE:
        t[C.IDX[c]] = random.randrange(8)
    if not A1.contains(tuple(t)):
        bad += 1
check("4000 random box elements all lie in forceLcs H 1", bad == 0, "misses %d" % bad)
for c in "fghijklmno":
    got = A1.contains(M.named(**{c: 1}))
    check("forceLcs H 1 contains <%s=1>: %s" % (c, got), got == (c in BOXFREE))

comms = []
for x in A1.table.values():
    for y in gens:
        comms.append(M.commP(x, y))
A2 = C.subgroup(comms, extra_normalisers=gens)
check("log2 |forceLcs H 2| = 13, and it does NOT contain <m=3>",
      A2.order_log2() == 13 and not A2.contains(KILL))
check("<m=3> IS achievable at gamma_2 and is NOT at stage four", A1.contains(KILL)
      and not A2.contains(KILL), "so the killer sits strictly between the two lattices")

# ---- 2 THE VERDICT ------------------------------------------------------------------------

say()
say("2  THE VERDICT: the kill transports, at every handle count and every handle")
say()
for h in range(1, 5):
    for jj in range(h):
        m2 = live_wit(C.stageX, h=h, jj=jj)
        z = [KILL] + [M.ONE] * (len(m2) - 1)
        d = C.dress(m2, z)
        sh = C.shift(m2, z)
        check("h=%d j=%d: the dressed frame is KILLED" % (h, jj), M.sqRelWord(d) == M.ONE)
        check("h=%d j=%d: the shift is the central translation liftO 7" % (h, jj),
              sh == M.liftC(7), M.show(sh))
        check("h=%d j=%d: dressing slot 0 reparametrises the point" % (h, jj),
              d == live_wit(M.mul(C.stageX, KILL), h=h, jj=jj))
say()
say("   => GaTwoForces, GaTwoCentral and GaTwoOrth are ALL FALSE at liveBlkWit h j stageX.")
say("      The live point inherits wave 60's point's gamma_2 vulnerability in full.")

# ---- 3 the certificate --------------------------------------------------------------------

say()
say("3  The killer as a commutator of the live point's OWN letters")
say()
cert = M.commP(S, M.mul(V, M.inv(U)))
check("commP(liveBlkSig * stageX, liveBlkV * liveBlkU^-1) = <m=3>", cert == KILL,
      M.show(cert))
check("…and it lies in forceLcs H 1", A1.contains(cert))
say("   (wave 63's point needed a PRODUCT of two commutators, "
    "`commP(S^-1, U)^2 * commP(Y, X U)`;")
say("    at the live point one commutator suffices.)")

# ---- 4 the exhaustive sigma-slot sweep -----------------------------------------------------

say()
say("4  How special is the killer?  The exhaustive sigma-slot sweep")
say()
REL = M.sqRelWord(mk)
BLOCK = M.commP(U, V)


def sig_shift(g):
    s = M.mul(S, g)
    return M.mul(M.inv(REL), M.mul(M.sqWord(s, X, Y), BLOCK))


bad = 0
for _ in range(3000):
    t = [0] * 15
    for c in BOXEVEN:
        t[C.IDX[c]] = 2 * random.randrange(4)
    for c in BOXFREE:
        t[C.IDX[c]] = random.randrange(8)
    u = list(t)
    for c in "io":
        u[C.IDX[c]] = random.randrange(8)
    if sig_shift(tuple(t)) != sig_shift(tuple(u)):
        bad += 1
check("the sigma-slot shift ignores the dressing's i and o (3000 random pairs)", bad == 0,
      "differences %d" % bad)
jshifts = [M.show(sig_shift(M.named(j=t))) for t in range(0, 8, 2)]
check("⚠ but it DOES read the dressing's j, where wave 63's point ignored j",
      len(set(jshifts)) == 4,
      "j = 0,2,4,6 give %s (liveBlkSig.d = 1 is odd; fiveSigMark.d = 0)" % ", ".join(jshifts))

tot = cen = odd = kil = 0
for f in range(0, 8, 2):
    for g in range(0, 8, 2):
        for hh in range(0, 8, 2):
            for jj2 in range(0, 8, 2):
                for k in range(8):
                    for ll in range(8):
                        for mm in range(8):
                            for nn in range(8):
                                t = [0] * 15
                                t[C.IDX["f"]], t[C.IDX["g"]], t[C.IDX["h"]] = f, g, hh
                                t[C.IDX["j"]], t[C.IDX["k"]], t[C.IDX["l"]] = jj2, k, ll
                                t[C.IDX["m"]], t[C.IDX["n"]] = mm, nn
                                sh = sig_shift(tuple(t))
                                tot += 1
                                if C.is_central(sh):
                                    cen += 1
                                    if sh[14] % 2 == 1:
                                        odd += 1
                                    if (sh[14] + REL[14]) % 8 == 0:
                                        kil += 1
say("   %d sigma dressings swept (exhaustive modulo the two ignored coordinates i and o):"
    % tot)
say("      %d act centrally, %d of those move the class-five row ODDLY, %d KILL"
    % (cen, odd, kil))
check("the killers are exactly one eighth of the central dressings", kil * 8 == cen,
      "%d * 8 = %d" % (kil, cen))
check("the kill is not an accident of one dressing", kil > 0)

# ---- 5 the general mechanism, MEASURED ----------------------------------------------------

say()
say("5  The general mechanism, MEASURED at random five-tuples and NOT proved anywhere")
say()
rng = random.Random(6402)


def rnd():
    return tuple(rng.randrange(8) for _ in range(15))


bad = 0
for _ in range(3000):
    Sr, Xr, Yr, Ur, Vr = rnd(), rnd(), rnd(), rnd(), rnd()
    hh = rng.randrange(1, 4)
    jj = rng.randrange(hh)
    t = rng.randrange(8)
    m0 = M.mirTuple(hh, jj, Sr, Xr, Yr, Ur, Vr)
    m1 = M.mirTuple(hh, jj, M.mul(Sr, M.named(m=t)), Xr, Yr, Ur, Vr)
    if M.mul(M.inv(M.sqRelWord(m0)), M.sqRelWord(m1)) != M.liftC((t * Xr[C.IDX["e"]]) % 8):
        bad += 1
check("at EVERY five-tuple, a sigma dressing by <m=t> shifts the relator by liftO (t * X.e)",
      bad == 0, "3000 random tuples, %d failures" % bad)
say()
say("   ⚠ This is MEASURED, not proved.  If it were proved, wave 63's kill and this one would")
say("     both be corollaries, and the vulnerability would be visibly a property of the WITNESS")
say("     STANDARD - which demands an odd `x0.e` (D_gauge_x0_e_odd) and an odd diagonal residue")
say("     (B_odd_residue) - rather than of two particular points.")

say()
say("=" * 100)
say("%d named checks, %d failures" % (CHECK[0], FAIL[0]))
say("=" * 100)

text = "\n".join(OUT) + "\n"
os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
with open(os.path.join(HERE, "results", "task_b.txt"), "w") as f:
    f.write(text)
print(text)
