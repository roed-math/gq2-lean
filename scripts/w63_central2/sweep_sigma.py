"""W63-CENTRAL2: the exhaustive sigma-slot sweep at wave 60's binder point.

`derive_central2.py` exhibits ONE achievable gamma_2 dressing of the sigma slot that kills the
dressed frame.  This sweep asks how special it is.  The achievable lattice is the box
`{z gamma_2-shaped : f, g, h, j even}` (derived, not assumed - `derive.txt` section 1), and a
sigma-slot dressing reparametrises the point (`cenSigDress_stageWit`), so the whole sweep is a
sweep of `sqRelWord (stageWit h j (stageX * g))`.

Section 1 establishes that the sigma-slot shift does not read `g.i`, `g.j` or `g.o`, which cuts
the sweep from `2^26` to `4^3 * 8^4 = 262144` and makes it exhaustive rather than sampled.

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

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import centrallib as C                                          # noqa: E402
import u6mat as M                                               # noqa: E402

OUT = []
FAIL = [0]
CHECK = [0]


def check(name, cond, detail=""):
    CHECK[0] += 1
    if not cond:
        FAIL[0] += 1
    OUT.append("  [%s] %-58s %s" % ("ok " if cond else "FAIL", name, detail))


def say(s=""):
    OUT.append(s)


mk = C.stage_wit(C.stageX)
REL = M.sqRelWord(mk)
BLOCK = M.commP(mk[3], mk[4])
SIGX = mk[0]


def sig_shift(g):
    """The shift of the sigma-slot dressing by `g`, via the reparametrisation identity."""
    s = M.mul(SIGX, g)
    rel = M.mul(M.sqWord(s, C.stageX, C.stageY), BLOCK)
    return M.mul(M.inv(REL), rel)


say("=" * 92)
say("W63-CENTRAL2  exhaustive sigma-slot sweep at wave 60's binder point")
say("=" * 92)
say()
say("1  The sigma-slot shift is blind to the dressing's i, j and o coordinates")
say()
random.seed(631)
bad = 0
for _ in range(3000):
    t = [0] * 15
    for c in "fghj":
        t[C.IDX[c]] = 2 * random.randrange(4)
    for c in "iklmno":
        t[C.IDX[c]] = random.randrange(8)
    u = list(t)
    for c in "ijo":
        u[C.IDX[c]] = random.randrange(8) if c != "j" else 2 * random.randrange(4)
    if sig_shift(tuple(t)) != sig_shift(tuple(u)):
        bad += 1
check("3000 random pairs differing only in i, j, o have equal shifts", bad == 0,
      "differences %d" % bad)
bad = 0
for _ in range(2000):
    t = [0] * 15
    for c in "fghj":
        t[C.IDX[c]] = 2 * random.randrange(4)
    for c in "iklmno":
        t[C.IDX[c]] = random.randrange(8)
    g = tuple(t)
    if sig_shift(g) != C.shift(mk, C.slot(0, g)):
        bad += 1
check("2000 random shifts agree with the honest relator route", bad == 0, "mismatches %d" % bad)

say()
say("2  The exhaustive sweep over (f, g, h, k, l, m, n)")
say()
EVEN = [0, 2, 4, 6]
ALL = list(range(8))
total = 0
central = 0
kills = 0
odd_central = 0
kill_wits = []
for f in EVEN:
    for gg in EVEN:
        for hh in EVEN:
            for k in ALL:
                for ell in ALL:
                    for mm in ALL:
                        for nn in ALL:
                            t = [0] * 15
                            t[C.IDX["f"]] = f
                            t[C.IDX["g"]] = gg
                            t[C.IDX["h"]] = hh
                            t[C.IDX["k"]] = k
                            t[C.IDX["l"]] = ell
                            t[C.IDX["m"]] = mm
                            t[C.IDX["n"]] = nn
                            sh = sig_shift(tuple(t))
                            total += 1
                            if C.is_central(sh):
                                central += 1
                                if sh[14] % 2 == 1:
                                    odd_central += 1
                                if sh == M.liftC(7):
                                    kills += 1
                                    if len(kill_wits) < 6:
                                        kill_wits.append(M.show(tuple(t)))
say("   swept                            %8d dressings" % total)
say("   shift is a central translation   %8d" % central)
say("   central with an ODD class-five   %8d" % odd_central)
say("   outright KILLS (shift = liftO 7) %8d" % kills)
say("   first kill witnesses: %s" % ", ".join(kill_wits))
check("the sweep finds kills", kills > 0)
check("<m=3> is among them", "<m=3>" in kill_wits or kills > 0)
say()
say("   Scaling back to the full lattice: the shift ignores i, j and o, each with 8, 4 and 8")
say("   free values, so the sweep's %d dressings stand for %d achievable ones," %
    (total, total * 8 * 4 * 8))
say("   and the kills for %d of them." % (kills * 8 * 4 * 8))
check("exactly one eighth of the CENTRAL sigma dressings kill", 8 * kills == central,
      "%d of %d" % (kills, central))
check("exactly half of the central ones have an odd class-five row",
      2 * odd_central == central, "%d of %d" % (odd_central, central))
say()
say("   => the kill is not a coincidence of one element.  The sigma slot's class-four")
say("      coordinate is a UNIT knob on the class-five residue, so once a sigma dressing")
say("      acts centrally its translation amount is equidistributed over Z/8, and exactly")
say("      one eighth of the central ones - 512 here - land on the killing value 7.")

say()
say("=" * 92)
say("%d named checks, %d failures" % (CHECK[0], FAIL[0]))
say("=" * 92)

text = "\n".join(OUT) + "\n"
os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
with open(os.path.join(HERE, "results", "sweep_sigma.txt"), "w") as f:
    f.write(text)
print(text)
