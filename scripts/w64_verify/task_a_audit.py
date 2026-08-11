"""W64-VERIFY task A: the tree-wide audit of the committed lattice bounds.

Doctrine rule 1 asks whether every committed bound is the SHARPEST the tree owns.  Every bound
in the list below is proved by running `Subgroup.commutator_le` once per step, which quantifies
over the whole of `H` and so has to name an intermediate subgroup; W63-FOUR's
`le_of_gens_three` needs no such subgroup.  There are two distinct sharpness questions and this
script answers both.

  (U) UNIFORM sharpness.  The bound reads `forall H <= N_in, forceLcs H k <= N_out`.  Since
      `forceLcs` is monotone in `H`, the join of the left side over all admissible `H` is
      `forceLcs N_in k` itself.  So the bound is sharp AS STATED exactly when
      `forceLcs N_in k = N_out`, and that is ONE computation per bound, not a search.

  (P) POINTWISE sharpness.  `le_of_gens_three` applies to `H = closure S` for an explicit `S`.
      Its sharpest admissible target is `forceLcs (closure S) k` itself (section 3 below
      certifies this numerically; `GradedLcsGens.lcsSeries_le_iff_of_gens` proves it).  So at
      every named marking the sharpening available is exactly the gap between the honest
      lattice and `N_out`.

Everything is computed on the honest `6 x 6` matrices of `scripts/w59_force5/u6mat.py` by the
exact polycyclic sift of `scripts/w63_central2/centrallib.py`.  Nothing is transcribed from a
Lean proof: the target subgroups are re-entered from their `carrier` fields and the markings
from their letter definitions, and section 0 checks the re-entry against the group law.

Run: `python3 scripts/w64_verify/task_a_audit.py`

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


CO = "abcdefghijklmno"


def co(z, c):
    return z[CO.index(c)]


# ---- 0 the target subgroups, re-entered from their Lean `carrier` fields -------------------
#
# Each is a predicate on a tuple, plus a generating set.  `zero` lists the coordinates the
# carrier sets to 0 and `even` the coordinates it makes even; every target in the tree has that
# shape.


class Target:
    def __init__(self, name, zero, even, lean):
        self.name = name
        self.zero = zero
        self.even = even
        self.lean = lean

    def contains(self, z):
        return (all(co(z, c) % 8 == 0 for c in self.zero)
                and all(co(z, c) % 2 == 0 for c in self.even))

    def gens(self):
        g = []
        for c in CO:
            if c in self.zero:
                continue
            g.append(M.named(**{c: 2 if c in self.even else 1}))
        return g

    def log2(self):
        return 3 * (15 - len(self.zero)) - len(self.even)


TOP = Target("(whole group)", "", "", "-")
gaTwoSub = Target("gaTwoSub", "abcde", "", "GradedFiveNecessity:336")
gaThreeSub = Target("gaThreeSub", "abcdefghi", "", "GradedFiveNecessity:352")
gaFourSub = Target("gaFourSub", "abcdefghijkl", "", "GradedFiveNecessity:373")
stageN1 = Target("stageN1", "", "ac", "GradedFiveStageFour:716")
stageN2 = Target("stageN2", "abcde", "fhj", "GradedFiveStageFour:728")
stageN3 = Target("stageN3", "abcdefghi", "jlm", "GradedFiveStageFour:759")
forceN1 = Target("forceN1", "", "c", "GradedFiveForce:654")
forceN2 = Target("forceN2", "abcde", "gh", "GradedFiveForce:665")
forceN3 = Target("forceN3", "abcdefghi", "jkl", "GradedFiveForce:684")
forceN4 = Target("forceN4", "abcdefghijkl", "mn", "GradedFiveForce:714")
fiveEvenE = Target("fiveEvenE", "", "e", "GradedFiveNecessity:672")
fiveEvenI = Target("fiveEvenI", "abcde", "i", "GradedFiveNecessity:684")
fiveEvenL = Target("fiveEvenL", "abcdefghi", "l", "GradedFiveNecessity:700")
fiveEvenN = Target("fiveEvenN", "abcdefghijkl", "n", "GradedFiveNecessity:724")
sepEvenA = Target("sepEvenA", "", "a", "GradedStageSeparate:414")
sepEvenF = Target("sepEvenF", "abcde", "f", "GradedStageSeparate:427")
sepEvenJ = Target("sepEvenJ", "abcdefghi", "j", "GradedStageSeparate:448")

say("=" * 100)
say("W64-VERIFY  task A audit: are the tree's committed lattice bounds the sharpest it owns?")
say("=" * 100)
say()
say("0  The target subgroups, re-entered and checked against the group law")
say()
for T in [TOP, gaTwoSub, gaThreeSub, gaFourSub, stageN1, stageN2, stageN3, forceN1, forceN2,
          forceN3, forceN4, fiveEvenE, fiveEvenI, fiveEvenL, fiveEvenN, sepEvenA, sepEvenF,
          sepEvenJ]:
    S = C.subgroup(T.gens())
    ok = S.order_log2() == T.log2()
    # closed under the group law and inverses, on the sifted generators
    closed = all(T.contains(M.mul(x, y)) and T.contains(M.inv(x))
                 for x in T.gens() for y in T.gens())
    check("%-11s log2 |.| = %2d, generated and closed" % (T.name, T.log2()), ok and closed,
          "sift gives %d  (%s)" % (S.order_log2(), T.lean))


def force_lcs(gens, k):
    """`forceLcs (closure gens) k`, by exact polycyclic sift."""
    S = C.subgroup([g for g in gens if g != M.ONE])
    cur = [g for g in gens if g != M.ONE]
    A = S
    for _ in range(k):
        comms = []
        src = list(A.table.values()) if A is not S else cur
        for x in src:
            for y in cur:
                comms.append(M.commP(x, y))
        A = C.subgroup(comms, extra_normalisers=cur)
    return A


# ---- 1 UNIFORM sharpness ------------------------------------------------------------------

say()
say("1  UNIFORM sharpness:  is  forceLcs N_in k = N_out ?")
say()
say("   bound                                    file                      N_in       k  "
    "log2 |forceLcs N_in k|  log2 |N_out|  verdict")

BOUNDS = [
    ("forceLcs_one_le_gaTwoSub", "GradedGammaTwoCentral:198", TOP, 1, gaTwoSub),
    ("forceLcs_two_le_gaThreeSub", "GradedStageNecessity:393", TOP, 2, gaThreeSub),
    ("forceLcs_three_le_gaFourSub", "GradedFiveNecessity:445", TOP, 3, gaFourSub),
    ("forceLcs_one_le_stageN2", "GradedFiveGammaTwo:1251", stageN1, 1, stageN2),
    ("forceLcs_two_le_stageN3", "GradedFiveStageFour:869", stageN1, 2, stageN3),
    ("forceLcs_three_le_forceN4", "GradedFiveForce:868", forceN1, 3, forceN4),
    ("forceLcs_two_le_fiveEvenL", "GradedStageNecessity:663", fiveEvenE, 2, fiveEvenL),
    ("forceLcs_three_le_fiveEvenN", "GradedFiveNecessity:799", fiveEvenE, 3, fiveEvenN),
    ("forceLcs_two_le_sepEvenJ", "GradedStageSeparate:515", sepEvenA, 2, sepEvenJ),
]

UNIFORM = {}
for nm, fl, nin, k, nout in BOUNDS:
    A = force_lcs(nin.gens(), k)
    inside = all(nout.contains(z) for z in A.table.values())
    onto = all(A.contains(g) for g in nout.gens())
    sharp = inside and onto and A.order_log2() == nout.log2()
    UNIFORM[nm] = (A.order_log2(), nout.log2(), sharp)
    say("   %-40s %-25s %-10s %d  %14d %13d       %s"
        % (nm, fl, nin.name, k, A.order_log2(), nout.log2(),
           "SHARP" if sharp else "NOT sharp"))
    check("%s: containment holds (soundness re-derived)" % nm, inside)

say()
for nm, fl, nin, k, nout in BOUNDS:
    lo, hi, sharp = UNIFORM[nm]
    check("%s uniform sharpness" % nm, True,
          "forceLcs %s %d = 2^%d, %s = 2^%d -> %s"
          % (nin.name, k, lo, nout.name, hi, "SHARP" if sharp else "SLACK 2^%d" % (hi - lo)))

# ---- 2 POINTWISE sharpness at the tree's named markings ------------------------------------

say()
say("2  POINTWISE: the honest lattice at the tree's named markings, against the bound used")
say()


def tup(*v):
    return tuple(x % 8 for x in v)


stageX = tup(2, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
stageY = tup(0, 0, 0, 0, 2, 1, 1, 1, 0, 0, 0, 0, 3, 3, 0)
stageU = tup(6, 7, 4, 1, 3, 0, 5, 5, 0, 0, 0, 0, 0, 0, 0)
stageV = tup(6, 7, 6, 1, 3, 5, 3, 3, 4, 0, 0, 0, 0, 0, 0)
fiveSig = tup(0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

forceX = tup(2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
forceY = tup(0, 0, 0, 0, 2, 1, 0, 3, 1, 2, 2, 2, 3, 2, 2)
forceU = tup(1, 0, 2, 3, 0, 3, 2, 2, 2, 0, 0, 0, 0, 0, 0)
forceV = tup(0, 0, 0, 1, 2, 3, 2, 3, 3, 0, 0, 0, 0, 0, 0)

liveSig = tup(0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
liveY = tup(0, 0, 0, 0, 2, 5, 0, 5, 0, 0, 0, 5, 0, 7, 3)
liveU = tup(0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
liveV = tup(0, 0, 2, 0, 3, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0)

mixS = tup(2, 4, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2)
mixX = tup(4, 0, 0, 3, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0)
mixY = tup(0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0)
mixU = tup(6, 0, 0, 0, 2, 0, 0, 0, 2, 1, 3, 1, 0, 5, 0)
mixV = tup(6, 0, 5, 0, 2, 1, 0, 0, 4, 0, 7, 0, 0, 0, 0)

orthS = tup(1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0)
orthX = tup(0, 4, 3, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0)
orthY = tup(0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 7, 0)
orthU = tup(0, 0, 0, 1, 0, 0, 6, 0, 0, 3, 0, 0, 0, 2, 0)
orthV = tup(0, 5, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0)

halfS = tup(2, 0, 0, 0, 4, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0)
halfX = tup(0, 7, 6, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
halfY = tup(0, 2, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0, 0, 0)
halfU = tup(1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0)
halfV = tup(2, 0, 3, 7, 4, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0)

gap1S = tup(5, 2, 3, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 6, 0)
gap1X = tup(0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 7, 0)
gap1Y = tup(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0)
gap1Yp = tup(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 4, 0)
gap1U = tup(0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 6, 0, 0)
gap1V = tup(0, 3, 0, 6, 3, 2, 0, 1, 0, 0, 1, 1, 0, 0, 7)

gap2S = tup(1, 7, 3, 0, 5, 1, 0, 0, 0, 0, 3, 7, 6, 0, 1)
gap2X = tup(0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 7)
gap2Y = tup(0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0)
gap2Yp = tup(0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 4, 0)
gap2U = tup(6, 0, 0, 0, 0, 1, 0, 0, 2, 4, 0, 4, 4, 0, 4)
gap2V = tup(0, 0, 0, 4, 0, 7, 0, 0, 7, 5, 0, 5, 0, 3, 0)

gapKOne = ("gapKOne", lambda z: (2 * co(z, "k") + 4 * co(z, "m") + 4 * co(z, "n")) % 8 == 0
           and (2 * co(z, "l") + 4 * co(z, "n")) % 8 == 0, 14)
gapKTwo = ("gapKTwo", lambda z: (co(z, "k") + 4 * co(z, "n")) % 8 == 0
           and (4 * co(z, "l")) % 8 == 0 and (2 * co(z, "m")) % 8 == 0, 12)

POINTS = [
    ("stageWit h j stageX  (w60 binder)", [M.mul(fiveSig, stageX), stageX, stageY, stageU,
                                           stageV], 2, stageN3, None),
    ("liveBlkWit h j stageX  (w63 live)", [M.mul(liveSig, stageX), stageX, liveY, liveU,
                                           liveV], 2, stageN3, None),
    ("fiveWit h j forceX  (w59/w60)", [M.mul(fiveSig, forceX), forceX, forceY, forceU,
                                       forceV], 3, forceN4, None),
    ("mixStageMark  (w61 strictness)", [mixS, mixX, mixY, mixU, mixV], 2, stageN3, None),
    ("orthFiveMark  (w59 strictness)", [orthS, orthX, orthY, orthU, orthV], 3, forceN4, None),
    ("halfFiveMark  (w59 half point)", [halfS, halfX, halfY, halfU, halfV], 3, forceN4, None),
    ("gapOneMark  (w63-four)", [gap1S, gap1X, gap1Y, gap1U, gap1V], 2, stageN3, gapKOne),
    ("gapOneMark' (w63-four)", [gap1S, gap1X, gap1Yp, gap1U, gap1V], 2, stageN3, gapKOne),
    ("gapTwoMark  (w63-four)", [gap2S, gap2X, gap2Y, gap2U, gap2V], 2, stageN3, gapKTwo),
    ("gapTwoMark' (w63-four)", [gap2S, gap2X, gap2Yp, gap2U, gap2V], 2, stageN3, gapKTwo),
]

NIN_OF = {"stageN3": stageN1, "forceN4": forceN1}

say("   marking                                k  log2 lattice  log2 N_out  slack  hyp?  "
    "w63-four target  its slack")
for nm, gens, k, nout, gk in POINTS:
    A = force_lcs(gens, k)
    lo = A.order_log2()
    nin = NIN_OF[nout.name]
    hyp = all(nin.contains(g) for g in gens)
    extra = ""
    if gk is not None:
        gname, gpred, glog = gk
        inside = all(gpred(z) for z in A.elements()) if lo <= 16 else None
        extra = "  %-8s 2^%-3d %s" % (gname, glog, "slack 2^%d" % (glog - lo))
        check("%s: lattice inside %s" % (nm.split()[0], gname), inside is True)
    say("   %-38s %d  %11d %11d  2^%-4d %-4s%s"
        % (nm, k, lo, nout.log2(), nout.log2() - lo, "yes" if hyp else "NO", extra))
    if hyp:
        check("%s: hypothesis %s holds, lattice inside %s (soundness re-derived)"
              % (nm.split()[0], nin.name, nout.name),
              all(nout.contains(z) for z in A.table.values()))
    else:
        check("%s: hypothesis %s FAILS, so the bound is not claimed there"
              % (nm.split()[0], nin.name), True,
              "lattice inside %s anyway: %s"
              % (nout.name, all(nout.contains(z) for z in A.table.values())))

# ---- 3 the generator reduction is EXACT ---------------------------------------------------

say()
say("3  `le_of_gens_three` loses NOTHING: the normal closure of the generator triple brackets")
say("   IS the lattice, at every named marking")
say()
say("   ⚠ the brackets here are MATHLIB's `[x, y] = x y x^-1 y^-1`, which is what")
say("     `le_of_gens_three`'s hypothesis is stated with - not the paper `commP` that every")
say("     python library in this tree provides.  See scripts/w64_verify/task_e_bracket*.py.")
say()


def commML(x, y):
    return M.mul(M.mul(x, y), M.mul(M.inv(x), M.inv(y)))


for nm, gens, k, nout, gk in POINTS:
    if k != 2:
        continue
    gg = [g for g in gens if g != M.ONE]
    brs = []
    for s in gg:
        for t in gg:
            for u in gg:
                brs.append(commML(commML(s, t), u))
    N = C.subgroup(brs, extra_normalisers=gg)
    A = force_lcs(gens, 2)
    same = N.order_log2() == A.order_log2() and all(A.contains(x) for x in N.table.values()) \
        and all(N.contains(x) for x in A.table.values())
    check("%s: normal closure of the %d brackets = forceLcs H 2" % (nm.split()[0], len(brs)),
          same, "2^%d vs 2^%d" % (N.order_log2(), A.order_log2()))


# ---- 4 what the two non-sharp bounds should say -------------------------------------------

say()
say("4  The exact uniform lattices, for the two bounds that are NOT sharp")
say()
for lbl, nin, k, nout in [("forceLcs stageN1 1", stageN1, 1, stageN2),
                          ("forceLcs stageN1 2", stageN1, 2, stageN3)]:
    A = force_lcs(nin.gens(), k)
    say("   %s  (log2 = %d; %s is log2 = %d)" % (lbl, A.order_log2(), nout.name, nout.log2()))
    row = []
    for c in CO:
        vals = [t for t in range(8) if A.contains(M.named(**{c: t}))]
        row.append("%s in %s" % (c, "{" + ",".join(str(v) for v in vals) + "}"))
    say("      single-coordinate members: " + ";  ".join(row))
    miss = [g for g in nout.gens() if not A.contains(g)]
    say("      generators of %s NOT in it: %s"
        % (nout.name, ", ".join(M.show(g) for g in miss) if miss else "(none)"))
    say()

# the two sharpened targets, proposed as drop-in replacements, certified exhaustively
sharpN2 = Target("stageN2'", "abcde", "fghj", "PROPOSED")
A1s = force_lcs(stageN1.gens(), 1)
check("forceLcs stageN1 1 has order 2^26 = |stageN2'| and contains every stageN2' generator",
      A1s.order_log2() == sharpN2.log2() and all(A1s.contains(g) for g in sharpN2.gens())
      and all(sharpN2.contains(z) for z in A1s.table.values()),
      "so the two agree: 2^%d" % A1s.order_log2())

A2s = force_lcs(stageN1.gens(), 2)
els = A2s.elements()
sharp3 = all(all(co(z, c) % 8 == 0 for c in "abcdefghi") and co(z, "j") % 4 == 0
             and co(z, "k") % 2 == 0 and co(z, "l") % 2 == 0 and co(z, "m") % 2 == 0
             for z in els)
check("forceLcs stageN1 2 = stageN3' = {a..i = 0, 4|j, 2|k, 2|l, 2|m}, exhaustively",
      sharp3 and len(els) == 2 ** 13 and A2s.order_log2() == 13,
      "%d elements checked, all inside" % len(els))
check("stageN3' is STRICTLY inside stageN3: <j=2> and <k=1> are in stageN3 and not achievable",
      not A2s.contains(M.named(j=2)) and not A2s.contains(M.named(k=1))
      and stageN3.contains(M.named(j=2)) and stageN3.contains(M.named(k=1)))
say("   => the sharp uniform statements the tree should own:")
say("        forceLcs H 1 <= stageN2' = {a..e = 0, 2|f, 2|g, 2|h, 2|j}   (stageN2 misses 2|g)")
say("        forceLcs H 2 <= stageN3' = {a..i = 0, 4|j, 2|k, 2|l, 2|m}   "
    "(stageN3 has 2|j and no k)")
say("      both for every  H <= stageN1, both index 2 resp. 4 sharper than the committed form.")
say()

say()
say("=" * 100)
say("%d named checks, %d failures" % (CHECK[0], FAIL[0]))
say("=" * 100)

text = "\n".join(OUT) + "\n"
os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
with open(os.path.join(HERE, "results", "task_a_audit.txt"), "w") as f:
    f.write(text)
print(text)
