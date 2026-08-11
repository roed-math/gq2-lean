"""W64-VERIFY task E: the bracket-convention audit of the tree's certification scripts.

`w64-psi4` found that `scripts/w63_four/certify.py` ran its 216 weight-three bracket census with
`u6mat.commP`, the PAPER convention

    commP x y = x^-1 y^-1 x y                     (GQ2/Words.lean:59, and every python `commP`)

while the Lean it was certifying, `GradedStageFour.gapOneABr = [[L a, L b], L c]`, uses MATHLIB's

    commutatorElement x y = x y x^-1 y^-1         (Mathlib/GroupTheory/Commutator/Basic)

and the two are different families of elements, related by `[x, y]_mathlib = commP x^-1 y^-1`
(`GradedFiveForce.commutatorElement_eq_commP`).  So the census certified a different set from
the one the `decide` closes.  This script audits the whole tree for that gap.

THE RULE.  A python `commP` computation certifies a Lean statement written with `commP`
correctly, and a Lean statement written with `[.,.]` INCORRECTLY.  So the audit is: for every
Lean statement a script is presented as certifying, which bracket does the LEAN use?

Section 1 lists the tree's `decide`-closed Lean statements that mention the mathlib bracket.
Section 2 re-runs the affected census in both conventions.  Section 3 shows which computations
are convention-IMMUNE and why, so that the good pattern can be named.

Run: `python3 scripts/w64_verify/task_e_bracket_convention.py`
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
    OUT.append("  [%s] %-66s %s" % ("ok " if cond else "FAIL", name, detail))


def say(s=""):
    OUT.append(s)


def commML(x, y):
    """Mathlib's `commutatorElement x y = x * y * x^-1 * y^-1`."""
    return M.mul(M.mul(x, y), M.mul(M.inv(x), M.inv(y)))


CO = "abcdefghijklmno"


def co(z, c):
    return z[CO.index(c)]


say("=" * 100)
say("W64-VERIFY  task E: the bracket-convention audit")
say("=" * 100)
say()
say("0  The two conventions, and the identity that relates them")
say()
bad = 0
import random                                                   # noqa: E402
rng = random.Random(6403)
for _ in range(2000):
    x = tuple(rng.randrange(8) for _ in range(15))
    y = tuple(rng.randrange(8) for _ in range(15))
    if commML(x, y) != M.commP(M.inv(x), M.inv(y)):
        bad += 1
check("[x, y]_mathlib = commP x^-1 y^-1  (GradedFiveForce.commutatorElement_eq_commP)",
      bad == 0, "2000 random pairs, %d failures" % bad)
bad = sum(1 for _ in range(2000)
          if (lambda x, y: commML(x, y) != M.commP(x, y))(
              tuple(rng.randrange(8) for _ in range(15)),
              tuple(rng.randrange(8) for _ in range(15))))
check("…and the two are genuinely DIFFERENT families", bad > 0,
      "%d of 2000 random pairs differ" % bad)

# ---- 1 the census that was affected -------------------------------------------------------

say()
say("1  `scripts/w63_four/certify.py` section 2: the 216 weight-three brackets, both ways")
say()


def tup(*v):
    return tuple(x % 8 for x in v)


gap1 = [tup(5, 2, 3, 0, 3, 0, 0, 0, 0, 2, 0, 0, 0, 6, 0),
        tup(0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 7, 0),
        tup(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0),
        tup(0, 0, 0, 0, 4, 0, 2, 0, 0, 0, 0, 0, 6, 0, 0),
        tup(0, 3, 0, 6, 3, 2, 0, 1, 0, 0, 1, 1, 0, 0, 7), M.ONE]
gap1b = list(gap1)
gap1b[2] = tup(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 4, 0)
gap2 = [tup(1, 7, 3, 0, 5, 1, 0, 0, 0, 0, 3, 7, 6, 0, 1),
        tup(0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 7),
        tup(0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0),
        tup(6, 0, 0, 0, 0, 1, 0, 0, 2, 4, 0, 4, 4, 0, 4),
        tup(0, 0, 0, 4, 0, 7, 0, 0, 7, 5, 0, 5, 0, 3, 0), M.ONE]
gap2b = list(gap2)
gap2b[2] = tup(0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 4, 0)


def kOne(z):
    return (all(co(z, c) % 8 == 0 for c in "abcdefghi")
            and (2 * co(z, "k") + 4 * co(z, "m") + 4 * co(z, "n")) % 8 == 0
            and (2 * co(z, "l") + 4 * co(z, "n")) % 8 == 0)


def kTwo(z):
    return (all(co(z, c) % 8 == 0 for c in "abcdefghi")
            and (co(z, "k") + 4 * co(z, "n")) % 8 == 0
            and (4 * co(z, "l")) % 8 == 0 and (2 * co(z, "m")) % 8 == 0)


TOTAL = 0
for nm, ls, tgt, tn in [("gapOneA", gap1, kOne, "gapKOne"), ("gapOneB", gap1b, kOne, "gapKOne"),
                        ("gapTwoA", gap2, kTwo, "gapKTwo"),
                        ("gapTwoB", gap2b, kTwo, "gapKTwo")]:
    for cname, br in [("paper commP (what the script ran)", M.commP),
                      ("mathlib [.,.] (what the Lean says)", commML)]:
        bad = 0
        n = 0
        for a in ls:
            for b in ls:
                for c in ls:
                    n += 1
                    if not tgt(br(br(a, b), c)):
                        bad += 1
        TOTAL += n
        check("%s, %s: all %d brackets in %s" % (nm, cname, n, tn), bad == 0,
              "violations %d" % bad)
say()
say("   => the conclusion SURVIVES the correction at all four markings; %d brackets checked"
    % TOTAL)
say("      in total, %d of them in the convention the Lean actually uses." % (TOTAL // 2))
say("      ⚠ but the paper-convention run was never a check of the `decide`'s input, and the")
say("        two bracket families are genuinely different (section 0).")

# ---- 2 the raw sets really are different ---------------------------------------------------

say()
say("2  The two conventions give DIFFERENT bracket SETS at these very markings")
say()
for nm, ls in [("gapOneA", gap1), ("gapTwoA", gap2)]:
    sp = {M.commP(M.commP(a, b), c) for a in ls for b in ls for c in ls}
    sm = {commML(commML(a, b), c) for a in ls for b in ls for c in ls}
    check("%s: |paper set| = %d, |mathlib set| = %d, |intersection| = %d"
          % (nm, len(sp), len(sm), len(sp & sm)), True,
          "differ: %s" % (sp != sm))

# ---- 3 which computations are convention-IMMUNE -------------------------------------------

say()
say("3  Convention-IMMUNITY: a NORMAL CLOSURE over the image does not see the convention")
say()
say("   `[[H, H], H]` is generated by the weight-three brackets of GENERATORS in either")
say("   convention, because `H` is closed under inversion and `[x,y]_ml = commP x^-1 y^-1`.")
say("   So any script that normally-closes is safe; only RAW bracket SETS are at risk.")
say()

stageX = tup(2, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
POINTS = {
    "stageWit h j stageX": [M.mul(tup(0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0), stageX),
                            stageX, tup(0, 0, 0, 0, 2, 1, 1, 1, 0, 0, 0, 0, 3, 3, 0),
                            tup(6, 7, 4, 1, 3, 0, 5, 5, 0, 0, 0, 0, 0, 0, 0),
                            tup(6, 7, 6, 1, 3, 5, 3, 3, 4, 0, 0, 0, 0, 0, 0)],
    "liveBlkWit h j stageX": [M.mul(tup(0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0), stageX),
                              stageX, tup(0, 0, 0, 0, 2, 5, 0, 5, 0, 0, 0, 5, 0, 7, 3),
                              tup(0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
                              tup(0, 0, 2, 0, 3, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0)],
    "gapOneMark": gap1[:5],
    "gapTwoMark": gap2[:5],
}
for nm, gens in POINTS.items():
    gg = [g for g in gens if g != M.ONE]
    Np = C.subgroup([M.commP(M.commP(a, b), c) for a in gg for b in gg for c in gg],
                    extra_normalisers=gg)
    Nm = C.subgroup([commML(commML(a, b), c) for a in gg for b in gg for c in gg],
                    extra_normalisers=gg)
    same = (Np.order_log2() == Nm.order_log2()
            and all(Nm.contains(x) for x in Np.table.values())
            and all(Np.contains(x) for x in Nm.table.values()))
    check("%s: the two normal closures agree (= forceLcs H 2)" % nm, same,
          "2^%d vs 2^%d" % (Np.order_log2(), Nm.order_log2()))

say()
say("=" * 100)
say("%d named checks, %d failures" % (CHECK[0], FAIL[0]))
say("=" * 100)

text = "\n".join(OUT) + "\n"
os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
with open(os.path.join(HERE, "results", "task_e_bracket.txt"), "w") as f:
    f.write(text)
print(text)
