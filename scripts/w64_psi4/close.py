"""W64-PSI4, step 2: the doctrine-rule-3 audit of the four now-unconditional forcing theorems.

`GQ2/Dyadic/SqCore/GradedStageFourClosed.lean` discharges the hypothesis of four CONDITIONAL
theorems of `GradedStageFour.lean`.  If the discharged identity were subtly not their hypothesis,
four false unconditional theorems would appear and nothing would complain.  Lean's own
type-checker settles that (`stageForces_gapOneA_of_psi psiOne_gapOneMark` elaborates only if the
statements agree up to definitional equality), but a wrong statement that happens to type-check
would be a wrong statement about the wrong marking, so this script re-establishes the whole chain
from outside Lean:

  A  the FOUR HYPOTHESES, textually.  The `hpsi` binder of each `stageForces_*_of_psi` is parsed
     out of `GradedStageFour.lean`, the corresponding theorem is parsed out of
     `GradedStageFourClosed.lean`, re-assembled as a Pi-type, and the two strings are compared
     after whitespace normalisation: same tuple type, same membership over ALL slots, same
     marking term, same certificate, same section variables.
  B  the IDENTITY, on the honest `6 x 6` matrices.  Not only on single-slot dressings (which is
     what W63-FOUR's `certify.txt` swept exhaustively) but on genuine five-slot tuples drawn from
     the target, which is the quantifier the Lean statement actually uses.
  C  the CONCLUSION, independently.  That the achievable lattice really lies in the target, that
     the relator really is an odd central translation, and that no achievable dressing kills -
     the statement the four theorems now assert without hypotheses.

Everything runs through wave 61's `sharp4lib` on wave 59's honest matrices; no Lean output and no
formula from `psilib` is trusted in part C.

BRACKET CONVENTION.  [MATHLIB]
WARNING: the Lean target of this script is written with MATHLIB's bracket, not with
commP.  Any raw bracket set computed here must be computed in mathlib's convention.
Lean declarations named here that use it: gapOneABr.

Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

import os
import random
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w63_four"))

import psilib as P                                                     # noqa: E402
import fourlib as F                                                    # noqa: E402
import derive as D                                                     # noqa: E402

OPEN = os.path.join(ROOT, "GQ2", "Dyadic", "SqCore", "GradedStageFour.lean")
CLOSED = os.path.join(ROOT, "GQ2", "Dyadic", "SqCore", "GradedStageFourClosed.lean")

# marking, the conditional theorem, the theorem discharging its hypothesis
PAIRS = [("gap-1a", "stageForces_gapOneA_of_psi", "psiOne_gapOneMark", "gapOneMark h j"),
         ("gap-1b", "stageForces_gapOneB_of_psi", "psiOne_gapOneMark'", "gapOneMark' h j"),
         ("gap-2a", "stageForces_gapTwoA_of_psi", "psiTwo_gapTwoMark", "gapTwoMark h j"),
         ("gap-2b", "stageForces_gapTwoB_of_psi", "psiTwo_gapTwoMark'", "gapTwoMark' h j")]

FAIL = []
SEED = 20260811
TRIALS = 4000


def check(name, ok, extra=""):
    print("   %-58s %s %s" % (name, "OK" if ok else "FAIL", extra))
    if not ok:
        FAIL.append(name)


def squash(s):
    return " ".join(s.split())


# ---- A  the hypotheses, textually ------------------------------------------------------------

def hypothesis_of(src, name):
    """The `hpsi` binder of a `stageForces_*_of_psi`, as a normalised Pi-type."""
    m = re.search(r"theorem %s\s*\n\s*\(hpsi : (.*?)\) :\n" % re.escape(name), src, re.S)
    assert m, name
    return squash(m.group(1))


def discharged_of(src, name):
    """A `psi*_gap*Mark*` theorem, re-assembled as the Pi-type it inhabits."""
    m = re.search(r"theorem %s \(z : (.*?)\) \(hz : (.*?)\) :\n(.*?) := by\n"
                  % re.escape(name), src, re.S)
    assert m, name
    return squash("∀ z : %s, (%s) → %s" % (m.group(1), m.group(2), m.group(3)))


def section_vars(src, marker):
    """The `variable` line governing the section containing `marker`."""
    idx = src.index(marker)
    return squash(re.findall(r"variable (\{h : ℕ\} \{j : Fin h\})", src[:idx])[-1])


def part_a():
    print("== A  the four hypotheses, textually")
    so, sc = open(OPEN).read(), open(CLOSED).read()
    for (name, cond, disc, _) in PAIRS:
        want = hypothesis_of(so, cond)
        got = discharged_of(sc, disc)
        check("%-8s %s discharges %s" % (name, disc, cond), want == got)
        if want != got:
            print("        want %s" % want)
            print("        got  %s" % got)
    check("both sections quantify h and j the same way",
          section_vars(so, "theorem stageForces_gapOneA_of_psi")
          == section_vars(sc, "theorem psiOne_gapOneMark "))
    # and the forcing theorems really are the conditional ones applied to the identities
    for (name, cond, disc, mark) in PAIRS:
        thm = "stageForces_%s" % {"gap-1a": "gapOneA", "gap-1b": "gapOneB",
                                  "gap-2a": "gapTwoA", "gap-2b": "gapTwoB"}[name]
        want = squash("theorem %s : StageForces (%s) := %s %s" % (thm, mark, cond, disc))
        check("%-8s %s is exactly %s %s" % (name, thm, cond, disc), want in squash(sc))
    print()


# ---- B  the identity on genuine five-slot tuples ---------------------------------------------

def part_b():
    print("== B  the identity on the honest matrices, five slots at a time")
    rng = random.Random(SEED)
    lets = P.lean_letters()
    for (name, names, target, cert, idx) in D.CASES:
        rows = P.lean_target(target)
        psi = P.lean_certificate(cert)
        mats = [tuple(lets[n][c] for c in P.FIELDS) for n in names]
        d = F.marking_data(mats)
        K = [v for v in _all6() if all(F.dot(r, v) == 0 for r in rows)]
        honest = F.L.shift
        bad = 0
        for _ in range(TRIALS):
            zs = [K[rng.randrange(len(K))] for _ in range(5)]
            if F.dot(psi, honest(mats, zs)) != 0:
                bad += 1
        check("%-8s certificate kills %d random five-slot target tuples" % (name, TRIALS),
              bad == 0, "(%d failures, |target| = %d)" % (bad, len(K)))
        # the five pullbacks are the ones W63-FOUR measured and the Lean proof combines
        lam = [tuple(F.dot(psi, d["mats"][i][s]) for s in range(6)) for i in range(5)]
        ours = [tuple(P.coeffs(P.psi_row(psi, *[lets[n] for n in names]), i)[t] % 8
                      for t in range(6)) for i in range(5)]
        check("%-8s the five slot pullbacks are the derived ones" % name, lam == ours,
              "(%s)" % " | ".join(P.show_vec(v) for v in lam))
    print()


_ALL6 = []


def _all6():
    if _ALL6:
        return _ALL6
    out = _ALL6
    for code in range(8 ** 6):
        v, t = [], code
        for _ in range(6):
            v.append(t % 8)
            t //= 8
        out.append(tuple(v))
    return out


# ---- C  the conclusion, independently --------------------------------------------------------

def part_c():
    print("== C  the conclusion the four theorems now assert, without hypotheses")
    lets = P.lean_letters()
    for (name, names, target, cert, idx) in D.CASES:
        rows = P.lean_target(target)
        mats = [tuple(lets[n][c] for c in P.FIELDS) for n in names]
        d = F.marking_data(mats)
        r = d["relator"]
        check("%-8s relator is a central translation with an ODD residue" % name,
              all(r[k] == 0 for k in range(14)) and r[14] % 2 == 1,
              "(<o=%d>)" % r[14])
        check("%-8s the achievable lattice lies in the target" % name,
              all(all(F.dot(rr, v) == 0 for rr in rows) for v in d["Av"]),
              "(lattice %d)" % len(d["Av"]))
        IB = F.L.image_basis(mats, d["Abasis"])
        check("%-8s no achievable dressing kills: the forcing HOLDS" % name,
              not F.L.kill_exists(mats, basis=IB))
    print()


# ---- D  the mathlib bracket convention, and the odd dressing ---------------------------------

def mbracket(a, b):
    """mathlib's `⁅a, b⁆ = a * b * a⁻¹ * b⁻¹`.

    ⚠ NOT `u6mat.commP`, which is the PAPER convention `x⁻¹ y⁻¹ x y`.  The Lean files use the
    mathlib bracket throughout - `gapOneABr`, `le_of_gens_three`, and the odd dressings below -
    so W63-FOUR's `certify.py`, which ran its 216-bracket census with `commP`, checked a
    different family from the one the Lean `decide` closes.  Both are true; this part checks
    the one the Lean proofs actually use.
    """
    return F.M.mul(F.M.mul(F.M.mul(a, b), F.M.inv(a)), F.M.inv(b))


# marking, the odd dressing as a bracket of slot indices, the slot it is carried on,
# and the class-five value the Lean file claims
ODD = [("gap-1a", (0, 4, 4), 3, 7), ("gap-1b", (0, 4, 4), 3, 7),
       ("gap-2a", (0, 4, 0), 1, 5), ("gap-2b", (0, 4, 0), 1, 5)]


def part_d():
    print("== D  the MATHLIB bracket convention, and the odd dressing")
    lets = P.lean_letters()
    for ((name, names, target, cert, idx), (_, tri, slot, val)) in zip(D.CASES, ODD):
        rows = P.lean_target(target)
        mats = [tuple(lets[n][c] for c in P.FIELDS) for n in names]
        slots = list(mats) + [F.ONE]
        bad = 0
        for a in slots:
            for b in slots:
                for c in slots:
                    w = mbracket(mbracket(a, b), c)
                    if any(w[k] for k in range(9)) or not all(F.dot(r, F.L.vec(w)) == 0
                                                             for r in rows):
                        bad += 1
        check("%-8s all 216 MATHLIB weight-three brackets lie in the target" % name, bad == 0,
              "(%d violations)" % bad)
        w = F.L.vec(mbracket(mbracket(slots[tri[0]], slots[tri[1]]), slots[tri[2]]))
        im = F.L.slot_shift(mats, slot, w)
        check("%-8s the odd dressing pairs to %d on slot %s" % (name, val, P.SLOT[slot]),
              im[5] == val and val % 2 == 1,
              "(w = %s, shift = %s)" % (F.M.show(F.L.elt(w)), F.M.show(F.L.elt(im))))
        check("%-8s ...and moves a class-four row, so it kills nothing" % name,
              (im[3], im[4]) != (0, 0), "(m = %d, n = %d)" % (im[3], im[4]))
        check("%-8s the odd dressing is inside the target too" % name,
              all(F.dot(r, w) == 0 for r in rows))
    print()


if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
    part_d()
    print("TOTAL FAILURES: %d" % len(FAIL))
    for f in FAIL:
        print("   %s" % f)
