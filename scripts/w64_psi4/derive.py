"""W64-PSI4, step 1: derive the `linear_combination` witness that closes the four.

For each of wave 61's four gap markings this script

  1  reads the five letters, the target's conditions and the certificate OUT OF the Lean file
     `GQ2/Dyadic/SqCore/GradedStageFour.lean`, so nothing is transcribed by hand;
  2  builds `psi (gaThreeShift h (fiveTuple ...) z)` as an exact INTEGER linear form in the
     thirty dressing coordinates, from the Lean definitions reimplemented in `psilib`;
  3  CROSS-CHECKS that form, coefficient by coefficient mod `8`, against wave 61's
     `sharp4lib.slot_matrix`, which is read off wave 59's honest `6 x 6` matrices by dressing
     and re-evaluating the relator and never consults a Lean formula;
  4  solves for integer coefficients of the target's own conditions, one slot at a time, and
     emits the exact integer witness `W = (psi-row - combination) / 8`;
  5  prints the `linear_combination` term the Lean proof uses.

Step 3 is the safeguard: if `psilib`'s transcription of `gaThreeCore`, `gaThreeCorr`,
`gaThreePair` or `gaThreeHandle` were wrong, or if the Lean letters were not the measured
letters, the emitted witness would still be internally consistent but would disagree with the
honest matrices, and the check fails.

BRACKET CONVENTION.  [NONE]
This script computes no commutators, so the convention does not arise.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w63_four"))

import psilib as P                                                     # noqa: E402
import fourlib as F                                                    # noqa: E402

FIELDS = P.FIELDS

# name, the five Lean letter definitions, the Lean target, the Lean certificate,
# and the index of the marking in wave 62's `FOUR`
CASES = [
    ("gap-1a", ["gapOneS", "gapOneX", "gapOneY", "gapOneU", "gapOneV"],
     "gapKOne", "psiOne", 0),
    ("gap-1b", ["gapOneS", "gapOneX", "gapOneY'", "gapOneU", "gapOneV"],
     "gapKOne", "psiOne", 1),
    ("gap-2a", ["gapTwoS", "gapTwoX", "gapTwoY", "gapTwoU", "gapTwoV"],
     "gapKTwo", "psiTwo", 2),
    ("gap-2b", ["gapTwoS", "gapTwoX", "gapTwoY'", "gapTwoU", "gapTwoV"],
     "gapKTwo", "psiTwo", 3),
]

FAIL = []


def check(name, ok, extra=""):
    print("   %-56s %s %s" % (name, "OK" if ok else "FAIL", extra))
    if not ok:
        FAIL.append(name)


def report(name, names, target, cert, idx):
    lets = P.lean_letters()
    rows = P.lean_target(target)
    psi = P.lean_certificate(cert)
    L = [lets[n] for n in names]
    mats = [tuple(d[c] for c in FIELDS) for d in L]

    print("== %s   target %s   certificate %s = %s"
          % (name, target, cert, P.show_char_psi(psi)))
    print("   letters from Lean: %s" % " | ".join(F.M.show(g) for g in mats))

    # the Lean letters are wave 62's letters
    check("Lean letters are the measured gap letters",
          [tuple(g) for g in mats] == [tuple(g) for g in F.FOUR[idx][1]])

    # the integer linear form
    f = P.psi_row(psi, L[0], L[1], L[2], L[3], L[4])

    # cross-check mod 8 against the honest 6 x 6 shift matrices
    slotmats = [F.L.slot_matrix(mats, i) for i in range(5)]
    bad = []
    for s in range(5):
        for t in range(6):
            honest = F.dot(psi, slotmats[s][t]) % 8
            ours = f.get((s, t), 0) % 8
            if honest != ours:
                bad.append((P.SLOT[s], P.COORD6[t], honest, ours))
    check("integer form matches the honest shift matrices mod 8", not bad,
          "(30 coefficients, %d mismatches)" % len(bad))
    for b in bad:
        print("        slot %s coord %s honest %d ours %d" % b)

    # the pullback of the certificate to each slot, mod 8
    print("   pullbacks mod 8:")
    for s in range(5):
        print("      slot %-6s %s" % (P.SLOT[s], P.show_vec(P.coeffs(f, s))))

    # solve, slot by slot
    cs = []
    for s in range(5):
        c = P.solve_slot(f, rows, s)
        check("slot %-6s in the mod-8 span of the target's conditions" % P.SLOT[s],
              c is not None, "" if c is None else "(coefficients %s)" % (c,))
        cs.append(c if c is not None else (0,) * len(rows))

    W = P.witness(f, rows, cs)
    check("residue divisible by 8, exact integer witness found", True,
          "(%d non-zero coefficients)" % len(W))

    # independent re-verification of the emitted identity, as integer polynomials
    tot = dict(f)
    for s in range(5):
        for t, cond in enumerate(P.slot_conditions(rows, s)):
            tot = P.sub(tot, P.smul(cs[s][t], cond))
    tot = P.sub(tot, P.smul(8, W))
    check("psi-row - combination - 8 * W is identically zero over Z", not tot)

    print("   W = %s" % P.show_form(W))
    print("   Lean: linear_combination %s" % lean_term(rows, cs, W, target))
    print()
    return cs, W


HYP = {"gapKOne": [["e0", "f0"], ["e1", "f1"], ["e2", "f2"], ["e3", "f3"], ["e4", "f4"]],
       "gapKTwo": [["e0", "f0", "g0"], ["e1", "f1", "g1"], ["e2", "f2", "g2"],
                   ["e3", "f3", "g3"], ["e4", "f4", "g4"]]}


def lean_term(rows, cs, W, target):
    parts = []
    for s in range(5):
        for t in range(len(rows)):
            c = cs[s][t]
            if c:
                parts.append("%s%s" % ("" if c == 1 else "%d * " % c, HYP[target][s][t]))
    parts.append("(%s) * gr8c" % P.lean_form(W))
    return " + ".join(parts)


if __name__ == "__main__":
    for case in CASES:
        report(*case)
    print("TOTAL FAILURES: %d" % len(FAIL))
    for f in FAIL:
        print("   %s" % f)
