"""W63-FOUR, step 4: the Lean file's letters, targets and certificates ARE the measured ones.

Wave 61 recorded the four gap markings as letters in `hunt_gap.txt`; wave 62 re-derived them in
`inspect_four.py`; this wave transcribed them into `GQ2/Dyadic/SqCore/GradedStageFour.lean` by
hand.  A transcription error would produce a Lean file that proves something true about the
wrong markings, which is exactly the kind of silent failure the campaign cannot afford.  So this
script parses the Lean file and checks, coordinate by coordinate, that

  * the twelve letter definitions reproduce wave 62's `FOUR` exactly;
  * `gapKOne` and `gapKTwo` are the subgroups `certify.py` certifies;
  * `psiOne` and `psiTwo` are the certificates `certify.py` certifies.

BRACKET CONVENTION.  [NONE]
This script computes no commutators, so the convention does not arise.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)

import certify as C                                                    # noqa: E402
import fourlib as F                                                    # noqa: E402

LEAN = os.path.join(ROOT, "GQ2", "Dyadic", "SqCore", "GradedStageFour.lean")

WANT = {"gap-1a": ["gapOneS", "gapOneX", "gapOneY", "gapOneU", "gapOneV"],
        "gap-1b": ["gapOneS", "gapOneX", "gapOneY'", "gapOneU", "gapOneV"],
        "gap-2a": ["gapTwoS", "gapTwoX", "gapTwoY", "gapTwoU", "gapTwoV"],
        "gap-2b": ["gapTwoS", "gapTwoX", "gapTwoY'", "gapTwoU", "gapTwoV"]}

# the conditions and certificates as the Lean file writes them, keyed to (j,k,l,m,n,o)
LEAN_KONE = ["2 * z.k + 4 * z.m + 4 * z.n = 0", "2 * z.l + 4 * z.n = 0"]
LEAN_KTWO = ["z.k + 4 * z.n = 0", "4 * z.l = 0", "2 * z.m = 0"]
LEAN_PSIONE = "w.l + 2 * w.n + 4 * w.o"
LEAN_PSITWO = "w.m + 4 * w.o"

COORD = "jklmno"


def form(v):
    parts = ["%d * z.%s" % (v[i], COORD[i]) for i in range(6) if v[i]]
    return " + ".join(p.replace("1 * ", "") for p in parts) + " = 0"


def main():
    src = open(LEAN).read()
    fails = []
    lean = {m.group(1): tuple(int(x) for x in m.group(2).split(","))
            for m in re.finditer(r"def (gap[A-Za-z]+'?) : SqU6 gr3R := ⟨([^⟩]*)⟩",
                                 src)}
    print("== letters")
    for (name, letters) in F.FOUR:
        for nm, py in zip(WANT[name], letters):
            good = lean.get(nm) == tuple(py)
            print("   %-8s %-10s %s" % (name, nm, "OK" if good else "FAIL"))
            if not good:
                fails.append((name, nm))

    print("== targets and certificates")
    for tag, rows, want in (("gapKOne", C.KONE, LEAN_KONE), ("gapKTwo", C.KTWO, LEAN_KTWO)):
        got = [form(r) for r in rows]
        good = got == want
        print("   %-8s %s   %s" % (tag, "OK" if good else "FAIL", " ; ".join(got)))
        if not good:
            fails.append((tag, got))
    for tag, psi, want in (("psiOne", C.PSIONE, LEAN_PSIONE), ("psiTwo", C.PSITWO, LEAN_PSITWO)):
        got = " + ".join(("%d * w.%s" % (psi[i], COORD[i])).replace("1 * ", "")
                         for i in range(6) if psi[i])
        good = got == want and ("def %s (w : SqU6 gr3R) : gr3R := %s" % (tag, want)) in src
        print("   %-8s %s   %s" % (tag, "OK" if good else "FAIL", got))
        if not good:
            fails.append((tag, got))

    print("\nTOTAL FAILURES: %d" % len(fails))
    for f in fails:
        print("   %s" % (f,))


if __name__ == "__main__":
    main()
