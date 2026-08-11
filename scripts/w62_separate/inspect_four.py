"""W62-SEPARATE: interrogate the FOUR wave-61 gap markings before trusting them.

Wave 61's `hunt_gap.py` reported four admissible stage-four markings at which the PARITY line
`StageOrth` fails and the forcing still holds.  They were MEASURED.  Before proving anything
this script rebuilds them from the recorded letters and checks, independently:

  * admissibility (relator central with an odd class-five residue);
  * `kill_exists` is FALSE, i.e. no achievable dressing kills - the forcing holds;
  * `orth_all` is FALSE, i.e. the parity line fails, with the explicit odd dressing;
  * `orth_central` is TRUE, i.e. the sharp line holds;
  * `orth_central_unrestricted`: does the sharp line hold with NO achievability at all?
    If it does, the Lean proof needs no lower-central-series input on the central side.
  * `modlow`: the mod-2 span candidate wave 61 reported at 0 of 1650.

Everything runs on wave 59's honest 6 x 6 matrix library through wave 61's `sharp4lib`.
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w61_sharp4"))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w60_stage4"))

import sharp4lib as L                                                  # noqa: E402
import modlib as MD                                                    # noqa: E402
import u6mat as M                                                      # noqa: E402

# ---- the four, as recorded in scripts/w61_sharp4/results/hunt_gap.txt ---------------------

P1S = M.named(a=5, b=2, c=3, e=3, j=2, n=6)
P1X = M.named(i=6, n=7)
P1Y = M.named(k=2, l=1)
P1Y2 = M.named(k=2, l=1, n=4)
P1U = M.named(e=4, g=2, m=6)
P1V = M.named(b=3, d=6, e=3, f=2, h=1, k=1, l=1, o=7)

P2S = M.named(a=1, b=7, c=3, e=5, f=1, k=3, l=7, m=6, o=1)
P2X = M.named(g=2, o=7)
P2Y = M.named(j=3)
P2Y2 = M.named(j=3, n=4)
P2U = M.named(a=6, f=1, i=2, j=4, l=4, m=4, o=4)
P2V = M.named(d=4, f=7, i=7, j=5, l=5, n=3)

FOUR = [("gap-1a", [P1S, P1X, P1Y, P1U, P1V]),
        ("gap-1b", [P1S, P1X, P1Y2, P1U, P1V]),
        ("gap-2a", [P2S, P2X, P2Y, P2U, P2V]),
        ("gap-2b", [P2S, P2X, P2Y2, P2U, P2V])]


def odd_witnesses(m, B):
    """Every achievable dressing of a single slot whose class-five row is ODD."""
    out = []
    for i in range(len(m)):
        mat = L.slot_matrix(m, i)
        for g in L.members(B):
            im = L.apply_matrix(mat, g)
            if im[5] % 2:
                out.append((i, g, im))
    return out


def report(name, m):
    print("== %s" % name)
    print("   letters: %s" % " | ".join(M.show(g) for g in m))
    r = L.relator(m)
    print("   relator: %s   admissible %s" % (M.show(r), L.admissible(m)))
    B = L.gamma3_basis(m)
    IB = L.image_basis(m, B)
    print("   |gamma_3(im)| %d   |image| %d   central image %s"
          % (MD.card(B, 6), MD.card(IB, 6), L.central_basis(IB)))
    print("   KILL %s   ORTH(all) %s   ORTH(central) %s"
          % (L.kill_exists(m, basis=IB), L.orth_all(m, B), L.orth_central(m, basis=IB)))
    print("   ORTH(central, NO achievability) %s   MODLOW %s"
          % (L.orth_central_unrestricted(m), L.modlow(m)))
    print("   covectors (j,k,l,m,n) of the class-five row, per slot:")
    for i in range(5):
        cm, cn, co = L.row_covectors(m, i)
        print("      %-6s o %s   m-row %s   n-row %s" % (L.SLOT[i], co, cm, cn))
    w = odd_witnesses(m, B)
    print("   %d single-slot achievable dressings with an ODD class-five row" % len(w))
    for (i, g, im) in w[:4]:
        print("      slot %-6s dressing (j,k,l,m,n,o)=%s -> shift %s" % (L.SLOT[i], g, im))
    print("   W60-HYP (stageN1 at every letter) %s   W60-CONS (stageN3) %s"
          % (L.stageN1_all(m), L.stageN3_all(B)))
    return B, IB


if __name__ == "__main__":
    for (name, m) in FOUR:
        report(name, m)
        print()
