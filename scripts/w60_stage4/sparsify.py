"""W60-STAGE4 step 1d: make the clean witness as sparse as the wave-59 one.

Greedy coordinate descent on the four free letters, preserving every property the Lean witness
needs:

  (P1) every letter has an even (1,2)-column and an even (3,4)-column;
  (P2) the undressed frame kills the relator at every handle count;
  (P3) the `a0 = a1`-dressed frame is central with an ODD class-five residue;
  (P4) every achievable `gamma_3`-dressing has `j`, `l` and `m` even;
  (P5) the handle block is live, with an odd class-four row (what a dead block cannot supply).

`x1` is re-solved by the two-sided cascade after every move, so the move set is really over
`(x0, U, V)` with `x1` derived.

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""
import sys
import os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))

import u6mat as M                                             # noqa: E402
import gam3lib as G                                           # noqa: E402
import pointlib as P                                          # noqa: E402
from search_clean import parity_span, sound, weight           # noqa: E402

SIG = M.sigFiveMark


def evaluate(X, U, V, ylimit=24):
    """The sparsest valid `x1` at (X, U, V), or None."""
    if any(z[0] % 2 or z[2] % 2 for z in (X, U, V)):
        return None
    sols = P.solve_y_central(SIG, X, U, V, limit=ylimit)
    if not sols:
        return None
    if not sound(parity_span(G.gamma3_module([SIG, X, sols[0], U, V]))):
        return None
    blk = M.commP(U, V)
    if blk == M.ONE or blk[12] % 2 == 0:
        return None
    return min(sols, key=lambda Y: (weight(Y), sum(Y)))


def total(X, U, V, Y):
    return (weight(X) + weight(U) + weight(V) + weight(Y),
            sum(X) + sum(U) + sum(V) + sum(Y))


def descend(X, U, V):
    Y = evaluate(X, U, V, 256)
    assert Y is not None, "seed is not valid"
    cur = (X, U, V, Y)
    improved = True
    while improved:
        improved = False
        best = total(*cur)
        for slot in range(3):
            for k in range(9):                       # only the letters' class-<= 2 columns
                for val in range(8):
                    cand = list(cur[:3])
                    if cand[slot][k] == val:
                        continue
                    cand[slot] = P.setc(cand[slot], k, val)
                    Yn = evaluate(*cand)
                    if Yn is None:
                        continue
                    t = total(cand[0], cand[1], cand[2], Yn)
                    if t < best:
                        best = t
                        cur = (cand[0], cand[1], cand[2], Yn)
                        improved = True
    return cur


SEEDS = [
    (M.named(a=2, e=5), M.named(a=6, b=7, c=4, d=1, e=3, g=5, h=5),
     M.named(a=6, b=7, c=6, d=1, e=3, f=5, g=3, h=3, i=4)),
]
if os.path.exists(os.path.join(HERE, "results", "seeds.txt")):
    for line in open(os.path.join(HERE, "results", "seeds.txt")):
        parts = line.strip().split("|")
        if len(parts) == 3:
            SEEDS.append(tuple(eval(p) for p in parts))

best = None
for seed in SEEDS:
    X, U, V, Y = descend(*seed)
    t = total(X, U, V, Y)
    print("   from seed: total weight %d, digit sum %d" % t)
    print("      x0 = %s   U = %s   V = %s" % (M.show(X), M.show(U), M.show(V)))
    print("      x1 = %s   residue %d" % (M.show(Y), P.residue(SIG, X, Y, U, V)[14]))
    if best is None or t < best[0]:
        best = (t, X, U, V, Y)

t, X, U, V, Y = best
print()
print("== the sparsest clean witness found ==")
print("   x0 = %s" % M.show(X))
print("   x1 = %s" % M.show(Y))
print("   U  = %s" % M.show(U))
print("   V  = %s" % M.show(V))
print("   residue = %d" % P.residue(SIG, X, Y, U, V)[14])
print("   handle block [U, V] = %s  (class-four row %d)"
      % (M.show(M.commP(U, V)), M.commP(U, V)[12]))
print("   as raw tuples:")
for nm, z in (("x0", X), ("x1", Y), ("U", U), ("V", V)):
    print("      %s = %s" % (nm, list(z)))
