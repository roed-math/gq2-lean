"""W63-LIVE5, the search that produced the point.

The sigma slot is pinned to `liveBlkSig = E_23 * E_45` (the committed `fiveSigMark` times the
single `(4,5)` elementary matrix, which by `SqU6.selPar_blockRead_of_gauge` is the minimal move
that makes the block channel live) and the `x0` slot to the committed
`GradedFiveStageFour.stageX`, so the gauge and the pivot anchor are inherited verbatim.

The search is over the handle letters and over the branches of the layered solve for the `x1`
slot, ordered by total coordinate weight.  The letter family is chosen from the mod-2 shape of
the commutator, computed symbolically in `derive_live5.py`:

    [u, v]_46 = u_45 v_56 + u_56 v_45                                     (mod 2)
    [u, v]_15 = u_45 v_14 + u_13 v_35 + u_35 v_13 + u_14 v_45             (mod 2)

once both letters have even `(1,2)`- and `(3,4)`-columns.  So a handle pair that is live in the
block row `(4,6)` and in the class-four row `(1,5)` at once needs `d`, `e` and `j` entries, and
that is the family enumerated here.

Run: `python3 scripts/w63_live5/minimise_live5.py`

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import livelib as L  # noqa: E402
from u6lib import U6, commP  # noqa: E402

SIG = U6({"b": 1, "d": 1})
SEED = 4242


def weight(p):
    return sum(1 for k in L.NAMES if p.co[k] % L.M != 0)


def main():
    rng = random.Random(SEED)
    X = L.STAGE_X
    Us = [U6({"c": c, "d": d, "e": e})
          for c in (2, 6) for d in (1, 3, 5, 7) for e in range(8)]
    Vs = [U6({"c": c, "d": d, "e": e, "j": j})
          for c in (0, 2, 4, 6) for d in range(8) for e in (1, 3, 5, 7) for j in range(8)]

    cand = []
    for U in Us:
        for V in Vs:
            if (U.co["d"] * V.co["e"] - U.co["e"] * V.co["d"]) % 2 != 1:
                continue
            blk = L.red(commP(U, V))
            if blk.co["m"] % 2 != 1:
                continue
            cand.append((weight(U) + weight(V), U, V, blk))
    cand.sort(key=lambda t: t[0])
    print(f"letters enumerated       : {len(Us)} x {len(Vs)} = {len(Us) * len(Vs)}")
    print(f"pairs with an odd (4,6) minor AND an odd (1,5) block row: {len(cand)}")
    print(f"lowest letter weights    : {sorted(set(c[0] for c in cand))[:5]}")
    print()

    best = None
    for base, U, V, blk in cand[:400]:
        if best is not None and base >= best[0]:
            break
        for _ in range(250):
            Y, _bad = L.solve_x1(SIG, X, L.rinv(blk), rng)
            if Y is None:
                break
            if not all(L.std_checks(SIG, X, Y, U, V).values()):
                continue
            w = base + weight(Y)
            if best is None or w < best[0]:
                best = (w, U, V, Y)
                print(f"  weight {w:3d}   U = {U}   V = {V}   Y = {Y}"
                      f"   residue = {L.dressed(SIG, X, Y, U, V, X)}")
    print()
    if best is None:
        print("NO WITNESS FOUND")
        return
    w, U, V, Y = best
    print(f"MINIMUM total weight of (U, V, x1) over the family: {w}")
    print(f"  total weight of the whole point (sigma, x0, x1, U, V): "
          f"{w + weight(SIG) + weight(X)}")
    print()
    print("THE POINT, in the campaign's fifteen coordinates a b c d e f g h i j k l m n o:")
    for nm, p in [("liveBlkSig", SIG), ("stageX", X), ("liveBlkY", Y),
                  ("liveBlkU", U), ("liveBlkV", V)]:
        print(f"  {nm:11s} = ⟨" + ", ".join(str(p.co[k] % L.M) for k in L.NAMES) + "⟩")


if __name__ == "__main__":
    main()
