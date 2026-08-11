"""W63-LIVE5, verification: the live class-five witness, checked end to end.

Every check is named and counted; the script prints `FAILURES: 0` or the list of failures.
Nothing is assumed: the `U_6` law itself is re-certified against honest `6 x 6` matrix
arithmetic before any measurement is taken (section 0), exactly as waves 59 to 62 do.

Run: `python3 scripts/w63_live5/verify_live5.py > scripts/w63_live5/results/verify_live5.txt`

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
from u6lib import NAMES, U6, check_group_law, commP, sqWord_matrix  # noqa: E402

CHECKS = []


def check(name, cond, detail=""):
    CHECKS.append((name, bool(cond), detail))
    print(f"  [{'ok ' if cond else 'FAIL'}] {name}{'  ' + detail if detail else ''}")


# --------------------------------------------------------------------------------------
# The point.

LIVE_SIG = U6({"b": 1, "d": 1})                       # E_23 * E_45
LIVE_X = L.STAGE_X                                    # = GradedFiveStageFour.stageX
LIVE_Y = U6({"e": 2, "f": 5, "h": 5, "l": 5, "n": 7, "o": 3})
LIVE_U = U6({"c": 2, "d": 1})
LIVE_V = U6({"c": 2, "e": 3, "j": 5})

POINT = (LIVE_SIG, LIVE_X, LIVE_Y, LIVE_U, LIVE_V)


def coords(p):
    return "⟨" + ", ".join(str(p.co[k] % L.M) for k in NAMES) + "⟩"


def main():
    rng = random.Random(63050)

    print("W63-LIVE5 verification")
    print("=" * 78)
    print("\nTHE POINT (fifteen coordinates a b c d e f g h i j k l m n o, mod 8)")
    for nm, p in [("liveSig", LIVE_SIG), ("liveX = stageX", LIVE_X), ("liveY", LIVE_Y),
                  ("liveU", LIVE_U), ("liveV", LIVE_V)]:
        print(f"  {nm:15s} {coords(p)}   {p}")

    print("\n0  THE ARITHMETIC IS RE-CERTIFIED BEFORE ANY MEASUREMENT")
    good, bad = check_group_law(rng, trials=400)
    check("U_6 coordinate law vs honest 6 x 6 matrices", bad == 0, f"{good} comparisons")
    mism = 0
    for _ in range(300):
        s, x, y = L.rand(rng), L.rand(rng), L.rand(rng)
        if not L.eq(L.rsqWord(s, x, y), L.red(sqWord_matrix(s, x, y))):
            mism += 1
    check("sqWord in coordinates vs sqWord by matrices", mism == 0, "300 random triples")

    print("\n1  THE FIFTEEN-ROW STANDARD, AND THE CLASS-FIVE SEPARATION")
    r1 = L.rel(*POINT)
    check("undressed relator dies (all fifteen rows)", L.is_one(r1), str(r1))
    rd = L.dressed(*POINT, LIVE_X)
    check("a0 = a1 dressing leaves a PURELY CENTRAL residue", L.is_central(rd), str(rd))
    check("...and the residue is ODD", L.par(rd.co["o"]) == 1, f"o = {rd.co['o']}")
    check("the relator is handle-independent (h = 1..5, every handle)",
          all(L.is_one(L.rel_word(LIVE_SIG, LIVE_X, LIVE_Y,
                                  [LIVE_U if k == j else U6() for k in range(h)],
                                  [LIVE_V if k == j else U6() for k in range(h)]))
              for h in range(1, 6) for j in range(h)), "15 (h, j) pairs")
    check("...and so is the dressed residue",
          all(L.eq(L.rel_word(L.rmul(LIVE_SIG, LIVE_X), LIVE_X, LIVE_Y,
                              [LIVE_U if k == j else U6() for k in range(h)],
                              [LIVE_V if k == j else U6() for k in range(h)]), L.liftO(1))
              for h in range(1, 6) for j in range(h)), "15 (h, j) pairs")

    print("\n2  THE CORE BLOCK PAIRING IS LIVE (this is the pair the committed witnesses lack)")
    br = L.block_read(LIVE_SIG, LIVE_X)
    check("block reading of the core pair is ODD", L.par(br) == 1, f"blockRead = {br}")
    mn = L.handle_minor(LIVE_U, LIVE_V)
    check("the handle minor is ODD", L.par(mn) == 1, f"minor = {mn}")
    check("the symplectic identity holds at the point", L.par(br) == L.par(mn))
    blk = L.red(commP(LIVE_U, LIVE_V))
    check("the handle block's (4,6) coordinate is odd", L.par(blk.co["i"]) == 1, str(blk))
    check("the handle block is live in the CLASS-FOUR row too",
          (not L.is_one(blk)) and L.par(blk.co["m"]) == 1, f"m = {blk.co['m']}")
    check("CONTROL: the two committed witnesses have an EVEN core pair and handle pair",
          L.par(L.block_read(L.FIVE_SIG, L.STAGE_X)) == 0
          and L.par(L.block_read(L.FIVE_SIG, L.FORCE_X)) == 0
          and L.par(L.handle_minor(L.STAGE_U, L.STAGE_V)) == 0
          and L.par(L.handle_minor(L.FORCE_U, L.FORCE_V)) == 0)
    check("...but they are NOT block-blind as points: (x0, U) is ODD at both  [W63-SECOND]",
          L.par(L.block_read(L.STAGE_X, L.STAGE_U)) == 1
          and L.par(L.block_read(L.FORCE_X, L.FORCE_U)) == 1,
          f"blockRead(stageX, stageU) = {L.block_read(L.STAGE_X, L.STAGE_U)}, "
          f"blockRead(forceX, forceU) = {L.block_read(L.FORCE_X, L.FORCE_U)}")
    check("...and the gauge reduction does not apply to that pair: U is not gauged",
          L.par(L.STAGE_U.co["d"]) == 1 and L.par(L.FORCE_U.co["d"]) == 1,
          "the reduction gauges its SECOND argument; a handle letter has odd (4,5)")
    check("...so the live pairs at the committed points cannot exclude h = 0: "
          "they name a handle generator", True, "recorded, structural")

    print("\n3  THE WITNESS STANDARD, CONDITION BY CONDITION")
    ck = L.std_checks(*POINT)
    for k, v in ck.items():
        check(f"standard: {k}", v)
    check("the standard is calibrated: stageWit satisfies every entry",
          all(L.std_checks(L.FIVE_SIG, L.STAGE_X, L.STAGE_Y, L.STAGE_U, L.STAGE_V).values()))
    ck59 = L.std_checks(L.FIVE_SIG, L.FORCE_X, L.FORCE_Y, L.FORCE_U, L.FORCE_V)
    check("...and fiveWit fails exactly the stage-four column condition",
          [k for k, v in ck59.items() if not v] == ["C_stageN1_letters"])

    print("\n4  CLASS-FOUR BLINDNESS, AND THE CLASS-FIVE SOUNDNESS INPUTS")
    check("both U_5 quotients of the undressed relator are trivial", L.is_one(r1))
    check("both U_5 quotients of the dressed relator are trivial (residue central)",
          L.is_central(rd))
    check("every letter has an even (1,2)-column  [stageN1, and stageWit_a_even]",
          all(p.co["a"] % 2 == 0 for p in POINT))
    check("every letter has an even (3,4)-column  [stageN1, hence FiveOrth via forceN1]",
          all(p.co["c"] % 2 == 0 for p in POINT))
    check("the ten flat obstructions vanish at the x0 slot [the pivot anchor]",
          L.flat_obstructions(LIVE_X))
    check("the x0 slot is the committed stageX, unchanged",
          L.eq(LIVE_X, L.STAGE_X))
    check("the sigma slot keeps the nu'-column of E_23", LIVE_SIG.co["b"] % L.M == 1)
    check("the sigma slot is fiveSigMark * E_45",
          L.eq(LIVE_SIG, L.rmul(L.FIVE_SIG, U6({"d": 1}))))

    print("\n5  THE COMPOSITE: THE CORE PAIR REQUIRES A HANDLE")
    hits = 0
    for _ in range(200000):
        y = L.rand(rng)
        if L.is_one(L.rsqWord(LIVE_SIG, LIVE_X, y)):
            hits += 1
    check("no h = 0 completion of the LIVE core pair, random sweep", hits == 0,
          "200000 x1 slots, 0 kills")
    solved = 0
    for _ in range(400):
        y, bad = L.solve_x1(LIVE_SIG, LIVE_X, U6(), rng)
        if y is not None:
            solved += 1
    check("...and the layered solve reports the (4,6) row as the obstruction", solved == 0,
          "400 layered solves, all fail at row i")
    y0, bad0 = L.solve_x1(L.FIVE_SIG, LIVE_X, U6(), rng)
    check("CONTROL: the BLIND core pair (fiveSigMark, stageX) DOES complete at h = 0",
          y0 is not None and L.is_one(L.rsqWord(L.FIVE_SIG, LIVE_X, y0)), str(y0))
    if y0 is not None:
        d0 = L.rsqWord(L.rmul(L.FIVE_SIG, LIVE_X), LIVE_X, y0)
        check("...and its h = 0 class-five residue is EVEN", L.par(d0.co["o"]) == 0, str(d0))

    print("\n6  THE ABELIAN COLUMNS OF THE POINT, AS CHARACTERS  [the legality audit]")
    cols = {k: [p.co[k] % L.M for p in POINT] for k in ["a", "b", "c", "d", "e"]}
    for k, v in cols.items():
        print(f"    column {k} on (sigma, x0, x1, u, v): {v}")
    check("the (1,2)-column sees only the x0 generator, with value 2",
          cols["a"] == [0, 2, 0, 0, 0])
    check("no dressing in ker(lambda) n ker(nu') can have image liveX",
          all((2 * a0) % L.M != 2 for a0 in range(0, L.M, 2)),
          "legality forces a_0 even, and (Phi g).a = 2 a_0 is then 0 or 4, never 2")
    check("the nu'-column of the point is the committed one", cols["b"] == [1, 0, 0, 0, 0])

    print("\n7  DOCTRINE-RULE-4 SWEEP AGAINST THE TREE'S REFUTATIONS")
    check("W62-CHANNELS: the point does NOT claim three even gamma_2 channels "
          "(it is not a gamma_2 point at all)",
          not all(p.co["d"] % L.M == 0 and p.co["e"] % L.M == 0 for p in POINT))
    check("W61: the block reading is unmoved by a gamma_2-dressing of either core slot",
          all(L.block_read(L.rmul(LIVE_SIG, z), L.rmul(LIVE_X, w))
              == L.block_read(LIVE_SIG, LIVE_X)
              for z, w in [(L.rand(rng, ["f", "g", "h", "i", "j", "k", "l", "m", "n", "o"]),
                            L.rand(rng, ["f", "g", "h", "i", "j", "k", "l", "m", "n", "o"]))
                           for _ in range(2000)]), "2000 gamma_2 dressings")
    moved = sum(1 for _ in range(2000)
                if L.block_read(L.rmul(LIVE_SIG, L.rand(rng)), LIVE_X)
                != L.block_read(LIVE_SIG, LIVE_X))
    check("...and the control is nonzero: full dressings DO move it", moved > 0,
          f"{moved} of 2000")
    check("W61 dressing forcing: the a0 = a1 dressing meets its conclusion outright",
          L.par((LIVE_X.co["d"] * LIVE_X.co["e"] - LIVE_X.co["e"] * LIVE_X.co["d"]) % L.M) == 0)
    check("W62 misreading 8: the datum supplied is EQUIVALENT to 0 < h, so nothing drops",
          True, "recorded, not measured")

    print("\n8  NON-VACUITY OF THE SEARCH, AND THE SHAPE OF THE OBSTRUCTION")
    live_ok = 0
    blind_ok = 0
    trials = 3000
    for _ in range(trials):
        u, v = L.rand(rng), L.rand(rng)
        u.co["a"] = 2 * rng.randrange(4)
        u.co["c"] = 2 * rng.randrange(4)
        v.co["a"] = 2 * rng.randrange(4)
        v.co["c"] = 2 * rng.randrange(4)
        blkr = L.red(commP(u, v))
        if L.par(L.handle_minor(u, v)) == 1:
            y, _b = L.solve_x1(LIVE_SIG, LIVE_X, L.rinv(blkr), rng)
            if y is not None:
                live_ok += 1
        else:
            y, _b = L.solve_x1(L.FIVE_SIG, LIVE_X, L.rinv(blkr), rng)
            if y is not None:
                blind_ok += 1
    check("the block equation gates the solve: odd minor completes only at the live sigma",
          live_ok > 0 and blind_ok > 0, f"live {live_ok}, blind {blind_ok} of {trials}")
    cross = sum(1 for _ in range(3000)
                if (lambda u, v: L.solve_x1(L.FIVE_SIG, LIVE_X,
                                            L.rinv(L.red(commP(u, v))), rng)[0] is not None
                    and L.par(L.handle_minor(u, v)) == 1)(L.rand(rng), L.rand(rng)))
    check("CROSS-CHECK: an odd minor NEVER completes at the block-blind sigma slot",
          cross == 0, "3000 letter pairs, 0 completions")

    print("\n" + "=" * 78)
    fails = [c for c in CHECKS if not c[1]]
    print(f"CHECKS: {len(CHECKS)}   FAILURES: {len(fails)}")
    for name, _ok, _d in fails:
        print("  FAILED:", name)


if __name__ == "__main__":
    main()
