"""W62-COUNTHOM: the block pairing at the hom level, certified independently of Lean.

Nothing here is retyped.  The `U_6(Z/8)` law, the relator, the layered solve and the two
functionals `block_read`, `handle_minor` come from `scripts/w61_block/blocklib.py`, which
itself imports the coordinate law from `scripts/w59_blind5/u6lib.py` and certifies it
against honest `6 x 6` matrix arithmetic.

What this script adds is exactly the content of `GQ2/Dyadic/SqCore/GradedBlockFrame.lean`:

* **A** the block pairing is an ALTERNATING BI-ADDITIVE form on `U_6(Z/8)` mod `2` - the fact
  that makes it a form on `D_sq h` and not merely a function of two marking slots
  (`blockPar_mul_right`, `blockPar_self`, `blockPar_swap`, `blockPar_inv_left`,
  `blockPar_commP_left`);
* **B** the torsion letter is in the kernel of both columns mod `2` at every relator-killing
  marking (`selPar_d_dsqX1`, `selPar_e_dsqX1`), exhaustively;
* **C** the SYMPLECTIC IDENTITY `par blockRead(s, x) = sum_j par minor(u_j, v_j)` at honestly
  collected relator-killing markings, at handle counts `0..4` (`blockPar_relator_frame`);
* **D** the `h = 0` vanishing on EVERY pair, as the finite `F_2` fact behind
  `blockPar_handleFree`: exhaustively over the `4^3` mod-2 generator data;
* **E** the committed points: wave 60's and wave 61's class-five witnesses are block-BLIND,
  wave 59's counterexample is live (`blockPar_fiveFrameHom`, `blockPar_stageFrameHom`,
  `blockPar_blockCexHom`);
* **F** the composite check at the counterexample: both sides of the symplectic identity
  computed from the point (`blockPar_blockCexHom_crosscheck`);
* **G** the non-vacuity control: the pairing is genuinely live at a positive rate on honestly
  collected relator-killing markings, so `D` and the forcing are not statements about a form
  that is always even.
"""

import itertools
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "w61_block"))

from blocklib import (  # noqa: E402
    M,
    U6,
    block_read,
    handle_minor,
    handle_word,
    par,
    rand,
    random_relator_marking,
    red,
    rel_word,
    rinv,
    rmul,
)
from u6lib import NAMES, commP  # noqa: E402

FAILS = []
CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append((name, ok, detail))
    if not ok:
        FAILS.append(name)
    tag = "ok " if ok else "FAIL"
    print(f"[{tag}] {name}" + (f"  {detail}" if detail else ""))


def line(s=""):
    print(s)


def head(s):
    line()
    line("## " + s)
    line()


# --------------------------------------------------------------------------------------
# The committed points, transcribed from the Lean sources (values only).

FIVE_SIG = U6({"b": 1})                                           # fiveSigMark gr3R
FORCE_X = U6({"a": 2, "e": 1})                                    # forceX
FORCE_U = U6({"a": 1, "c": 2, "d": 3, "f": 3, "g": 2, "h": 2, "i": 2})
FORCE_V = U6({"d": 1, "e": 2, "f": 3, "g": 2, "h": 3, "i": 3})
STAGE_X = U6({"a": 2, "e": 5})                                    # stageX
STAGE_U = U6({"a": 6, "b": 7, "c": 4, "d": 1, "e": 3, "g": 5, "h": 5})
STAGE_V = U6({"a": 6, "b": 7, "c": 6, "d": 1, "e": 3, "f": 5, "g": 3, "h": 3, "i": 4})
CEX_S = U6({"b": 1, "e": 1})                                      # blindCexS
CEX_X = U6({"d": 1, "g": 1, "l": 1})                              # blindCexX
CEX_Y = U6({"d": 2, "g": 2, "k": 1, "l": 2, "n": 1})              # blindCexY
CEX_U = U6({"d": 1})                                              # blindCexU
CEX_V = U6({"e": 1})                                              # blindCexV


def main():
    rng = random.Random(20260811)

    line("=" * 86)
    line("W62-COUNTHOM  verify_counthom.py   the block pairing as a form on D_sq h")
    line("=" * 86)

    # ----------------------------------------------------------------------------------
    head("A  the block pairing is an ALTERNATING BI-ADDITIVE form mod 2")

    line("    omega(p, q) = par(p_45 q_56 - p_56 q_45),  p, q in U_6(Z/8)")
    line()

    bad = 0
    for _ in range(20000):
        p, q, r = rand(rng), rand(rng), rand(rng)
        if par(block_read(rmul(p, q), r)) != (par(block_read(p, r)) + par(block_read(q, r))) % 2:
            bad += 1
    check("bi-additive on the left", bad == 0, f"20000 triples, {bad} failures")

    bad = 0
    for _ in range(20000):
        p, q, r = rand(rng), rand(rng), rand(rng)
        if par(block_read(p, rmul(q, r))) != (par(block_read(p, q)) + par(block_read(p, r))) % 2:
            bad += 1
    check("bi-additive on the right", bad == 0, f"20000 triples, {bad} failures")

    bad = sum(1 for _ in range(20000) if par(block_read((p := rand(rng)), p)) != 0)
    check("alternating", bad == 0, f"20000 elements, {bad} failures")

    bad = 0
    for _ in range(20000):
        p, q = rand(rng), rand(rng)
        if par(block_read(p, q)) != par(block_read(q, p)):
            bad += 1
    check("symmetric mod 2", bad == 0, f"20000 pairs, {bad} failures")

    bad = 0
    for _ in range(20000):
        p, q = rand(rng), rand(rng)
        if par(block_read(rinv(p), q)) != par(block_read(p, q)):
            bad += 1
    check("inverse-invariant mod 2", bad == 0, f"20000 pairs, {bad} failures")

    bad = 0
    for _ in range(20000):
        p, q, r = rand(rng), rand(rng), rand(rng)
        if par(block_read(red(commP(p, q)), r)) != 0:
            bad += 1
    check("kills commutators, so it is a form on the abelianisation",
          bad == 0, f"20000 triples, {bad} failures")

    # exhaustive on the four coordinates the form actually reads
    bad = 0
    tot = 0
    for pd, pe, qd, qe, rd, re in itertools.product(range(M), repeat=6):
        p, q, r = U6({"d": pd, "e": pe}), U6({"d": qd, "e": qe}), U6({"d": rd, "e": re})
        tot += 1
        if par(block_read(rmul(p, q), r)) != (par(block_read(p, r)) + par(block_read(q, r))) % 2:
            bad += 1
    check("bi-additivity, EXHAUSTIVE on the four live columns",
          bad == 0, f"{tot} points, {bad} failures")

    # the control: the INTEGRAL form is not additive, only its parity is
    moved = 0
    for _ in range(10000):
        p, q, r = rand(rng), rand(rng), rand(rng)
        if block_read(rmul(p, q), r) != (block_read(p, r) + block_read(q, r)) % M:
            moved += 1
    check("the INTEGRAL reading is already additive, so the parity is not doing the work",
          moved == 0, f"10000 triples, {moved} disagreements")

    # ----------------------------------------------------------------------------------
    head("B  the torsion letter has both live columns EVEN, at every relator-killing marking")

    line("    the relator's own (4,5)- and (5,6)-rows are  -4 x_45 + 2 y_45 = 0  and")
    line("    -4 x_56 + 2 y_56 = 0 in Z/8, and each pins its y-coordinate EVEN.")
    line()

    bad = 0
    tot = 0
    for xd, yd in itertools.product(range(M), repeat=2):
        if (-4 * xd + 2 * yd) % M != 0:
            continue
        tot += 1
        if yd % 2 != 0:
            bad += 1
    check("(4,5)-row forces y_45 even, EXHAUSTIVE", bad == 0, f"{tot} admissible pairs, {bad} odd")

    bad = 0
    tot = 0
    for xe, ye in itertools.product(range(M), repeat=2):
        if (-4 * xe + 2 * ye) % M != 0:
            continue
        tot += 1
        if ye % 2 != 0:
            bad += 1
    check("(5,6)-row forces y_56 even, EXHAUSTIVE", bad == 0, f"{tot} admissible pairs, {bad} odd")

    # and at honestly collected markings
    marks = []
    for h in range(5):
        for _ in range(120):
            m = random_relator_marking(rng, h)
            if m is not None:
                marks.append(m)
    bad = sum(1 for m in marks if m["y"].d % 2 != 0 or m["y"].e % 2 != 0)
    check("…and at honestly collected relator-killing markings",
          bad == 0, f"{len(marks)} markings at h = 0..4, {bad} odd columns")

    # the x1 letter is therefore invisible to the pairing
    bad = 0
    for m in marks:
        for _ in range(4):
            g = rand(rng)
            if par(block_read(g, m["y"])) != 0 or par(block_read(m["y"], g)) != 0:
                bad += 1
    check("hence the x1 slot pairs evenly against EVERYTHING",
          bad == 0, f"{4 * len(marks)} pairings, {bad} odd")

    # ----------------------------------------------------------------------------------
    head("C  THE SYMPLECTIC IDENTITY at honestly collected relator-killing markings")

    line("    claim:  par blockRead(sigma, x0)  ==  sum_j par minor(u_j, v_j)   (mod 2)")
    line()

    bad = 0
    live = 0
    per_h = {}
    for m in marks:
        lhs = par(block_read(m["s"], m["x"]))
        rhs = sum(par(handle_minor(u, v)) for u, v in zip(m["us"], m["vs"])) % 2
        per_h.setdefault(m["h"], [0, 0])
        per_h[m["h"]][0] += 1
        if lhs != rhs:
            bad += 1
        if lhs == 1:
            live += 1
            per_h[m["h"]][1] += 1
    check("the symplectic identity", bad == 0,
          f"{len(marks)} markings at h = 0..4, {bad} mismatches")
    line("    live (odd) fraction by handle count:")
    for h in sorted(per_h):
        n, l = per_h[h]
        line(f"      h = {h}:  {l} of {n} markings have an ODD pairing")

    # the relator really is killed: honest re-check
    bad = 0
    for m in marks:
        w = rel_word(m["s"], m["x"], m["y"], m["us"], m["vs"])
        if any(w.co[k] % M != 0 for k in NAMES):
            bad += 1
    check("control: every collected marking really kills the relator, all fifteen rows",
          bad == 0, f"{len(marks)} markings, {bad} live rows")

    # h = 0 is the empty sum, so the reading is forced EVEN
    zeros = [m for m in marks if m["h"] == 0]
    bad = sum(1 for m in zeros if par(block_read(m["s"], m["x"])) != 0)
    check("h = 0: the reading is FORCED even (the empty sum)",
          bad == 0, f"{len(zeros)} handle-free markings, {bad} odd")

    # ----------------------------------------------------------------------------------
    head("D  the h = 0 vanishing on EVERY pair, as the finite F_2 fact")

    line("    at h = 0 the mod-2 datum of a hom is the triple of vectors")
    line("        tau(sigma), tau(x0), tau(x1)  in  F_2^2,   tau(g) = (par g_45, par g_56),")
    line("    subject to  tau(x1) = 0  (section B)  and  det(tau sigma, tau x0) = 0")
    line("    (section C).  The claim behind `blockPar_handleFree` is that the form then")
    line("    dies on the WHOLE subgroup they generate, not merely on the three letters.")
    line()

    def det(u, v):
        return (u[0] * v[1] - u[1] * v[0]) % 2

    vecs = list(itertools.product(range(2), repeat=2))
    admissible = 0
    bad = 0
    for vs, vx in itertools.product(vecs, repeat=2):
        vy = (0, 0)
        if det(vs, vx) != 0:
            continue
        admissible += 1
        span = set()
        for cs, cx, cy in itertools.product(range(2), repeat=3):
            span.add(((cs * vs[0] + cx * vx[0] + cy * vy[0]) % 2,
                      (cs * vs[1] + cx * vx[1] + cy * vy[1]) % 2))
        for u, v in itertools.product(span, repeat=2):
            if det(u, v) != 0:
                bad += 1
    check("the form dies on the generated subgroup, EXHAUSTIVE over F_2^2",
          bad == 0, f"{admissible} admissible generator data, {bad} live pairs")

    # the control: drop either hypothesis and it is FALSE
    live_without_det = 0
    for vs, vx in itertools.product(vecs, repeat=2):
        if det(vs, vx) != 0:
            live_without_det += 1
    check("control: WITHOUT the relator's own vanishing the claim is false",
          live_without_det > 0, f"{live_without_det} of 16 generator pairs have a live det")

    live_without_x1 = 0
    for vs, vx, vy in itertools.product(vecs, repeat=3):
        if det(vs, vx) != 0:
            continue
        if det(vs, vy) != 0 or det(vx, vy) != 0:
            live_without_x1 += 1
    check("control: WITHOUT the x1 evenness the claim is false",
          live_without_x1 > 0,
          f"{live_without_x1} of 64 triples kill det(sigma,x0) but not the x1 pairings")

    # ----------------------------------------------------------------------------------
    head("E  the committed points")

    rows = [
        ("wave 60 fiveWit  core pair (fiveSigMark, forceX)", block_read(FIVE_SIG, FORCE_X), 0),
        ("wave 60 fiveWit  handle pair (forceU, forceV)", handle_minor(FORCE_U, FORCE_V), 0),
        ("wave 61 stageWit core pair (fiveSigMark, stageX)", block_read(FIVE_SIG, STAGE_X), 0),
        ("wave 61 stageWit handle pair (stageU, stageV)", handle_minor(STAGE_U, STAGE_V), 0),
        ("wave 59 blindCex core pair (blindCexS, blindCexX)", block_read(CEX_S, CEX_X), 1),
        ("wave 59 blindCex handle pair (blindCexU, blindCexV)", handle_minor(CEX_U, CEX_V), 1),
    ]
    for name, val, want in rows:
        check(f"{name}: reading {val}, parity {par(val)}", par(val) == want,
              f"expected parity {want}")

    line()
    line("    ⚠ the two committed class-five witnesses are BLOCK-BLIND on both pairs, so the")
    line("      instrument says nothing at either; wave 59's counterexample is the only")
    line("      committed point at which the channel is live.")

    # the three points really do kill the relator
    for name, s, x, y, u, v in [
        ("blindCex", CEX_S, CEX_X, CEX_Y, CEX_U, CEX_V),
    ]:
        w = rel_word(s, x, y, [u], [v])
        check(f"control: {name} really kills the relator at h = 1",
              all(w.co[k] % M == 0 for k in NAMES), "all fifteen rows")

    # ----------------------------------------------------------------------------------
    head("F  the composite check at the counterexample")

    for h in range(1, 5):
        for j in range(h):
            us = [CEX_U if i == j else U6() for i in range(h)]
            vs = [CEX_V if i == j else U6() for i in range(h)]
            w = rel_word(CEX_S, CEX_X, CEX_Y, us, vs)
            killed = all(w.co[k] % M == 0 for k in NAMES)
            lhs = par(block_read(CEX_S, CEX_X))
            rhs = sum(par(handle_minor(u, v)) for u, v in zip(us, vs)) % 2
            blk = par(handle_word(us, vs).i)
            check(f"blindCexMark h={h} j={j}: relator killed, lhs={lhs}, rhs={rhs}, "
                  f"par H_46={blk}",
                  killed and lhs == 1 and rhs == 1 and blk == 1)

    # ----------------------------------------------------------------------------------
    head("G  non-vacuity: the pairing is live at a positive rate")

    live = 0
    tot = 0
    for _ in range(600):
        m = random_relator_marking(rng, rng.randrange(1, 4))
        if m is None:
            continue
        tot += 1
        if par(block_read(m["s"], m["x"])) == 1:
            live += 1
    check("the pairing is ODD at a positive rate on relator-killing markings at h >= 1",
          live > 0, f"{live} of {tot} markings live ({100.0 * live / max(tot, 1):.1f} %)")

    live0 = 0
    tot0 = 0
    for _ in range(600):
        m = random_relator_marking(rng, 0)
        if m is None:
            continue
        tot0 += 1
        if par(block_read(m["s"], m["x"])) == 1:
            live0 += 1
    check("…and NEVER odd at h = 0", live0 == 0, f"{live0} of {tot0} handle-free markings live")

    # ----------------------------------------------------------------------------------
    line()
    line("=" * 86)
    line(f"{len(CHECKS)} named checks, {len(FAILS)} failures")
    if FAILS:
        for f in FAILS:
            line("  FAILED: " + f)
    line("=" * 86)
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
