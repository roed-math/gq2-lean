"""W63-FOUR, step 3: certify, independently of Lean, everything the Lean file asserts.

`GQ2/Dyadic/SqCore/GradedStageFour.lean` names four markings, two target subgroups of `gamma_3`
and two certificate functionals.  This script checks, on wave 59's honest `6 x 6` matrices
through wave 61's `sharp4lib`:

  1  the relators, so the markings really are the wave-61 gap markings and really are ADMISSIBLE
     (central translation, odd class-five residue);
  2  every one of the 216 weight-three brackets of the six slot values lies in the target - the
     entire arithmetic input to the Lean lattice bound;
  3  the targets are stable under conjugation by every letter, which is what makes the
     generator reduction apply;
  4  the honest achievable lattice `forceLcs H 2` lies inside the target, so the bound is not
     vacuous, together with the index that measures the slack;
  5  the certificate functional kills the stage-four shift of EVERY dressing whose slots lie in
     the target - the one identity the Lean file still carries as a hypothesis;
  6  the certificate does NOT kill the relator's inverse, which is what turns 5 into the
     forcing;
  7  the wave-61 and wave-62 verdicts, re-run: no achievable dressing kills, the parity line
     fails, the sharp line holds.
"""

import fourlib as F

UNIT6 = [tuple(1 if t == s else 0 for t in range(6)) for s in range(6)]

# The Lean targets, as their defining Z/8-linear functionals on (j, k, l, m, n, o).
KONE = [(0, 2, 0, 4, 4, 0), (0, 0, 2, 0, 4, 0)]
KTWO = [(0, 1, 0, 0, 4, 0), (0, 0, 4, 0, 0, 0), (0, 0, 0, 2, 0, 0)]
PSIONE = (0, 0, 1, 0, 2, 4)
PSITWO = (0, 0, 0, 1, 0, 4)

CASES = [("gap-1a  (gapOneMark)", 0, KONE, PSIONE, 5),
         ("gap-1b  (gapOneMark')", 1, KONE, PSIONE, 5),
         ("gap-2a  (gapTwoMark)", 2, KTWO, PSITWO, 1),
         ("gap-2b  (gapTwoMark')", 3, KTWO, PSITWO, 1)]

FAIL = []


def check(name, ok, extra=""):
    print("   %-58s %s %s" % (name, "OK" if ok else "FAIL", extra))
    if not ok:
        FAIL.append(name)


def in_kernel(rows, v):
    return all(F.dot(r, v) == 0 for r in rows)


def kernel_members(rows):
    """Every member of the target subgroup of `gamma_3`, by exhaustion over `(Z/8)^6`."""
    out = []
    for code in range(8 ** 6):
        v, t = [], code
        for _ in range(6):
            v.append(t % 8)
            t //= 8
        v = tuple(v)
        if in_kernel(rows, v):
            out.append(v)
    return out


def report(name, idx, rows, psi, res):
    letters = F.FOUR[idx][1]
    print("== %s" % name)
    print("   letters: %s" % " | ".join(F.M.show(g) for g in letters))
    d = F.marking_data(letters)

    # 1  the relator
    r = d["relator"]
    check("relator is the central translation <o=%d>" % res,
          F.M.show(r) == "<o=%d>" % res and F.L.admissible(letters), "(admissible)")

    # 2  the 216 weight-three brackets
    slots = list(letters) + [F.ONE]
    bad = 0
    for a in slots:
        for b in slots:
            for c in slots:
                w = F.M.commP(F.M.commP(a, b), c)
                if any(w[k] for k in range(9)) or not in_kernel(rows, F.L.vec(w)):
                    bad += 1
    check("all %d weight-three brackets lie in the target" % (len(slots) ** 3), bad == 0,
          "(%d violations)" % bad)

    # 3  conjugation stability of the target
    K = kernel_members(rows)
    bad = 0
    for v in K:
        p = F.L.elt(v)
        for g in slots:
            for gg in (g, F.M.inv(g)):
                if not in_kernel(rows, F.L.vec(F.M.conjP(p, gg))):
                    bad += 1
    check("target stable under conjugation by every slot value", bad == 0,
          "(|target| = %d)" % len(K))

    # 4  the honest lattice sits inside it
    Av = d["Av"]
    check("forceLcs H 2 lies inside the target",
          all(in_kernel(rows, v) for v in Av),
          "(lattice %d, target %d, slack index %d)" % (len(Av), len(K), len(K) // len(Av)))

    # 5  the certificate identity, on the WHOLE target and not just on the lattice
    lam = [tuple(F.dot(psi, d["mats"][i][s]) for s in range(6)) for i in range(5)]
    bad = sum(1 for i in range(5) for v in K if F.dot(lam[i], v))
    check("certificate kills every single-slot shift from the target", bad == 0,
          "(%d of %d slot/target pairs)" % (bad, 5 * len(K)))
    print("      psi = %s" % F.show_char(psi))
    for i in range(5):
        print("         slot %-6s pullback %s" % (F.SLOT[i], F.show_char(lam[i])))

    # …and on genuine five-slot tuples, by an independent sweep over a spanning family
    gens = [(i, v) for i in range(5) for v in F.MD.howell(list(K), 6)]
    bad = 0
    for (i, v) in gens:
        zs = [(0,) * 6] * 5
        zs[i] = v
        if F.dot(psi, F.shift_of(d["mats"], zs)) != 0:
            bad += 1
    check("…and on a spanning family of five-slot dressings", bad == 0)

    # 6  the certificate separates the relator's inverse
    inv = tuple((-x) % 8 for x in F.L.vec(r))
    check("certificate does NOT kill the relator's inverse", F.dot(psi, inv) != 0,
          "(psi = %d)" % F.dot(psi, inv))

    # 7  the wave-61 / wave-62 verdicts
    IB = F.L.image_basis(letters, Av)
    check("no achievable dressing kills (the forcing HOLDS)",
          not F.L.kill_exists(letters, basis=IB))
    check("the parity line StageOrth FAILS", not F.L.orth_all(letters, Av))
    check("the sharp line StageCentral HOLDS", F.L.orth_central(letters, basis=IB))
    print()


if __name__ == "__main__":
    for (nm, idx, rows, psi, res) in CASES:
        report(nm, idx, rows, psi, res)
    print("TOTAL FAILURES: %d" % len(FAIL))
    for f in FAIL:
        print("   %s" % f)
