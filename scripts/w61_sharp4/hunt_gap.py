"""W61-SHARP4: the hunt for the gap between the PARITY line and the SHARP line.

The parity line `ORTH` - every achievable stage-four dressing moves the class-five row evenly -
is sufficient for the forcing.  It is not necessary: a dressing with an odd class-five pairing
only kills if it also leaves the two class-four rows alone, which at stage four is a real
condition because a `gamma_3`-dressing moves them.  This script looks for admissible markings
where `ORTH` FAILS and the forcing HOLDS, and reports the achievable odd dressing together
with the class-four row it disturbs.

BRACKET CONVENTION.  [NONE]
This script computes no commutators, so the convention does not arise.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

import random
import sys
import time

import sharp4lib as L                                                  # noqa: I100
import modlib as MD                                                    # noqa: E402
import u6mat as M                                                      # noqa: E402


def rl(rng, density, even=()):
    v = [rng.randrange(8) if rng.random() < density else 0 for _ in range(15)]
    for k in even:
        v[k] = 2 * rng.randrange(4)
    return tuple(v)


def witness(m, B):
    """An achievable dressing with an ODD pairing, and the class-four rows it moves."""
    for i in range(len(m)):
        mat = L.slot_matrix(m, i)
        for g in L.members(B):
            im = L.apply_matrix(mat, g)
            if im[5] % 2:
                return i, g, im
    return None


def hunt(budget, seed, density, even):
    rng = random.Random(seed)
    t0 = time.time()
    n = hits = 0
    out = []
    while time.time() - t0 < budget:
        S, X, U, V = (rl(rng, density, even) for _ in range(4))
        for Y in L.solve_y(S, X, U, V, want=2, budget=1200):
            m = [S, X, Y, U, V]
            if not L.admissible(m):
                continue
            n += 1
            B = L.gamma3_basis(m)
            IB = L.image_basis(m, B)
            if L.kill_exists(m, basis=IB):
                continue
            if L.orth_all(m, B):
                continue
            hits += 1
            out.append((m, B, IB))
    return n, hits, out


if __name__ == "__main__":
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 60.0
    total = totalhits = 0
    for (seed, density, even) in ((6101, 0.35, ()), (61301, 0.3, (L.IA, L.IC)),
                                  (61302, 0.45, ()), (61303, 0.3, (L.IE,))):
        n, hits, out = hunt(budget, seed, density, even)
        total += n
        totalhits += hits
        print("seed %d density %.2f even %s: %d admissible, %d with ORTH failing and the "
              "forcing holding" % (seed, density, even, n, hits))
        for (m, B, IB) in out[:3]:
            print("   letters: %s" % " | ".join(M.show(g) for g in m))
            print("   covectors %s" % ([L.covector(m, i) for i in range(5)],))
            print("   |gamma_3| %d  image %s  central %s"
                  % (MD.card(B, 6), MD.card(IB, 6), L.central_basis(IB)))
            w = witness(m, B)
            if w:
                print("   odd achievable dressing at slot %s: %s -> shift %s"
                      % (L.SLOT[w[0]], w[1], w[2]))
    print("TOTAL %d admissible, %d with the parity line failing and the forcing holding"
          % (total, totalhits))
