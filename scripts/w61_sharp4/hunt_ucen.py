"""W61-SHARP4: the hunt for a marking where the PARITY LINE fails and the forcing holds for
EVERY dressing tuple whatsoever.

The mechanism: a `gamma_3`-dressing moves the two class-four rows as well as the class-five
one, and a kill has to leave them alone.  If the class-four row is an EVEN multiple of the
coordinate the class-five covector reads - say `shift.m = 2 * z.j` - then `shift.m = 0` forces
`z.j` into `{0, 4}` over `Z/8`, hence even, hence the class-five pairing even.  Nothing mod 2
sees this, which is why the parity line is not the sharp line.

A necessary condition is that all five class-five covector entries vanish, i.e. every letter
has even `(1,2)`- and `(5,6)`-columns, since the `gamma_4`-shaped tuples always act centrally.

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


def hunt(budget, seed, density):
    rng = random.Random(seed)
    t0 = time.time()
    n = hits = 0
    out = []
    while time.time() - t0 < budget:
        def rl():
            v = [rng.randrange(8) if rng.random() < density else 0 for _ in range(15)]
            v[L.IA] = 2 * rng.randrange(4)
            v[L.IE] = 2 * rng.randrange(4)
            return tuple(v)
        S, X, U, V = rl(), rl(), rl(), rl()
        for Y in L.solve_y(S, X, U, V, want=2, budget=1200):
            m = [S, X, Y, U, V]
            if not L.admissible(m):
                continue
            n += 1
            if not L.orth_central_unrestricted(m):
                continue
            B = L.gamma3_basis(m)
            if L.orth_all(m, B):
                continue
            hits += 1
            out.append((m, B))
    return n, hits, out


if __name__ == "__main__":
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 60.0
    tot = tothits = 0
    for (seed, density) in ((61401, 0.3), (61402, 0.45), (61403, 0.2), (61404, 0.6)):
        n, hits, out = hunt(budget, seed, density)
        tot += n
        tothits += hits
        print("seed %d density %.2f: %d admissible, %d with ORTH failing and the forcing "
              "holding UNCONDITIONALLY" % (seed, density, n, hits))
        for (m, B) in out[:3]:
            print("   letters: %s" % " | ".join(M.show(g) for g in m))
            print("   covectors %s   |gamma_3| %d" % ([L.covector(m, i) for i in range(5)],
                                                      MD.card(B, 6)))
            for i in range(5):
                print("     slot %-5s matrix %s" % (L.SLOT[i], L.slot_matrix(m, i)))
    print("TOTAL %d admissible, %d hits" % (tot, tothits))
