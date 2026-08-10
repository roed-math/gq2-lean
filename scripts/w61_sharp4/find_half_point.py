"""W61-SHARP4: the search for the MIXED stage-four point.

Target: an admissible marking - relator a CENTRAL translation with an ODD class-five residue,
handle block live - at which

* every letter has an even `(1,2)`-column `a`, an even `(5,6)`-column `e` and an even LAST
  class-two coordinate `i`, so four of each slot covector's five entries vanish and the
  covectors read the dressing's `l` alone;
* every achievable stage-four dressing therefore has an even `l`, by wave 60's own
  `fiveEvenI_of_commutator` / `fiveEvenL_of_commutator` chain one filtration step short of
  where that wave used it, so the parity line HOLDS and the forcing follows;
* and wave 60's stage-four soundness condition FAILS - in its hypothesis (a letter with an odd
  `(3,4)`-column) and, better, in its conclusion (an achievable triple commutator with an odd
  `j`, `l` or `m`).

That combination makes the point a witness that the carried condition is strictly stronger
than the line.
"""

import random
import sys
import time

import sharp4lib as L                                                  # noqa: I100
import modlib as MD                                                    # noqa: E402
import u6mat as M                                                      # noqa: E402


def cons_breaker(m):
    """A triple commutator of the marking's own letters with an odd `j`, `l` or `m`."""
    best = None
    for a in range(5):
        for b in range(5):
            for c in range(5):
                z = M.commP(M.commP(m[a], m[b]), m[c])
                if any(z[k] for k in range(9)):
                    continue
                v = L.vec(z)
                if v[0] % 2 or v[2] % 2 or v[3] % 2:
                    w = sum(1 for x in z if x)
                    if best is None or w < best[2]:
                        best = ((a, b, c), z, w)
    return best


def hunt(budget, seed, density):
    rng = random.Random(seed)
    t0 = time.time()
    n = 0
    out = []
    while time.time() - t0 < budget:
        def rl():
            v = [rng.randrange(8) if rng.random() < density else 0 for _ in range(15)]
            for k in (L.IA, L.IE, L.II):
                v[k] = 2 * rng.randrange(4)
            return tuple(v)
        S, X, U, V = rl(), rl(), rl(), rl()
        if M.commP(U, V) == M.ONE:
            continue
        for Y in L.solve_y(S, X, U, V, want=6, budget=1200):
            m = [S, X, Y, U, V]
            if not L.admissible(m):
                continue
            n += 1
            if Y[L.II] % 2:
                continue
            covs = [L.covector(m, i) for i in range(5)]
            if any(c[0] or c[1] or c[3] or c[4] for c in covs):
                continue                       # the covectors must read the dressing's `l` alone
            if all(c[2] == 0 for c in covs):
                continue                       # ...and at least one of them must really read it
            br = cons_breaker(m)
            hyp = L.stageN1_all(m)
            B = L.gamma3_basis(m)
            if L.stageN3_all(B) and hyp:
                continue                       # wave 60's condition must fail somewhere
            score = sum(1 for g in m for x in g if x) + (0 if br else 30) + (0 if not hyp
                                                                            else 30)
            out.append((score, m, br, hyp, B))
            out.sort(key=lambda t: t[0])
            out = out[:6]
    return n, out


if __name__ == "__main__":
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 60.0
    for (seed, density) in ((61601, 0.3), (61602, 0.45)):
        n, out = hunt(budget, seed, density)
        print("== seed %d density %.2f: %d admissible markings, %d kept ==" % (seed, density,
                                                                               n, len(out)))
        for (score, m, br, hyp, B) in out:
            IB = L.image_basis(m, B)
            print("  letters: %s" % " | ".join(M.show(g) for g in m))
            print("    residue %d  W60-HYP %s  W60-CONS %s  ORTH %s  KILL %s  |gamma_3| %d"
                  % (L.relator(m)[L.IO], hyp, L.stageN3_all(B), L.orth_all(m, B),
                     L.kill_exists(m, basis=IB), MD.card(B, 6)))
            print("    covectors %s" % ([L.covector(m, i) for i in range(5)],))
            print("    lattice basis %s" % (B,))
            if br:
                print("    CONS breaker [[m%d,m%d],m%d] = %s"
                      % (br[0][0], br[0][1], br[0][2], M.show(br[1])))
            print("    columns (a,c,e,f,i) %s"
                  % [(g[L.IA], g[L.IC], g[L.IE], g[L.IF], g[L.II]) for g in m])
            print()
