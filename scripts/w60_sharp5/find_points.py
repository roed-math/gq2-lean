"""W60-SHARP5: find the class-five markings that separate the sharp line from wave 59's.

Two targets, the class-five transpositions of `GradedFrameNecessity`'s sections 5 and 6.

  A  ORTHOGONAL: all six covector entries `(X.a, X.e, U.a, U.e, V.a, V.e)` even, so the
     increment pairing vanishes for ARBITRARY class-four moves, while the achievable
     `gamma_4`-lattice is ODD, so `GradedFiveForce.forceLcs_three_le_forceN4`'s conclusion
     fails and so does its hypothesis.
  B  HALF: `U.a` odd, so one covector `(0, 1)` really reads the moves and the orthogonal
     route is unavailable; every letter has an even FIFTH abelian column, which forces the
     second class-four coordinate even; and the first is odd, so wave 59's conclusion fails.

Both must be admissible: the relator CENTRAL with an ODD class-five residue, the class-five
form of wave 59's `hres` + `hva`.  The x1-slot is produced by the layered solve; the search
minimises the letters' weight so that the Lean file carries readable constants.
"""

import random
import sys
import time

import sharp5lib as L
import u6mat as M

EVEN = [0, 2, 4, 6]
ODD = [1, 3, 5, 7]


def weight(lets):
    return sum(1 for g in lets for c in g if c) + sum(min(c, 8 - c) for g in lets for c in g)


def constraints(kind, rng):
    if kind == "A":
        return ({L.IA: rng.choice(ODD)},
                {L.IA: rng.choice(EVEN), L.IE: rng.choice(EVEN)},
                {L.IA: rng.choice(EVEN), L.IE: rng.choice(EVEN)},
                {L.IA: rng.choice(EVEN), L.IE: rng.choice(EVEN)})
    return ({L.IE: rng.choice(EVEN)},
            {L.IA: rng.choice(EVEN), L.IE: rng.choice(EVEN)},
            {L.IA: rng.choice(ODD), L.IE: rng.choice(EVEN)},
            {L.IA: rng.choice(EVEN), L.IE: rng.choice(EVEN)})


def wanted(kind, X, U, V, lets, lam4):
    if not L.five_orth(X, U, V, lam4):
        return False
    if L.lam4_even(lam4):                       # wave 59's CONSEQUENCE must fail
        return False
    if kind == "A":
        return L.covectors(X, U, V) == ((0, 0), (0, 0), (0, 0))
    return (L.covectors(X, U, V) == ((0, 0), (0, 0), (0, 1))
            and L.letters_even(lets, L.IE)
            and sorted({(a % 2, b % 2) for (a, b) in lam4}) == [(0, 0), (1, 0)])


def search(kind, seed, seconds, density):
    rng = random.Random(seed)
    t0 = time.time()
    best = []
    tried = 0
    while time.time() - t0 < seconds:
        tried += 1
        fS, fX, fU, fV = constraints(kind, rng)

        def rl(fix):
            v = [0] * 15
            for k in range(15):
                if rng.random() < density:
                    v[k] = rng.randrange(8)
            for k, x in fix.items():
                v[k] = x
            return tuple(v)

        S, X, U, V = rl(fS), rl(fX), rl(fU), rl(fV)
        if kind == "B" and any(g[L.IE] % 2 for g in (S, X, U, V)):
            continue
        _, _, _, lam0 = L.lattices([S, X, L.ONE, U, V])
        if L.lam4_even(lam0):
            continue
        for Y in L.solve_Y(S, X, U, V, want=4, odd_only=True, budget=3000):
            lets = [S, X, Y, U, V]
            _, _, _, lam4 = L.lattices(lets)
            if wanted(kind, X, U, V, lets, lam4):
                best.append((weight(lets), lets))
        best.sort(key=lambda t: t[0])
        best = best[:8]
    return tried, best


def report(tag, lets):
    S, X, Y, U, V = lets
    _, _, _, lam4 = L.lattices(lets)
    print("%s S=%s X=%s Y=%s U=%s V=%s" % (tag, M.show(S), M.show(X), M.show(Y),
                                           M.show(U), M.show(V)))
    print("   relator %s  covectors(X,V,U)=%s  Lam4mod2=%s  orth=%s  lam4_even=%s"
          % (M.show(L.relator(S, X, Y, U, V)), L.covectors(X, U, V),
             sorted({(a % 2, b % 2) for (a, b) in lam4}),
             L.five_orth(X, U, V, lam4), L.lam4_even(lam4)))
    print("   even-a %s  even-b %s  even-c %s  even-d %s  even-e %s"
          % tuple(L.letters_even(lets, i) for i in (L.IA, L.IB, L.IC, L.ID, L.IE)))


if __name__ == "__main__":
    kind = sys.argv[1] if len(sys.argv) > 1 else "A"
    secs = float(sys.argv[2]) if len(sys.argv) > 2 else 60.0
    dens = float(sys.argv[3]) if len(sys.argv) > 3 else 0.3
    tried, best = search(kind, 60000 + ord(kind) + int(dens * 100), secs, dens)
    print("kind %s density %.2f: %d candidates tried, %d hits" % (kind, dens, tried, len(best)))
    for w, lets in best:
        report("  w=%-3d" % w, lets)
