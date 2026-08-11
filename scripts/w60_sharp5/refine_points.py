"""W60-SHARP5: refine the two separating markings to the constants the Lean file carries.

Tighter than `find_points.py`: the covector entries that must be even are required to be
ZERO, so the increment pairing vanishes on the nose rather than merely evenly; the letters'
weight is minimised; and an explicit FOUR-FOLD commutator of the letters with an odd
class-four coordinate is demanded, because that is the achievability witness the Lean proof
has to exhibit (a membership proof, not a census).

BRACKET CONVENTION.  [PAPER-RAW]
This script builds RAW nested bracket sets, and its Lean target is written with commP,
so the paper convention is the right one to compute.  Raw bracket sets are the only
computations in this tree that can be wrong about the convention: check this line
before repointing the script at a [.,.]-written statement.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

import random
import sys
import time

import sharp5lib as L
import u6mat as M

NAMES = ("S", "X", "Y", "U", "V")


def quad_witness(lets):
    """A four-fold commutator of the letters lying outside `forceN4`, with its recipe."""
    out = []
    for a in range(5):
        for b in range(5):
            for c in range(5):
                for d in range(5):
                    z = M.commP(M.commP(M.commP(lets[a], lets[b]), lets[c]), lets[d])
                    if z[L.IM] % 2 or z[L.IN] % 2:
                        out.append((NAMES[a], NAMES[b], NAMES[c], NAMES[d], z))
    return out


def weight(lets):
    return sum(1 for g in lets for c in g if c) + sum(min(c, 8 - c) for g in lets for c in g)


def ok(kind, lets):
    S, X, Y, U, V = lets
    _, _, _, lam4 = L.lattices(lets)
    if L.lam4_even(lam4) or not L.five_orth(X, U, V, lam4):
        return None
    if not L.admissible(S, X, Y, U, V):
        return None
    if M.commP(U, V) == L.ONE:                  # the handle block must be LIVE
        return None
    if not any(X[i] for i in (L.IA, L.IB, L.IC, L.ID, L.IE)):
        return None                             # …and the x0-slot a real letter
    if kind == "A":
        if any(g[i] for g in (X, U, V) for i in (L.IA, L.IE)):
            return None
    else:
        if any(g[i] % 2 for g in (X, V) for i in (L.IA, L.IE)):
            return None
        if U[L.IE] % 2 or U[L.IA] % 2 == 0:
            return None
        if not L.letters_even(lets, L.IE):
            return None
        if sorted({(a % 2, b % 2) for (a, b) in lam4}) != [(0, 0), (1, 0)]:
            return None
    if not quad_witness(lets):
        return None
    return lam4


def search(kind, seed, seconds, density):
    rng = random.Random(seed)
    t0 = time.time()
    best = []
    tried = 0
    while time.time() - t0 < seconds:
        tried += 1

        def rl(zero, fix):
            v = [0] * 15
            for k in range(15):
                if rng.random() < density:
                    v[k] = rng.randrange(8)
            for k in zero:
                v[k] = 0
            for k, x in fix.items():
                v[k] = x
            return tuple(v)

        ev = [0, 2, 4, 6]
        if kind == "A":
            S = rl([], {})
            X = rl([L.IA, L.IE], {L.IB: rng.randrange(8), L.IC: rng.randrange(8)})
            U = rl([L.IA, L.IE], {})
            V = rl([L.IA, L.IE], {})
        else:
            S = rl([], {L.IE: rng.choice(ev)})
            X = rl([], {L.IA: rng.choice(ev), L.IE: rng.choice(ev),
                        L.IC: rng.randrange(8)})
            U = rl([], {L.IA: rng.choice([1, 3, 5, 7]), L.IE: rng.choice(ev)})
            V = rl([], {L.IA: rng.choice(ev), L.IE: rng.choice(ev)})
        _, _, _, lam0 = L.lattices([S, X, L.ONE, U, V])
        if L.lam4_even(lam0):
            continue
        for Y in L.solve_Y(S, X, U, V, want=4, odd_only=True, budget=3000):
            lets = [S, X, Y, U, V]
            if ok(kind, lets):
                best.append((weight(lets), lets))
        best.sort(key=lambda t: t[0])
        best = best[:6]
    return tried, best


def report(tag, lets):
    S, X, Y, U, V = lets
    _, _, _, lam4 = L.lattices(lets)
    print("%s S=%s X=%s Y=%s U=%s V=%s" % ((tag,) + tuple(M.show(g) for g in lets)))
    print("   relator %s  covectors %s  Lam4mod2 %s  |Lam4| %d"
          % (M.show(L.relator(S, X, Y, U, V)), L.covectors(X, U, V),
             sorted({(a % 2, b % 2) for (a, b) in lam4}), len(lam4)))
    print("   even a/b/c/d/e at every letter: %s"
          % [L.letters_even(lets, i) for i in (L.IA, L.IB, L.IC, L.ID, L.IE)])
    w = quad_witness(lets)
    print("   %d four-fold commutators outside forceN4; first: [[[%s,%s],%s],%s] = %s"
          % ((len(w),) + w[0][:4] + (M.show(w[0][4]),)))


if __name__ == "__main__":
    kind = sys.argv[1] if len(sys.argv) > 1 else "A"
    secs = float(sys.argv[2]) if len(sys.argv) > 2 else 120.0
    dens = float(sys.argv[3]) if len(sys.argv) > 3 else 0.2
    tried, best = search(kind, 60500 + ord(kind) + int(dens * 1000), secs, dens)
    print("kind %s density %.2f: %d tried, %d hits" % (kind, dens, tried, len(best)))
    for w, lets in best:
        report("  w=%-3d" % w, lets)
