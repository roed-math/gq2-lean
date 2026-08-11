"""W62-SEPARATE: layered solve for a relator that is gamma_3-SHAPED with an ODD `j`.

Wave 60's layered solve zeroes the relator's rows in class order; here it is stopped after
class two, which is exactly the condition that the relator lies in the dressings' own
filtration layer `gamma_3`.  Among those the search wants an ODD class-four `j` (the
class-three obstruction) and an ODD class-five residue (so the forcing's conclusion is false
and `StageForces` has its full content), together with a double-commutator dressing pairing
oddly (the parity line fails).

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
import os, random, sys, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
for d in ("w61_sharp4", "w59_force5", "w60_stage4", "w60_sharp5"):
    sys.path.insert(0, os.path.join(os.path.dirname(HERE), d))
import sharp4lib as L, sharp5lib as S5, u6mat as M                     # noqa: E402

IJ, IO = 9, 14
CLASS9 = list(range(9))


def solve_Y_ga3(S, X, U, V, want=2, budget=60000):
    """Every `x1`-slot making the relator `gamma_3`-shaped with an odd `j` and an odd residue."""
    out, state = [], {"n": 0}

    def rec(pos, Y):
        if len(out) >= want or state["n"] > budget:
            return
        if pos == 9:
            r = S5.frelator(S, X, Y, U, V)
            if r[IJ] % 2 and r[IO] % 2:
                out.append(Y)
            return
        k = CLASS9[pos]
        for v in range(8):
            state["n"] += 1
            Yv = Y[:k] + (v,) + Y[k + 1:]
            if S5.frelator(S, X, Yv, U, V)[k] == 0:
                rec(pos + 1, Yv)
                if len(out) >= want:
                    return

    rec(0, M.ONE)
    return out


def witness(m):
    """A double commutator of the letters pairing ODDLY at some slot."""
    for (a, b, c) in itertools.product(range(5), repeat=3):
        z = M.commP(M.commP(m[a], m[b]), m[c])
        if any(z[k] for k in range(9)):
            continue
        v = L.vec(z)
        for i in range(5):
            sh = L.slot_shift(m, i, v)
            if sh[5] % 2:
                return (i, (L.SLOT[a], L.SLOT[b], L.SLOT[c]), z, sh)
    return None


def weight(m):
    return sum(1 for g in m for x in g if x) + sum(min(x, 8 - x) for g in m for x in g)


def small(rng, density, cap):
    return tuple(rng.randrange(1, cap + 1) if rng.random() < density else 0 for _ in range(15))


if __name__ == "__main__":
    seed, tries = int(sys.argv[1]), int(sys.argv[2])
    dens = float(sys.argv[3]) if len(sys.argv) > 3 else 0.25
    cap = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    rng = random.Random(seed)
    best, n = None, 0
    for _ in range(tries):
        S, X, U, V = (small(rng, dens, cap) for _ in range(4))
        for Y in solve_Y_ga3(S, X, U, V, want=1, budget=20000):
            m = [S, X, Y, U, V]
            w = witness(m)
            if w is None:
                continue
            n += 1
            wt = weight(m)
            if best is None or wt < best[0]:
                best = (wt, m, w)
    print("hits %d of %d" % (n, tries))
    if best:
        wt, m, (i, names, z, sh) = best
        r = L.relator(m)
        print("weight %d" % wt)
        print("letters  %s" % " | ".join(M.show(g) for g in m))
        print("relator  %s" % M.show(r))
        print("dressing %s = [[%s,%s],%s] at slot %s -> shift %s"
              % (M.show(z), names[0], names[1], names[2], L.SLOT[i], sh))
        print("covectors %s" % ([L.covector(m, t) for t in range(5)],))
