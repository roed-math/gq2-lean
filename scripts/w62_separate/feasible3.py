"""W62-SEPARATE: which LETTER CONDITION does a provable separating marking need?

`feasible2.py` says the mod-2 problem is feasible.  A Lean proof cannot quote the achievable
lattice, though: it can only quote a congruence subgroup delivered by a two-step commutator
chain, and such a chain reads the letters' COLUMNS.  So this script asks the question in the
form Lean will have to answer it.

For a set `C` of columns declared even at every letter, `even_coords(C)` is the set of dressing
coordinates that are then even on every achievable stage-four dressing - computed by sampling
letter patterns with those columns even and intersecting, so it is a lower bound on what a
chain can deliver and an upper bound on what is true.  The search then asks for a letter pattern
with the columns in `C` even at which

  (A) `cov_o~ = lambda_m cov_m + lambda_n cov_n` on the coordinates outside `even_coords(C)`,
      at every slot, where `cov_o~` deletes the `x1`-slot's `(j, k, l)` (centrality kills them);
  (B) `cov_o` is nonzero on some achievable dressing, i.e. the parity line fails.

Output: the cheapest `C` that admits both, which is the letter condition the Lean file carries.

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

import itertools
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
for d in ("w61_sharp4", "w59_force5", "w60_stage4", "w60_sharp5"):
    sys.path.insert(0, os.path.join(os.path.dirname(HERE), d))

import u6mat as M                                                      # noqa: E402
import feasible2 as F2                                                 # noqa: E402

COLS = "abcdefghi"
NAME = "jklmn"


def rand_pattern(rng, C, x1=False):
    v = [rng.randrange(2) for _ in range(9)]
    for c in C:
        v[c] = 0
    if x1:
        for k in range(5):
            v[k] = 0
    return F2.letter(v)


def even_coords(C, rng, tries=120):
    """The dressing coordinates even on every achievable dressing, for every letter pattern
    whose columns in `C` are even."""
    out = set(range(5))
    for _ in range(tries):
        ls = [rand_pattern(rng, C) for _ in range(4)] + [rand_pattern(rng, C, x1=True)]
        span = F2.achievable_span(ls)
        out &= {s for s in range(5) if all(g[s] == 0 for g in span)}
        if not out:
            break
    return out


def criterion(S, X, Y, U, V, E):
    """(A) with the coordinates in `E` treated as even, and (B)."""
    ls = [S, X, Y, U, V]
    span = F2.achievable_span(ls)
    o, mm, nn = F2.covectors(S, X, Y, U, V)
    lam = None
    for (lm, ln) in ((1, 0), (0, 1), (1, 1), (0, 0)):
        ok = True
        for i in range(5):
            for s in range(5):
                if s in E or (i == 2 and s in (0, 1, 2)):
                    continue                            # closed by achievability or centrality
                if (o[i][s] - lm * mm[i][s] - ln * nn[i][s]) % 2:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            lam = (lm, ln)
            break
    fails = any(F2.dot(o[i], g) for i in range(5) for g in span)
    return lam, fails


def search(seed=62041, tries=4000):
    rng = random.Random(seed)
    ecache = {}
    best = {}
    for _ in range(tries):
        k = rng.randrange(1, 5)
        C = tuple(sorted(rng.sample(range(9), k)))
        if C not in ecache:
            ecache[C] = even_coords(C, random.Random(hash(C) & 0xffff))
        E = ecache[C]
        S, X, U, V = (rand_pattern(rng, C) for _ in range(4))
        Y = rand_pattern(rng, C, x1=True)
        lam, fails = criterion(S, X, Y, U, V, E)
        if lam is not None and fails:
            key = (C, lam)
            if key not in best:
                best[key] = (S, X, Y, U, V, E)
    return best, ecache


if __name__ == "__main__":
    best, ecache = search()
    print("column conditions that admit a provable separating pattern:")
    for (C, lam), (S, X, Y, U, V, E) in sorted(best.items(), key=lambda t: len(t[0][0])):
        print("  even columns %-6s  lambda %s  even dressing coords %s"
              % ("".join(COLS[c] for c in C), lam,
                 "".join(NAME[s] for s in sorted(E)) or "-"))
        print("     S %s | X %s | Y %s | U %s | V %s"
              % tuple(M.show(g) for g in (S, X, Y, U, V)))
    print()
    print("even-coordinate table for the single-column conditions:")
    for c in range(9):
        C = (c,)
        if C not in ecache:
            ecache[C] = even_coords(C, random.Random(c))
        print("   %s even at every letter  =>  %s even on every achievable dressing"
              % (COLS[c], "".join(NAME[s] for s in sorted(ecache[C])) or "-"))
