"""W60-STAGE4 step 1 (route b): is there a class-five sigma point WITHOUT the wave-59 hole?

Wave 59's exclusion is against stage-five refinements and false one filtration step wider: at
its point `gamma_3` of the image contains the whole `gamma_4` of the carrier, so it contains
`gamma_4`-SHAPED dressings with an ODD class-four coordinate, and those kill the dressed frame.
Wave 59 asked whether a different point avoids that.  This script answers it.

The search.  Keep the sigma marking `E_23 = <b=1>` (the committed lift of `sigFourMark`) and
the gauge shape of the `x0` slot; vary the two handle letters and the `x0` slot; and for each
choice SOLVE for the `x1` slot by the class-by-class cascade of `pointlib.solve_y`, which is
exact and enumerates every solution.  Then filter:

  (1) the undressed frame kills the relator                        [by construction]
  (2) the `a0 = a1`-dressed frame is CENTRAL with an ODD residue    [the exclusion is live]
  (3) every letter has an even `(3,4)`-column                       [wave 59's soundness input]
  (4) no `gamma_4`-SHAPED member of `gamma_3(im)` kills any slot    [the wave-59 hole, closed]

Test (4) uses the committed translation identities of `GradedFiveDefect` /`GradedFiveForce`
(`SqU6.sqWord_mul_gaFour`, `commP_mul_gaFour`), which are theorems, and `verify_stage4.py`
re-checks them against honest collection.  A candidate that survives (4) is then put through
the FULL honest `gamma_3` census, which also covers dressings with a live class-three part.
"""
import sys
import os
import random
import itertools

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))

import u6mat as M                                             # noqa: E402
import modlib as MD                                           # noqa: E402
import gam3lib as G                                           # noqa: E402
import pointlib as P                                          # noqa: E402

SIG = M.sigFiveMark


def ga4_kill_slots(S, X, Y, U, V, res, shaped):
    """Which slots a gamma_4-SHAPED achievable dressing can kill, by the committed identities.

    `shaped` is the set of (m, n, o) of the gamma_4-shaped members of gamma_3(im); `S` is the
    DRESSED sigma-slot letter and `res` the dressed relator's class-five residue.
    """
    hit = []
    for (m, n, o) in shaped:
        # slot 0, sigma: a pure central translation
        if (m * X[4] - n * X[0] + res) % 8 == 0:
            hit.append((0, (m, n, o)))
        # slot 1, x0: class-four rows move by -4m, -4n; class-five by the Fox term
        if (-4 * m) % 8 == 0 and (-4 * n) % 8 == 0:
            sh = -4 * o + (10 * X[4] - S[4] - 8 * Y[4]) * m - (10 * X[0] - S[0] - 8 * Y[0]) * n
            if (sh + res) % 8 == 0:
                hit.append((1, (m, n, o)))
        # slot 2, x1
        if (2 * m) % 8 == 0 and (2 * n) % 8 == 0:
            sh = 2 * o + Y[4] * m - Y[0] * n
            if (sh + res) % 8 == 0:
                hit.append((2, (m, n, o)))
        # the two handle slots: pure central translations against the opposite letter
        if (m * V[4] - n * V[0] + res) % 8 == 0:
            hit.append((3, (m, n, o)))
        if (U[0] * n - U[4] * m + res) % 8 == 0:
            hit.append((4, (m, n, o)))
    return hit


def analyse(X, U, V, ysols):
    """The first `x1`-solution making the dressed frame central with an odd residue."""
    for Y in ysols:
        r = P.residue(SIG, X, Y, U, V)
        if r[14] % 2 == 0:
            continue
        if any(r[k] for k in range(14)):
            continue
        return Y, r[14]
    return None, None


def even_c(letters):
    return all(z[2] % 2 == 0 for z in letters)


def report(X, U, V, Y, res, shaped, hits):
    print("   x0=%s  U=%s  V=%s" % (M.show(X), M.show(U), M.show(V)))
    print("      x1=%s   residue=%d   |gamma_4-shaped of gamma_3(im)|=%d"
          % (M.show(Y), res, len(shaped)))
    print("      (m,n) parities present: %s"
          % sorted({(m % 2, n % 2) for (m, n, o) in shaped}))
    print("      gamma_4-shaped kills: %s"
          % (", ".join("%s by %s" % (P.SLOT[s], M.show(G.elt((0, 0, 0) + z))) for s, z in hits[:4])
             if hits else "NONE"))


def main():
    random.seed(60001)
    tried = 0
    live = 0
    clean = []
    # the gauge family for the x0 slot: `a` even, `e` odd, the rest zero
    xs = [M.named(a=a, e=e) for a in (0, 2, 4, 6) for e in (1, 3, 5, 7)]

    def rand_letter(a_even, c_even):
        d = {}
        d["a"] = random.randrange(0, 8, 2) if a_even else random.randrange(8)
        d["b"] = random.randrange(8)
        d["c"] = random.randrange(0, 8, 2) if c_even else random.randrange(8)
        d["d"] = random.randrange(8)
        d["e"] = random.randrange(8)
        for k in "fghi":
            d[k] = random.randrange(8)
        return M.named(**d)

    NTRY = int(os.environ.get("W60_NTRY", "4000"))
    for _ in range(NTRY):
        X = random.choice(xs)
        # soundness needs even c throughout; the analysis of the wave-59 mechanism says the
        # a-column is the other lever, so sample both parities of it and let the filter decide
        a_even = random.random() < 0.75
        U = rand_letter(a_even, True)
        V = rand_letter(a_even, True)
        tried += 1
        ysols = P.solve_y(SIG, X, U, V, limit=24)
        if not ysols:
            continue
        Y, res = analyse(X, U, V, ysols)
        if Y is None:
            continue
        if not even_c([SIG, X, Y, U, V]):
            continue
        live += 1
        b3 = G.gamma3_module([SIG, X, Y, U, V])
        shaped = G.ga4_shaped_elements(b3)
        S = M.mul(SIG, X)
        hits = ga4_kill_slots(S, X, Y, U, V, res, shaped)
        if not hits:
            clean.append((X, U, V, Y, res, shaped))
            if len(clean) <= 6:
                print("== a point with NO gamma_4-shaped hole ==")
                report(X, U, V, Y, res, shaped, hits)
    print()
    print("tried %d (X, U, V) triples; %d gave a live odd-residue central point;"
          % (tried, live))
    print("%d of those had no gamma_4-shaped achievable kill." % len(clean))
    return clean


if __name__ == "__main__":
    main()
