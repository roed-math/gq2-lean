"""W60-STAGE4 step 1c (route b): a class-five sigma point with NO stage-four hole.

The stage-four translation identity of `derive_stage4.py` makes the target exact.  The
class-five row of the shift is AFFINE in the dressings and every one of its terms is one
dressing coordinate against a frame quantity:

    z.o                    with the Frobenius weights (-4, 2)          -> always even
    z.n                    against the letters' FIRST abelian column   -> even if every `a` is
    z.k                    against `a * e` products and even blocks    -> even if every `a` is
    z.j, z.l, z.m          against columns that can be odd             -> must themselves be even

So the class-five residue cannot be moved by an odd amount as soon as

    (S1) every letter has an even `(3,4)`-column     [wave 59's own soundness input]
    (S2) every letter has an even `(1,2)`-column     [kills the z.n and z.k channels]
    (S3) every achievable `gamma_3`-dressing has `j`, `l` and `m` even

and `derive_chain.py` shows (S1) + (S2) already give (S3) by a two-step subgroup chain.  The
wave-59 point fails (S2): its `U`-letter has `a = 1`, which is exactly the coordinate making
`[[sigma, U], x1] = <m=5, n=6>` carry an odd class-four coordinate.

Search.  `diagnose.py` shows the two relators ALWAYS agree below class five, so the cascade
never dies on disagreement, only on parity; and the greedy sparsest-lift walk is a cheap
pre-filter.  Candidates are then checked on `gamma_3(im)` and ranked by sparsity so the Lean
witness stays readable.

BRACKET CONVENTION.  [NONE]
This script computes no commutators, so the convention does not arise.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""
import sys
import os
import random

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))

import u6mat as M                                             # noqa: E402
import modlib as MD                                           # noqa: E402
import gam3lib as G                                           # noqa: E402
import pointlib as P                                          # noqa: E402
from diagnose import first_fail                               # noqa: E402

SIG = M.sigFiveMark


def parity_span(basis):
    """The F_2-span of the (j,k,l,m,n) parities of a Howell basis of gamma_3(im)."""
    span = {(0, 0, 0, 0, 0)}
    for r in basis:
        g = tuple(r[i] % 2 for i in range(5))
        span |= {tuple((a + b) % 2 for a, b in zip(p, g)) for p in span}
    return span


def sound(span):
    """(S3): every achievable dressing has j, l and m even."""
    return all(p[0] == 0 and p[2] == 0 and p[3] == 0 for p in span)


def weight(p):
    return sum(1 for x in p if x)


def main():
    random.seed(int(os.environ.get("W60_SEED", "60031")))
    NTRY = int(os.environ.get("W60_NTRY", "60000"))
    live = 0
    found = []
    for t in range(NTRY):
        X = M.named(a=random.randrange(0, 8, 2), e=random.choice((1, 3, 5, 7)))

        def letter(sp):
            d = {"a": random.randrange(0, 8, 2), "c": random.randrange(0, 8, 2)}
            for k in "bde":
                d[k] = random.randrange(8)
            for k in "fghi":
                d[k] = 0 if random.random() < sp else random.randrange(8)
            return M.named(**d)

        sp = random.choice((0.0, 0.25, 0.5))
        U, V = letter(sp), letter(sp)
        if first_fail(X, U, V)[0] != "OK":
            continue
        live += 1
        sols = P.solve_y_central(SIG, X, U, V, limit=32)
        if not sols:
            continue
        span = parity_span(G.gamma3_module([SIG, X, sols[0], U, V]))
        if not sound(span):
            continue
        best = min(sols, key=lambda Y: (weight(Y), sum(Y)))
        res = P.residue(SIG, X, best, U, V)[14]
        found.append((weight(best), X, U, V, best, res, sorted(span)))
        found.sort(key=lambda r: (r[0], r[5]))
        w, X_, U_, V_, Y_, res_, sp_ = found[0]
        print("[%d/%d] live %d, clean %d; best weight %d residue %d"
              % (t, NTRY, live, len(found), w, res_))
        print("        x0 = %s   U = %s   V = %s" % (M.show(X_), M.show(U_), M.show(V_)))
        print("        x1 = %s" % M.show(Y_))
        sys.stdout.flush()
    print()
    print("== %d tries, %d live points, %d CLEAN ==" % (NTRY, live, len(found)))
    for rec in found[:6]:
        w, X_, U_, V_, Y_, res_, sp_ = rec
        print("   weight %2d  residue %d   parities (j,k,l,m,n): %s" % (w, res_, sp_))
        print("      x0 = %s   U = %s   V = %s" % (M.show(X_), M.show(U_), M.show(V_)))
        print("      x1 = %s" % M.show(Y_))
    return found


if __name__ == "__main__":
    main()
