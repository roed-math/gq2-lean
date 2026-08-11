"""W62-SEPARATE: the exact mod-2 feasibility question for a LEAN-PROVABLE separating marking.

A proof that the forcing holds while the parity line fails has, at mod-2 resolution, exactly two
resources:

  * `CENTRALITY`, which over `Z/8` says more than "even".  The three class-three rows of the
    shift are `-4 z1.x + 2 z2.x`, so a central shift forces the `x1`-slot's `j`, `k` and `l`
    EVEN, whatever the letters are and with no achievability.  This is the `Z/8` content wave
    61 set aside when it called the class-three rows "even for free".
  * `ACHIEVABILITY`, which at mod-2 resolution is the `F_2`-span of the double commutators'
    `(j, k, l, m, n)`, a Lean-provable object (a two-step commutator chain lands in exactly such
    a congruence subgroup).

Write `cov_o`, `cov_m`, `cov_n` for the five slots' class-five and class-four covectors.  Then

  (A) the forcing is provable at mod-2 resolution iff some `lambda` in `F_2^2` has
      `cov_o~ = lambda_m cov_m + lambda_n cov_n` on the achievable span at every slot, where
      `cov_o~` is `cov_o` with the `x1`-slot's `(j, k, l)` entries deleted (centrality kills
      them);
  (B) the parity line fails iff `cov_o` itself is nonzero on the span at some slot.

This script decides whether (A) and (B) can hold together, over the letters' column parities.
The answer decides the lane: a feasible pattern is lifted to an admissible marking and proved;
an infeasible verdict is a certified negative, and says the four wave-61 markings are hard for a
reason rather than by accident.
"""

import itertools
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
for d in ("w61_sharp4", "w59_force5", "w60_stage4", "w60_sharp5"):
    sys.path.insert(0, os.path.join(os.path.dirname(HERE), d))

import u6mat as M                                                      # noqa: E402

IA, IB, IC, ID, IE = 0, 1, 2, 3, 4
IF, IG, IH, II = 5, 6, 7, 8
IJ, IK, IL, IM, IN, IO = 9, 10, 11, 12, 13, 14
G3 = [IJ, IK, IL, IM, IN]
NAME = "jklmn"


def letter(bits9):
    return tuple(list(bits9) + [0] * 6)


def span_of(vecs):
    """A reduced `F_2` basis of the span."""
    basis = []
    for v in vecs:
        r = [x % 2 for x in v]
        for b in basis:
            p = next(i for i in range(len(b)) if b[i])
            if r[p]:
                r = [(r[i] + b[i]) % 2 for i in range(len(r))]
        if any(r):
            basis.append(r)
            basis.sort(key=lambda b: next(i for i in range(len(b)) if b[i]))
    return basis


def achievable_span(ls):
    """The `F_2`-span of `(j, k, l, m, n)` over the achievable stage-four dressings.

    Generated exactly as `sharp4lib.gamma3_gens`, which `validate_sharp4.py` checked against an
    honest element-by-element closure: `[[a,b],c]` and its two further brackets.
    """
    t3 = {M.commP(M.commP(a, b), c) for a in ls for b in ls for c in ls}
    t4 = {M.commP(z, c) for z in t3 for c in ls}
    t5 = {M.commP(z, c) for z in t4 for c in ls}
    return span_of([tuple(z[k] % 2 for k in G3) for z in (t3 | t4 | t5)])


def covectors(S, X, Y, U, V):
    """`(cov_o, cov_m, cov_n)` at the five slots, mod 2, on `(j, k, l, m, n)`."""
    def o_of(L, cj, ck, cl):
        return (L[II] + cj, L[IA] * L[IE] + ck, L[IF] + L[IA] * L[IB] + cl, L[IE], L[IA])

    def m_of(L):
        return (L[ID], L[IA], 0, 0, 0)

    def n_of(L):
        return (0, L[IE], L[IB], 0, 0)

    cj0 = S[ID] * X[IE] + S[IE] * X[ID] + Y[ID] * Y[IE]
    cl0 = S[IA] * X[IB] + S[IB] * X[IA] + Y[IA] * Y[IB]
    cjf = S[ID] * X[IE] + S[IE] * X[ID]
    clf = S[IA] * X[IB] + S[IB] * X[IA]
    cjh = U[ID] * V[IE] + U[IE] * V[ID]
    clh = U[IA] * V[IB] + U[IB] * V[IA]
    F = S                                              # the Fox letter is `S` mod 2
    o = [o_of(X, cj0, 0, cl0), o_of(F, cjf, 0, clf),
         o_of(Y, S[IE] * Y[ID], S[IA] * Y[IE] + S[IE] * Y[IA], S[IA] * Y[IB]),
         o_of(V, cjh, 0, clh), o_of(U, cjh, 0, clh)]
    mm = [m_of(X), m_of(F), m_of(Y), m_of(V), m_of(U)]
    nn = [n_of(X), n_of(F), n_of(Y), n_of(V), n_of(U)]
    red = lambda t: tuple(x % 2 for x in t)                          # noqa: E731
    return [red(c) for c in o], [red(c) for c in mm], [red(c) for c in nn]


def dot(u, v):
    return sum(a * b for a, b in zip(u, v)) % 2


def verdict(S, X, Y, U, V):
    """`(provable, parity_line_fails)` at mod-2 resolution, plus the witnessing lambda."""
    ls = [S, X, Y, U, V]
    span = achievable_span(ls)
    o, mm, nn = covectors(S, X, Y, U, V)
    otilde = [list(c) for c in o]
    for s in (0, 1, 2):
        otilde[2][s] = 0                               # centrality kills the x1-slot's j, k, l
    lam = None
    for (lm, ln) in ((0, 0), (1, 0), (0, 1), (1, 1)):
        if all(dot(otilde[i], g) == (lm * dot(mm[i], g) + ln * dot(nn[i], g)) % 2
               for i in range(5) for g in span):
            lam = (lm, ln)
            break
    fails = any(dot(o[i], g) for i in range(5) for g in span)
    return lam, fails, span, o


def rand_letter(rng, x1=False):
    v = [rng.randrange(2) for _ in range(9)]
    if x1:
        for k in range(5):
            v[k] = 0                                   # admissibility: `Y`'s class-one is even
    return letter(v)


def search(seed, tries, verbose=True):
    rng = random.Random(seed)
    hits = []
    stats = {"provable": 0, "fails": 0, "both": 0}
    for _ in range(tries):
        S, X, U, V = (rand_letter(rng) for _ in range(4))
        Y = rand_letter(rng, x1=True)
        lam, fails, span, o = verdict(S, X, Y, U, V)
        if lam is not None:
            stats["provable"] += 1
        if fails:
            stats["fails"] += 1
        if lam is not None and fails:
            stats["both"] += 1
            hits.append((S, X, Y, U, V, lam, span, o))
    return hits, stats


def exhaustive(cols=(IA, IB, ID, IE, IF, II)):
    """Sweep the columns the covectors read, exhaustively, with the rest zero."""
    hits = []
    n = 0
    pats = list(itertools.product((0, 1), repeat=len(cols)))
    for pS in pats:
        for pX in pats:
            for pU in pats:
                for pV in pats:
                    for pY in pats:
                        def mk(p, x1=False):
                            v = [0] * 9
                            for c, b in zip(cols, p):
                                v[c] = b
                            if x1:
                                for k in range(5):
                                    v[k] = 0
                            return letter(v)
                        S, X, U, V = mk(pS), mk(pX), mk(pU), mk(pV)
                        Y = mk(pY, x1=True)
                        n += 1
                        lam, fails, span, o = verdict(S, X, Y, U, V)
                        if lam is not None and fails:
                            hits.append((S, X, Y, U, V, lam))
    return hits, n


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "random"
    if mode == "random":
        tries = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
        hits, stats = search(62031, tries)
        print("random parity patterns: %d tried, %s" % (tries, stats))
        for h in hits[:6]:
            print("   S %s | X %s | Y %s | U %s | V %s   lambda %s"
                  % tuple([M.show(g) for g in h[:5]] + [h[5]]))
    else:
        hits, n = exhaustive()
        print("exhaustive over the six covector columns: %d patterns, %d feasible" % (n, len(hits)))
        for h in hits[:10]:
            print("   S %s | X %s | Y %s | U %s | V %s   lambda %s"
                  % tuple([M.show(g) for g in h[:5]] + [h[5]]))
