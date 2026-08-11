"""W62-CHANNELS step 3: the honest census, over markings rather than parity patterns.

`sweep_f2.py` swept the parity patterns; this file sweeps MARKINGS, with the honest 6 x 6 group
law, and asks the two questions the wave exists to answer.

    A.  ON the class-two-forced gauge: is there a marking whose three channels are all even on
        the achievable lattice and whose class-five separation bit is ODD?
    B.  OFF the gauge, with only what the RELATOR itself forces (`x1`'s abelian columns even):
        same question, with the bit taken as the honest difference of the two relators' `(1,6)`
        rows rather than wave 58's closed form.

Question A is the wave's target.  Question B is its escape hatch, and the reason the census is
run over markings and not only over parities: off the gauge the bit is not wave 58's form, so
the parity sweep cannot answer it.

The "channels even" test is over the ten pairwise commutators of the marking's letters against
the five permuted letters, which `derive_channels.py` sections 1 to 3 certify is the whole of
the achievable lattice's image under the functional.  A third pass then runs the expensive
check: honest relator-killing points found by wave 60's layered solve.
"""
import sys
import os
import random
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w60_stage4"))

import u6mat as M                                               # noqa: E402
import pointlib as P                                            # noqa: E402
import chanlib as C                                             # noqa: E402

SIG = M.sigFiveMark
BUDGET = float(os.environ.get("W62_BUDGET", "900"))


def rand_letter(rng, **fix):
    d = {k: rng.randrange(8) for k in M.COORDS}
    d["a"] = rng.randrange(0, 8, 2)
    d["c"] = rng.randrange(0, 8, 2)
    d.update(fix)
    return M.named(**d)


def gauge_x(rng):
    d = {k: rng.randrange(8) for k in M.COORDS}
    for k in "acdfgh":
        d[k] = rng.randrange(0, 8, 2)
    d["b"] = 0
    return M.named(**d)


def relator_y(rng, gauge):
    """An `x1` slot with the columns the RELATOR forces even (a, b, c, d, e)."""
    d = {k: rng.randrange(8) for k in M.COORDS}
    for k in "abcde":
        d[k] = rng.randrange(0, 8, 2)
    if gauge:
        d["b"] = 0
    return M.named(**d)


def diffbit(S0, X, Y, U, V):
    r0 = C.residue(SIG, X, Y, U, V)
    r1 = C.residue(S0, X, Y, U, V)
    return (C.co(r1, "o") - C.co(r0, "o")) % 2


def sweep(rng, name, xgen, ygen, n):
    """Count markings by (channels even?, bit odd?)."""
    tab = {(0, 0): 0, (0, 1): 0, (1, 0): 0, (1, 1): 0}
    hits = []
    for _ in range(n):
        X = xgen(rng)
        Y = ygen(rng)
        U = rand_letter(rng)
        V = rand_letter(rng)
        S0 = M.mul(SIG, X)
        ev, bad = C.channels_even(S0, X, Y, U, V)
        b = diffbit(S0, X, Y, U, V)
        tab[(1 if ev else 0, b)] += 1
        if ev and b:
            hits.append((X, Y, U, V))
    print("   %-46s  markings %6d" % (name, n))
    print("      channels EVEN and bit ODD   (the target) : %6d" % tab[(1, 1)])
    print("      channels EVEN and bit even              : %6d" % tab[(1, 0)])
    print("      channels odd  and bit ODD               : %6d" % tab[(0, 1)])
    print("      channels odd  and bit even              : %6d" % tab[(0, 0)])
    return hits


def main():
    rng = random.Random(62003)
    print("=" * 96)
    print("== W62-CHANNELS: the marking census ==")
    print("=" * 96)
    print()

    print("== A. ON the class-two-forced gauge ==")
    print()
    hits_gauge = sweep(rng, "x0 on the gauge, x1 with even abelian columns",
                       gauge_x, lambda r: relator_y(r, True), 8000)
    print()

    print("== B. OFF the gauge: only what the relator forces ==")
    print()
    print("   `x1`'s abelian columns are even at every marking killing the four abelian rows")
    print("   (`sqRelWord_lower_x1_even`), so that much is kept; the `x0` slot is free apart")
    print("   from `stageN1`.")
    print()
    hits_free = sweep(rng, "x0 free (stageN1 only), x1 relator-shaped",
                      rand_letter, lambda r: relator_y(r, False), 8000)
    print()
    if hits_free:
        print("   ⭐ OFF-GAUGE HITS EXIST.  The first three:")
        for (X, Y, U, V) in hits_free[:3]:
            print("      x0 = %s" % M.show(X))
            print("      x1 = %s" % M.show(Y))
            print("      U  = %s" % M.show(U))
            print("      V  = %s" % M.show(V))
            print("      x0.d, x0.f parities = %d, %d   (the gauge asks for 0, 0)"
                  % (C.co(X, "d") % 2, C.co(X, "f") % 2))
            print()
        pd = sum(1 for (X, _, _, _) in hits_free if C.co(X, "d") % 2)
        pf = sum(1 for (X, _, _, _) in hits_free if C.co(X, "f") % 2)
        print("   of the %d off-gauge hits, %d have x0.d odd and %d have x0.f odd;"
              % (len(hits_free), pd, pf))
        print("   %d have NEITHER, which would be a hit inside the gauge's x0 columns."
              % sum(1 for (X, _, _, _) in hits_free
                    if C.co(X, "d") % 2 == 0 and C.co(X, "f") % 2 == 0))
    else:
        print("   NO off-gauge hit either, at this sample size.")
    print()

    print("=" * 96)
    print("== C. honest relator-killing points, by wave 60's layered solve ==")
    print("=" * 96)
    print()
    print("   Budget %.0f s.  Each point: the undressed frame kills the relator, the `a0 = a1`"
          % BUDGET)
    print("   frame is central with an ODD class-five residue, every letter is `stageN1`.")
    print()
    print("   The layered solve enumerates EVERY `x1` slot making a given `(x0, U, V)` triple")
    print("   live, so one triple supplies thousands of genuine binder points differing in the")
    print("   `x1` letter.  Wave 60's committed triple first, then whatever a random search")
    print("   turns up inside the budget of %.0f s." % BUDGET)
    print()
    STU = M.named(a=6, b=7, c=4, d=1, e=3, g=5, h=5)
    STV = M.named(a=6, b=7, c=6, d=1, e=3, f=5, g=3, h=3, i=4)
    triples = []
    for a in (0, 2, 4, 6):
        for e in (1, 3, 5, 7):
            X = M.named(a=a, e=e)
            if P.solve_y_central(SIG, X, STU, STV, limit=1):
                triples.append(("wave 60's U, V" if (a, e) != (2, 5)
                                else "wave 60's COMMITTED triple", X, STU, STV))
    t0 = time.time()
    tried = 0
    rand_live = 0
    while time.time() - t0 < BUDGET:
        tried += 1
        X = M.named(a=rng.randrange(0, 8, 2), e=rng.randrange(1, 8, 2))
        U = rand_letter(rng)
        V = rand_letter(rng)
        if P.solve_y_central(SIG, X, U, V, limit=1):
            rand_live += 1
            triples.append(("random triple %d" % rand_live, X, U, V))
    tlive = tev = todd = 0
    for (name, X, U, V) in triples:
        live = evens = oddchan = 0
        for Y in P.solve_y_central(SIG, X, U, V, limit=None):
            r0 = C.residue(SIG, X, Y, U, V)
            r1 = C.residue(M.mul(SIG, X), X, Y, U, V)
            if r0 != M.ONE:
                continue
            if any(r1[k] for k in range(14)) or r1[14] % 2 == 0:
                continue
            if not all(C.stageN1(t) for t in [SIG, X, Y, U, V]):
                continue
            if not all(C.co(Y, k) % 2 == 0 for k in "abcde"):
                print("   *** an x1 slot with an ODD abelian column at a live point ***")
            live += 1
            S0 = M.mul(SIG, X)
            ev, bad = C.channels_even(S0, X, Y, U, V)
            evens += ev
            oddchan += (C.chan(M.commP(X, Y), Y) % 2 == 1)
        print("   %-26s x0 = %-14s live points %6d" % (name, M.show(X), live))
        print("      all three channels even (the target)          : %6d" % evens)
        print("      chan([x0,x1], x1) ODD (the theorem's verdict) : %6d" % oddchan)
        tlive += live
        tev += evens
        todd += oddchan
    print()
    print("   %d live (x0, U, V) triples in all: %d from the `x0` gauge family against wave"
          % (len(triples), len(triples) - rand_live))
    print("   60's handle letters, and %d from %d random triples in %.0f s."
          % (rand_live, tried, time.time() - t0))
    print("   %d live binder points.  Channels all even: %d.  chan([x0,x1], x1) odd: %d of %d."
          % (tlive, tev, todd, tlive))
    print()
    print("=" * 96)


if __name__ == "__main__":
    main()
