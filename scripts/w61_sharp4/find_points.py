"""W61-SHARP4: the search for the Lean witness points.

Every candidate is a class-five sigma witness in the campaign's sense: the UNDRESSED frame
kills the relator and the `a0 = a1` dressing leaves a CENTRAL relator with an ODD class-five
residue (`pointlib.solve_y_central`, wave 60's own solver, imported not re-implemented).

Three targets:

* `orth`   - all five stage-four slot covectors vanish mod 2, so EVERY `gamma_3`-dressing
             moves the class-five row evenly, while wave 60's soundness hypothesis and/or its
             conclusion FAIL: the witness that the carried condition is strictly stronger than
             the parity line;
* `ucen`   - the parity line FAILS on the achievable lattice and yet the forcing HOLDS for
             EVERY dressing tuple whatsoever, because a dressing whose class-four rows vanish
             has an even class-five pairing: the witness that the parity line is itself
             strictly stronger than the sharp line;
* `latcen` - the same strictness, but witnessed only through the achievable lattice.

Sparse letters are preferred, and an odd achievable triple commutator is reported so the Lean
file can exhibit an ACHIEVABLE odd dressing rather than an arbitrary one.
"""

import random
import sys
import time

import sharp4lib as L                                                  # noqa: I100
import modlib as MD                                                    # noqa: E402
import pointlib as PL                                                  # noqa: E402
import u6mat as M                                                      # noqa: E402


def weight(lets):
    return sum(1 for g in lets for x in g if x)


def report(lets):
    m = list(lets)
    B = L.gamma3_basis(m)
    IB = L.image_basis(m, B)
    evenA = all(g[L.IA] % 2 == 0 for g in m)
    return dict(m=m, B=B, hyp=L.stageN1_all(m), cons=L.stageN3_all(B),
                snd=(evenA and L.stageN3_all(B)),
                orth=L.orth_all(m, B), modlow=L.modlow(m),
                ucen=L.orth_central_unrestricted(m),
                ga4=L.orth_gafour(m, B), cen=L.orth_central(m, basis=IB),
                kill=L.kill_exists(m, basis=IB),
                covs=[L.covector(m, i) for i in range(5)],
                res=L.relator(m)[L.IO])


def odd_triple(m):
    """An ACHIEVABLE dressing with an odd stage-four pairing, exhibited as a triple commutator
    of the marking's own letters, with the slot it pairs oddly against."""
    best = None
    for a in range(5):
        for b in range(5):
            for c in range(5):
                z = M.commP(M.commP(m[a], m[b]), m[c])
                if any(z[k] for k in range(9)):
                    continue
                for i in range(5):
                    if L.slot_shift(m, i, L.vec(z))[5] % 2:
                        w = sum(1 for x in z if x)
                        if best is None or w < best[3]:
                            best = ((a, b, c), i, z, w)
    return best


def letters(rng, mode):
    """Four families of letter tuples `(S, X, U, V)`; the `x1`-slot is solved for."""
    if mode == 0:                                       # sparse random
        def rl():
            v = [0] * 15
            for _ in range(rng.randrange(1, 5)):
                v[rng.randrange(9)] = rng.randrange(8)
            return tuple(v)
        return rl(), rl(), rl(), rl()
    if mode == 1:                                       # perturb the committed point
        lets = [list(M.mul(M.named(b=1), L.stageX)), list(L.stageX), list(L.stageU),
                list(L.stageV)]
        for _ in range(rng.randrange(1, 4)):
            lets[rng.randrange(4)][rng.randrange(9)] = rng.randrange(8)
        return tuple(tuple(g) for g in lets)
    if mode == 2:                                       # sparse, outer columns even
        def rl2():
            v = [0] * 15
            for _ in range(rng.randrange(1, 5)):
                v[rng.randrange(9)] = rng.randrange(8)
            v[L.IA] = 2 * rng.randrange(4)
            v[L.IE] = 2 * rng.randrange(4)
            return tuple(v)
        return rl2(), rl2(), rl2(), rl2()
    def rl3():                                          # sparse, several columns even
        v = [0] * 15
        for _ in range(rng.randrange(1, 6)):
            v[rng.randrange(9)] = rng.randrange(8)
        for k in (L.IA, L.IB, L.IE, L.IF, L.II):
            v[k] = 2 * rng.randrange(4)
        return tuple(v)
    return rl3(), rl3(), rl3(), rl3()


def wanted(target, r):
    if r["kill"]:
        return False
    if target == "orth":
        return (all(all(e == 0 for e in c) for c in r["covs"])
                and not (r["hyp"] and r["cons"]))
    if target == "ucen":
        return (not r["orth"]) and r["ucen"]
    return (not r["orth"]) and r["cen"]


def search(budget, seed, target):
    rng = random.Random(seed)
    t0 = time.time()
    found = []
    tried = 0
    while time.time() - t0 < budget:
        S, X, U, V = letters(rng, rng.randrange(4))
        if M.commP(U, V) == M.ONE:
            continue
        for Y in L.solve_y(S, X, U, V, want=2, budget=1500):
            tried += 1
            r = report((S, X, Y, U, V))
            if wanted(target, r):
                lets = (S, X, Y, U, V)
                found.append((weight(lets), lets, r))
                found.sort(key=lambda t: t[0])
                found = found[:5]
    return found, tried


def show_point(w, lets, r):
    print(" weight %2d  X=%-26s U=%-30s V=%-30s" % (w, M.show(lets[1]), M.show(lets[3]),
                                                    M.show(lets[4])))
    print("   Y=%s" % M.show(lets[2]))
    print("   residue %d | hyp %s cons %s snd %s | orth %s ucen %s modlow %s ga4 %s cen %s"
          % (r["res"], r["hyp"], r["cons"], r["snd"], r["orth"], r["ucen"],
             bool(r["modlow"]), r["ga4"], r["cen"]))
    print("   covectors (j,k,l,m,n): %s" % (r["covs"],))
    print("   gamma_3(im) card %d  basis %s" % (MD.card(r["B"], 6), r["B"]))
    ot = odd_triple(r["m"])
    if ot:
        print("   odd achievable [[m%d,m%d],m%d] = %s pairing oddly at slot %s"
              % (ot[0][0], ot[0][1], ot[0][2], M.show(ot[2]), L.SLOT[ot[1]]))
    print()


if __name__ == "__main__":
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 60.0
    targets = sys.argv[2].split(",") if len(sys.argv) > 2 else ["orth", "ucen", "latcen"]
    for (i, tgt) in enumerate(targets):
        print("==== target %s ====" % tgt)
        found, tried = search(budget, 61200 + i, tgt)
        print("  %d candidate markings examined, %d kept" % (tried, len(found)))
        for (w, lets, r) in found:
            show_point(w, lets, r)
