"""W60-SHARP5: certify the two separating class-five markings, end to end.

Everything here is recomputed through `scripts/w59_force5/u6mat.py`, the honest 6 x 6 matrix
library, and nothing is taken from the fast product.  The output is what the Lean file's
constants and `decide`s have to match.

  ORTH  all three covectors `(slot.e, slot.a)` are ZERO, so the increment pairing vanishes
        for ARBITRARY class-four moves; the achievable lattice is nevertheless ODD, so wave
        59's `forceLcs_three_le_forceN4` fails at its conclusion and at its hypothesis.
  HALF  the `U`-covector is `(0, 1)`, so the orthogonal route is unavailable and the moves
        really are read; every letter has an even fifth abelian column, which forces the
        SECOND class-four coordinate even; the FIRST is odd.

Both are admissible: relator CENTRAL with an ODD class-five residue.
"""

import itertools

import sharp5lib as L                                                # noqa: I100
import u6mat as M                                                    # noqa: E402

NAMES = ("S", "X", "Y", "U", "V")

POINTS = {
    "WITNESS (wave 59's binder point)": (
        M.mul(M.sigFiveMark, M.sepX), M.sepX, M.sepY, M.sepU, M.sepV),
    "ORTH": (M.named(a=1, l=2), M.named(b=4, c=3, j=5), M.named(c=2, f=2, n=7),
             M.named(d=1, g=6, j=3, n=2), M.named(b=5, i=3)),
    "HALF": (M.named(a=2, e=4, f=3), M.named(b=7, c=6, e=2),
             M.named(b=2, f=1, g=2, j=3), M.named(a=1, m=3),
             M.named(a=2, c=3, d=7, e=4, n=7)),
}

OUT = []
FAILURES = []


def say(s=""):
    print(s)
    OUT.append(s)


def gate(name, got, want=True):
    ok = (got == want)
    say("  [%s] %s%s" % ("PASS" if ok else "FAIL", name,
                         "" if ok else "   got %r want %r" % (got, want)))
    if not ok:
        FAILURES.append(name)


def lean_tuple(p):
    return "⟨" + ", ".join(str(c) for c in p) + "⟩"


def quad_witnesses(lets):
    out = []
    for a, b, c, d in itertools.product(range(5), repeat=4):
        z = M.commP(M.commP(M.commP(lets[a], lets[b]), lets[c]), lets[d])
        if z[L.IM] % 2 or z[L.IN] % 2:
            out.append((NAMES[a], NAMES[b], NAMES[c], NAMES[d], z))
    return out


def report(tag, lets):
    S, X, Y, U, V = lets
    say("== %s ==" % tag)
    for nm, g in zip(NAMES, lets):
        say("  %s = %-56s  Lean %s" % (nm, M.show(g), lean_tuple(g)))
    r = L.relator(S, X, Y, U, V)
    say("  relator = %s" % M.show(r))
    gate("the relator is a CENTRAL translation", L.is_central(r))
    gate("…with an ODD class-five residue", r[L.IO] % 2, 1)

    A, L2, L3, L4 = L.lattices(lets)
    slow = L.lattices_slow(lets)
    gate("the lattice engine agrees with the slow route",
         [sorted(x) for x in (A, L2, L3, L4)], [sorted(x) for x in slow])
    g3, g4 = L.gamma34(lets)
    gate("the honest closure of gamma_4 has the same (m, n)-image",
         {(z[12], z[13]) for z in g4}, L4)
    say("  |A| = %d, |Lam2| = %d, |Lam3| = %d, |Lam4| = %d, |gamma_3| = %d, |gamma_4| = %d"
        % (len(A), len(L2), len(L3), len(L4), len(g3), len(g4)))
    say("  Lam4 = %s" % sorted(L4))
    say("  covectors ((X.e,X.a),(V.e,V.a),(U.e,U.a)) = %s" % (L.covectors(X, U, V),))

    gate("* THE SHARP INVARIANT HOLDS", L.five_orth(X, U, V, L4))
    if tag == "WITNESS (wave 59's binder point)":
        gate("wave 59's CONSEQUENCE holds here (the point is inside its own chain)",
             L.lam4_even(L4))
        gate("wave 59's HYPOTHESIS holds here", L.letters_even(lets, L.IC))
        gate("* at the WITNESS the sharp line and wave 59's CONSEQUENCE COINCIDE, because "
             "the two live covectors span the mod-2 dual",
             L.five_orth(X, U, V, L4) == L.lam4_even(L4))
    else:
        gate("* wave 59's CONSEQUENCE (every achievable dressing in forceN4) FAILS",
             L.lam4_even(L4), False)
        gate("* wave 59's HYPOTHESIS (every slot has an even (3,4)-column) FAILS",
             L.letters_even(lets, L.IC), False)
    for idx, nm in ((L.IA, "a"), (L.IB, "b"), (L.IC, "c"), (L.ID, "d"), (L.IE, "e")):
        say("  every letter even in %s : %s" % (nm, L.letters_even(lets, idx)))

    ws = quad_witnesses(lets)
    say("  %d four-fold commutators of the letters lie outside forceN4" % len(ws))
    for w in ws[:4]:
        say("    [[[%s, %s], %s], %s] = %s" % (w[0], w[1], w[2], w[3], M.show(w[4])))

    g4elts = L.gaFour_elements(L4)
    kill = L.kill_exists(S, X, Y, U, V, g4elts, lib=M)
    gate("* NO achievable five-slot refinement kills the relator (honest search)",
         kill, False)

    # the unrestricted sweep, per slot: which unachievable class-four moves DO kill.
    # Slot `z3` dresses the handle-U slot and pairs against V's columns; slot `z4` dresses
    # the handle-V slot and pairs against U's.  The slot names below are the DRESSED slot.
    hits = []
    per = [0, 0, 0]
    for slot in range(3):
        for mm in range(8):
            for nn in range(8):
                for t in range(8):
                    trip = [M.ONE, M.ONE, M.ONE]
                    trip[slot] = M.named(m=mm, n=nn)
                    if L.refined(S, X, Y, U, V, trip[0], M.ONE, M.liftC(t),
                                 trip[1], trip[2]) == M.ONE:
                        hits.append((NAMES[[0, 3, 4][slot]], mm, nn, t))
                        per[slot] += 1
    say("  UNRESTRICTED single-slot class-four moves that kill, by dressed slot"
        " (512 each): sigma %d, handle-U %d, handle-V %d" % tuple(per))
    if hits:
        say("    first: dressed slot %s, move <m=%d, n=%d>, exponent liftC6 %d" % hits[0])
    say()
    return hits


def orth_extra(lets):
    """The orthogonal point's pairing vanishes for every class-four move, achievable or not."""
    S, X, Y, U, V = lets
    bad = 0
    for m0, n0, m3, n3, m4, n4 in itertools.product(range(8), repeat=6):
        if (m0 + n0 + m3 + n3 + m4 + n4) % 7:                        # a 1-in-7 sample
            continue
        z0 = M.named(m=m0, n=n0)
        z3 = M.named(m=m3, n=n3)
        z4 = M.named(m=m4, n=n4)
        if L.incr_pair(X, U, V, z0, z3, z4) != 0:
            bad += 1
    gate("the increment pairing vanishes IDENTICALLY (sampled over all three slots)", bad, 0)


if __name__ == "__main__":
    hits = {}
    for tag, lets in POINTS.items():
        if all(g == M.ONE for g in lets):
            say("== %s == (not filled in)" % tag)
            continue
        hits[tag] = report(tag, list(lets))
        if tag == "ORTH":
            orth_extra(list(lets))
    say("failures: %s" % (FAILURES if FAILURES else "none"))
    with open("results/points_sharp5.txt", "w") as fh:
        fh.write("\n".join(OUT) + "\n")
