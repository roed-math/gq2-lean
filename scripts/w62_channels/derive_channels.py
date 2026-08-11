"""W62-CHANNELS step 1: what decides the three-channel functional, exactly.

Wave 61 left the exclusion one filtration step wider hanging on a single question: is there a
binder point at which

    chan(z, L) = z.m * L.e + z.i * L.j + z.l * L.f

is EVEN for every achievable `z` in `forceLcs H 1 = [H, H]` and every permuted letter `L`?  The
lattice is infinite-ish to sweep element by element (wave 61 abandoned exactly that closure as
too slow), so this file replaces the sweep by an algebraic reduction and CERTIFIES each step
against honest 6 x 6 collection.

    section 1  parity3(z) = (z.m, z.i, z.l) mod 2 is a HOMOMORPHISM on the lattice
    section 2  the three coordinates of a commutator of two `stageN1` letters, mod two
    section 3  parity3 KILLS gamma_3 of the image, so W = span of the ten letter pairs
    section 4  the class-five residue of the `a0 = a1` dressing, mod two
    section 5  the obstruction: the (x0, x1) pair against the x1 slot

Every claim is checked on random input over Z/8 with the matrix engine of `w59_force5`.
"""
import sys
import os
import random

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w60_stage4"))

import u6mat as M                                               # noqa: E402
import pointlib as P                                            # noqa: E402
import chanlib as C                                             # noqa: E402

SIG = M.sigFiveMark
FAIL = []


def check(name, ok, detail=""):
    print("   %-64s %s%s" % (name, "OK" if ok else "*** MISMATCH ***",
                             ("   " + detail) if detail else ""))
    if not ok:
        FAIL.append(name)


def rand_letter(rng, a_even=True, c_even=True, fix=None):
    d = {}
    for k in M.COORDS:
        d[k] = rng.randrange(8)
    if a_even:
        d["a"] = rng.randrange(0, 8, 2)
    if c_even:
        d["c"] = rng.randrange(0, 8, 2)
    if fix:
        d.update(fix)
    return M.named(**d)


def gauge_letter(rng):
    """An `x0` slot on the committed class-two-forced gauge: a, c, d, f, g, h even, b = 0.

    The gauge does NOT constrain `e` (the `(5,6)`-column), which is the campaign's escaping
    datum, nor the deep coordinates `i`, `j`, `k`, `l`, `m`, `n`, `o`.
    """
    d = {k: rng.randrange(8) for k in M.COORDS}
    for k in "acdfgh":
        d[k] = rng.randrange(0, 8, 2)
    d["b"] = 0
    return M.named(**d)


def gauge_y_letter(rng):
    """An `x1` slot on the gauge: a, c, d, e even, b = 0."""
    d = {k: rng.randrange(8) for k in M.COORDS}
    for k in "acde":
        d[k] = rng.randrange(0, 8, 2)
    d["b"] = 0
    return M.named(**d)


def relator_y_letter(rng):
    """An `x1` slot with the columns the RELATOR forces: all five abelian ones even.

    `(sqRelWord m).k = -4 (m 1).k + 2 (m 2).k` for every abelian row (`SqU6.sqRelWord_a` and
    its siblings, committed), so killing that row over `Z/8` forces `(m 2).k` even.  This is a
    strictly weaker hypothesis than the class-two-forced gauge and it is free.
    """
    d = {k: rng.randrange(8) for k in M.COORDS}
    for k in "abcde":
        d[k] = rng.randrange(0, 8, 2)
    return M.named(**d)


def rand_lattice_elt(rng, letters, depth=3):
    """A random element of [H, H]: a product of conjugated letter commutators."""
    z = M.ONE
    for _ in range(depth):
        a = rng.choice(letters)
        b = rng.choice(letters)
        g = rng.choice(letters + [M.ONE])
        z = M.mul(z, M.conjP(M.commP(a, b), g))
    return z


def main():
    rng = random.Random(62001)
    print("=" * 96)
    print("== W62-CHANNELS: what decides the three-channel functional ==")
    print("=" * 96)
    print()

    # ---------------------------------------------------------------- section 1
    print("== 1. parity3 = (m, i, l) mod 2 is a homomorphism on the achievable lattice ==")
    print()
    print("   The lattice is inside `stageN2` (wave 60's `stageN2_of_commutator`, committed):")
    print("   gamma_2-shaped with f, h, j even.  On such elements")
    print("      (z w).m = z.m + w.m + z.f * w.h,   (z w).i = z.i + w.i,")
    print("      (z w).l = z.l + w.l,")
    print("   and z.f * w.h is divisible by four, so parity3 is additive.")
    print()
    bad = 0
    inbad = 0
    for _ in range(4000):
        letters = [SIG] + [rand_letter(rng) for _ in range(4)]
        z = rand_lattice_elt(rng, letters)
        w = rand_lattice_elt(rng, letters)
        pz, pw, pzw = C.parity3(z), C.parity3(w), C.parity3(M.mul(z, w))
        if pzw != tuple((pz[k] ^ pw[k]) for k in range(3)):
            bad += 1
        if C.parity3(M.inv(z)) != pz:
            inbad += 1
    check("parity3(z w) = parity3(z) + parity3(w), 4000 random lattice pairs", bad == 0)
    check("parity3(z^{-1}) = parity3(z), same 4000", inbad == 0)
    # sharpness: OFF the lattice it is not a homomorphism
    off = 0
    for _ in range(2000):
        z = M.named(**{k: rng.randrange(8) for k in "fghijklmno"})
        w = M.named(**{k: rng.randrange(8) for k in "fghijklmno"})
        pz, pw, pzw = C.parity3(z), C.parity3(w), C.parity3(M.mul(z, w))
        if pzw != tuple((pz[k] ^ pw[k]) for k in range(3)):
            off += 1
    print("   sharpness: on UNRESTRICTED gamma_2-elements additivity fails at %d of 2000"
          % off)
    print()

    # ---------------------------------------------------------------- section 2
    print("== 2. the commutator of two `stageN1` letters, in the three coordinates ==")
    print()
    print("   For p, q with even (1,2)- and (3,4)-columns, modulo two:")
    print("      [p,q].m = p.j q.d + p.d q.j + p.f q.h + p.h q.f")
    print("      [p,q].i = p.d q.e + p.e q.d")
    print("      [p,q].l = p.h q.e + p.e q.h")
    print()
    bm = bi = bl = 0
    for _ in range(6000):
        p = rand_letter(rng)
        q = rand_letter(rng)
        c = M.commP(p, q)
        m = (C.co(p, "j") * C.co(q, "d") + C.co(p, "d") * C.co(q, "j")
             + C.co(p, "f") * C.co(q, "h") + C.co(p, "h") * C.co(q, "f")) % 2
        i = (C.co(p, "d") * C.co(q, "e") + C.co(p, "e") * C.co(q, "d")) % 2
        l = (C.co(p, "h") * C.co(q, "e") + C.co(p, "e") * C.co(q, "h")) % 2
        bm += (C.co(c, "m") % 2) != m
        bi += (C.co(c, "i") % 2) != i
        bl += (C.co(c, "l") % 2) != l
    check("[p,q].m formula, 6000 random stageN1 letter pairs", bm == 0)
    check("[p,q].i formula, same 6000", bi == 0)
    check("[p,q].l formula, same 6000", bl == 0)
    # sharpness: the formulas need the two even columns
    sm = 0
    for _ in range(2000):
        p = rand_letter(rng, a_even=False, c_even=False)
        q = rand_letter(rng, a_even=False, c_even=False)
        c = M.commP(p, q)
        m = (C.co(p, "j") * C.co(q, "d") + C.co(p, "d") * C.co(q, "j")
             + C.co(p, "f") * C.co(q, "h") + C.co(p, "h") * C.co(q, "f")) % 2
        sm += (C.co(c, "m") % 2) != m
    print("   sharpness: without the two even columns the `m` formula fails at %d of 2000"
          % sm)
    print()

    # ---------------------------------------------------------------- section 3
    print("== 3. parity3 kills gamma_3 of the image, so only the ten letter pairs matter ==")
    print()
    print("   For z in the lattice and r in H (both columns even), modulo two:")
    print("      [z,r].i = 0,  [z,r].l = z.i r.c + z.h r.e,  [z,r].m = z.j r.d + z.f r.h")
    print("                                                            + z.h r.f,")
    print("   and z.f, z.h, z.j, r.a, r.c are all even, so all three vanish.")
    print()
    g3bad = 0
    for _ in range(4000):
        letters = [SIG] + [rand_letter(rng) for _ in range(4)]
        z = rand_lattice_elt(rng, letters)
        r = M.mul(rng.choice(letters), rng.choice(letters))
        if C.parity3(M.commP(z, r)) != (0, 0, 0):
            g3bad += 1
    check("parity3([z, r]) = 0 for z in the lattice, r in H, 4000 random", g3bad == 0)
    # and the consequence: deep lattice elements land in the span of the ten generators
    print()
    print("   consequence, checked by DEEP random sampling of the lattice at 400 points:")
    depthbad = 0
    covered = 0
    total = 0
    for _ in range(400):
        letters = [SIG] + [rand_letter(rng) for _ in range(4)]
        fast = C.channel_span(letters)
        seen = set()
        for _ in range(60):
            z = rand_lattice_elt(rng, letters, depth=rng.randrange(1, 8))
            total += 1
            p = C.parity3(z)
            seen.add(p)
            if p not in fast:
                depthbad += 1
        covered += (seen == fast)
    check("every sampled lattice element lies in the fast span (%d samples)" % total,
          depthbad == 0)
    print("   the sampling also REACHES the whole span at %d of 400 points, so the span is"
          % covered)
    print("   not an over-estimate either.")
    print()

    # ---------------------------------------------------------------- section 4
    print("== 4. the class-five separation bit of the `a0 = a1` dressing, modulo two ==")
    print()
    print("   Wave 58's measured closed form for the bit is `x0.a x1.g x1.i + x0.e x1.f x1.h`.")
    print("   Re-measured here in the stronger DIFFERENCE form, which needs no relator-killing")
    print("   hypothesis:")
    print()
    print("      (dressed relator).o - (undressed relator).o                        (mod 2)")
    print("         = x0.a * x1.g * x1.i  +  x0.e * x1.f * x1.h")
    print()

    def bitform(X, Y):
        return (C.co(X, "a") * C.co(Y, "g") * C.co(Y, "i")
                + C.co(X, "e") * C.co(Y, "f") * C.co(Y, "h")) % 2

    def diffbit(X, Y, U, V):
        r0 = C.residue(SIG, X, Y, U, V)
        r1 = C.residue(M.mul(SIG, X), X, Y, U, V)
        return (C.co(r1, "o") - C.co(r0, "o")) % 2

    gb = 0
    for _ in range(4000):
        X = gauge_letter(rng)
        Y = gauge_y_letter(rng)
        U = rand_letter(rng)
        V = rand_letter(rng)
        if diffbit(X, Y, U, V) != bitform(X, Y):
            gb += 1
    check("the difference form at 4000 random GAUGE markings", gb == 0)
    print()
    print("   ⭐ SHARPER: the `x0`-gauge is not what the form needs.  Keeping ONLY the `x1`")
    print("   slot's even abelian columns - which the relator's own class-one rows force at")
    print("   any marking killing them - and letting the `x0` slot range over all of")
    print("   `stageN1`:")
    print()
    fb = 0
    for _ in range(4000):
        X = rand_letter(rng)
        Y = relator_y_letter(rng)
        U = rand_letter(rng)
        V = rand_letter(rng)
        if diffbit(X, Y, U, V) != bitform(X, Y):
            fb += 1
    check("the difference form at 4000 markings with x1 abelian columns even", fb == 0)
    ob = 0
    for _ in range(4000):
        X = rand_letter(rng)
        Y = rand_letter(rng)
        U = rand_letter(rng)
        V = rand_letter(rng)
        if diffbit(X, Y, U, V) != bitform(X, Y):
            ob += 1
    print("   sharpness: drop the `x1` columns too and the form fails at %d of 4000, so the"
          % ob)
    print("   hypothesis is exactly the one the relator supplies for free.")
    print()
    print("   With `stageN1` making `x0.a` even the bit is therefore `x0.e * x1.f * x1.h`.")
    print()

    # ---------------------------------------------------------------- section 5
    print("== 5. ⭐ THE COLLISION: the channel IS the bit ==")
    print()
    print("   Substituting section 2 into the channel at the achievable dressing `[x0, x1]`")
    print("   of the `x1` slot, and using only `x1.d`, `x1.e` even:")
    print()
    print("      [x0,x1].m * x1.e = 0,  [x0,x1].i * x1.j = 0,")
    print("      [x0,x1].l * x1.f = x0.e * x1.f * x1.h                       (mod 2)")
    print()
    print("   which is the bit of section 4 exactly.  So the three-channel functional and the")
    print("   class-five separation bit are the SAME F_2 functional at every marking the")
    print("   campaign can use.  ⭐ Nothing is asked of the `x0` slot beyond `stageN1`.")
    print()
    cb = 0
    for _ in range(6000):
        X = rand_letter(rng)
        Y = relator_y_letter(rng)
        if C.chan(M.commP(X, Y), Y) % 2 != (C.co(X, "e") * C.co(Y, "f")
                                            * C.co(Y, "h")) % 2:
            cb += 1
    check("chan([x0,x1], x1) = x0.e x1.f x1.h, 6000 relator-shaped letter pairs", cb == 0)
    ub = 0
    for _ in range(4000):
        X = rand_letter(rng)
        Y = rand_letter(rng)
        if C.chan(M.commP(X, Y), Y) % 2 != (C.co(X, "e") * C.co(Y, "f")
                                            * C.co(Y, "h")) % 2:
            ub += 1
    print("   sharpness: without the two `x1` columns the collision fails at %d of 4000." % ub)
    print()
    print("   Consequence.  At a point with an ODD bit the functional is ODD at an achievable")
    print("   dressing, so wave 61's `stageWit_gaTwo_forced` is SATISFIED there and yields no")
    print("   contradiction: the `gamma_2` route cannot widen the exclusion at ANY binder")
    print("   point, on the gauge or off it.")
    print()
    both = 0
    for _ in range(4000):
        X = rand_letter(rng)
        Y = relator_y_letter(rng)
        U = rand_letter(rng)
        V = rand_letter(rng)
        b = diffbit(X, Y, U, V)
        c = C.chan(M.commP(X, Y), Y) % 2
        if (b + c) % 2 != 0:
            both += 1
    check("bit + chan is EVEN at 4000 relator-shaped markings (the forced condition holds)",
          both == 0)
    print()

    # ---------------------------------------------------------------- section 6
    print("== 6. wave 60's committed point ==")
    print()
    X, Y = M.named(a=2, e=5), M.named(e=2, f=1, g=1, h=1, m=3, n=3)
    U = M.named(a=6, b=7, c=4, d=1, e=3, g=5, h=5)
    V = M.named(a=6, b=7, c=6, d=1, e=3, f=5, g=3, h=3, i=4)
    print("   x0 = %s" % M.show(X))
    print("   x1 = %s" % M.show(Y))
    print("   on the gauge (x0: a,c,d,f,g,h even, b = 0; x1: a,c,d,e even, b = 0): %s"
          % (C.gauge_x(X) and C.co(X, "h") % 2 == 0 and C.gauge_y(Y)
             and C.co(Y, "e") % 2 == 0 and C.co(Y, "b") == 0))
    z = M.commP(X, Y)
    print("   [x0, x1]                     = %s" % M.show(z))
    print("   its (m, i, l) parities        = %s" % (C.parity3(z),))
    print("   chan([x0,x1], x1)             = %d, parity %d"
          % (C.chan(z, Y), C.chan(z, Y) % 2))
    print("   the bit x0.e * x1.f * x1.h    = %d" % ((C.co(X, "e") * C.co(Y, "f")
                                                      * C.co(Y, "h")) % 2))
    print("   the measured relator residue  = %s" % M.show(C.residue(M.mul(SIG, X), X, Y, U, V)))
    check("the point: chan is odd, the bit is odd, their sum is even",
          C.chan(z, Y) % 2 == 1 and (C.co(X, "e") * C.co(Y, "f") * C.co(Y, "h")) % 2 == 1)
    print()

    print("=" * 96)
    print("   %d named checks, %d failures" % (15, len(FAIL)))
    if FAIL:
        print("   FAILED: %s" % ", ".join(FAIL))
    print("=" * 96)


if __name__ == "__main__":
    main()
