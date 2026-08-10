"""W59-FORCE5 step 1: everything the Lean file will claim, measured first and independently.

Sections
  0. the independent matrix library `u6mat` agrees with wave 58's coordinate library on
     random input; every load-bearing verdict below is taken with `u6mat`, and only the
     large closures (a cross-check, not a load-bearing input) use the faster wave-58 one;
  1. the section-3.2 point: both relator values, at every handle count and every handle,
     and the triviality of both U_5-quotients at both dressings;
  2. the achievable lattices, computed TWICE: structurally (pairings of the previous level
     against the letters' abelian columns) and by honest closure of the image subgroup's
     lower central series.  The two must agree;
  3. the class-five translation identity of the five-slot refinement, against honest
     collection;
  4. the exclusion sweep: no achievable five-slot refinement kills the dressed relator, and
     unrestricted ones do, so achievability is load-bearing;
  5. sharpness: the achievable gamma_4-lattice is EXACTLY the even lattice, so the Lean
     span is neither too small (the forcing would be vacuous) nor too large;
  6. cross-checks against wave 58's measured closed form and against the class-four files.
"""
import sys
import os
import random

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w58_sigma5"))

import u6mat as M                                             # noqa: E402
import u6lib as W58                                           # noqa: E402

fails = 0
checks = 0


def check(name, got, want=True):
    global fails, checks
    checks += 1
    ok = (got == want)
    if not ok:
        fails += 1
    print(("PASS " if ok else "FAIL ") + name + ("" if ok else "   got %s want %s" % (got, want)))


def note(s):
    print("   " + s)


# =========================================================================================
print("== 0. the independent library agrees with wave 58's ==")
random.seed(59001)
bad = 0
cmp = 0
for _ in range(1500):
    p = tuple(random.randrange(8) for _ in range(15))
    q = tuple(random.randrange(8) for _ in range(15))
    for got, want in ((M.mul(p, q), W58.mul(p, q)), (M.inv(p), W58.inv(p)),
                      (M.commP(p, q), W58.commP(p, q)), (M.conjP(p, q), W58.conjP(p, q)),
                      (M.sqWord(p, q, M.mul(p, q)), W58.sqWord(p, q, W58.mul(p, q))),
                      (M.sqRelWord([p, q, M.mul(p, q), q, p]),
                       W58.sqRelWord([p, q, W58.mul(p, q), q, p]))):
        cmp += 1
        if got != want:
            bad += 1
check("%d comparisons of mul / inv / commP / conjP / sqWord / sqRelWord: 0 mismatches" % cmp,
      bad, 0)
note("`u6mat` builds the group law from honest 6 x 6 matrices and inverts by back")
note("substitution; wave 58's `u6lib` uses the coordinate formula and a Neumann series.")

# =========================================================================================
print()
print("== 1. the section-3.2 point ==")
sigma, X, Y, U, V = M.sigFiveMark, M.sepX, M.sepY, M.sepU, M.sepV
note("sigma = %s" % M.show(sigma))
note("U     = %s" % M.show(U))
note("V     = %s" % M.show(V))
note("x0    = %s" % M.show(X))
note("x1    = %s" % M.show(Y))
note("[U,V] = %s" % M.show(M.commP(U, V)))

undressed = [sigma, X, Y, U, V]
dressed = [M.mul(sigma, X), X, Y, U, V]
check("sqRelWord(undressed) = 1                            (h = 1)", M.sqRelWord(undressed), M.ONE)
check("sqRelWord(a0 = a1 dressed) = liftC 7                (h = 1)",
      M.sqRelWord(dressed), M.liftC(7))

allh = []
for h in range(1, 5):
    for j in range(h):
        allh.append(M.sqRelWord(M.mirTuple(h, j, sigma, X, Y, U, V)) == M.ONE and
                    M.sqRelWord(M.mirTuple(h, j, M.mul(sigma, X), X, Y, U, V)) == M.liftC(7))
check("both verdicts hold at every handle count h = 1..4 and every handle (%d cases)"
      % len(allh), all(allh))

check("the handle block is LIVE", M.commP(U, V) != M.ONE)
check("...and live in the x15 row: [U,V].m is ODD", M.commP(U, V)[12] % 2, 1)

for nm, m in (("undressed", undressed), ("dressed  ", dressed)):
    r = M.sqRelWord(m)
    check("toU5L(sqRelWord(%s)) = 1   (the left class-four quotient)" % nm,
          M.toU5L(r), (0,) * 10)
    check("toU5R(sqRelWord(%s)) = 1   (the right class-four quotient)" % nm,
          M.toU5R(r), (0,) * 10)
note("so the whole committed class-<=4 machinery reads BOTH dressings as trivial.")

note("gauge audit of the class-two-forced gauge (GradedSigmaFour.sigFourRead_gauge):")
note("  x0 abelian columns (x12, x34, x45) = (%d, %d, %d);  nu'-column x23 = %d"
     % (X[0], X[2], X[3], X[1]))
note("  x0 lower class-two (x13, x24) = (%d, %d);  x1 abelian (y12, y34, y45) = (%d, %d, %d)"
     % (X[5], X[6], Y[0], Y[2], Y[3]))
note("  the ONE odd datum: x0's fifth abelian column x56 = %d" % X[4])
check("every datum the committed gauge constrains is even, and x56 is odd",
      all(v % 2 == 0 for v in (X[0], X[2], X[3], X[5], X[6], Y[0], Y[2], Y[3]))
      and X[1] == 0 and X[4] % 2 == 1)

# =========================================================================================
print()
print("== 2. the achievable lattices, two independent ways ==")


def span(vecs, dim):
    """The subgroup of (Z/8)^dim generated by `vecs`."""
    seen = {(0,) * dim}
    frontier = [(0,) * dim]
    gens = sorted({v for v in vecs if any(v)})
    while frontier:
        nxt = []
        for p in frontier:
            for g in gens:
                q = tuple((p[k] + g[k]) % 8 for k in range(dim))
                if q not in seen:
                    seen.add(q)
                    nxt.append(q)
        frontier = nxt
    return seen


letters = [sigma, X, Y, U, V]
abel = [(g[0], g[1], g[2], g[3], g[4]) for g in letters]      # (a, b, c, d, e)
note("the letters' abelian columns (a, b, c, d, e):")
for nm, v in zip(("sigma", "x0", "x1", "U", "V"), abel):
    note("  %-5s = %s" % (nm, v))


def pair2(p, q):
    """(f, g, h, i) of [p, q], for elements with abelian columns p and q."""
    return ((p[0] * q[1] - p[1] * q[0]) % 8, (p[1] * q[2] - p[2] * q[1]) % 8,
            (p[2] * q[3] - p[3] * q[2]) % 8, (p[3] * q[4] - p[4] * q[3]) % 8)


def pair3(w, v):
    """(j, k, l) of [z, g] for z in gamma_2 with (f,g,h,i) = w and g with abelian columns v."""
    return ((-w[1] * v[0] + w[0] * v[2]) % 8, (-w[2] * v[1] + w[1] * v[3]) % 8,
            (-w[3] * v[2] + w[2] * v[4]) % 8)


def pair4(z, v):
    """(m, n) of [z, g] for z in gamma_3 with (j,k,l) = z and g with abelian columns v."""
    return ((z[0] * v[3] - z[1] * v[0]) % 8, (z[1] * v[4] - z[2] * v[1]) % 8)


A = span(abel, 5)
L2 = span([pair2(p, q) for p in abel for q in abel], 4)
L3 = span([pair3(w, v) for w in L2 for v in abel], 3)
L4 = span([pair4(z, v) for z in L3 for v in abel], 2)
note("structural:  |A| = %d, |Lam2| = %d, |Lam3| = %d, |Lam4| = %d"
     % (len(A), len(L2), len(L3), len(L4)))


def subgroup(seeds, conj_gens, mul=W58.mul, conjP=W58.conjP, inv=W58.inv):
    """The smallest conjugation-closed subgroup containing `seeds`, by greedy generators."""
    seen = {M.ONE}
    gens = []
    for s in sorted({t for t in seeds if t != M.ONE}):
        if s in seen:
            continue
        gens.append(s)
        gens.append(inv(s))
        changed = True
        while changed:
            changed = False
            for p in list(seen):
                for g in gens:
                    q = mul(p, g)
                    if q not in seen:
                        seen.add(q)
                        changed = True
                for c in conj_gens:
                    q = conjP(p, c)
                    if q not in seen:
                        seen.add(q)
                        changed = True
    return seen


g3 = subgroup([W58.commP(W58.commP(a, b), c)
               for a in letters for b in letters for c in letters], letters)
g4 = subgroup([W58.commP(z, g) for z in g3 for g in letters], letters)
g5 = subgroup([W58.commP(z, g) for z in g4 for g in letters], letters)
note("closure:     |gamma_3| = %d, |gamma_4| = %d, |gamma_5| = %d"
     % (len(g3), len(g4), len(g5)))
note("(gamma_2 of the image is far too large to enumerate; wave 58 did not either.")
note(" its (f,g,h,i)-lattice is checked by sampling instead.)")

random.seed(59004)
bad = 0
hit = set()
for _ in range(3000):
    def word():
        p = M.ONE
        for _ in range(random.randrange(1, 5)):
            p = W58.mul(p, random.choice(letters))
        return p
    z = W58.commP(word(), word())
    t = (z[5], z[6], z[7], z[8])
    hit.add(t)
    if t not in L2:
        bad += 1
check("3000 sampled commutators of image elements land in the structural Lam2", bad, 0)
check("the two computations of the gamma_3 (j,k,l)-lattice agree",
      {(z[9], z[10], z[11]) for z in g3}, L3)
check("* the two computations of the gamma_4 (m,n)-lattice agree",
      {(z[12], z[13]) for z in g4}, L4)

check("every achievable gamma_3-dressing has EVEN (x14, x25, x36)",
      sorted({(z[0] % 2, z[1] % 2, z[2] % 2) for z in L3}), [(0, 0, 0)])
check("** every achievable gamma_4-dressing has EVEN (x15, x26)",
      sorted({(z[0] % 2, z[1] % 2) for z in L4}), [(0, 0)])
check("every achievable gamma_5-dressing has EVEN x16",
      sorted({z[14] % 2 for z in g5}), [0])

note("")
note("THE GENERATORS THE LEAN SPANS WILL CARRY")
g2gens = sorted({pair2(p, q) for p in abel for q in abel} - {(0, 0, 0, 0)})
note("Lam2, as pairings of the letters' abelian columns:")
for p, q in [(i, j) for i in range(5) for j in range(5) if i < j]:
    nm = ("sigma", "x0", "x1", "U", "V")
    v = pair2(abel[p], abel[q])
    if any(v):
        note("  [%-5s, %-5s] -> (f,g,h,i) = %s" % (nm[p], nm[q], v))
note("Lam2 = span of the %d nonzero pairings; every element:  %s"
     % (len(g2gens), "f,g,h,i all even" if all(all(c % 2 == 0 for c in t) for t in L2)
        else "NOT all even"))
note("Lam3, as pairings of Lam2 against the letters:")
seen3 = set()
for w in sorted(L2):
    for nmv, v in zip(("sigma", "x0", "x1", "U", "V"), abel):
        t = pair3(w, v)
        if any(t):
            seen3.add(t)
note("  %d distinct nonzero (j,k,l)-generators; all even: %s"
     % (len(seen3), all(all(c % 2 == 0 for c in t) for t in seen3)))
note("Lam4, as pairings of Lam3 against the letters, by letter:")
for nmv, v in zip(("sigma", "x0", "x1", "U", "V"), abel):
    gs = sorted({pair4(z, v) for z in L3})
    note("  %-5s : span %s ... (%d distinct), all even = %s"
         % (nmv, sorted(gs)[:6], len(gs), all(a % 2 == 0 and b % 2 == 0 for (a, b) in gs)))
note("Lam3 as a set: %s" % (sorted(L3) if len(L3) <= 40 else "%d elements" % len(L3)))
note("Lam4 as a set: %s" % (sorted(L4) if len(L4) <= 40 else "%d elements" % len(L4)))
note("Lam2 as a set: %s" % (sorted(L2) if len(L2) <= 40 else "%d elements" % len(L2)))

# =========================================================================================
print()
print("== 3. the class-five translation identity of the five-slot refinement ==")
random.seed(59002)
bad = 0
tot = 0
for _ in range(1200):
    def ga4():
        return M.named(m=random.randrange(8), n=random.randrange(8), o=random.randrange(8))

    def ga5():
        return M.named(o=random.randrange(8))
    z0, w1, w2, z3, z4 = ga4(), ga5(), ga5(), ga4(), ga4()
    for h in (1, 2):
        for j in range(h):
            m = M.mirTuple(h, j, sigma, X, Y, U, V)
            mm = list(m)
            mm[0] = M.mul(mm[0], z0)
            mm[1] = M.mul(mm[1], w1)
            mm[2] = M.mul(mm[2], w2)
            mm[3 + 2 * j] = M.mul(mm[3 + 2 * j], z3)
            mm[4 + 2 * j] = M.mul(mm[4 + 2 * j], z4)
            inc = (z0[12] * m[1][4] - z0[13] * m[1][0]
                   + (-4 * w1[14] + 2 * w2[14])
                   + (z3[12] * m[4 + 2 * j][4] - z3[13] * m[4 + 2 * j][0])
                   + (m[3 + 2 * j][0] * z4[13] - m[3 + 2 * j][4] * z4[12])) % 8
            tot += 1
            if M.sqRelWord(mm) != M.mul(M.sqRelWord(m), M.liftC(inc)):
                bad += 1
check("the identity holds at %d refinements (h = 1, 2, every handle)" % tot, bad, 0)
note("increment = (z0.m*x0.e - z0.n*x0.a) + (-4*w1.o + 2*w2.o)")
note("          + (z3.m*V.e - z3.n*V.a) + (U.a*z4.n - U.e*z4.m)")
random.seed(59012)
bad = 0
tot = 0
for _ in range(400):
    m = [tuple(random.randrange(8) for _ in range(15)) for _ in range(5)]
    z0 = M.named(m=random.randrange(8), n=random.randrange(8), o=random.randrange(8))
    z3 = M.named(m=random.randrange(8), n=random.randrange(8), o=random.randrange(8))
    z4 = M.named(m=random.randrange(8), n=random.randrange(8), o=random.randrange(8))
    w1 = M.named(o=random.randrange(8))
    w2 = M.named(o=random.randrange(8))
    mm = [M.mul(m[0], z0), M.mul(m[1], w1), M.mul(m[2], w2),
          M.mul(m[3], z3), M.mul(m[4], z4)]
    inc = (z0[12] * m[1][4] - z0[13] * m[1][0] + (-4 * w1[14] + 2 * w2[14])
           + (z3[12] * m[4][4] - z3[13] * m[4][0])
           + (m[3][0] * z4[13] - m[3][4] * z4[12])) % 8
    tot += 1
    if M.sqRelWord(mm) != M.mul(M.sqRelWord(m), M.liftC(inc)):
        bad += 1
check("...and at %d RANDOM markings, not just the witness point" % tot, bad, 0)

# =========================================================================================
print()
print("== 4. the exclusion: no ACHIEVABLE refinement kills the dressed relator ==")
base = dressed
G4 = sorted(g4)
G5 = sorted(g5)
flip = 0
tot = 0
for i in range(5):
    for z in (G4 if i in (0, 3, 4) else G5):
        m = list(base)
        m[i] = M.mul(m[i], z)
        tot += 1
        if M.sqRelWord(m)[14] % 2 != 1:
            flip += 1
check("%d single-slot ACHIEVABLE refinements: the class-five residue stays ODD" % tot, flip, 0)
random.seed(59003)
flip = 0
tot = 0
for _ in range(4000):
    m = list(base)
    for i in range(5):
        m[i] = M.mul(m[i], random.choice(G4) if i in (0, 3, 4) else random.choice(G5))
    tot += 1
    if M.sqRelWord(m)[14] % 2 != 1:
        flip += 1
check("%d random FIVE-SLOT achievable refinements: residue stays ODD (never 0)" % tot, flip, 0)
uf = 0
ut = 0
for a in range(8):
    for b in range(8):
        z = M.named(m=a, n=b)
        for i in (0, 3, 4):
            mm = list(base)
            mm[i] = M.mul(mm[i], z)
            ut += 1
            if M.sqRelWord(mm)[14] % 2 != 1:
                uf += 1
note("UNRESTRICTED gamma_4 moves: %d of %d flip the parity" % (uf, ut))
check("achievability is load-bearing: some unrestricted move DOES flip it", uf > 0)

note("")
note("SCOPE PROBES: the Lean theorem dresses the sigma and handle slots by achievable")
note("gamma_4-elements and the two exponent slots by achievable gamma_5-elements, exactly as")
note("`GradedSigmaFour.sigFourWit_sigma_forced` does one class down.  Two wider classes of")
note("refinement are measured here; the first is harmless and the SECOND IS NOT.")
kill4 = 0
tot4 = 0
for i in range(5):
    for z in G4:
        m = list(base)
        m[i] = W58.mul(m[i], z)
        tot4 += 1
        if W58.sqRelWord(m) == M.ONE:
            kill4 += 1
check("   gamma_4 dressings on ALL FIVE slots (%d single-slot moves): none kills the frame"
      % tot4, kill4, 0)
G3 = sorted(g3)
kill3 = 0
tot3 = 0
par3 = 0
for i in range(5):
    for z in G3:
        m = list(base)
        m[i] = W58.mul(m[i], z)
        tot3 += 1
        r = W58.sqRelWord(m)
        if r == M.ONE:
            kill3 += 1
        if r[14] % 2 == 0:
            par3 += 1
check("⚠⚠ achievable gamma_3 dressings (%d single-slot moves): %d DO kill the frame"
      % (tot3, kill3), kill3, 1280)
note("   ...and %d of them make the class-five residue even." % par3)
note("   THE FINDING: gamma_3 of the image contains the WHOLE of gamma_4 of the carrier here,")
note("   so it contains gamma_4-shaped dressings with an ODD class-four coordinate - exactly")
note("   the ones gamma_4 of the image excludes.  The exclusion therefore holds for the")
note("   stage-five refinement class and not one filtration step wider.  `scope_probe.py`")
note("   locates the killers slot by slot and checks the committed class-four point for the")
note("   same phenomenon (it does NOT have it); `gamma3_witness.py` produces the short word")
note("   `[[sigma, U], x1] = <m=5, n=6>`, which the Lean file carries as `fiveWit_gaThree_kill`.")

# =========================================================================================
print()
print("== 5. sharpness of the achievable gamma_4-lattice ==")
even2 = {(2 * a % 8, 2 * b % 8) for a in range(8) for b in range(8)}
check("* Lam4 is EXACTLY the even lattice {(2a, 2b)}: neither too small nor too large",
      L4, even2)
note("so the Lean span is the sharpest bound the tree owns at this point: it contains every")
note("achievable move (nothing is excluded by fiat) and every element of it is even.")

# =========================================================================================
print()
print("== 6. cross-checks ==")
form = (X[0] * Y[6] * Y[8] + X[4] * Y[5] * Y[7]) % 2
check("wave 58's closed form x12*y24*y46 + x56*y13*y35 = %d is ODD, matching the residue 7"
      % form, form, M.sqRelWord(dressed)[14] % 2)
sfH = (X[0] * (X[6] - X[2]) - X[2] * (X[0] + X[5]) + X[5] * X[2] - X[6] * X[0]) % 8
note("sigFourH(x0, x0) = %d (even, as GradedSigmaFive.sigFourH_diag says: -2*x.a*x.c)" % sfH)
check("the coupling coefficient sigFourH is even on the diagonal here", sfH % 2, 0)
check("the block's (4,6) coordinate H_46 = [U,V].i is EVEN (wave 58 section 4.2)",
      M.commP(U, V)[8] % 2, 0)
check("the class-four rows of BOTH relators vanish (m and n)",
      (M.sqRelWord(undressed)[12], M.sqRelWord(undressed)[13],
       M.sqRelWord(dressed)[12], M.sqRelWord(dressed)[13]), (0, 0, 0, 0))

print()
print("TOTAL CHECKS: %d   FAILURES: %d" % (checks, fails))
sys.exit(1 if fails else 0)
