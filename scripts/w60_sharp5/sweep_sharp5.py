"""W60-SHARP5: the class-five census.

Is `GradedFiveForce`'s soundness condition NECESSARY?  The lane's brief says compute first, so
this is the computation.  Wave 59 answered the class-four version of the question with a
6932-marking census (`scripts/w59_invariant/results/sweep_necessity.txt`); this is its
class-five transposition.

An ADMISSIBLE marking is a one-handle-live five-tuple `(S, X, Y, U, V)` whose relator is a
CENTRAL translation with an ODD class-five residue: exactly the situation in which the
class-five sigma forcing has content, and the class-five form of wave 59's `hres` + `hva`.
The x1-slot is produced by the layered solve of `sharp5lib`, so a perturbed set of letters is
pushed back onto an admissible marking rather than discarded.

At each admissible marking four verdicts are compared:

  SHARP    all three mod-2 covectors `(slot.e, slot.a)` annihilate the achievable
           `gamma_4`-dressings' `(m, n)`-lattice                       [the proposed line]
  W59-HYP  every slot has an even `(3,4)`-column (`forceN1`)          [what wave 59 carries]
  W59-CONS every achievable `gamma_4`-dressing is even (`forceN4`)    [what wave 59 proves]
  KILL     an INDEPENDENT search over achievable refinements, evaluated through the honest
           group law, finds one that kills the relator

The claim under test is `SHARP <-> not KILL`, and the question the wave asked is how many
markings have `not W59-CONS` (or `not W59-HYP`) together with `not KILL`.

BRACKET CONVENTION.  [NONE]
This script computes no commutators, so the convention does not arise.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

import itertools
import random
import sys
import time

import sharp5lib as L                                                # noqa: I100
import fastu6 as FU                                                  # noqa: E402
import u6mat as M                                                    # noqa: E402

OUT = []


def say(s=""):
    print(s)
    OUT.append(s)


def check(name, got, want=True):
    ok = (got == want)
    say("  [%s] %s%s" % ("PASS" if ok else "FAIL", name,
                         "" if ok else "   got %r want %r" % (got, want)))
    return ok


FAILURES = []


def gate(name, got, want=True):
    if not check(name, got, want):
        FAILURES.append(name)


# =========================================================================================
def section0():
    say("== 0. the two libraries, and the lattice engine ==")
    bad, tot = FU.crosscheck(4000)
    gate("the fast product agrees with u6mat's honest 6x6 matrices (%d comparisons)" % tot,
         bad, 0)
    S = M.mul(M.sigFiveMark, M.sepX)
    lets = [S, M.sepX, M.sepY, M.sepU, M.sepV]
    fast = L.lattices(lets)
    slow = L.lattices_slow(lets)
    gate("the lattice engine agrees with wave 59's (spanning over the whole abelian image)",
         [sorted(x) for x in fast], [sorted(x) for x in slow])
    g3, g4 = L.gamma34(lets)
    gate("|gamma_3| of the witness image = 16384 (wave 59's figure)", len(g3), 16384)
    gate("|gamma_4| of the witness image = 128 (wave 59's figure)", len(g4), 128)
    gate("the honest gamma_3 (j,k,l)-image is the computed Lam3",
         {(z[9], z[10], z[11]) for z in g3}, fast[2])
    gate("* the honest gamma_4 (m,n)-image is the computed Lam4",
         {(z[12], z[13]) for z in g4}, fast[3])
    say("  |A| = %d, |Lam2| = %d, |Lam3| = %d, |Lam4| = %d at the witness"
        % tuple(len(x) for x in fast))
    say()


# =========================================================================================
def section1():
    say("== 1. the class-five increment pairing, against honest collection ==")
    rng = random.Random(60101)
    bad = 0
    tot = 0
    pts = [(M.mul(M.sigFiveMark, M.sepX), M.sepX, M.sepY, M.sepU, M.sepV)]
    for _ in range(40):
        pts.append(tuple(tuple(rng.randrange(8) for _ in range(15)) for _ in range(5)))
    for (S, X, Y, U, V) in pts:
        r = L.relator(S, X, Y, U, V)
        for _ in range(100):
            z0 = M.named(m=rng.randrange(8), n=rng.randrange(8), o=rng.randrange(8))
            z3 = M.named(m=rng.randrange(8), n=rng.randrange(8), o=rng.randrange(8))
            z4 = M.named(m=rng.randrange(8), n=rng.randrange(8), o=rng.randrange(8))
            w1 = M.liftC(rng.randrange(8))
            w2 = M.liftC(rng.randrange(8))
            tot += 1
            lhs = L.refined(S, X, Y, U, V, z0, w1, w2, z3, z4)
            rhs = M.mul(r, M.liftC(L.incr_full(X, U, V, z0, w1, w2, z3, z4)))
            if lhs != rhs:
                bad += 1
    gate("the translation identity of `sqRelWord_fiveLift` at %d refinements of 41 markings"
         % tot, bad, 0)
    say("  (the pairing is the whole increment modulo the exponent slots' `-4 w1.o + 2 w2.o`)")
    say()


# =========================================================================================
def verdicts(lets):
    S, X, Y, U, V = lets
    _, _, _, lam4 = L.lattices(lets)
    sharp = L.five_orth(X, U, V, lam4)
    hyp = L.letters_even(lets, L.IC)
    cons = L.lam4_even(lam4)
    kill = L.kill_exists(S, X, Y, U, V, L.gaFour_elements(lam4))
    return sharp, hyp, cons, kill, lam4


def family_witness():
    """The wave-59 point, and its dressings by achievable class-four and class-five moves."""
    rng = random.Random(60111)
    S0 = M.mul(M.sigFiveMark, M.sepX)
    out = []
    for _ in range(60):
        z = M.named(m=2 * rng.randrange(4), n=2 * rng.randrange(4), o=rng.randrange(8))
        w = M.liftC(rng.randrange(8))
        out.append((M.mul(S0, z), M.sepX, M.mul(M.sepY, w), M.sepU, M.sepV))
    out.append((S0, M.sepX, M.sepY, M.sepU, M.sepV))
    return [t for t in out if L.admissible(*t)]


def family_neighbours(budget_seconds):
    """Single- and double-coordinate perturbations of the witness letters, re-solved."""
    S0 = M.mul(M.sigFiveMark, M.sepX)
    base = [S0, M.sepX, M.sepU, M.sepV]
    out = []
    t0 = time.time()
    for (slot, k, v) in itertools.product(range(4), range(15), range(8)):
        if time.time() - t0 > budget_seconds:
            break
        lets = list(base)
        if lets[slot][k] == v:
            continue
        lets[slot] = lets[slot][:k] + (v,) + lets[slot][k + 1:]
        for Y in L.solve_Y(lets[0], lets[1], lets[2], lets[3], want=2, odd_only=True,
                           budget=1200):
            out.append((lets[0], lets[1], Y, lets[2], lets[3]))
    return out


def family_covector(budget_seconds):
    """Markings sweeping the six covector entries over all 64 parity patterns."""
    rng = random.Random(60121)
    S0 = M.mul(M.sigFiveMark, M.sepX)
    out = []
    t0 = time.time()
    while time.time() - t0 < budget_seconds:
        pat = [rng.randrange(2) for _ in range(6)]
        S = S0
        X = list(M.sepX)
        U = list(M.sepU)
        V = list(M.sepV)
        for (cell, bit) in zip(((X, L.IA), (X, L.IE), (U, L.IA), (U, L.IE),
                                (V, L.IA), (V, L.IE)), pat):
            cell[0][cell[1]] = rng.randrange(8) // 2 * 2 + bit
        for tgt in (X, U, V):
            k = rng.randrange(15)
            if k not in (L.IA, L.IE):
                tgt[k] = rng.randrange(8)
        X, U, V = tuple(X), tuple(U), tuple(V)
        for Y in L.solve_Y(S, X, U, V, want=1, odd_only=True, budget=1200):
            out.append((S, X, Y, U, V))
    return out


def family_random(budget_seconds, density, seed=60131, lam4_odd=False, slots_even=False):
    """Random letters, optionally pre-filtered so that the achievable lattice is ODD (which
    is where wave 59's CONSEQUENCE fails) or so that the covector entries are even."""
    rng = random.Random(seed)
    out = []
    t0 = time.time()
    while time.time() - t0 < budget_seconds:
        def rl(zero=()):
            v = [rng.randrange(8) if rng.random() < density else 0 for _ in range(15)]
            for k in zero:
                v[k] = 2 * rng.randrange(4)
            return tuple(v)
        z = (L.IA, L.IE) if slots_even else ()
        S, X, U, V = rl(), rl(z), rl(z), rl(z)
        if lam4_odd and L.lam4_even(L.lattices([S, X, L.ONE, U, V])[3]):
            continue
        for Y in L.solve_Y(S, X, U, V, want=2, odd_only=True, budget=1200):
            out.append((S, X, Y, U, V))
    return out


def section2(scale):
    say("== 2. the census ==")
    fams = [("witness + achievable dressings", family_witness()),
            ("neighbours of the witness letters", family_neighbours(15 * scale)),
            ("covector sweep", family_covector(25 * scale)),
            ("random letters (density .25)", family_random(15 * scale, 0.25)),
            ("random letters (density .5)", family_random(15 * scale, 0.5, seed=60132)),
            ("random, achievable lattice ODD", family_random(60 * scale, 0.3, seed=60133,
                                                             lam4_odd=True)),
            ("random, ODD lattice + even covectors",
             family_random(60 * scale, 0.3, seed=60134, lam4_odd=True, slots_even=True))]
    tot = 0
    agree = 0
    disagree = 0
    n_sharp = 0
    n_hyp = 0
    n_cons = 0
    n_kill = 0
    gold = 0                       # W59-CONS fails and the forcing holds
    gold_hyp = 0                   # W59-HYP fails and the forcing holds
    gold_both = 0                  # outside BOTH sufficient conditions, forcing holds
    inside_broken = 0              # W59-CONS holds and the forcing fails
    seen = set()
    covpat = {}
    for (name, fam) in fams:
        fam = [t for t in fam if L.admissible(*t)]
        fresh = [t for t in fam if t not in seen]
        seen.update(fresh)
        loc = 0
        for lets in fresh:
            sharp, hyp, cons, kill, lam4 = verdicts(list(lets))
            tot += 1
            loc += 1
            if sharp == (not kill):
                agree += 1
            else:
                disagree += 1
                say("  DISAGREEMENT at %s" % (tuple(M.show(g) for g in lets),))
            n_sharp += sharp
            n_hyp += hyp
            n_cons += cons
            n_kill += kill
            if (not cons) and sharp:
                gold += 1
            if (not hyp) and sharp:
                gold_hyp += 1
            slots_even = all(g[i] % 2 == 0 for g in (lets[1], lets[3], lets[4])
                             for i in (L.IA, L.IE))
            if (not cons) and (not slots_even) and sharp:
                gold_both += 1
            if cons and not sharp:
                inside_broken += 1
            covpat.setdefault(L.covectors(lets[1], lets[3], lets[4]), [0, 0])
            covpat[L.covectors(lets[1], lets[3], lets[4])][0] += 1
            covpat[L.covectors(lets[1], lets[3], lets[4])][1] += sharp
        say("  family %-36s %5d admissible markings" % (name, loc))
    say()
    say("  TOTAL admissible markings swept                                  %6d" % tot)
    gate("the sharp criterion and the independent kill search agree everywhere",
         disagree, 0)
    say("  markings at which the forcing HOLDS (sharp / no kill)            %6d" % n_sharp)
    say("  markings at which the forcing FAILS (a kill exists)              %6d" % n_kill)
    say("  markings inside W59-HYP  (every slot has an even (3,4)-column)   %6d" % n_hyp)
    say("  markings inside W59-CONS (every achievable dressing even)        %6d" % n_cons)
    say("  ** W59-CONS FAILS and the forcing HOLDS                          %6d" % gold)
    say("  ** W59-HYP  FAILS and the forcing HOLDS                          %6d" % gold_hyp)
    say("  ** outside BOTH sufficient conditions and the forcing HOLDS      %6d" % gold_both)
    gate("no marking inside W59-CONS ever breaks the forcing", inside_broken, 0)
    say()
    say("  by covector pattern ((X.e,X.a),(V.e,V.a),(U.e,U.a)):  count / forcing holds")
    for pat in sorted(covpat):
        say("    %s  %6d / %6d" % (pat, covpat[pat][0], covpat[pat][1]))
    say()
    return tot, gold, gold_hyp, gold_both


# =========================================================================================
def section3():
    say("== 3. the five slot-column conditions, and which force what ==")
    rng = random.Random(60141)
    rows = []
    for idx, nm in ((L.IA, "a = x_{12}"), (L.IB, "b = x_{23}"), (L.IC, "c = x_{34}"),
                    (L.ID, "d = x_{45}"), (L.IE, "e = x_{56}")):
        mbad = nbad = 0
        for _ in range(4000):
            ab = []
            for _ in range(5):
                v = [rng.randrange(8) for _ in range(5)]
                v[idx] = 2 * rng.randrange(4)
                ab.append(tuple(v))
            L2 = L.span([L.pair2(p, q) for p in ab for q in ab], 4)
            L3 = L.span([L.pair3(w, v) for w in L2 for v in ab], 3)
            L4 = L.span([L.pair4(z, v) for z in L3 for v in ab], 2)
            if any(mm % 2 for (mm, _) in L4):
                mbad += 1
            if any(nn % 2 for (_, nn) in L4):
                nbad += 1
        rows.append((nm, mbad, nbad))
        say("  every letter even in %-10s ->  m always even: %-5s   n always even: %-5s"
            % (nm, mbad == 0, nbad == 0))
    gate("even c forces BOTH class-four coordinates even (wave 59's chain)",
         [r[1:] for r in rows if r[0].startswith("c")], [(0, 0)])
    gate("even b and even d do too, and neither implies even c",
         [r[1:] for r in rows if r[0][0] in "bd"], [(0, 0), (0, 0)])
    gate("even a forces ONLY the first, even e ONLY the second",
         [(r[0][0], r[1] == 0, r[2] == 0) for r in rows if r[0][0] in "ae"],
         [("a", True, False), ("e", False, True)])
    say()


# =========================================================================================
if __name__ == "__main__":
    scale = float(sys.argv[1]) if len(sys.argv) > 1 else 1.0
    t0 = time.time()
    section0()
    section1()
    tot, gold, gold_hyp, gold_both = section2(scale)
    section3()
    say("== summary ==")
    say("  %d admissible class-five markings; %d with wave 59's CONSEQUENCE failing and the"
        % (tot, gold))
    say("  forcing holding; %d with its HYPOTHESIS failing and the forcing holding; %d"
        % (gold_hyp, gold_both))
    say("  outside both sufficient conditions with the forcing holding.")
    say("  failures: %s" % (FAILURES if FAILURES else "none"))
    say("  elapsed %.0f s" % (time.time() - t0))
    with open("results/sweep_sharp5.txt", "w") as fh:
        fh.write("\n".join(OUT) + "\n")
