"""W61-SHARP4: the STAGE-FOUR census.

Is wave 60's stage-four soundness condition NECESSARY?  The lane's brief says compute first,
so this is the computation, in the shape wave 59 (`w59_invariant`) and wave 60 (`w60_sharp5`)
used for the other two soundness lines.

An ADMISSIBLE marking is a one-handle-live five-tuple `(S, X, Y, U, V)` whose relator is a
CENTRAL translation with an ODD class-five residue: exactly the situation the stage-four
exclusion is about, and wave 60's census condition verbatim.  The `x1`-slot is produced by
`sharp5lib`'s layered solve, so a perturbed set of letters is pushed back onto an admissible
marking rather than discarded.

At each marking eight verdicts are compared.

  W60-HYP   every letter has an even `(1,2)`- and `(3,4)`-column          (`stageN1`)
  W60-SND   every letter has an even `(1,2)`-column AND every achievable
            dressing has `j`, `l`, `m` even       (the exact hypothesis of `gaThreeShiftO_even`)
  W60-CONS  every achievable dressing has `j`, `l`, `m` even              (`stageN3`)
  ORTH      every achievable dressing moves the class-five row EVENLY   [the parity line]
  MODLOW    the class-five row is congruent mod 2 to a fixed combination of the two
            class-four rows                       [achievability-free sufficient condition]
  GA4       every achievable gamma_4-SHAPED dressing pairs evenly       [necessary]
  CEN       every achievable dressing whose shift is CENTRAL moves the class-five row
            evenly                                                       [the sharp line]
  KILL      an EXACT search - not a sample - over all achievable five-slot stage-four
            dressings finds one that kills the relator

The claims under test are `CEN <-> not KILL`, `ORTH -> CEN`, `MODLOW -> CEN` and
`not KILL -> GA4`, and the question the wave asked is how many markings have the wave-60
condition failing with the forcing holding.

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

import sharp4lib as L                                                  # noqa: I100
import u6mat as M                                                      # noqa: E402

OUT = []
FAILURES = []


def say(s=""):
    print(s)
    OUT.append(s)


def check(name, got, want=True):
    ok = (got == want)
    say("  [%s] %s%s" % ("PASS" if ok else "FAIL", name,
                         "" if ok else "   got %r want %r" % (got, want)))
    return ok


def gate(name, got, want=True):
    if not check(name, got, want):
        FAILURES.append(name)


def verdicts(m):
    B = L.gamma3_basis(m)
    IB = L.image_basis(m, B)
    evenA = all(g[L.IA] % 2 == 0 for g in m)
    cons = L.stageN3_all(B)
    return dict(hyp=L.stageN1_all(m), snd=(evenA and cons), cons=cons,
                orth=L.orth_all(m, B), modlow=bool(L.modlow(m)),
                ga4=L.orth_gafour(m, B), cen=L.orth_central(m, basis=IB),
                kill=L.kill_exists(m, basis=IB))


# =========================================================================================
def family_witness(rng):
    """The committed stage-four point, and its own achievable dressings."""
    m0 = L.stage_point()
    out = [tuple(m0)]
    B = L.gamma3_basis(m0)
    mem = sorted(L.members(B))
    for _ in range(80):
        z = L.elt(rng.choice(mem))
        i = rng.randrange(5)
        mm = list(m0)
        mm[i] = M.mul(mm[i], z)
        out.append(tuple(mm))
    return out


def family_neighbours(budget):
    """Single-coordinate perturbations of the point's four free letters, re-solved."""
    m0 = L.stage_point()
    base = [m0[0], m0[1], m0[3], m0[4]]
    out = []
    t0 = time.time()
    for (slot, k, v) in itertools.product(range(4), range(15), range(8)):
        if time.time() - t0 > budget:
            break
        lets = list(base)
        if lets[slot][k] == v:
            continue
        lets[slot] = lets[slot][:k] + (v,) + lets[slot][k + 1:]
        for Y in L.solve_y(lets[0], lets[1], lets[2], lets[3], want=2, budget=1200):
            out.append((lets[0], lets[1], Y, lets[2], lets[3]))
    return out


def family_columns(budget, seed):
    """Markings sweeping the `(1,2)`- and `(3,4)`-column parities that wave 60's chain reads,
    which is where its hypothesis is expected to fail."""
    rng = random.Random(seed)
    m0 = L.stage_point()
    out = []
    t0 = time.time()
    while time.time() - t0 < budget:
        lets = [list(m0[0]), list(m0[1]), list(m0[3]), list(m0[4])]
        for g in lets:
            for k in (L.IA, L.IC):
                g[k] = rng.randrange(8)
            g[rng.randrange(15)] = rng.randrange(8)
        S, X, U, V = (tuple(g) for g in lets)
        for Y in L.solve_y(S, X, U, V, want=1, budget=1200):
            out.append((S, X, Y, U, V))
    return out


def family_random(budget, density, seed, even_ea=False):
    """Random letters; `even_ea` pre-sets the two outer abelian columns even, which is where
    the class-five covectors die and the stage-four ones need not."""
    rng = random.Random(seed)
    out = []
    t0 = time.time()
    while time.time() - t0 < budget:
        def rl():
            v = [rng.randrange(8) if rng.random() < density else 0 for _ in range(15)]
            if even_ea:
                v[L.IA] = 2 * rng.randrange(4)
                v[L.IE] = 2 * rng.randrange(4)
            return tuple(v)
        S, X, U, V = rl(), rl(), rl(), rl()
        for Y in L.solve_y(S, X, U, V, want=2, budget=1200):
            out.append((S, X, Y, U, V))
    return out


def family_orthhunt(budget, seed):
    """Markings whose five slot covectors are pushed towards zero: the stage-four analogue of
    wave 60's orthogonal family."""
    rng = random.Random(seed)
    out = []
    t0 = time.time()
    while time.time() - t0 < budget:
        def rl(sparse):
            v = [0] * 15
            for k in range(15):
                if rng.random() < sparse:
                    v[k] = rng.randrange(8)
            for k in (L.IA, L.IE, L.IB, L.IF, L.II):
                v[k] = 2 * rng.randrange(4)
            return tuple(v)
        S, X, U, V = rl(0.4), rl(0.4), rl(0.4), rl(0.4)
        for Y in L.solve_y(S, X, U, V, want=2, budget=1200):
            out.append((S, X, Y, U, V))
    return out


# =========================================================================================
def section1(scale):
    say("== 1. the census ==")
    rng = random.Random(61001)
    fams = [("the committed point + its own dressings", family_witness(rng)),
            ("neighbours of the point's letters", family_neighbours(30 * scale)),
            ("column sweep ((1,2)- and (3,4)-columns)", family_columns(45 * scale, 61011)),
            ("random letters (density .3)", family_random(30 * scale, 0.3, 61021)),
            ("random letters (density .5)", family_random(30 * scale, 0.5, 61022)),
            ("random, outer columns even", family_random(45 * scale, 0.35, 61023,
                                                         even_ea=True)),
            ("covector hunt", family_orthhunt(45 * scale, 61031)),
            ("random letters (density .35)", family_random(45 * scale, 0.35, 6101)),
            ("random letters (density .45)", family_random(45 * scale, 0.45, 61302))]
    keys = ["hyp", "snd", "cons", "orth", "modlow", "ga4", "cen", "kill"]
    tot = 0
    counts = {k: 0 for k in keys}
    gold_hyp = gold_snd = gold_cons = gold_orth = 0
    bad_cen = bad_orth = bad_modlow = bad_ga4 = bad_snd = 0
    orth_strict = modlow_strict = both_strict = 0
    pats = {}
    seen = set()
    for (name, fam) in fams:
        fresh = [t for t in fam if t not in seen and L.admissible(list(t))]
        seen.update(fresh)
        for lets in fresh:
            m = list(lets)
            v = verdicts(m)
            tot += 1
            for k in keys:
                counts[k] += v[k]
            forcing = not v["kill"]
            if forcing and not v["hyp"]:
                gold_hyp += 1
            if forcing and not v["snd"]:
                gold_snd += 1
            if forcing and not v["cons"]:
                gold_cons += 1
            if forcing and not v["orth"]:
                gold_orth += 1
            if v["cen"] != forcing:
                bad_cen += 1
                say("  DISAGREEMENT (CEN vs KILL) at %s" % (tuple(M.show(g) for g in lets),))
            if v["orth"] and not v["cen"]:
                bad_orth += 1
            if v["modlow"] and not v["cen"]:
                bad_modlow += 1
            if forcing and not v["ga4"]:
                bad_ga4 += 1
            if v["snd"] and not v["orth"]:
                bad_snd += 1
            if v["cen"] and not v["orth"]:
                orth_strict += 1
            if v["cen"] and not v["modlow"]:
                modlow_strict += 1
            if v["cen"] and not v["orth"] and not v["modlow"]:
                both_strict += 1
            pats[tuple(v[k] for k in keys)] = pats.get(tuple(v[k] for k in keys), 0) + 1
        say("  family %-42s %5d admissible markings" % (name, len(fresh)))
    say()
    say("  TOTAL admissible stage-four markings swept                        %6d" % tot)
    say("  the forcing HOLDS (no achievable stage-four kill)                 %6d"
        % (tot - counts["kill"]))
    say("  the forcing FAILS (an achievable stage-four kill exists)          %6d"
        % counts["kill"])
    say()
    say("  inside W60-HYP  (all letters even in the (1,2)- and (3,4)-columns) %6d"
        % counts["hyp"])
    say("  inside W60-SND  (the exact hypothesis of `gaThreeShiftO_even`)     %6d"
        % counts["snd"])
    say("  inside W60-CONS (every achievable dressing has j, l, m even)       %6d"
        % counts["cons"])
    say("  inside ORTH     (the parity line on the whole lattice)             %6d"
        % counts["orth"])
    say("  inside MODLOW   (class-five row = fixed combination of class-four) %6d"
        % counts["modlow"])
    say("  inside GA4      (the gamma_4-shaped part pairs evenly)             %6d"
        % counts["ga4"])
    say("  inside CEN      (the sharp line)                                   %6d"
        % counts["cen"])
    say()
    say("  ** W60-HYP  FAILS and the forcing HOLDS                            %6d" % gold_hyp)
    say("  ** W60-SND  FAILS and the forcing HOLDS                            %6d" % gold_snd)
    say("  ** W60-CONS FAILS and the forcing HOLDS                            %6d" % gold_cons)
    say("  ** ORTH     FAILS and the forcing HOLDS                            %6d" % gold_orth)
    say()
    gate("the sharp line CEN and the exact kill search agree everywhere", bad_cen, 0)
    gate("ORTH is sufficient   (ORTH -> no kill)", bad_orth, 0)
    gate("MODLOW is sufficient (MODLOW -> no kill)", bad_modlow, 0)
    gate("GA4 is necessary     (no kill -> GA4)", bad_ga4, 0)
    gate("W60's soundness hypothesis implies the parity line", bad_snd, 0)
    say("  ORTH is STRICTLY stronger than the sharp line at                   %6d markings"
        % orth_strict)
    say("  MODLOW is STRICTLY stronger than the sharp line at                 %6d markings"
        % modlow_strict)
    say("  the sharp line holds and BOTH sufficient conditions fail at        %6d markings"
        % both_strict)
    say()
    say("  verdict patterns (%s):" % " ".join(keys))
    for p in sorted(pats):
        say("    %s  %6d" % ("  ".join("%-5s" % x for x in p), pats[p]))
    say()
    return tot, gold_hyp, gold_snd, gold_cons, gold_orth, orth_strict, both_strict


# =========================================================================================
if __name__ == "__main__":
    scale = float(sys.argv[1]) if len(sys.argv) > 1 else 1.0
    t0 = time.time()
    res = section1(scale)
    say("== summary ==")
    say("  %d admissible stage-four markings; %d with wave 60's HYPOTHESIS failing and the"
        % (res[0], res[1]))
    say("  forcing holding, %d with its exact soundness hypothesis failing, %d with its"
        % (res[2], res[3]))
    say("  CONCLUSION failing; and %d with the PARITY LINE itself failing and the forcing"
        % res[4])
    say("  still holding, which is what makes the sharp line the CENTRAL one.")
    say("  failures: %s" % (FAILURES if FAILURES else "none"))
    say("  elapsed %.0f s" % (time.time() - t0))
    with open("results/sweep_sharp4.txt", "w") as fh:
        fh.write("\n".join(OUT) + "\n")
