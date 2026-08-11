"""W61-SHARP4: the validation run behind `GradedStageNecessity`.

Every number the Lean file's docstring quotes, and every fact its points assert, is checked
here through the honest `6 x 6` matrices of `scripts/w59_force5/u6mat.py`.  The engine is
`sharp4lib`, which reads each stage-four shift off the group law rather than from a formula;
section 3 then compares the transcribed covectors of `GradedFiveStageFour` against those
honest shifts, so the Lean coefficients are measured, not trusted.

Sections:

  0  the imported machinery: the fast product, and the Howell module against honest closure
  1  the shift map is additive across slots and linear in each slot (the census's licence)
  2  the exact kill test against an independent brute-force search
  3  the stage-four covectors, honest against transcribed, and the arity table
  4  the mixed point of Lean section 4
  5  wave 60's orthogonal point, which dies at stage four (Lean section 6)
  6  the closed orthogonal route (Lean section 5): four even columns kill every covector AND
     the class-five bit, three do not
  7  wave 60's committed stage-four point, unchanged

BRACKET CONVENTION.  [PAPER-RAW]
This script builds RAW nested bracket sets, and its Lean target is written with commP,
so the paper convention is the right one to compute.  Raw bracket sets are the only
computations in this tree that can be wrong about the convention: check this line
before repointing the script at a [.,.]-written statement.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

import random
import sys
import time

import sharp4lib as L                                                  # noqa: I100
import fastu6 as FU                                                    # noqa: E402
import modlib as MD                                                    # noqa: E402
import pointlib as PL                                                  # noqa: E402
import u6mat as M                                                      # noqa: E402

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


# =========================================================================================
def section0():
    say("== 0. the imported machinery ==")
    bad, tot = FU.crosscheck(4000)
    gate("wave 60's fast product agrees with u6mat's honest 6 x 6 matrices (%d)" % tot, bad, 0)
    for (name, m) in (("wave 60's stage-four point", L.stage_point()),
                      ("wave 59's binder point", L.wave59_point())):
        B = L.gamma3_basis(m)
        g3, _, _ = PL.gamma_series(m)
        gate("the Howell gamma_3(im) matches honest closure at %s (|gamma_3| = %d)"
             % (name, len(g3)), MD.card(B, 6), len(g3))
        gate("...and elementwise", {L.vec(z) for z in g3}, L.members(B))
    say()


# =========================================================================================
def section1():
    say("== 1. the stage-four shift map is linear ==")
    rng = random.Random(61701)
    pts = [L.stage_point(), L.wave59_point()]
    for _ in range(8):
        pts.append([tuple(rng.randrange(8) for _ in range(15)) for _ in range(5)])
    badadd = badlin = badone = 0
    tot = 0
    for m in pts:
        for _ in range(120):
            zs = [tuple(rng.randrange(8) for _ in range(6)) for _ in range(5)]
            tot += 1
            parts = [L.slot_shift(m, i, zs[i]) for i in range(5)]
            summed = tuple(sum(p[t] for p in parts) % 8 for t in range(6))
            if L.shift(m, zs) != summed:
                badadd += 1
            i = rng.randrange(5)
            w1 = tuple(rng.randrange(8) for _ in range(6))
            w2 = tuple(rng.randrange(8) for _ in range(6))
            a, b = L.slot_shift(m, i, w1), L.slot_shift(m, i, w2)
            c = L.slot_shift(m, i, tuple((w1[t] + w2[t]) % 8 for t in range(6)))
            if c != tuple((a[t] + b[t]) % 8 for t in range(6)):
                badlin += 1
            if L.shift(m, [(0,) * 6] * 5) != (0,) * 6:
                badone += 1
    gate("the shift is additive ACROSS slots (%d tuples, 10 markings)" % tot, badadd, 0)
    gate("...and linear IN each slot (`gaThreeShift_mul` measured)", badlin, 0)
    gate("...and trivial at the trivial dressing", badone, 0)
    say("  (this is what licenses computing the achievable image as a module rather than by")
    say("   enumeration, and it is the measured form of the Lean `gaThreeShift_mul`)")
    say()


# =========================================================================================
def brute_kill(m, B):
    """An independent kill search: dress ONE slot by each achievable element and run the
    honest group law.  It can only confirm kills, never rule them out, which is exactly why
    the module test exists."""
    for i in range(5):
        for g in sorted(L.members(B)):
            mm = list(m)
            mm[i] = M.mul(mm[i], L.elt(g))
            if M.sqRelWord(mm) == M.ONE:
                return True
    return False


def section2(budget):
    say("== 2. the exact kill test against a brute-force search ==")
    rng = random.Random(61711)
    n = agree = brute = mod = 0
    t0 = time.time()
    while time.time() - t0 < budget:
        def rl():
            v = [rng.randrange(8) if rng.random() < 0.35 else 0 for _ in range(15)]
            return tuple(v)
        S, X, U, V = rl(), rl(), rl(), rl()
        for Y in L.solve_y(S, X, U, V, want=2, budget=1200):
            m = [S, X, Y, U, V]
            if not L.admissible(m):
                continue
            B = L.gamma3_basis(m)
            if MD.card(B, 6) > 4096:
                continue                                   # keep the brute force honest-sized
            n += 1
            k1 = L.kill_exists(m, B)
            k2 = brute_kill(m, B)
            mod += k1
            brute += k2
            if k2 and not k1:
                say("  DISAGREEMENT: brute force kills where the module test says no")
            else:
                agree += 1
    gate("no brute-force kill is missed by the exact test (%d markings)" % n, agree, n)
    say("  markings where the module test finds a kill                        %6d" % mod)
    say("  markings where the single-slot brute force finds one               %6d" % brute)
    say("  (the module test also sees multi-slot kills, so it is the larger count)")
    say()


# =========================================================================================
def section3():
    say("== 3. the stage-four covectors: honest against transcribed ==")
    rng = random.Random(61721)
    bad = 0
    tot = 0
    lens = {}
    for _ in range(400):
        m = [tuple(rng.randrange(8) if rng.random() < 0.5 else 0 for _ in range(15))
             for _ in range(5)]
        for i in range(5):
            tot += 1
            hon = L.covector(m, i)
            if hon != L.covector_formula(m, i):
                bad += 1
            lens[i] = max(lens.get(i, 0), sum(1 for e in hon if e))
    gate("the covectors transcribed from `GradedFiveStageFour` match the honest shift (%d)"
         % tot, bad, 0)
    say("  live entries seen per slot (of the five (j,k,l,m,n)):")
    for i in range(5):
        say("    slot %-6s %d" % (L.SLOT[i], lens[i]))
    say("  so the stage-four line reads FIVE covectors of length FIVE at one handle,")
    say("  against class four's two of length two and class five's three of length two.")
    say()


# =========================================================================================
def section4():
    say("== 4. the mixed point of Lean section 4 ==")
    S = M.named(a=2, b=4, i=2, o=2)
    X = M.named(a=4, d=3, e=4, i=2)
    Y = M.named(d=2, l=1)
    U = M.named(a=6, e=2, i=2, j=1, k=3, l=1, n=5)
    V = M.named(a=6, c=5, e=2, f=1, i=4, k=7)
    m = [S, X, Y, U, V]
    B = L.gamma3_basis(m)
    gate("the relator is the central translation <o = 7>", L.relator(m), M.liftC(7))
    gate("every letter has an even (1,2)-column", all(g[L.IA] % 2 == 0 for g in m))
    gate("...an even (5,6)-column", all(g[L.IE] % 2 == 0 for g in m))
    gate("...and an even outer class-two column", all(g[L.II] % 2 == 0 for g in m))
    gate("W60-HYP FAILS: the handle-V letter's (3,4)-column is odd", V[L.IC] % 2, 1)
    br = M.commP(M.commP(X, V), V)
    gate("W60-CONS FAILS: [[x0, V], V] = <l=4, m=7, o=2>", br, M.named(l=4, m=7, o=2))
    gate("...with an ODD first class-four coordinate", br[L.IM] % 2, 1)
    gate("every achievable dressing has an even `l` (the outer chain's output)",
         all(r[2] % 2 == 0 for r in B))
    gate("the parity line HOLDS", L.orth_all(m, B))
    gate("the sharp line HOLDS", L.orth_central(m, L.gamma3_basis(m)))
    gate("and NO achievable stage-four dressing kills the relator",
         L.kill_exists(m, B), False)
    gate("...confirmed by the independent brute force", brute_kill(m, B), False)
    say("  |gamma_3(im)| = %d, covectors %s"
        % (MD.card(B, 6), [L.covector(m, i) for i in range(5)]))
    say()


# =========================================================================================
def section5():
    say("== 5. wave 60's class-five ORTHOGONAL point dies at stage four ==")
    S = M.named(a=1, l=2)
    X = M.named(b=4, c=3, j=5)
    Y = M.named(c=2, f=2, n=7)
    U = M.named(d=1, g=6, j=3, n=2)
    V = M.named(b=5, i=3)
    m = [S, X, Y, U, V]
    B = L.gamma3_basis(m)
    gate("the relator is the central translation <o = 1>", L.relator(m), M.liftC(1))
    gate("all three class-five covectors (slot.e, slot.a) vanish",
         [(g[L.IE] % 2, g[L.IA] % 2) for g in (X, U, V)], [(0, 0), (0, 0), (0, 0)])
    gen = M.commP(M.commP(V, S), X)
    gate("[[V, sigma], x0] = <j = 1>", gen, M.named(j=1))
    p5 = gen
    for _ in range(4):
        p5 = M.mul(p5, gen)
    gate("...and its fifth power is <j = 5>", p5, M.named(j=5))
    mm = list(m)
    mm[3] = M.mul(mm[3], p5)
    gate("dressing the handle-U slot by it KILLS the relator", M.sqRelWord(mm), M.ONE)
    kills = sum(1 for i in range(5) for g in L.members(B)
                if M.sqRelWord([M.mul(m[t], L.elt(g)) if t == i else m[t]
                                for t in range(5)]) == M.ONE)
    say("  single-slot achievable stage-four kills at this point            %6d of %d"
        % (kills, 5 * MD.card(B, 6)))
    gate("the stage-four forcing FAILS here", L.kill_exists(m, B))
    say("  stage-four covectors %s" % ([L.covector(m, i) for i in range(5)],))
    say("  (the killing dressing is <j = 5>: no class-five covector reads `j`)")
    say()


# =========================================================================================
def section6(budget):
    say("== 6. the orthogonal route is CLOSED at stage four ==")
    rng = random.Random(61731)
    bad_cov = bad_bit = 0
    tot = 0
    for _ in range(2000):
        def rl(cols):
            v = [rng.randrange(8) for _ in range(15)]
            for k in cols:
                v[k] = 2 * rng.randrange(4)
            return tuple(v)
        m = [rl((L.IA, L.IE, L.IF, L.II)) for _ in range(5)]
        tot += 1
        if any(any(e for e in L.covector(m, i)) for i in range(5)):
            bad_cov += 1
        if L.relator(m)[L.IO] % 2:
            bad_bit += 1
    gate("four even columns (a, e, f, i) kill EVERY stage-four covector (%d markings)" % tot,
         bad_cov, 0)
    gate("...and force the class-five selection bit EVEN (`stageQ_bit_even`)", bad_bit, 0)
    for cols, label in (((L.IA, L.IE), "a, e"), ((L.IA, L.IE, L.IF), "a, e, f"),
                        ((L.IA, L.IE, L.II), "a, e, i"), ((L.IF, L.II), "f, i")):
        odd = 0
        for _ in range(2000):
            m = [tuple(2 * rng.randrange(4) if k in cols else rng.randrange(8)
                       for k in range(15)) for _ in range(5)]
            odd += L.relator(m)[L.IO] % 2
        say("  even in %-8s: the bit is still odd at %4d of 2000 markings" % (label, odd))
    say("  so THREE of the four columns leave the forcing with content and four do not:")
    say("  the free hypothesis exists and is vacuous, which is new at stage four.")
    # the converse of the covector statement, measured
    rng2 = random.Random(61741)
    bad = 0
    n = 0
    t0 = time.time()
    while time.time() - t0 < budget:
        m = [tuple(rng2.randrange(8) if rng2.random() < 0.5 else 0 for _ in range(15))
             for _ in range(5)]
        if any(any(e for e in L.covector(m, i)) for i in range(5)):
            continue
        n += 1
        if not all(g[k] % 2 == 0 for g in m for k in (L.IA, L.IE, L.IF, L.II)):
            bad += 1
    gate("...and every marking with all covectors zero has the four columns even (%d found)"
         % n, bad, 0)
    say()


# =========================================================================================
def section7():
    say("== 7. wave 60's committed stage-four point, unchanged ==")
    m = L.stage_point()
    B = L.gamma3_basis(m)
    gate("the relator is <o = 1>", L.relator(m), M.liftC(1))
    gate("W60-HYP holds (all letters even in the (1,2)- and (3,4)-columns)", L.stageN1_all(m))
    gate("W60-CONS holds (every achievable dressing has j, l, m even)", L.stageN3_all(B))
    gate("the parity line holds", L.orth_all(m, B))
    gate("the sharp line holds, and no achievable dressing kills",
         (L.orth_central(m, B), L.kill_exists(m, B)), (True, False))
    say("  |gamma_3(im)| = %d; covectors %s"
        % (MD.card(B, 6), [L.covector(m, i) for i in range(5)]))
    say("  nothing wave 60 proved is retracted: its point is inside every condition here.")
    say()


# =========================================================================================
if __name__ == "__main__":
    scale = float(sys.argv[1]) if len(sys.argv) > 1 else 1.0
    t0 = time.time()
    section0()
    section1()
    section2(40 * scale)
    section3()
    section4()
    section5()
    section6(20 * scale)
    section7()
    say("== summary ==")
    say("  failures: %s" % (FAILURES if FAILURES else "none"))
    say("  elapsed %.0f s" % (time.time() - t0))
    with open("results/validate.txt", "w") as fh:
        fh.write("\n".join(OUT) + "\n")
