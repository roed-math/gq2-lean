"""W62-SEPARATE: the file's own composites, checked against the honest engine.

Doctrine iii - check composites, including your own.  Three claims the Lean file or its
docstring makes are tested here on wave 59's honest matrices through wave 61's `sharp4lib`:

  A  `stageOrth_of_ae`: even `(1,2)`- and `(5,6)`-columns at every letter give the PARITY line,
     with no condition on the outer class-two column `i` (wave 61's `stageOrth_of_outer` asks
     for it).  Tested at markings that have an ODD `i` somewhere, so wave 61's condition fails
     and the new one applies.
  B  the mirror chain `forceLcs_two_le_sepEvenJ`: even `(1,2)`-columns give every achievable
     stage-four dressing an even `j`.
  C  the docstring's reason for wave 61's `MODLOW` count of 0: `MODLOW` forces the `(1,2)`- and
     `(5,6)`-columns even at every letter, hence (by A) implies the parity line.
"""
import os, random, sys
HERE = os.path.dirname(os.path.abspath(__file__))
for d in ("w61_sharp4", "w59_force5", "w60_stage4", "w60_sharp5"):
    sys.path.insert(0, os.path.join(os.path.dirname(HERE), d))
import sharp4lib as L, sharp5lib as S5, u6mat as M                     # noqa: E402

OUT, FAIL = [], []
IA, IE, II, IJ = 0, 4, 8, 9


def say(s=""):
    print(s)
    OUT.append(s)


def gate(name, got, want=True):
    ok = (got == want)
    say("  [%s] %s%s" % ("PASS" if ok else "FAIL", name,
                         "" if ok else "   got %r want %r" % (got, want)))
    if not ok:
        FAIL.append(name)


def rnd_ae(rng, density=0.4):
    """A letter with even `a` and even `e` columns, everything else free."""
    v = [rng.randrange(8) if rng.random() < density else 0 for _ in range(15)]
    v[IA] = 2 * rng.randrange(4)
    v[IE] = 2 * rng.randrange(4)
    return tuple(v)


rng = random.Random(6202)
say("== A. the two-column parity line ==")
n = oddi = 0
bad = []
for _ in range(400):
    S, X, U, V = (rnd_ae(rng) for _ in range(4))
    for Y in S5.solve_Y(S, X, U, V, want=1, odd_only=True, budget=3000):
        m = [S, X, Y, U, V]
        if not L.admissible(m) or not all(g[IA] % 2 == 0 and g[IE] % 2 == 0 for g in m):
            continue
        n += 1
        if any(g[II] % 2 for g in m):
            oddi += 1
        B = L.gamma3_basis(m)
        if not L.orth_all(m, B):
            bad.append(m)
say("  %d admissible markings with even (1,2)- and (5,6)-columns, %d of them with an ODD outer"
    " class-two column somewhere" % (n, oddi))
gate("the parity line holds at every one of them", len(bad) == 0)
gate("the sample reaches markings outside wave 61's three-column condition", oddi > 0)

say()
say("== B. the mirror chain: even (1,2)-columns give every achievable dressing an even j ==")
n = badj = 0
for _ in range(400):
    ls = []
    for _ in range(5):
        v = [rng.randrange(8) if rng.random() < 0.4 else 0 for _ in range(15)]
        v[IA] = 2 * rng.randrange(4)
        ls.append(tuple(v))
    n += 1
    B = L.gamma3_basis(ls)
    if any(g[0] % 2 for g in B):
        badj += 1
gate("no achievable dressing has an odd j, over %d random letter tuples" % n, badj == 0)

say()
say("== C. why MODLOW is empty ==")
n = mod = badcol = 0
for _ in range(300):
    ls = [tuple(rng.randrange(8) if rng.random() < 0.4 else 0 for _ in range(15))
          for _ in range(5)]
    n += 1
    if L.modlow(ls):
        mod += 1
        if not all(g[IA] % 2 == 0 and g[IE] % 2 == 0 for g in ls):
            badcol += 1
say("  %d random letter tuples, %d with MODLOW" % (n, mod))
gate("every MODLOW tuple has even (1,2)- and (5,6)-columns at every letter", badcol == 0)

say()
say("== D. the separating marking is outside the two-column condition, as it must be ==")
sep = [M.named(a=1, c=1, h=1), M.named(a=1), M.named(a=2),
       M.named(d=1, e=1, g=1, m=1, n=1), M.named(a=1, i=1, k=1, n=1)]
gate("some letter of sepMark has an ODD (1,2)-column",
     any(g[IA] % 2 for g in sep))
gate("its relator's class-three row is odd", L.relator(sep)[IJ] % 2 == 1)

say()
say("== summary ==")
say("  failures: %s" % (", ".join(FAIL) if FAIL else "none"))
with open(os.path.join(HERE, "results", "check_ae.txt"), "w") as f:
    f.write("$ python3 check_ae.py\n\n" + "\n".join(OUT) + "\n")
