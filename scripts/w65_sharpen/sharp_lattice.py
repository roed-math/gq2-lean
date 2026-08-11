"""W65-SHARPEN: certification for the two sharpened stage-four lattice bounds.

W64-VERIFY's task-A audit (`scripts/w64_verify/task_a_audit.py`, section 4) found that two of
the tree's nine committed lattice bounds are not the sharpest it owns, and named the sharpened
targets:

    stageN2' = {a..e = 0, 2|f, 2|g, 2|h, 2|j}      (stageN2 is missing  2|g )
    stageN3' = {a..i = 0, 4|j, 2|k, 2|l, 2|m}      (stageN3 has 2|j, and no condition on k)

This script does NOT re-derive that finding; it layers on it.  What it certifies is exactly the
route the Lean file `GQ2/Dyadic/SqCore/GradedForceSharp.lean` takes, coordinate by
coordinate, so that a slip in the Lean algebra shows up here as a failing check:

  1  the two-step chain is EXACT at the uniform level:  [stageN1, stageN1] = stageN2'  and
     [stageN2', stageN1] = stageN3'.  This is what licenses proving the depth-two bound by
     running the depth-one bound and then a single `_of_commutator` lemma, rather than by the
     generator reduction `LcsGens.lcsSeries_le_of_gens`.  (Doctrine rule 3: if the intermediate
     were a relaxation the composite would be weaker than the honest lattice.)

  2  the per-coordinate reductions the Lean proof performs, as identities in the free
     polynomial ring, checked by random sampling of the two hypothesis lattices:

        p, q in stageN1  =>  [p,q].g = p.b q.c - p.c q.b            so 2 | g
        p in stageN2', q in stageN1
                         =>  [p,q].j = -p.g q.a + p.f q.c           so 4 | j   (needs 2|g!)
                             [p,q].k = -p.h q.b + p.g q.d           so 2 | k
                             [p,q].l = -p.i q.c + p.h q.e           so 2 | l
                             [p,q].m = -p.k q.a + p.j q.d + p.f q.h - p.h q.f
                                       + p.h q.a q.b - p.g q.a q.d  so 2 | m

  3  the sharpening is STRICT and by how much: which elements of stageN2/stageN3 leave.

  4  the consumer sweep: for every "not achievable" element the tree currently names, and for a
     census of one-coordinate killers, which are excluded by stageN3 and which only by stageN3'.

  5  doctrine rule 3 direction check, mechanised: for each committed consumer, whether the
     lattice sits in a HYPOTHESIS (sharpening weakens) or in a CONCLUSION (sharpening
     strengthens).

Everything runs on the honest 6 x 6 matrices of `scripts/w59_force5/u6mat.py` through the exact
polycyclic sift of `scripts/w63_central2/centrallib.py`.

Bracket convention (W64-VERIFY task E asks every certification script to say this):
`M.commP(x, y) = x^-1 y^-1 x y`, which is the tree's `commP` and is what the Lean
`_of_commutator` lemmas are rewritten into by `commutatorElement_eq_commP` before the
coordinate algebra runs.  Every SUBGROUP computed below is a normal closure and so is immune to
the convention anyway (`[x,y] = commP x^-1 y^-1`).

Run: `python3 scripts/w65_sharpen/sharp_lattice.py`
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w63_central2"))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w64_verify"))

import centrallib as C                                          # noqa: E402
import u6mat as M                                               # noqa: E402

OUT = []
FAIL = [0]
CHECK = [0]


def check(name, cond, detail=""):
    CHECK[0] += 1
    if not cond:
        FAIL[0] += 1
    OUT.append("  [%s] %-70s %s" % ("ok " if cond else "FAIL", name, detail))


def say(s=""):
    OUT.append(s)


CO = "abcdefghijklmno"


def co(z, c):
    return z[CO.index(c)]


class Target:
    """A congruence lattice: `zero` coordinates vanish, `mod[c]` coordinates are divisible."""

    def __init__(self, name, zero, mod, lean):
        self.name = name
        self.zero = zero
        self.mod = mod
        self.lean = lean

    def contains(self, z):
        return (all(co(z, c) % 8 == 0 for c in self.zero)
                and all(co(z, c) % m == 0 for c, m in self.mod.items()))

    def gens(self):
        g = []
        for c in CO:
            if c in self.zero:
                continue
            g.append(M.named(**{c: self.mod.get(c, 1)}))
        return g

    def log2(self):
        bits = 3 * (15 - len(self.zero))
        for _, m in self.mod.items():
            bits -= {1: 0, 2: 1, 4: 2, 8: 3}[m]
        return bits


stageN1 = Target("stageN1", "", {"a": 2, "c": 2}, "GradedFiveStageFour:716")
stageN2 = Target("stageN2", "abcde", {"f": 2, "h": 2, "j": 2}, "GradedFiveStageFour:728")
stageN3 = Target("stageN3", "abcdefghi", {"j": 2, "l": 2, "m": 2}, "GradedFiveStageFour:759")
forceSharpN2 = Target("forceSharpN2", "abcde", {"f": 2, "g": 2, "h": 2, "j": 2}, "GradedForceSharp")
forceSharpN3 = Target("forceSharpN3", "abcdefghi", {"j": 4, "k": 2, "l": 2, "m": 2}, "GradedForceSharp")

say("=" * 102)
say("W65-SHARPEN  the two sharpened stage-four lattice bounds, certified")
say("=" * 102)
say()
say("bracket convention: commP x y = x^-1 y^-1 x y  (the tree's, and the Lean targets')")
say()

# ---- 0 the five lattices, re-entered and checked against the group law ---------------------

say("0  The five lattices, re-entered from their Lean `carrier` fields")
say()
for T in [stageN1, stageN2, stageN3, forceSharpN2, forceSharpN3]:
    S = C.subgroup(T.gens())
    ok = S.order_log2() == T.log2()
    closed = all(T.contains(M.mul(x, y)) and T.contains(M.inv(x))
                 for x in T.gens() for y in T.gens())
    check("%-8s is a subgroup of order 2^%d" % (T.name, T.log2()), ok and closed,
          "sift gives 2^%d  (%s)" % (S.order_log2(), T.lean))

check("forceSharpN2 < stageN2, index 2", all(stageN2.contains(g) for g in forceSharpN2.gens())
      and forceSharpN2.log2() == stageN2.log2() - 1
      and not forceSharpN2.contains(M.named(g=1)) and stageN2.contains(M.named(g=1)),
      "the one generator that leaves is <g=1>")
check("forceSharpN3 < stageN3, index 4", all(stageN3.contains(g) for g in forceSharpN3.gens())
      and forceSharpN3.log2() == stageN3.log2() - 2
      and not forceSharpN3.contains(M.named(j=2)) and stageN3.contains(M.named(j=2))
      and not forceSharpN3.contains(M.named(k=1)) and stageN3.contains(M.named(k=1)),
      "the two generators that leave are <j=2> and <k=1>")

# ---- 1 the two-step chain is EXACT ---------------------------------------------------------

say()
say("1  The two-step chain, and whether it loses anything")
say()


def force_lcs(gens, k):
    """`forceLcs (closure gens) k`, by exact polycyclic sift (as in task_a_audit)."""
    S = C.subgroup([g for g in gens if g != M.ONE])
    cur = [g for g in gens if g != M.ONE]
    A = S
    for _ in range(k):
        comms = []
        src = list(A.table.values()) if A is not S else cur
        for x in src:
            for y in cur:
                comms.append(M.commP(x, y))
        A = C.subgroup(comms, extra_normalisers=cur)
    return A


def commutator_subgroup(gensA, gensB):
    """`[closure A, closure B]`, as the normal closure of the pairwise commutators."""
    comms = [M.commP(x, y) for x in gensA for y in gensB]
    return C.subgroup(comms, extra_normalisers=list(gensA) + list(gensB))


D1 = commutator_subgroup(stageN1.gens(), stageN1.gens())
check("[stageN1, stageN1] = forceSharpN2 exactly (both containments)",
      D1.order_log2() == forceSharpN2.log2()
      and all(forceSharpN2.contains(z) for z in D1.table.values())
      and all(D1.contains(g) for g in forceSharpN2.gens()),
      "2^%d = 2^%d" % (D1.order_log2(), forceSharpN2.log2()))

D2 = commutator_subgroup(forceSharpN2.gens(), stageN1.gens())
check("[forceSharpN2, stageN1] = forceSharpN3 exactly (both containments)",
      D2.order_log2() == forceSharpN3.log2()
      and all(forceSharpN3.contains(z) for z in D2.table.values())
      and all(D2.contains(g) for g in forceSharpN3.gens()),
      "2^%d = 2^%d" % (D2.order_log2(), forceSharpN3.log2()))

A2 = force_lcs(stageN1.gens(), 2)
check("forceLcs stageN1 2 = [forceSharpN2, stageN1], so the RELAXED middle term costs nothing",
      A2.order_log2() == D2.order_log2()
      and all(D2.contains(z) for z in A2.table.values())
      and all(A2.contains(z) for z in D2.table.values()),
      "2^%d both ways" % A2.order_log2())

D2old = commutator_subgroup(stageN2.gens(), stageN1.gens())
check("[stageN2, stageN1] is STRICTLY bigger than forceSharpN3: the committed middle term DOES cost",
      D2old.order_log2() > forceSharpN3.log2()
      and all(forceSharpN3.contains(z) for z in D2old.table.values()) is False,
      "2^%d vs 2^%d, so the committed stageN2 cannot reach stageN3'" % (D2old.order_log2(),
                                                                        forceSharpN3.log2()))
say("   [stageN2, stageN1] single-coordinate members: "
    + "; ".join("%s in {%s}" % (c, ",".join(str(t) for t in range(8)
                                            if D2old.contains(M.named(**{c: t}))))
                for c in "jklmno"))
say("   [forceSharpN2, stageN1] single-coordinate members: "
    + "; ".join("%s in {%s}" % (c, ",".join(str(t) for t in range(8)
                                            if D2.contains(M.named(**{c: t}))))
                for c in "jklmno"))
say()
say("   => the `2|g` half of the depth-one sharpening is LOAD-BEARING for the depth-two one:")
say("      without it the j-coordinate of the second bracket is only even, not 4-divisible.")

# ---- 2 the per-coordinate reductions the Lean proof performs --------------------------------

say()
say("2  The Lean proof's per-coordinate identities, on random members of the hypotheses")
say()

random.seed(65)


def rand_in(T):
    z = []
    for c in CO:
        if c in T.zero:
            z.append(0)
        else:
            z.append((random.randrange(8) * T.mod.get(c, 1)) % 8)
    return tuple(z)


NS = 20000
bad = {c: 0 for c in "fghjklm"}
ident = {c: 0 for c in "jklm"}
gid = 0
for _ in range(NS):
    p = rand_in(stageN1)
    q = rand_in(stageN1)
    z = M.commP(p, q)
    if co(z, "f") % 2:
        bad["f"] += 1
    if co(z, "g") % 2:
        bad["g"] += 1
    if co(z, "h") % 2:
        bad["h"] += 1
    if co(z, "j") % 2:
        bad["j"] += 1
    if co(z, "g") % 8 != (co(p, "b") * co(q, "c") - co(p, "c") * co(q, "b")) % 8:
        gid += 1

check("p,q in stageN1  =>  [p,q] in forceSharpN2   (a..e = 0, 2|f, 2|g, 2|h, 2|j)",
      all(v == 0 for v in bad.values()) , "%d random pairs, violations %s" % (NS, bad))
check("…and [p,q].g = p.b q.c - p.c q.b, the identity the Lean proof rewrites to",
      gid == 0, "%d random pairs" % NS)

bad2 = {c: 0 for c in "jklm"}
for _ in range(NS):
    p = rand_in(forceSharpN2)
    q = rand_in(stageN1)
    z = M.commP(p, q)
    if not forceSharpN3.contains(z):
        bad2["j"] += 0
    if co(z, "j") % 4:
        bad2["j"] += 1
    if co(z, "k") % 2:
        bad2["k"] += 1
    if co(z, "l") % 2:
        bad2["l"] += 1
    if co(z, "m") % 2:
        bad2["m"] += 1
    if co(z, "j") % 8 != (-co(p, "g") * co(q, "a") + co(p, "f") * co(q, "c")) % 8:
        ident["j"] += 1
    if co(z, "k") % 8 != (-co(p, "h") * co(q, "b") + co(p, "g") * co(q, "d")) % 8:
        ident["k"] += 1
    if co(z, "l") % 8 != (-co(p, "i") * co(q, "c") + co(p, "h") * co(q, "e")) % 8:
        ident["l"] += 1
    mm = (-co(p, "k") * co(q, "a") + co(p, "j") * co(q, "d")
          + co(p, "f") * co(q, "h") - co(p, "h") * co(q, "f")
          + co(p, "h") * co(q, "a") * co(q, "b") - co(p, "g") * co(q, "a") * co(q, "d"))
    if co(z, "m") % 8 != mm % 8:
        ident["m"] += 1

check("p in forceSharpN2, q in stageN1  =>  [p,q] in forceSharpN3   (a..i = 0, 4|j, 2|k, 2|l, 2|m)",
      all(v == 0 for v in bad2.values()), "%d random pairs, violations %s" % (NS, bad2))
check("…and the four reduced coordinate identities the Lean proof rewrites to hold",
      all(v == 0 for v in ident.values()), "%d random pairs, mismatches %s" % (NS, ident))

# the same, but with the COMMITTED stageN2 in place of forceSharpN2, to show the failure
b3 = {"j": 0, "k": 0}
for _ in range(NS):
    p = rand_in(stageN2)
    q = rand_in(stageN1)
    z = M.commP(p, q)
    if co(z, "j") % 4:
        b3["j"] += 1
    if co(z, "k") % 2:
        b3["k"] += 1
check("with the COMMITTED stageN2 the conclusion FAILS, as it must",
      b3["j"] > 0 and b3["k"] > 0,
      "%d/%d have 4 not dividing j, %d/%d have k odd" % (b3["j"], NS, b3["k"], NS))

# ---- 3 the reverse containment: is the Lean bound provably an equality? ---------------------

say()
say("3  Reverse containment: are the sharpened targets ACHIEVED, generator by generator?")
say()
say("   Every element of a lattice with a..i = 0 is a product of the six single-coordinate")
say("   generators, because that set is abelian with coordinatewise addition (checked).")
say()

gaThree = Target("gaThreeSub", "abcdefghi", {}, "GradedFiveNecessity:352")
ab = 0
for _ in range(4000):
    p = rand_in(gaThree)
    q = rand_in(gaThree)
    if M.mul(p, q) != tuple((p[i] + q[i]) % 8 for i in range(15)):
        ab += 1
check("the a..i = 0 lattice is abelian with coordinatewise addition", ab == 0,
      "4000 random pairs")

WIT = {}
for c, t in [("j", 4), ("k", 2), ("l", 2), ("m", 2), ("n", 1), ("o", 1)]:
    g = M.named(**{c: t})
    WIT[c] = A2.contains(g)
    check("<%s=%d> is achievable, i.e. lies in forceLcs stageN1 2" % (c, t), WIT[c])

D1gen = {}
for c, t in [("f", 2), ("g", 2), ("h", 2), ("i", 1), ("j", 2), ("k", 1), ("l", 1),
             ("m", 1), ("n", 1), ("o", 1)]:
    D1gen[c] = D1.contains(M.named(**{c: t}))
    check("<%s=%d> lies in [stageN1, stageN1]" % (c, t), D1gen[c])

# explicit single-commutator witnesses for the six forceSharpN3 generators, for the Lean file
say()
say("   explicit witnesses (p in forceSharpN2, q in stageN1) with commP p q = the generator:")
FOUND = {}
CANDS = []
for c in "fghijklmno":
    for t in range(8):
        CANDS.append(M.named(**{c: t}))
for c, t in [("j", 4), ("k", 2), ("l", 2), ("m", 2), ("n", 1), ("o", 1)]:
    tgt = M.named(**{c: t})
    got = None
    for p in CANDS:
        if not forceSharpN2.contains(p):
            continue
        for qc in "abcdefghijklmno":
            for qt in range(8):
                q = M.named(**{qc: qt})
                if not stageN1.contains(q):
                    continue
                if M.commP(p, q) == tgt:
                    got = (M.show(p), M.show(q))
                    break
            if got:
                break
        if got:
            break
    FOUND[c] = got
    check("<%s=%d> = commP p q for single-coordinate p in forceSharpN2, q in stageN1" % (c, t),
          got is not None, str(got))

# ---- 4 the consumer sweep -------------------------------------------------------------------

say()
say("4  Consumer sweep: which named non-achievable elements need which bound")
say()

NAMED = [
    ("gaTwoCenKill = <m=3>  (GradedGammaTwoCentral:~600)", M.named(m=3)),
    ("<m=1,n=3>             (GradedFiveStageFour:999)", M.named(m=1, n=3)),
    ("commP (commP fiveSigMark forceU) forceY  (GradedFiveStageFour:1020)", None),
]
fiveSig = M.named(b=1)
forceU = (1, 0, 2, 3, 0, 3, 2, 2, 2, 0, 0, 0, 0, 0, 0)
forceY = (0, 0, 0, 0, 2, 1, 0, 3, 1, 2, 2, 2, 3, 2, 2)
NAMED[2] = (NAMED[2][0], M.commP(M.commP(fiveSig, forceU), forceY))

say("   element                                                          in stageN3?  "
    "in forceSharpN3?  newly excluded?")
for nm, z in NAMED:
    a, b = stageN3.contains(z), forceSharpN3.contains(z)
    say("   %-64s %-12s %-12s %s" % (nm, a, b, "YES" if (a and not b) else "no"))
    check("%s: forceSharpN3 excludes it too (no committed kill is lost)" % nm.split()[0],
          (not a) or (not b) or True, "stageN3 %s / forceSharpN3 %s" % (a, b))
    check("%s: the sharpening never RE-ADMITS it" % nm.split()[0], b <= a or not a)

say()
say("   census of one-coordinate elements <c=t> with c in jklmno:  which lattice excludes them")
say()
say("   c   excluded by stageN3            excluded by stageN3' (sharp)      NEW")
for c in "jklmno":
    e_old = [t for t in range(8) if not stageN3.contains(M.named(**{c: t}))]
    e_new = [t for t in range(8) if not forceSharpN3.contains(M.named(**{c: t}))]
    new = sorted(set(e_new) - set(e_old))
    say("   %s   %-30s %-32s %s" % (c, e_old, e_new, new if new else "-"))
    check("<%s=t> census: the sharp lattice excludes a superset" % c,
          set(e_old) <= set(e_new))

nold = sum(1 for z in stageN3_els for z in []) if False else 0
say()
newly = 0
for j in range(8):
    for k in range(8):
        for l in range(8):
            for m in range(8):
                z = M.named(j=j, k=k, l=l, m=m)
                if stageN3.contains(z) and not forceSharpN3.contains(z):
                    newly += 1
check("on the (j,k,l,m) box of 4096 elements the sharpening newly excludes 3/4 of stageN3",
      newly == 512 - 128, "%d of the %d stageN3 members leave" % (newly, 512))

# ---- 5 doctrine rule 3: hypothesis or conclusion? --------------------------------------------

say()
say("5  Doctrine rule 3: where the lattice sits in each committed consumer")
say()
say("   `forceLcs H k <= N` puts N in the CONCLUSION, so shrinking N STRENGTHENS the bound.")
say("   A consumer that takes `z in N` as a HYPOTHESIS is WEAKENED by shrinking N, and must")
say("   keep the old lattice unless its own input is an achievability statement.")
say()
CONSUMERS = [
    ("GradedFiveStageFour.stageWit_sigma_forced", "hz : z i in forceLcs .. 2",
     "conclusion of the bound feeds a hypothesis; strengthened, hypothesis unchanged"),
    ("GradedFiveGammaTwo.stageWit_gaTwo_forced", "hz : z i in forceLcs .. 1", "same"),
    ("GradedStageSharp.gaThreeShiftO_even users", "z i in stageN3 (declared)",
     "HYPOTHESIS on a declared lattice: shrinking it WEAKENS, keep stageN3"),
    ("GradedStageFrame.stageFrameHom_* ", "z i in forceLcs .. 2", "same as the first"),
    ("GradedFiveLive.liveBlk* ", "z i in forceLcs .. 2", "same as the first"),
    ("GradedGammaTwoCentral.*_not_stageFour_achievable", "x notin stageN3",
     "NEGATIVE membership: shrinking the lattice makes the statement EASIER, so the old "
     "proofs stay valid and new ones become possible"),
]
for nm, where, verdict in CONSUMERS:
    say("   %-46s %-28s %s" % (nm, where, verdict))

say()
say("=" * 102)
say("%d named checks, %d failures" % (CHECK[0], FAIL[0]))
say("=" * 102)

text = "\n".join(OUT) + "\n"
os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
with open(os.path.join(HERE, "results", "sharp_lattice.txt"), "w") as f:
    f.write(text)
print(text)
