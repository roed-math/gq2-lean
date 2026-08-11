"""W63-CENTRAL2: the gamma_2 centrality line at class five, and the KILL that decides it.

Every measurement is taken on the honest `6 x 6` matrices of `scripts/w59_force5/u6mat.py`;
the gamma_2 shift is read off the relator rather than from any emitted closed form, and the
achievable lattices are computed by the polycyclic sift of `centrallib.py`, not declared.

Sections
  0  the binder point and its relator
  1  the achievable gamma_2 lattice `forceLcs H 1`, exactly
  2  the achievable stage-four lattice `forceLcs H 2`, and where the killer sits
  3  THE KILL: an achievable gamma_2 dressing of the SIGMA slot that kills the frame
  4  the kill's certificate as a product of commutators of the point's own letters
  5  the three lines at the point: forcing, parity, centrality - all three FAIL
  6  wave 62's odd-channel witness is NOT central: the two lines are separated
  7  the gamma_2 shift is not a homomorphism of the dressing tuple
  8  the general mechanism: the sigma slot's class-four coordinate against `x0.e`

BRACKET CONVENTION.  [IMMUNE]
This script only ever sifts brackets into a closure, which is convention-IMMUNE (the
generated subgroup is the same in either convention), so nothing here depends on the
choice.  Its Lean target is written with commP.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import centrallib as C                                          # noqa: E402
import u6mat as M                                               # noqa: E402

OUT = []
FAIL = [0]
CHECK = [0]


def check(name, cond, detail=""):
    CHECK[0] += 1
    if not cond:
        FAIL[0] += 1
    OUT.append("  [%s] %-58s %s" % ("ok " if cond else "FAIL", name, detail))


def say(s=""):
    OUT.append(s)


# ---- 0 the binder point -------------------------------------------------------------------

say("=" * 92)
say("W63-CENTRAL2  derivation log")
say("=" * 92)
say()
say("0  Wave 60's stage-four binder point  stageWit h j stageX")
say()

mk = C.stage_wit(C.stageX)
S, X, Y, U, V = mk[0], mk[1], mk[2], mk[3], mk[4]
say("   sigma slot  fiveSigMark * stageX = %s" % M.show(S))
say("   x0 slot     stageX               = %s" % M.show(X))
say("   x1 slot     stageY               = %s" % M.show(Y))
say("   handle U    stageU               = %s" % M.show(U))
say("   handle V    stageV               = %s" % M.show(V))
say()
rel = M.sqRelWord(mk)
check("relator is the central translation <o=1>", rel == M.liftC(1), M.show(rel))
check("undressed frame kills outright",
      M.sqRelWord(C.stage_wit(M.ONE)) == M.ONE)
check("stageX.e is ODD (the channel the residue runs on)", C.co(X, "e") % 2 == 1,
      "stageX.e = %d" % C.co(X, "e"))

# ---- 1 the achievable gamma_2 lattice -----------------------------------------------------

say()
say("1  The achievable gamma_2 lattice  forceLcs (stageImage h j stageX) 1 = [H, H]")
say()

gens = [g for g in mk if g != C.ONE]
H = C.subgroup(gens)
A1 = C.derived_of(gens)
say("   log2 |H|              = %d" % H.order_log2())
say("   log2 |forceLcs H 1|   = %d      (|.| = %d)" % (A1.order_log2(), 2 ** A1.order_log2()))
check("|forceLcs H 1| = 67108864, wave 61's own census count", 2 ** A1.order_log2() == 67108864)

# the lattice is exactly the box {gamma_2-shaped, f g h j even}
BOXEVEN = "fghj"
BOXFREE = "iklmno"


def in_box(z):
    return (all(z[k] == 0 for k in range(5))
            and all(z[C.IDX[c]] % 2 == 0 for c in BOXEVEN))


box_size = (4 ** len(BOXEVEN)) * (8 ** len(BOXFREE))
check("the box {gamma_2, f g h j even} has the same order", box_size == 2 ** A1.order_log2(),
      "box = %d" % box_size)
random.seed(63)
bad = 0
for _ in range(4000):
    t = [0] * 15
    for c in BOXEVEN:
        t[C.IDX[c]] = 2 * random.randrange(4)
    for c in BOXFREE:
        t[C.IDX[c]] = random.randrange(8)
    if not A1.contains(tuple(t)):
        bad += 1
check("4000 random box elements all lie in forceLcs H 1", bad == 0, "misses %d" % bad)
bad = 0
for e in A1.elements() if A1.order_log2() <= 16 else []:
    if not in_box(e):
        bad += 1
for c in "fghijklmno":
    want_odd = c in BOXFREE
    got = A1.contains(M.named(**{c: 1}))
    check("forceLcs H 1 contains <%s=1>: %s" % (c, got), got == want_odd)
say()
say("   => the achievable gamma_2 lattice is EXACTLY {z gamma_2-shaped : f, g, h, j even},")
say("      so its class-four coordinate m is UNRESTRICTED and in particular takes odd values.")

# ---- 2 the achievable stage-four lattice --------------------------------------------------

say()
say("2  The achievable stage-four lattice  forceLcs H 2, and where the killer sits")
say()
comms = []
for x in A1.table.values():
    for y in gens:
        comms.append(M.commP(x, y))
A2 = C.subgroup(comms, extra_normalisers=gens)
say("   log2 |forceLcs H 2|   = %d" % A2.order_log2())
check("forceLcs H 2 does NOT contain <m=1>", not A2.contains(M.named(m=1)))
check("forceLcs H 2 does NOT contain <m=3>", not A2.contains(M.named(m=3)))
check("forceLcs H 2 does contain <m=2>", A2.contains(M.named(m=2)))
check("every element of forceLcs H 2 has even m (stageN3, committed)",
      all(C.co(e, "m") % 2 == 0 for e in A2.elements()))
say()
say("   => the wider lattice is what supplies an ODD class-four coordinate.  Wave 60's")
say("      soundness chain forceLcs_two_le_stageN3 forces m even, and that is exactly the")
say("      hypothesis the gamma_2 lattice breaks.")

# ---- 3 the kill ---------------------------------------------------------------------------

say()
say("3  THE KILL: <m=3> on the SIGMA slot")
say()
KILL = M.named(m=3)
check("<m=3> is achievable at gamma_2", A1.contains(KILL))
check("<m=3> is gamma_3-shaped (so its SHAPE is not what is new)", M.is_ga(KILL, 3))
check("<m=3> is NOT achievable at stage four", not A2.contains(KILL))
for h in range(1, 5):
    for jj in range(h):
        m2 = C.stage_wit(C.stageX, h=h, jj=jj)
        z = [KILL] + [C.ONE] * (len(m2) - 1)
        d = C.dress(m2, z)
        sh = C.shift(m2, z)
        check("h=%d j=%d: the dressed frame is KILLED" % (h, jj), M.sqRelWord(d) == M.ONE)
        check("h=%d j=%d: the shift is the central translation liftO 7" % (h, jj),
              sh == M.liftC(7), M.show(sh))
        check("h=%d j=%d: dressing slot 0 by w reparametrises the point" % (h, jj),
              d == C.stage_wit(M.mul(C.stageX, KILL), h=h, jj=jj))

# ---- 4 the certificate --------------------------------------------------------------------

say()
say("4  The kill as a product of commutators of the point's own letters")
say()
cert = M.mul(M.power(M.commP(M.inv(S), U), 2), M.commP(Y, M.mul(X, U)))
say("   commP(S^-1, U)^2 * commP(Y, X*U) = %s" % M.show(cert))
check("the certificate equals <m=3>", cert == KILL)
check("commP(S^-1, U) lies in [H, H]", A1.contains(M.commP(M.inv(S), U)))
check("commP(Y, X*U) lies in [H, H]", A1.contains(M.commP(Y, M.mul(X, U))))
say("   (in Lean: commP p q = commutator (p^-1) (q^-1), so both factors are honest")
say("    commutators of members of the image subgroup.)")

# ---- 5 the three lines --------------------------------------------------------------------

say()
say("5  The three gamma_2 lines at the point")
say()
zkill = [KILL] + [C.ONE] * (len(mk) - 1)
shk = C.shift(mk, zkill)
chk = C.shift_chan(mk, zkill)
check("GaTwoForces FAILS  (an achievable kill with an odd residue)",
      M.sqRelWord(C.dress(mk, zkill)) == M.ONE and C.co(rel, "o") % 2 == 1)
check("GaTwoCentral FAILS (the shift is central with an ODD class-five row)",
      C.is_central(shk) and shk[14] % 2 == 1, "shift = %s" % M.show(shk))
check("GaTwoOrth FAILS    (the same shift has an odd class-five row)", shk[14] % 2 == 1)
check("the kill's three-channel functional is ODD", chk % 2 == 1, "chan = %d" % chk)
check("wave 62's transport holds at the kill: residue + chan is even",
      (C.co(rel, "o") + chk) % 2 == 0)
say()
say("   => wave 62's even-channel hypothesis is LOAD-BEARING: the conclusion is FALSE")
say("      without it, so no restatement - on centrality or on anything else - removes it.")

# ---- 6 wave 62's witness is not central ---------------------------------------------------

say()
say("6  Wave 62's odd-channel witness  [x0, x1] on the x1 slot")
say()
w62 = [C.ONE, C.ONE, M.commP(X, Y)] + [C.ONE] * (len(mk) - 3)
sh62 = C.shift(mk, w62)
check("[x0, x1] is achievable at gamma_2", A1.contains(M.commP(X, Y)))
check("its three-channel functional is ODD", C.shift_chan(mk, w62) % 2 == 1,
      "chan = %d" % C.shift_chan(mk, w62))
check("its shift is NOT central", not C.is_central(sh62), "shift = %s" % M.show(sh62))
say()
say("   => the centrality line does not see wave 62's witness at all: the parity line fails")
say("      there and the centrality line does not.  A separate dressing was needed, and the")
say("      one section 3 produces is central.")

# ---- 7 the shift is not a homomorphism ----------------------------------------------------

say()
say("7  The gamma_2 shift is NOT a homomorphism of the dressing tuple")
say()


def boxrand():
    t = [0] * 15
    for c in BOXEVEN:
        t[C.IDX[c]] = 2 * random.randrange(4)
    for c in BOXFREE:
        t[C.IDX[c]] = random.randrange(8)
    return tuple(t)


for i in range(5):
    bad = 0
    for _ in range(200):
        g1, g2 = boxrand(), boxrand()
        if C.shift(mk, C.slot(i, M.mul(g1, g2))) != M.mul(C.shift(mk, C.slot(i, g1)),
                                                          C.shift(mk, C.slot(i, g2))):
            bad += 1
    say("   slot %d: multiplicativity fails at %3d of 200 random achievable pairs" % (i, bad))
bad = 0
for _ in range(200):
    z1 = [boxrand() for _ in range(5)]
    z2 = [boxrand() for _ in range(5)]
    zz = [M.mul(z1[k], z2[k]) for k in range(5)]
    if C.shift(mk, zz) != M.mul(C.shift(mk, z1), C.shift(mk, z2)):
        bad += 1
say("   five-slot: multiplicativity fails at %3d of 200 random achievable pairs" % bad)
check("multiplicativity genuinely fails (wave 61's power engine does not transpose)", bad > 0)

# ---- 8 the general mechanism --------------------------------------------------------------

say()
say("8  The mechanism: the sigma slot's class-four coordinate against  x0.e")
say()
say("   gaThreePair z L = z.m L.e - z.n L.a + z.j L.i - z.l L.f + z.l(L.a L.b) - z.k(L.a L.e)")
say("   so a sigma-slot dressing's class-four coordinate m is paired against x0.e, and at")
say("   wave 60's point x0.e = 5 is a UNIT.  The class-five row of a slot-0 dressing by")
say("   <m=t> is therefore 5t, which runs over all of Z/8 as t does.")
bad = 0
for t in range(8):
    sh = C.shift(mk, C.slot(0, M.named(m=t)))
    if sh != M.liftC((5 * t) % 8):
        bad += 1
check("slot-0 dressing by <m=t> has shift liftO (5t), t = 0..7", bad == 0)
say()
say("   The same reading is wave 61's stage-four covector table, whose sigma row is")
say("   (L.i, L.a L.e, L.f + L.a L.b, L.e, L.a) against the dressing's (j,k,l,m,n): the")
say("   m-entry is L.e.  Wave 60's exclusion survives only because forceLcs H 2 <= stageN3")
say("   makes that coordinate even.  One filtration step wider it is not even.")

say()
say("=" * 92)
say("%d named checks, %d failures" % (CHECK[0], FAIL[0]))
say("=" * 92)

text = "\n".join(OUT) + "\n"
os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
with open(os.path.join(HERE, "results", "derive.txt"), "w") as f:
    f.write(text)
print(text)
