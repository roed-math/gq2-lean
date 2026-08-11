"""W62-SEPARATE: every claim about the separating marking, checked on honest 6x6 matrices.

The marking (`sepS, sepX, sepY, sepU, sepV`) is the one the Lean file commits.  Everything here
runs through `scripts/w59_force5/u6mat.py` - matrix multiplication and back-substitution
inverses - and wave 61's `sharp4lib`, so no formula transcribed into Lean is trusted.

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
import os, sys, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
for d in ("w61_sharp4", "w59_force5", "w60_stage4", "w60_sharp5"):
    sys.path.insert(0, os.path.join(os.path.dirname(HERE), d))
import sharp4lib as L, u6mat as M, modlib as MD                        # noqa: E402

OUT, FAIL = [], []
IJ, IO = 9, 14


def say(s=""):
    print(s)
    OUT.append(s)


def gate(name, got, want=True):
    ok = (got == want)
    say("  [%s] %s%s" % ("PASS" if ok else "FAIL", name,
                         "" if ok else "   got %r want %r" % (got, want)))
    if not ok:
        FAIL.append(name)


sepS = M.named(a=1, c=1, h=1)
sepX = M.named(a=1)
sepY = M.named(a=2)
sepU = M.named(d=1, e=1, g=1, m=1, n=1)
sepV = M.named(a=1, i=1, k=1, n=1)
m = [sepS, sepX, sepY, sepU, sepV]
sepZ = M.commP(M.commP(sepS, sepU), sepU)

say("== 1. the marking ==")
say("  letters  %s" % " | ".join(M.show(g) for g in m))
r = L.relator(m)
say("  relator  %s" % M.show(r))
gate("the relator is gamma_3-shaped", all(r[k] == 0 for k in range(9)))
gate("the relator's class-three row j is ODD", r[IJ] % 2 == 1)
gate("the relator's class-five residue is ODD", r[IO] % 2 == 1)
gate("the relator is exactly <j=7, o=7>", r == M.named(j=7, o=7))
gate("the handle block is live", M.commP(sepU, sepV) != M.ONE)
gate("the relator is NOT central (so wave 61's admissibility fails here)",
     any(r[k] for k in range(14)), True)

say()
say("== 2. the dressing ==")
say("  [[sigma, U], U] = %s" % M.show(sepZ))
gate("the dressing is <l=1, m=1>", sepZ == M.named(l=1, m=1))
gate("the dressing is gamma_3-shaped", all(sepZ[k] == 0 for k in range(9)))
B = L.gamma3_basis(m)
gate("the dressing is achievable (in the honest gamma_3 of the image)",
     L.in_module(B, L.vec(sepZ)))
sh = L.slot_shift(m, 4, L.vec(sepZ))
say("  shift of the V-handle slot: %s" % (sh,))
gate("the shift is CENTRAL (its five lower rows vanish)", all(sh[t] == 0 for t in range(5)))
gate("the shift's class-five row is ODD", sh[5] % 2 == 1)
gate("the shift is exactly <o=7>", sh == (0, 0, 0, 0, 0, 7))
dressed = [sepS, sepX, sepY, sepU, M.mul(sepV, sepZ)]
say("  relator of the dressed marking: %s" % M.show(L.relator(dressed)))
gate("dressed relator = relator * <o=7>", L.relator(dressed) == M.mul(r, M.named(o=7)))

say()
say("== 3. the three verdicts ==")
IB = L.image_basis(m, B)
gate("KILL: no achievable stage-four dressing kills the relator (the forcing HOLDS)",
     L.kill_exists(m, basis=IB), False)
gate("ORTH: the parity line FAILS", L.orth_all(m, B), False)
gate("CEN: the sharp line FAILS too", L.orth_central(m, basis=IB), False)
say("  |gamma_3(im)| %d   |image| %d   central image %s"
    % (MD.card(B, 6), MD.card(IB, 6), L.central_basis(IB)))
say("  covectors %s" % ([L.covector(m, i) for i in range(5)],))

say()
say("== 4. the obstruction is the class-three row, exactly ==")
bad = [(v, L.shift(m, [(0,) * 6] * 3 + [(0,) * 6, v])) for v in L.members(B)]
gate("every achievable single-slot shift has an EVEN class-three j-row",
     all(s[0] % 2 == 0 for (_, s) in bad))
allshift = []
for i in range(5):
    mat = L.slot_matrix(m, i)
    for g in L.members(B):
        allshift.append(L.apply_matrix(mat, g))
gate("every achievable single-slot shift has even j, k and l rows",
     all(s[0] % 2 == 0 and s[1] % 2 == 0 and s[2] % 2 == 0 for s in allshift))
odd = [(i, g) for i in range(5) for g in L.members(B)
       if L.apply_matrix(L.slot_matrix(m, i), g)[5] % 2]
say("  %d single-slot achievable dressings pair ODDLY" % len(odd))

say()
say("== 5. the ZMod 8 content: mod 2 the obstruction is invisible ==")
gate("the shift's class-three rows vanish identically mod 2 (so no covector sees them)",
     all(s[0] % 2 == 0 and s[1] % 2 == 0 and s[2] % 2 == 0 for s in allshift))
gate("the relator's class-three row is nonzero mod 2", r[IJ] % 2 == 1)

say()
say("== summary ==")
say("  failures: %s" % (", ".join(FAIL) if FAIL else "none"))
with open(os.path.join(HERE, "results", "verify_sep.txt"), "w") as f:
    f.write("$ python3 verify_sep.py\n\n" + "\n".join(OUT) + "\n")
