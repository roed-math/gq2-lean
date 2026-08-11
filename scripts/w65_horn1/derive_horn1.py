"""W65-HORN1: the class-five row of the diagonal residue, derived and certified.

Every claim in `GQ2/Dyadic/SqCore/GradedCensusHorn.lean`'s docstring that is not itself a Lean
theorem is checked here, from the committed exact `U_6` engine of `scripts/w64_sep0h/seplib.py`
(which certifies its own coordinate law against honest integer `6 x 6` matrices).

The object throughout is the DIAGONAL RESIDUE

    D  =  sqWord(s * x, x, y) * sqWord(s, x, y)^{-1},

which is the relator of the diagonally dressed frame once the undressed frame kills, and whose
`(1,6)` row is the class-five separation bit W64-CENSUS5's horn 1 reads.

Sections:
  0  the engine, against the committed Lean shapes;
  1  the row modulo 2 under three hypothesis sets, and what survives;
  2  the FACTORED identity and its 207-monomial witness, against the committed Lean file;
  3  the counterexamples: exhaustive small search, and the two minimal supports;
  4  the gauge is not a proof artefact: sampling at an ungauged sigma;
  5  calibration at the committed points.
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "scripts", "w64_sep0h"))

import seplib as L                                                # noqa: E402

NAMES = L.NAMES
CHECKS = []


def head(t):
    print()
    print("=" * 98)
    print("== " + t)
    print("=" * 98)
    print()


def ok(cond, label, detail=""):
    CHECKS.append(bool(cond))
    print(f"   [{'ok ' if cond else 'FAIL'}] {label:<66} {detail}")


# ----------------------------------------------------------------------------------------------
# symbolic letters, with the even columns carried as 2 * (a fresh half)


def sym(prefix, evens=(), zeros=()):
    co = {}
    for k in NAMES:
        if k in zeros:
            co[k] = L.PolyRing.zero
        elif k in evens:
            co[k] = L.s_scal(2, L.s_var(prefix + k))      # the Lean file's half-variable names
        else:
            co[k] = L.s_var(prefix + "." + k)
    return L.U6(co, L.PolyRing)


def residue(s, x, y):
    return L.mul(L.sqWord(L.mul(s, x), x, y), L.inv(L.sqWord(s, x, y)))


def odd_part(p):
    return {m: c % 2 for m, c in p.items() if c % 2}


def show(ms, limit=99):
    return ", ".join("*".join(m) for m in sorted(ms, key=lambda t: (len(t), t))[:limit])


YEV = ("a", "b", "c", "d", "e")

head("0  THE ENGINE, against the committed Lean shapes")
print("   `seplib` re-certifies its coordinate law against honest integer 6 x 6 matrices;")
print("   here we only pin the shapes the Lean file quotes.")
print()

s0, x0, y0 = sym("s"), sym("x"), sym("y")
D0 = residue(s0, x0, y0)
ok(len(D0.co["o"]) == 210, "the class-five row of the residue has 210 terms, no hypotheses",
   len(D0.co["o"]))
ok(all(not D0.co[k] for k in ("a", "b", "c", "d", "e", "f", "g", "h", "i")),
   "the residue lies in gamma_4: its nine rows of class <= 2 vanish identically")
low = L.sqWord(L.mul(s0, x0), x0, y0)
ok(all(low.co[k] == L.sqWord(s0, x0, y0).co[k] for k in
       ("a", "b", "c", "d", "e", "f", "g", "h", "i")),
   "`SqU6.sqWord_diagDress_low` reproduced: the dressing moves no row of class <= 2")

head("1  THE ROW MODULO 2, under three hypothesis sets")
print("   The `x1` letter's five abelian columns are EVEN throughout: that is forced by the")
print("   relator's own five abelian rows (`censHorn_x1_cols_even`), not assumed.")
print()

TARGET = ("x.e", "y.f", "y.h")


def sweep(sev=(), xev=("a", "c"), xzero=()):
    s = sym("s", evens=sev)
    x = sym("x", evens=xev, zeros=xzero)
    y = sym("y", evens=YEV)
    D = residue(s, x, y)
    tgt = L.s_mul(L.s_var("x.e"), L.s_mul(L.s_var("y.f"), L.s_var("y.h")))
    return D, odd_part(L.s_sub(D.co["o"], tgt))


_, oddA = sweep()
ok(len(oddA) == 17, "under `stageN1` on x0 alone: 17 correction monomials survive", len(oddA))
print(f"        {show(oddA)}")
gears = {"s.a", "s.c", "s.e", "s.f", "s.j"}
ok(all(gears & set(m) for m in oddA),
   "every correction reads the SIGMA slot, through a, c, e, f or j", "0 exceptions")
noxe = [m for m in oddA if "x.e" not in m]
ok(len(noxe) == 6, "6 of the 17 do NOT carry the gearing x.e: these are what horn 1 fears", len(noxe))
print(f"        {show(noxe)}")
ok(all({"s.a", "s.e"} & set(m) for m in noxe),
   "and every one of those 6 carries s.a or s.e", "so two sigma columns suffice")

_, oddB = sweep(xev=("a", "c", "f", "g"), xzero=("b",))
ok(len(oddB) == 8, "under the tree's committed x0 gauge (`sqWord_diagDress_o_gauge`): 8 survive",
   len(oddB))

_, oddC = sweep(sev=("a", "c", "e"))
ok(len(oddC) == 2, "under this file's gauge (sigma a, c, e even): 2 survive, both with x.e",
   len(oddC))
print(f"        {show(oddC)}")
ok(all("x.e" in m for m in oddC), "so the whole row is a multiple of the gearing")

head("2  THE FACTORED IDENTITY, and the witness in the committed Lean file")

s, x, y = sym("s", ("a", "c", "e")), sym("x", ("a", "c")), sym("y", YEV)
D = residue(s, x, y)
Q = L.s_add(L.s_add(L.s_mul(L.s_var("y.f"), L.s_var("y.h")),
                    L.s_mul(L.s_var("s.f"), L.s_var("x.h"))),
            L.s_mul(L.s_var("s.j"), L.s_var("x.d")))
rest = L.s_sub(D.co["o"], L.s_mul(L.s_var("x.e"), Q))
ok(not odd_part(rest), "D.o - x.e * (y.f*y.h + s.f*x.h + s.j*x.d) is EVEN over Z", "0 odd terms")
wit = {m: c // 2 for m, c in rest.items()}
ok(len(wit) == 207, "the even witness has 207 monomials", len(wit))
ok(max(len(m) for m in wit) == 5, "of degree at most 5", max(len(m) for m in wit))


def lean_mono(m, c):
    body = " * ".join(m)
    if c == 1:
        return "+ " + body
    if c == -1:
        return "- " + body
    return f"+ {c} * {body}" if c > 0 else f"- {abs(c)} * {body}"


emitted = ["    " + lean_mono(m, wit[m]) for m in sorted(wit, key=lambda t: (len(t), t))]
with open(os.path.join(HERE, "results", "witness_o.lean.txt"), "w") as fh:
    fh.write("\n".join(emitted) + "\n")

leanfile = os.path.join(ROOT, "GQ2", "Dyadic", "SqCore", "GradedCensusHorn.lean")
committed = []
if os.path.exists(leanfile):
    grab = False
    for line in open(leanfile):
        if line.startswith("def censHornWit"):
            grab = True
            continue
        if grab:
            if not line.startswith("    "):
                break
            committed.append(line.rstrip("\n"))
ok(committed == emitted,
   "the witness in `GQ2/Dyadic/SqCore/GradedCensusHorn.lean` IS this one, line for line",
   f"{len(committed)} committed lines")

head("3  THE COUNTEREXAMPLES: the recorded form at an ungauged sigma")
print("   Recorded: the row is `x0.e * x1.f * x1.h` mod 2 under `stageN1` plus the relator's")
print("   own x1 columns.  Exhaustive small search, with x1 = 1 (its columns are then 0, so")
print("   the recorded hypotheses hold) and every letter on `stageN1`.")
print()


def mk(**kw):
    return L.U6({k: kw.get(k, 0) for k in NAMES}, L.IntRing)


def cent_odd(s, x, y):
    D = L.red(residue(s, x, y))
    return (all(D.co[k] % 8 == 0 for k in NAMES if k != "o"), D.co["o"] % 8)


FREE = [k for k in NAMES if k not in ("a", "c")]        # stageN1 pins the a and c columns
hits = []
for sc in FREE:                                          # every ONE-column sigma on stageN1
    for i, xc1 in enumerate(FREE):                       # every TWO-column x0 on stageN1
        for xc2 in FREE[i + 1:]:
            s_, x_ = mk(**{sc: 1}), mk(**{xc1: 1, xc2: 1})
            central, o = cent_odd(s_, x_, mk())
            if central and o % 2 == 1 and x_.e % 2 == 0:
                hits.append((sc, (xc1, xc2), o))
ok(len(hits) == 2, "exactly TWO counterexamples in the whole one-column/two-column range",
   len(hits))
for sc, xc, o in hits:
    print(f"        sigma = <{sc} = 1>,  x0 = <{xc[0]} = 1, {xc[1]} = 1>,  x1 = 1"
          f"   ->  residue = liftO {o}")
ok(all(sc == "e" for sc, _, _ in hits), "both have sigma = <e = 1>: the fifth abelian column",
   "the column `stageN1` cannot see")
ok(all(o == 1 for _, _, o in hits), "both residues are liftO 1: CENTRAL with an ODD (1,6) row")

gauged = [h for h in hits if mk(**{h[0]: 1}).e % 2 == 0]
ok(not gauged, "and NONE of them survives the added hypothesis 2 | s.e", f"{len(gauged)} left")

for sc, xc, o in hits:                                   # independent 6 x 6 matrix recheck
    s_, x_ = mk(**{sc: 1}), mk(**{xc[0]: 1, xc[1]: 1})
    P = L.mat_mul(L.mat_of(L.sqWord(L.mul(s_, x_), x_, mk())),
                  L.mat_of(L.inv(L.sqWord(s_, x_, mk()))))
    idpart = all(P[r][c] % 8 == (1 if r == c else 0)
                 for r in range(6) for c in range(6) if (r, c) != (0, 5))
    ok(idpart and P[0][5] % 8 == 1,
       f"honest 6 x 6 matrices agree at sigma=<{sc}=1>, x0=<{xc[0]}=1,{xc[1]}=1>",
       f"(1,6) entry {P[0][5] % 8}")

head("4  THE GAUGE IS NOT A PROOF ARTEFACT: sampling at an ungauged sigma")
print("   Random letters with x0 on `stageN1` and x1's five abelian columns even, keeping only")
print("   the samples whose residue is CENTRAL (the census's own condition on the diagonal")
print("   frame).  The bare frame is NOT solved for a handle block here, so these are residues")
print("   of the right shape and not certified full binder points.")
print()


def rnd(evens=(), gauge=()):
    return L.U6({k: (2 * random.randrange(4) if (k in evens or k in gauge)
                     else random.randrange(8)) for k in NAMES}, L.IntRing)


random.seed(20260811)
for label, sg in (("ungauged sigma", ()), ("gauged sigma (a, c, e even)", ("a", "c", "e"))):
    cen = odd = bad = 0
    for _ in range(400000):
        s_, x_ = rnd(gauge=sg), rnd(evens=("a", "c"))
        y_ = rnd(evens=YEV)
        central, o = cent_odd(s_, x_, y_)
        if not central:
            continue
        cen += 1
        if o % 2 == 1:
            odd += 1
            if x_.e % 2 == 0:
                bad += 1
    print(f"   {label:<28} {cen:6d} central, {odd:5d} odd, {bad:4d} of those with EVEN x0.e")
    if sg:
        ok(bad == 0, "gauged: an EVEN gearing never produces an odd row", f"0 of {odd}")
    else:
        ok(bad > 0, "ungauged: an EVEN gearing produces odd rows in quantity", f"{bad} of {odd}")

head("5  CALIBRATION at the committed points")

SIGMARK = mk(b=1)                                          # `fiveSigMark` = E_23
LIVESIG = mk(b=1, d=1)                                     # `liveBlkSig`
STAGEX = mk(a=2, e=5)                                      # `stageX`
STAGEY = mk(e=2, f=1, g=1, h=1, m=3, n=3)                  # `stageY`
LIVEY = mk(e=2, f=5, h=5, l=5, n=7, o=3)                   # `liveBlkY`

for nm, sig in (("fiveSigMark", SIGMARK), ("liveBlkSig", LIVESIG)):
    ok(sig.a % 2 == 0 and sig.c % 2 == 0 and sig.e % 2 == 0,
       f"{nm} lies on the gauge (a, c, e all even)",
       f"a={sig.a} c={sig.c} e={sig.e}")
    ok(sig.f % 2 == 0 and sig.j % 2 == 0,
       f"{nm} also kills the two extra cofactor terms s.f * x.h and s.j * x.d",
       f"f={sig.f} j={sig.j}")

for nm, sig, yy in (("stageWit", SIGMARK, STAGEY), ("liveBlkWit", LIVESIG, LIVEY)):
    q = (yy.f * yy.h + sig.f * STAGEX.h + sig.j * STAGEX.d) % 2
    pred = (STAGEX.e * q) % 2
    _, o = cent_odd(sig, STAGEX, yy)
    ok(pred == o % 2, f"{nm}: the factored row predicts the committed bit",
       f"predicted {pred}, residue row {o % 2}")
    ok(STAGEX.e % 2 == 1, f"{nm}: the gearing stageX.e is ODD, as horn 1 now proves",
       f"stageX.e = {STAGEX.e}")
    ok(q == (yy.f * yy.h) % 2,
       f"{nm}: at this sigma the cofactor collapses to wave 58's `x1.f * x1.h`", f"q = {q}")

head(f"{len(CHECKS)} named checks, {CHECKS.count(False)} failures")
sys.exit(1 if False in CHECKS else 0)
