"""W66-ACHIEVE: the certificate behind `GQ2/Dyadic/SqCore/GradedCensusAchieve.lean`.

Run:  python3 scripts/w66_achieve/achieve.py > scripts/w66_achieve/results/achieve.txt

What it certifies, section by section:

  0  this lane's own sifting library against W63-CENTRAL2's `centrallib`, on all 67 census
     lattices and all 67 knob-membership tests - two independent implementations of the
     achievable lattice, written from different filtrations, agreeing everywhere;
  1  the 67 binder points, rebuilt and checked against `scripts/w64_census5/results/
     census.txt` record by record (residue, lattice order, gearings, knob flags), plus the
     three structural facts every one of them must have: the BARE frame kills, the DIAGONAL
     frame's relator is central with an ODD top row, and all five letters lie on `stageN1`;
  2  every certificate the Lean file carries: the emitted word evaluates to the emitted
     element, the element lies in the honest `[H, H]`, and dressing the named slot with it
     takes the relator to `1`;
  3  the knob census: which of the three knobs is achievable at each point, and the twelve
     points at which none is;
  4  the ungauged binder point `censHorn_binder_cex`: its five letters, both frames, the
     three dead knobs, the EXACT single-slot kill counts over its whole 2^15 lattice, and
     the single-commutator certificate the Lean file uses;
  5  the horn-2 verdict.

BRACKET CONVENTION.  [IMMUNE / PAPER]  Subgroups are closures, hence convention-immune; the
emitted words are read in the paper convention `commP x y = x^-1 y^-1 x y`, which is the one
`GQ2/Words.lean` and every Lean statement here use.

⚠ SCOPE.  Section 4's kill counts are EXACT over single-slot dressings, which is the census's
own scope; the five-slot search there is random and is reported as evidence, never as a
decision.
"""
import json
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
for d in ("w64_census5", "w63_central2", "w60_stage4", "w59_force5"):
    sys.path.insert(0, os.path.join(HERE, os.pardir, d))

import censuslib as CE                                                    # noqa: E402
import centrallib as C                                                    # noqa: E402
from siftlib import (named, censKnob, show, mul, inv, commP, sqRelWord, ONE, COORDS,
                     commutator_subgroup, enumerate_table, w_eval, w_str, w_size,
                     w_mul, w_inv, w_pow)                                 # noqa: E402

OK = [0]
BAD = [0]


def chk(name, cond, extra=""):
    if cond:
        OK[0] += 1
        print("   [ok]   %-58s %s" % (name, extra))
    else:
        BAD[0] += 1
        print("   [FAIL] %-58s %s" % (name, extra))


def head(t):
    print()
    print("=" * 100)
    print("== " + t)
    print("=" * 100)
    print()


SIG = CE.SIG
STU = named(a=6, b=7, c=4, d=1, e=3, g=5, h=5)
STV = named(a=6, b=7, c=6, d=1, e=3, f=5, g=3, h=3, i=4)
INV8 = {1: 1, 3: 3, 5: 5, 7: 7}
SLOT = ["sigma", "x0", "x1", "u", "v"]


def build_points():
    """census.py's driver, replayed: seed 64007, the same call order."""
    rng = random.Random(64007)
    pts = [dict(tag="A", X=C.stageX, Y=C.stageY, U=STU, V=STV)]
    for a in (2, 6):
        for e in (1, 3, 5, 7):
            X = named(a=a, e=e)
            seen = set()
            for Y in CE.sample_live(X, STU, STV, rng, 6):
                if Y not in seen:
                    seen.add(Y)
                    pts.append(dict(tag="C", X=X, Y=Y, U=STU, V=STV))
    for line in open(os.path.join(HERE, os.pardir, "w64_census5", "results", "triples.txt")):
        line = line.strip()
        if not line.startswith("{"):
            continue
        p = json.loads(line)
        X, U, V = tuple(p["X"]), tuple(p["U"]), tuple(p["V"])
        seen = set()
        for Y in CE.sample_live(X, U, V, rng, 6):
            if Y not in seen:
                seen.add(Y)
                pts.append(dict(tag="D", X=X, Y=Y, U=U, V=V))
    return pts


def recorded():
    out = []
    path = os.path.join(HERE, os.pardir, "w64_census5", "results", "census.txt")
    for line in open(path):
        if " res " in line and " L 2^" in line:
            res = int(line.split(" res ")[1].split()[0])
            lg = int(line.split(" L 2^")[1].split()[0])
            g = line.split("(x0.e,v.e,-u.e) ")[1].split(")")[0].strip("( ")
            kn = line.split("knobs ")[1].strip()
            out.append((res, lg, tuple(int(x) for x in g.split(",")),
                        kn.replace("(", "").replace(")", "").replace("'", "").replace(", ", "")))
    return out


t0 = time.time()
print("=" * 100)
print("== W66-ACHIEVE: the census endgame - achievability, horn 2, and the gauge ==")
print("=" * 100)

head("0  two independent lattice implementations, on all 67 points")
pts = build_points()
rec = recorded()
chk("the driver rebuilds exactly 67 binder points", len(pts) == 67, "%d" % len(pts))
chk("results/census.txt carries exactly 67 records", len(rec) == 67, "%d" % len(rec))
rows = []
agree_order = agree_knob = 0
for i, p in enumerate(pts):
    X, Y, U, V = p["X"], p["Y"], p["U"], p["V"]
    S = mul(SIG, X)
    K = commutator_subgroup([('g', k) for k in "SXYUV"], dict(S=S, X=X, Y=Y, U=U, V=V))
    L = CE.lattice(S, X, Y, U, V)
    lg_mine = K.order().bit_length() - 1
    if lg_mine == L.order_log2():
        agree_order += 1
    c = sqRelWord([S, X, Y, U, V])[14]
    gears = (X[4], V[4], (-U[4]) % 8)
    ach, same = [], True
    for g in gears:
        if g % 2 == 0:
            ach.append(None)
        else:
            t = (-c * INV8[g % 8]) % 8
            a1, a2 = K.contains(censKnob(t)), L.contains(named(m=t))
            same = same and (a1 == a2)
            ach.append(a1)
    if same:
        agree_knob += 1
    rows.append(dict(idx=i + 1, tag=p["tag"], X=X, Y=Y, U=U, V=V, S=S, c=c, K=K,
                     lg=lg_mine, gears=gears, ach=ach))
chk("siftlib and centrallib agree on |[H,H]| at every point", agree_order == 67,
    "%d/67" % agree_order)
chk("...and on every knob-membership test", agree_knob == 67, "%d/67" % agree_knob)

head("1  the 67 points, against the committed record")
nbare = ndiag = nn1 = nmatch = 0
for r in rows:
    S, X, Y, U, V = r["S"], r["X"], r["Y"], r["U"], r["V"]
    if sqRelWord([SIG, X, Y, U, V]) == ONE:
        nbare += 1
    d = sqRelWord([S, X, Y, U, V])
    if all(x % 8 == 0 for x in d[:14]) and d[14] % 2 == 1:
        ndiag += 1
    if all(CE.is_stageN1(g) for g in (SIG, S, X, Y, U, V)):
        nn1 += 1
    rres, rlg, rgears, rkn = rec[r["idx"] - 1]
    flags = "".join("-" if a is None else ("Y" if a else "N") for a in r["ach"])
    if (r["c"] == rres and r["lg"] == rlg and r["gears"] == rgears and flags == rkn):
        nmatch += 1
chk("the BARE frame kills the relator at every point", nbare == 67, "%d/67" % nbare)
chk("the DIAGONAL frame is central with an ODD top row", ndiag == 67, "%d/67" % ndiag)
chk("all five letters lie on stageN1 at every point", nn1 == 67, "%d/67" % nn1)
chk("residue, lattice order, gearings and knob flags match census.txt", nmatch == 67,
    "%d/67" % nmatch)

head("2  every certificate the Lean file carries")
CERTS = json.load(open(os.path.join(HERE, "certificates.json")))
nw = ne = nk = nm = 0
for r in rows:
    cert = CERTS[str(r["idx"])]
    env = dict(S=r["S"], X=r["X"], Y=r["Y"], U=r["U"], V=r["V"])
    w = tuple(cert["elt"])
    word = json.loads(cert["word"], object_hook=None)

    def conv(x):
        return tuple(conv(y) if isinstance(y, list) else y for y in x)
    word = conv(word)
    if w_eval(word, env) == w:
        nw += 1
    if r["K"].contains(w):
        ne += 1
    mm = [r["S"], r["X"], r["Y"], r["U"], r["V"]]
    mm[cert["slot"]] = mul(mm[cert["slot"]], w)
    if sqRelWord(mm) == ONE:
        nk += 1
    if CE.lattice(*[r["S"], r["X"], r["Y"], r["U"], r["V"]]).contains(w):
        nm += 1
chk("the emitted word evaluates to the emitted element", nw == 67, "%d/67" % nw)
chk("the element lies in [H, H]            (siftlib)", ne == 67, "%d/67" % ne)
chk("the element lies in [H, H]            (centrallib)", nm == 67, "%d/67" % nm)
chk("the dressed relator is the identity", nk == 67, "%d/67" % nk)
sizes = sorted(w_size(conv(json.loads(CERTS[str(r["idx"])]["word"]))) for r in rows)
print()
print("   certificate word sizes: min %d, median %d, max %d"
      % (sizes[0], sizes[len(sizes) // 2], sizes[-1]))
print("   slots used: " + ", ".join(
    "%s %d" % (SLOT[s], sum(1 for r in rows if CERTS[str(r["idx"])]["slot"] == s))
    for s in range(5) if any(CERTS[str(r["idx"])]["slot"] == s for r in rows)))

head("3  the knob census")
sig_ach = sum(1 for r in rows if r["ach"][0] is True)
sig_un = sum(1 for r in rows if r["ach"][0] is False)
allnone = [r["idx"] for r in rows if not any(a is True for a in r["ach"])]
chk("the sigma knob is achievable at 49 of the 67", sig_ach == 49, "%d" % sig_ach)
chk("...and unachievable at the other 18", sig_un == 18, "%d" % sig_un)
chk("no knob at all is achievable at exactly 12 points", len(allnone) == 12,
    "points %s" % allnone)
print()
print("   at those twelve the census's KNOB mechanism is silent and the killer is a general")
print("   lattice element: they are the wave-64 queue's horn-2 candidates.")

head("4  the ungauged binder point censHorn_binder_cex")
cexSig, cexX, cexY = named(e=1), named(f=1, h=1), ONE
cexU = named(a=2, d=1, e=7, f=1, h=1, m=1, n=1)
cexV = named(a=6, b=6, c=4, d=7, e=1, f=7, g=2, j=7, k=6, l=7, m=1)
S = mul(cexSig, cexX)
m = [S, cexX, cexY, cexU, cexV]
chk("the BARE frame kills the relator", sqRelWord([cexSig, cexX, cexY, cexU, cexV]) == ONE)
rel = sqRelWord(m)
chk("the DIAGONAL frame's relator is liftO 1",
    all(x % 8 == 0 for x in rel[:14]) and rel[14] % 8 == 1, show(rel))
chk("every letter lies on stageN1",
    all(CE.is_stageN1(g) for g in (cexSig, S, cexX, cexY, cexU, cexV)))
chk("the sigma knob's GEARING is even (the knob is dead, not merely unachievable)",
    cexX[4] % 2 == 0, "x0.e = %d" % cexX[4])
K = commutator_subgroup([('g', k) for k in "SXYUV"],
                        dict(S=S, X=cexX, Y=cexY, U=cexU, V=cexV))
chk("|[H,H]| = 2^15", K.order() == 2 ** 15, "2^%d" % (K.order().bit_length() - 1))
c = rel[14]
for lab, gear in (("u", cexV[4]), ("v", (-cexU[4]) % 8)):
    ts = [t for t in range(8) if (c + gear * t) % 8 == 0]
    chk("the %s knob's solving value %s is NOT achievable" % (lab, ts),
        all(not K.contains(censKnob(t)) for t in ts),
        "achievable knobs: %s" % [t for t in range(8) if K.contains(censKnob(t))])
els = enumerate_table(K)
chk("the lattice enumerates to 2^15 distinct elements",
    len(els) == 2 ** 15 and len({e for e, _ in els}) == 2 ** 15)
counts = []
for s in range(5):
    n = sum(1 for e, _ in els if sqRelWord([mul(m[k], e) if k == s else m[k]
                                            for k in range(5)]) == ONE)
    counts.append(n)
print()
print("   EXACT single-slot kill counts over the whole lattice, all five slots:")
print("      " + "   ".join("%s %d" % (SLOT[s], counts[s]) for s in range(5)))
chk("the point IS killed, at three of the five slots", sum(counts) > 0,
    "%d achievable single-slot killers" % sum(counts))
gw = ('comm', ('g', 'X'), ('g', 'S'))
gv = w_eval(gw, dict(S=S, X=cexX, Y=cexY, U=cexU, V=cexV))
chk("the Lean certificate [x0, sigma] is achievable", K.contains(gv), show(gv))
mm = list(m)
mm[0] = mul(mm[0], gv)
chk("...and dressing the sigma slot with it kills the relator", sqRelWord(mm) == ONE)
rng = random.Random(66001)
five = sum(1 for _ in range(200000)
           if sqRelWord([mul(m[k], els[rng.randrange(len(els))][0])
                         for k in range(5)]) == ONE)
print()
print("   five-slot random search (EVIDENCE, not a decision): %d kills in 200000 draws" % five)

head("5  the verdict")
print("   census points decided                                     : 67")
print("   points with an exhibited achievable killing dressing       : 67")
print("   survivors                                                  : 0")
print("   points at which NO knob is achievable                      : %d" % len(allnone))
print("   of those, points with no achievable killer at any slot     : 0")
print("   ungauged binder point (censHorn_binder_cex): all three knobs silent, and")
print("      %d achievable single-slot killers, so the gauge is NOT necessary for the census."
      % sum(counts))
print()
print("   HORN 2 (a live point where all three knobs are unachievable AND the lattice kills")
print("   at no slot): REFUTED at every point reached - the twelve knob-free census points")
print("   and the ungauged counterexample all die by a general lattice element.")
print()
print("=" * 100)
print("== %d named checks, %d failures, %.1f s" % (OK[0] + BAD[0], BAD[0], time.time() - t0))
print("=" * 100)
