"""W64-CENSUS5 step 2: the census proper - does ANY binder point survive at `gamma_2`?

W63-CENTRAL2 refuted the `gamma_2` route at one point by an exhaustive sweep of one slot.  This
runs the same decision at MANY points and at ALL FIVE slots, exactly (not by sampling), using
`censuslib.slot_kill_census`.  For each binder point it records

  * the three GEARINGS `x0.e`, `v_j.e`, `u_j.e` of the class-four knobs of sections 1 and 2 of
    `GQ2/Dyadic/SqCore/GradedGammaTwoCensus.lean`, and whether each knob is ACHIEVABLE;
  * the EXACT number of achievable single-slot `gamma_2`-dressings that kill the dressed frame,
    slot by slot;
  * wave 58's class-five separation bit.

Sections:
  A  wave 60's committed point, against W63-CENTRAL2's own number;
  B  the `x0` sweep at wave 60's handle letters: which `x0` are live at all;
  C  the wide `x1` census at every live `x0`, with a RANDOMISED sample of live `x1` slots;
  D  fresh handle letters, found by random search (`scripts/w64_census5/results/triples.txt`);
  E  W63-LIVE5's point;
  F  the verdict: how many points survive at the sigma slot, and how many survive everywhere.

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""
import json
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import censuslib as CE                                            # noqa: E402
import centrallib as C                                            # noqa: E402
import pointlib as P                                              # noqa: E402
import u6mat as M                                                 # noqa: E402

SLOTS = ["sigma", "x0", "x1", "u_j", "v_j"]
TOTALS = dict(points=0, sig_dead=0, all_dead=0, knob_unach=0, xe_even=0, bit_even=0)


def head(t):
    print()
    print("=" * 106)
    print("== " + t)
    print("=" * 106)
    print()


def report(X, Y, U, V, tag, L=None, quiet=False):
    """One binder point, decided exactly at all five slots."""
    S = M.mul(CE.SIG, X)
    if L is None:
        L = CE.lattice(S, X, Y, U, V)
    res = CE.rel(S, X, Y, U, V)[14]
    kills = [None] * 5
    for s in CE.FAST_SLOTS:
        kills[s] = CE.slot_kill_census(S, X, Y, U, V, s, L=L, want_examples=0)["kills"]
    if sum(kills[s] for s in CE.FAST_SLOTS) == 0:
        for s in (1, 2):                       # only the survivors pay for the nested sweep
            kills[s] = CE.slot_kill_exact(S, X, Y, U, V, s, L=L, want_examples=0)["kills"]
    gears = [CE.co(X, "e"), CE.co(V, "e"), (-CE.co(U, "e")) % 8]
    ach = []
    for g in gears:
        if g % 2 == 0:
            ach.append(None)
        else:
            t = (-res * CE.INV8[g % 8]) % 8
            ach.append(L.contains(M.named(m=t)))
    TOTALS["points"] += 1
    if kills[0] == 0:
        TOTALS["sig_dead"] += 1
    if all(k == 0 for k in kills if k is not None):
        TOTALS["all_dead"] += 1
    if ach[0] is False:
        TOTALS["knob_unach"] += 1
    if gears[0] % 2 == 0:
        TOTALS["xe_even"] += 1
    if CE.w58_bit(X, Y) == 0:
        TOTALS["bit_even"] += 1
    if not quiet:
        print("   %-26s res %d  L 2^%-2d  gearings (x0.e,v.e,-u.e) %s  knobs %s"
              % (tag, res, L.order_log2(), tuple(gears),
                 tuple("-" if a is None else ("Y" if a else "N") for a in ach)))
        print("   %-26s kills per slot (sigma,x0,x1,u,v) %-30s   w58 bit %d"
              % ("", str(kills), CE.w58_bit(X, Y)))
    return dict(res=res, kills=kills, gears=gears, ach=ach, order=L.order_log2())


def main():
    rng = random.Random(64007)
    t00 = time.time()
    print("=" * 106)
    print("== W64-CENSUS5: the gamma_2 census over binder points ==")
    print("=" * 106)

    STU = M.named(a=6, b=7, c=4, d=1, e=3, g=5, h=5)
    STV = M.named(a=6, b=7, c=6, d=1, e=3, f=5, g=3, h=3, i=4)

    head("A  wave 60's committed binder point")
    r = report(C.stageX, C.stageY, STU, STV, "wave 60 (stageWit stageX)")
    print()
    print("   W63-CENTRAL2's exhaustive sigma sweep scaled back to 131072 killing dressings;")
    print("   this census says %d.  %s" % (r["kills"][0],
          "AGREE" if r["kills"][0] == 131072 else "*** DISAGREE ***"))

    head("B  the `x0` sweep at wave 60's handle letters: which `x0` are LIVE at all")
    print("   `x0 = <a, e>` over all 32 values with `a` even.  A triple is live when some `x1`")
    print("   makes the undressed frame kill and the `a0 = a1` frame central with an ODD")
    print("   residue.  The enumeration is `pointlib.solve_y_central`, exhaustive per triple.")
    print()
    live_triples = []
    for a in (0, 2, 4, 6):
        row = []
        for e in range(8):
            X = M.named(a=a, e=e)
            got = P.solve_y_central(CE.SIG, X, STU, STV, limit=1)
            row.append("L" if got else ".")
            if got:
                live_triples.append(X)
        print("   a = %d :  e = 0..7  ->  %s" % (a, " ".join(row)))
    print()
    print("   %d of 32 are live.  Every live one has an ODD `e`: %s"
          % (len(live_triples), all(CE.co(X, "e") % 2 for X in live_triples)))
    print("   Every live one has `a = 2` or `a = 6`, i.e. `a == 2 mod 4`: %s"
          % all(CE.co(X, "a") % 4 == 2 for X in live_triples))

    head("C  the wide `x1` census at every live `x0`")
    print("   Live `x1` slots are drawn by a RANDOMISED cascade so the sample spreads over the")
    print("   solution set instead of clustering on the sparse lifts.")
    print()
    for X in live_triples:
        Ys = CE.sample_live(X, STU, STV, rng, 6)
        seen = set()
        for Y in Ys:
            if Y in seen:
                continue
            seen.add(Y)
            report(X, Y, STU, STV, "x0 = %s" % M.show(X))
        sys.stdout.flush()

    head("D  FRESH handle letters")
    print("   Live triples with handle letters unrelated to wave 60's, found by random search")
    print("   over `stageN1` letters.  Six parallel searches tried 2942 random triples in 2400 s")
    print("   each and produced 2 live ones (both with a sparse `x0`); a seventh search produced")
    print("   the third.  Live triples are the census's bottleneck, not the decision procedure.")
    print()
    tri = []
    path = os.path.join(HERE, "results", "triples.txt")
    if os.path.exists(path):
        for line in open(path):
            line = line.strip()
            if line.startswith("{"):
                tri.append(json.loads(line))
    for p in tri:
        X, U, V = tuple(p["X"]), tuple(p["U"]), tuple(p["V"])
        print("   x0 = %s" % M.show(X))
        print("   u  = %s" % M.show(U))
        print("   v  = %s" % M.show(V))
        Ys = CE.sample_live(X, U, V, rng, 6)
        seen = set()
        for Y in Ys:
            if Y in seen:
                continue
            seen.add(Y)
            report(X, Y, U, V, "fresh handle")
        print()
        sys.stdout.flush()

    head("E  W63-LIVE5's point")
    print("   `liveBlkWit h j stageX` reuses `stageX` in the `x0` slot, which is the slot the")
    print("   sigma knob's gearing reads.  Its sigma letter is `liveBlkSig * stageX` rather")
    print("   than `sigFiveMark * stageX`, so it is reported directly rather than through the")
    print("   census helper.")
    print()
    lbSig = M.named(b=1, d=1)
    lbY = M.named(e=2, f=5, h=5, l=5, n=7, o=3)
    lbU = M.named(c=2, d=1)
    lbV = M.named(c=2, e=3, j=5)
    S = M.mul(lbSig, C.stageX)
    L = CE.lattice(S, C.stageX, lbY, lbU, lbV)
    res = CE.rel(S, C.stageX, lbY, lbU, lbV)[14]
    kills = [CE.slot_kill_census(S, C.stageX, lbY, lbU, lbV, s, L=L, want_examples=0)["kills"]
             if s in CE.FAST_SLOTS else None for s in range(5)]
    print("   undressed relator %s ; `a0 = a1` relator %s"
          % (M.show(CE.rel(lbSig, C.stageX, lbY, lbU, lbV)),
             M.show(CE.rel(S, C.stageX, lbY, lbU, lbV))))
    print("   L = 2^%d ; gearings (x0.e, v.e, -u.e) = (%d, %d, %d)"
          % (L.order_log2(), CE.co(C.stageX, "e"), CE.co(lbV, "e"), (-CE.co(lbU, "e")) % 8))
    print("   `censKnob 3` achievable: %s ; it kills: %s"
          % (L.contains(M.named(m=3)),
             CE.rel(M.mul(S, M.named(m=3)), C.stageX, lbY, lbU, lbV) == M.ONE))
    print("   kills per slot (sigma, x0, x1, u, v) %s" % (kills,))
    print("   certificate: censKnob 3 = [u, sigma x0] * [sigma x0, v] : %s"
          % (M.mul(M.commP(lbU, S), M.commP(S, lbV)) == M.named(m=3)))

    head("F  THE VERDICT")
    print("   binder points decided exactly at all five slots : %d" % TOTALS["points"])
    print("   with NO achievable killing dressing at the sigma slot   : %d" % TOTALS["sig_dead"])
    print("   with NO achievable killing dressing at ANY of the five  : %d" % TOTALS["all_dead"])
    print("   where the solving sigma knob is NOT achievable          : %d" % TOTALS["knob_unach"])
    print("   with an EVEN `x0.e`                                     : %d" % TOTALS["xe_even"])
    print("   with an EVEN wave-58 separation bit                     : %d" % TOTALS["bit_even"])
    print()
    if TOTALS["all_dead"] == 0:
        print("   ⭐ Every point reached is KILLED by an achievable single-slot gamma_2")
        print("   dressing, so the `gamma_2` route is dead at every binder point this census")
        print("   reaches.  ⚠ The knob is NOT always what kills: at the points whose knobs are")
        print("   unachievable or whose gearings are even, the killer is a general element of")
        print("   the achievable lattice.  The knob theorems are a proved SUFFICIENT mechanism")
        print("   and a criterion a census can check, not a classification of the killers.")
    else:
        print("   ⚠ %d points survive every single-slot dressing; they are the census's real"
              % TOTALS["all_dead"])
        print("   finding and need a five-slot search.")
    print()
    print("   total run time %.0f s" % (time.time() - t00))
    print("=" * 106)


if __name__ == "__main__":
    main()
