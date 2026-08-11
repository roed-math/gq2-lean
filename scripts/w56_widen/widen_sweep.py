"""W56-WIDEN, part 3: the Z/8 sweep and the honest-collection validation.

T0  library sanity against the committed Lean facts.
T1  EXHAUSTIVE, mod 2: at every one of the live mod-2 classes (four parity rows, the fourteen
    pairings of `sqRelWord_selLamTwo_ne_one` even, class-four selection bit odd), the two
    pairings `h*F - i*B`, `h*E - i*A` and the `g`-column of ALL 66 census generators of
    `gamma2(im Phi)`, computed by honest U5 group arithmetic over F2 (not by the hand-derived
    closed forms).  Parity of an integer polynomial depends only on the variables mod 2, so
    this is a complete check of the pairings.
T2  EXHAUSTIVE over the whole Z/8 binder: the size of the live set.
T3  the separation: live Z/8 corners at which some census generator's `(h, i)` falls OUTSIDE
    the committed `selLamThreePlus` span in `(Z/8)^2`.  One such corner settles "was the gap
    real?".
T4  the honest object, not a generating set: random elements `p, q` of `K = <five frame
    slots>` over Z/8 at live corners; check (a) `p` satisfies the Lean shape predicate
    `selFrameW`, (b) `commP p q` has even `g` and even `U`- and `V`-pairings.
T5  end to end against honest group collection: random five-slot dressings with every slot
    drawn from `gamma2(K)`, checked to leave `sqRelWord` nontrivial at live corners -- the
    conclusion of the new theorem, measured.

Run:  python3 scripts/w56_widen/widen_sweep.py

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "w55_row"))
import u5lib as U  # noqa: E402

N = 8
RNG = random.Random(20260810)


# --------------------------------------------------------------------------------------
# the witness frame
# --------------------------------------------------------------------------------------

def sel_lift_wit(A, B, C, D, E, F, T, S, P, Q, R, n=N):
    """selLiftWit 1 0 A B C D E F T S P Q R, the five slots at one handle."""
    return [
        (0, 1, 0, 0, 0, 0, 0, 0, 0, 0),
        ((B * T - A * S) % n, 0, (D * T - C * S) % n, (F * T - E * S) % n,
         (-(2 * (T * S * B))) % n, (S * (T * C) + T * S * D) % n, 0, 0, 0, 0),
        (0, 0, 0, 0, P % n, Q % n, R % n, (-((A + B) * Q)) % n, 0, 0),
        (A % n, 0, C % n, E % n, 0, (-(T * C)) % n, 0, 0, 0, 0),
        (B % n, 0, D % n, F % n, (-(B * S)) % n, 0, 0, 0, 0, 0),
    ]


def pairings14(A, B, C, D, E, F, T, S, P, Q, R):
    return [
        (2 * (A * C)) * F + (C * E) * B,
        (A * D + B * C) * F + (D * E) * B,
        (A * D + B * C) * F + (C * F) * B,
        (2 * (B * D)) * F + (D * F) * B,
        R * B,
        (P * C - Q * A) * F - (Q * E) * B,
        (P * D - Q * B) * F - (Q * F) * B,
        A * (C * E) + E * (2 * (A * C)),
        A * (D * E) + E * (A * D + B * C),
        A * (C * F) + E * (A * D + B * C),
        A * (D * F) + E * (2 * (B * D)),
        A * R,
        A * (Q * E) - E * (P * C - Q * A),
        A * (Q * F) - E * (P * D - Q * B),
    ]


def bit(A, B, C, D, E, F, T, S, P, Q, R):
    return ((A * (C * F) + B * (D * E)) * T + P * R) % 2


# --------------------------------------------------------------------------------------
# the census generating set of gamma2(im Phi)
# --------------------------------------------------------------------------------------

SLOTNAMES = ["sigma", "x0", "x1", "U", "V"]
PAIRS = [(i, k) for i in range(5) for k in range(i + 1, 5)]


def census_gens(m, n=N):
    out = []
    for (i, k) in PAIRS:
        out.append(U.commP(m[i], m[k], n))
    for (i, k) in PAIRS:
        z = U.commP(m[i], m[k], n)
        for s in m:
            out.append(U.commP(z, s, n))
    sq = U.mul(m[2], m[2], n)
    out.append(sq)
    for s in m:
        out.append(U.commP(sq, s, n))
    return out


def gen_names():
    out = ["[%s,%s]" % (SLOTNAMES[i], SLOTNAMES[k]) for (i, k) in PAIRS]
    for (i, k) in PAIRS:
        for s in SLOTNAMES:
            out.append("[[%s,%s],%s]" % (SLOTNAMES[i], SLOTNAMES[k], s))
    out.append("x1^2")
    for s in SLOTNAMES:
        out.append("[x1^2,%s]" % s)
    return out


def lam3plus_span(A, B, C, D, E, F, T, S, P, Q, R):
    gens = [
        ((-(2 * (A * C))) % N, (C * E) % N),
        ((-(A * D + B * C)) % N, (D * E) % N),
        ((-(A * D + B * C)) % N, (C * F) % N),
        ((-(2 * (B * D))) % N, (D * F) % N),
        (0, (2 * R) % N),
        ((2 * (Q * A - P * C)) % N, (2 * (R * T - Q * E)) % N),
        ((2 * (Q * B - P * D)) % N, (2 * (R * S - Q * F)) % N),
        (0, R % N),
        ((P * C - Q * A) % N, (Q * E) % N),
        ((P * D - Q * B) % N, (Q * F) % N),
    ]
    span = {(0, 0)}
    frontier = [(0, 0)]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = ((x[0] + g[0]) % N, (x[1] + g[1]) % N)
                if y not in span:
                    span.add(y)
                    nxt.append(y)
        frontier = nxt
    return span


# --------------------------------------------------------------------------------------
# the Lean shape predicate `selFrameW`, over Z/8
# --------------------------------------------------------------------------------------

def shape_ok(p, A, B, C, D, E, F, P, Q, R):
    """`selFrameSub C D E F P`: `a` even, `(c, d) = al*(C, E) + be*(D, F)` mod 2 with one
    shared `(al, be)`, and `e = ep*P` mod 2."""
    a, b, c, d, e, f, g = p[:7]
    ok_a = (a % 2 == 0)
    ok_cd = any(((c - al * C - be * D) % 2 == 0 and (d - al * E - be * F) % 2 == 0)
                for al in (0, 1) for be in (0, 1))
    ok_e = any((e - ep * P) % 2 == 0 for ep in (0, 1))
    return ok_a and ok_cd and ok_e


def random_word(gens, length):
    p = U.ONE
    for _ in range(length):
        g = RNG.choice(gens)
        if RNG.random() < 0.5:
            g = U.inv(g)
        p = U.mul(p, g)
    return p


# --------------------------------------------------------------------------------------

def live_points_exhaustive():
    """Every (A,...,S) in (Z/8)^8 with the four rows even, the fourteen pairings even and
    the class-four bit odd; halves taken canonically as the W54 census did."""
    live = []
    n_rows = 0
    for A in range(8):
        for S in range(8):
            for B in range(8):
                for T in range(8):
                    if (A * S - B * T) % 2:
                        continue
                    P = ((B * T - A * S) % 8) // 2
                    for C in range(8):
                        for D in range(8):
                            if (T * D - S * C) % 2:
                                continue
                            Q = ((S * C - T * D) % 8) // 2
                            for E in range(8):
                                for F in range(8):
                                    if (C * F - D * E) % 2 or (E * S - F * T) % 2:
                                        continue
                                    n_rows += 1
                                    R = ((D * E - C * F) % 8) // 2
                                    W2 = ((F * T - E * S) % 8) // 2
                                    if bit(A, B, C, D, E, F, T, S, P, Q, R) != 1:
                                        continue
                                    if any(x % 2 for x in
                                           pairings14(A, B, C, D, E, F, T, S, P, Q, R)):
                                        continue
                                    live.append((A, B, C, D, E, F, T, S, P, Q, R, W2))
    return n_rows, live


def main():
    out = []
    w = out.append
    w("W56-WIDEN part 3: the Z/8 sweep and the honest-collection validation")
    w("=" * 86)
    w("")
    fails = 0

    # ---- T0 ----------------------------------------------------------------------
    w("T0  library sanity against committed Lean facts")
    w("-" * 86)
    m = sel_lift_wit(2, 0, 2, 0, 0, 1, 0, 1, 3, 1, 3)
    r = U.sqRelWord(m)
    ok = r == U.liftC(5)
    w("  sqRelWord (selLiftWit 1 0 2 0 2 0 0 1 0 1 3 1 3) = liftC 5 : %s"
      % ("OK" if ok else "FAIL %s" % (r,)))
    fails += 0 if ok else 1
    m2 = sel_lift_wit(0, 1, 1, 1, 2, 0, 2, 0, 1, 3, 1)
    ok2 = U.sqRelWord(m2) == U.liftC(5)
    w("  sqRelWord (selLiftWit 1 0 0 1 1 1 2 0 2 0 1 3 1) = liftC 5 : %s"
      % ("OK" if ok2 else "FAIL"))
    fails += 0 if ok2 else 1
    c02 = U.commP(m2[0], m2[2])
    ok3 = c02 == (0, 0, 0, 0, 0, 0, 0, 0, 1, 0)
    w("  commP slot0 slot2 there = (0,..,0,1,0)  [GradedGammaTwo]   : %s"
      % ("OK" if ok3 else "FAIL %s" % (c02,)))
    fails += 0 if ok3 else 1
    # the three committed gamma2-level moves, as closed forms
    A_, B_, C_, D_, E_, F_, T_, S_, P_, Q_, R_ = 2, 0, 2, 0, 0, 1, 0, 1, 3, 1, 3
    mm = sel_lift_wit(A_, B_, C_, D_, E_, F_, T_, S_, P_, Q_, R_)
    z1 = U.commP(mm[0], mm[2])
    z2 = U.commP(mm[2], mm[3])
    z3 = U.commP(mm[2], mm[4])
    ok4 = (z1[7] % 8, z1[8] % 8) == (0, R_ % 8)
    ok5 = (z2[7] % 8, z2[8] % 8) == ((P_ * C_ - Q_ * A_) % 8, (Q_ * E_) % 8)
    ok6 = (z3[7] % 8, z3[8] % 8) == ((P_ * D_ - Q_ * B_) % 8, (Q_ * F_) % 8)
    w("  the three committed gamma2 moves reproduce their (h,i)     : %s"
      % ("OK" if (ok4 and ok5 and ok6) else "FAIL"))
    fails += 0 if (ok4 and ok5 and ok6) else 1
    w("")

    # ---- T1 : exhaustive mod 2 -----------------------------------------------------
    w("T1  EXHAUSTIVE mod 2: all 66 census generators at every live mod-2 class,")
    w("    by honest U5 group arithmetic over F2")
    w("-" * 86)
    names = gen_names()
    nlive2 = 0
    tested = bad_u = bad_v = bad_g = 0
    for bits in range(4096):
        v = [(bits >> k) & 1 for k in range(12)]
        A, B, C, D, E, F, T, S, P, Q, R, W2 = v
        if (A * S - B * T) % 2 or (T * D - S * C) % 2 or (C * F - D * E) % 2 \
                or (E * S - F * T) % 2:
            continue
        if any(x % 2 for x in pairings14(A, B, C, D, E, F, T, S, P, Q, R)):
            continue
        if bit(A, B, C, D, E, F, T, S, P, Q, R) != 1:
            continue
        nlive2 += 1
        m2c = sel_lift_wit(A, B, C, D, E, F, T, S, P, Q, R, n=2)
        for z in census_gens(m2c, n=2):
            tested += 1
            if (z[7] * F + z[8] * B) % 2:
                bad_u += 1
            if (z[7] * E + z[8] * A) % 2:
                bad_v += 1
            if z[6] % 2:
                bad_g += 1
    w("  live mod-2 classes                          : %d  (of 4096)" % nlive2)
    w("  census generators tested (66 per class)     : %d" % tested)
    w("  U-slot pairing  h*F - i*B  odd              : %d" % bad_u)
    w("  V-slot pairing  h*E - i*A  odd              : %d" % bad_v)
    w("  generator g-column odd                      : %d" % bad_g)
    fails += bad_u + bad_v + bad_g
    w("")

    # ---- T2 : exhaustive Z/8 live count ---------------------------------------------
    w("T2  EXHAUSTIVE over the whole Z/8 binder: the live set")
    w("-" * 86)
    n_rows, live = live_points_exhaustive()
    w("  binder points with the four parity rows even            : %d" % n_rows)
    w("  ... fourteen pairings even AND class-four bit odd (LIVE): %d" % len(live))
    w("")

    # ---- T3 : the separation ---------------------------------------------------------
    w("T3  is the honest object strictly wider than selLamThreePlus?  EXHAUSTIVE")
    w("-" * 86)
    sep = 0
    first = None
    counts = {}
    for pt in live:
        A, B, C, D, E, F, T, S, P, Q, R, W2 = pt
        mm = sel_lift_wit(A, B, C, D, E, F, T, S, P, Q, R)
        span = lam3plus_span(A, B, C, D, E, F, T, S, P, Q, R)
        hit = [(nm, (z[7] % N, z[8] % N))
               for nm, z in zip(names, census_gens(mm))
               if (z[7] % N, z[8] % N) not in span]
        if hit:
            sep += 1
            for nm, _ in hit:
                counts[nm] = counts.get(nm, 0) + 1
            if first is None:
                first = (pt, hit, len(span))
    w("  live corners (ALL)                                          : %d" % len(live))
    w("  ... at which some census generator leaves selLamThreePlus   : %d" % sep)
    if first:
        pt, hit, ns = first
        w("  first separating corner: (A..S) = %s, halves (P,Q,R,W2) = %s"
          % (tuple(pt[:8]), tuple(pt[8:])))
        w("    |selLamThreePlus span in (Z/8)^2| = %d" % ns)
        for nm, hi in hit[:10]:
            w("      %-22s (h, i) = %-8s OUTSIDE selLamThreePlus" % (nm, hi))
        w("  generators responsible, by frequency:")
        for nm in sorted(counts, key=lambda x: -counts[x]):
            w("      %-22s %d" % (nm, counts[nm]))
    w("")
    w("  Control: the same test OFF the live set (rows even, but the fourteen pairings")
    w("  not all even), to show the containment is a consequence of the hypotheses.")
    ctrl = 0
    ctrl_n = 0
    ctrl_first = None
    ctrl_counts = {}
    for A in range(8):
        for B in range(8):
            for C in range(8):
                for D in range(8):
                    for E in range(8):
                        for F in range(8):
                            T, S = 1, 1
                            if ((A * S - B * T) % 2 or (T * D - S * C) % 2
                                    or (C * F - D * E) % 2 or (E * S - F * T) % 2):
                                continue
                            P = ((B * T - A * S) % 8) // 2
                            Q = ((S * C - T * D) % 8) // 2
                            R = ((D * E - C * F) % 8) // 2
                            ctrl_n += 1
                            mm = sel_lift_wit(A, B, C, D, E, F, T, S, P, Q, R)
                            span = lam3plus_span(A, B, C, D, E, F, T, S, P, Q, R)
                            hit = [nm for nm, z in zip(names, census_gens(mm))
                                   if (z[7] % N, z[8] % N) not in span]
                            if hit:
                                ctrl += 1
                                for nm in hit:
                                    ctrl_counts[nm] = ctrl_counts.get(nm, 0) + 1
                                if ctrl_first is None:
                                    ctrl_first = ((A, B, C, D, E, F, T, S), (P, Q, R), hit)
    w("    control corners (T = S = 1, rows even)                    : %d" % ctrl_n)
    w("    ... with some generator outside selLamThreePlus           : %d" % ctrl)
    if ctrl_first:
        w("    first: (A..S) = %s halves (P,Q,R) = %s" % (ctrl_first[0], ctrl_first[1]))
        w("           outside: %s" % ", ".join(ctrl_first[2][:6]))
        w("    generators responsible, by frequency (top 8):")
        for nm in sorted(ctrl_counts, key=lambda x: -ctrl_counts[x])[:8]:
            w("        %-22s %d" % (nm, ctrl_counts[nm]))
    w("")
    w("  Monomial census on the live set (which products are forced even):")
    monos = {"A*C": lambda v: v[0] * v[2], "B*D": lambda v: v[1] * v[3],
             "A*D": lambda v: v[0] * v[3], "B*C": lambda v: v[1] * v[2],
             "A*D+B*C": lambda v: v[0] * v[3] + v[1] * v[2],
             "C*E": lambda v: v[2] * v[4], "C*F": lambda v: v[2] * v[5],
             "D*E": lambda v: v[3] * v[4], "D*F": lambda v: v[3] * v[5],
             "A*E": lambda v: v[0] * v[4], "B*F": lambda v: v[1] * v[5],
             "A*F": lambda v: v[0] * v[5], "B*E": lambda v: v[1] * v[4],
             "A*F+B*E": lambda v: v[0] * v[5] + v[1] * v[4],
             "A": lambda v: v[0], "B": lambda v: v[1], "R": lambda v: v[10],
             "P": lambda v: v[8], "Q": lambda v: v[9]}
    for nm, fn in monos.items():
        odd = sum(1 for pt in live if fn(pt) % 2)
        w("      %-10s odd at %6d of %d live corners" % (nm, odd, len(live)))
    w("")

    # ---- T4 : the honest object, random elements ------------------------------------
    w("T4  random elements of K = <five frame slots> over Z/8, and their commutators")
    w("-" * 86)
    sample4 = live if len(live) <= 4000 else RNG.sample(live, 4000)
    n_sh = n_cm = 0
    bad_sh = bad_cg = bad_cu = bad_cv = 0
    for pt in sample4:
        A, B, C, D, E, F, T, S, P, Q, R, W2 = pt
        mm = sel_lift_wit(A, B, C, D, E, F, T, S, P, Q, R)
        els = [random_word(mm, RNG.randint(1, 9)) for _ in range(8)]
        for x in els:
            n_sh += 1
            if not shape_ok(x, A, B, C, D, E, F, P, Q, R):
                bad_sh += 1
        for x in els[:4]:
            for y in els[4:]:
                z = U.commP(x, y)
                n_cm += 1
                if z[6] % 2:
                    bad_cg += 1
                if (z[7] * F - z[8] * B) % 2:
                    bad_cu += 1
                if (z[7] * E - z[8] * A) % 2:
                    bad_cv += 1
    w("  random elements of K tested against `selFrameW`  : %d" % n_sh)
    w("  ... outside the shape predicate                  : %d" % bad_sh)
    w("  random commutators [p, q] with p, q in K         : %d" % n_cm)
    w("  ... g-column odd                                 : %d" % bad_cg)
    w("  ... U-slot pairing odd                           : %d" % bad_cu)
    w("  ... V-slot pairing odd                           : %d" % bad_cv)
    fails += bad_sh + bad_cg + bad_cu + bad_cv
    w("")

    # ---- T5 : end to end, honest collection ------------------------------------------
    w("T5  end to end: five-slot dressings drawn from gamma2(K), by honest collection")
    w("-" * 86)
    sample5 = live if len(live) <= 1200 else RNG.sample(live, 1200)
    n_dr = kills = n_ga2 = bad_ga2 = 0
    for pt in sample5:
        A, B, C, D, E, F, T, S, P, Q, R, W2 = pt
        mm = sel_lift_wit(A, B, C, D, E, F, T, S, P, Q, R)
        pool = [U.commP(random_word(mm, RNG.randint(1, 6)), random_word(mm, RNG.randint(1, 6)))
                for _ in range(6)]
        pool.append(U.mul(mm[2], mm[2]))
        for x in pool:
            n_ga2 += 1
            if not U.is_ga_two(x):
                bad_ga2 += 1
        for _ in range(4):
            z = []
            for _ in range(5):
                v = U.ONE
                for _ in range(RNG.randint(0, 3)):
                    g = RNG.choice(pool)
                    if RNG.random() < 0.5:
                        g = U.inv(g)
                    v = U.mul(v, g)
                z.append(v)
            n_dr += 1
            if U.sqRelWord([U.mul(mm[i], z[i]) for i in range(5)]) == U.ONE:
                kills += 1
    w("  gamma2(K) elements drawn          : %d  (not gamma2-shaped: %d)" % (n_ga2, bad_ga2))
    w("  five-slot gamma2(im Phi) dressings: %d" % n_dr)
    w("  ... that kill the relator (ZERO)  : %d" % kills)
    fails += kills + bad_ga2
    w("")

    w("=" * 86)
    w("TOTAL MISMATCHES: %d" % fails)
    w("=" * 86)

    text = "\n".join(out)
    print(text)
    with open("scripts/w56_widen/results/widen_sweep.txt", "w") as fh:
        fh.write(text + "\n")
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
