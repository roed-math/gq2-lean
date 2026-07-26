#!/usr/bin/env python3
"""SL1-N experiment driver: everything reported in `docs/orchestration/sl1-numerics.md`.

    python3 sl1_report.py [all|calib|census|funs|regress|sample|witness] [kmax]

* calib   -- tower dims / coker dims / dbar-additivity / SL2 move effects
* census  -- the k=3 mod-2 seed census (168 classes) + the k=3 pinning table
* funs    -- coker functionals at the refined triples, k = 3..kmax, both directions
* regress -- the pinning identity via controlled fresh-digit installs (all four patterns)
* sample  -- broad sampling: S^P-orbits, alternative SL1 solutions, deviation moves
* witness -- the explicit 2^{k-3} witnesses that realize the deviation moves

Every experiment tests the CROSS PINNING IDENTITY

      delta(T)  =  e_q * T_p^{2^{k-1}} + e_p * T_q^{2^{k-1}}   in  Z_k(D)/Im dbar_T

with {p,q} the two tail slots and e_i the chi-deviation digit at 2^{k-1}.
"""
import random
import sys
import time

from sl1_climb import (Ctx, abel2, chi_digits_top, climb, coker_coords, column_pair,
                       combo_to_move, crossed_digit, good_seeds, gen_matrix_ok,
                       move_kernel, mul_triple, pw2, rand_lambda_move,
                       roots_and_addir, seed_census, theta_D)
from span_model import bracketing
from sl1_hunt2 import Solver

TOWER = {3: 10, 4: 20, 5: 44, 6: 94}          # spike section 2.3 machine table


# --------------------------------------------------------------------------- calib
def calib(kmax=5):
    print("## calibration (N_k = #Lyndon(<=k) on 3 letters)\n")
    print(f"{'dir':>4} {'k':>2} {'N_k':>5} {'rk R_k':>7} {'dim Z_k(D)':>11} {'spike':>6} "
          f"{'rk(R+Im dbar)':>14} {'coker':>6} {'tails add':>10}")
    for direction in (1, 2):
        T = good_seeds(direction)[0]
        for k in range(3, kmax + 1):
            c = Ctx(direction, k)
            s = Solver()
            for av in c.ratom_coords(k):
                s.insert(av)
            rR, Nk = s.rank, len(c.lyn)
            sol = c.base_span(T)
            add = 0
            for tv in c.tail_coords(T):
                rem, _ = sol.reduce(tv)
                if rem:
                    add += 1
                    sol.insert(tv)
            print(f"{direction:>4} {k:>2} {Nk:>5} {rR:>7} {Nk - rR:>11} "
                  f"{TOWER.get(k, '-'):>6} {sol.rank - add:>14} "
                  f"{(Nk - rR) - (sol.rank - add - rR):>6} {add:>10}")
            if k < kmax:
                T, info = climb(c, T, (0, 0))
                assert T is not None, info

    print("\n## dbar additivity (the F_2-linear model) and the SL2 witness moves\n")
    rng = random.Random(11)
    bad = 0
    for direction in (1, 2):
        T = good_seeds(direction)[0]
        for k in range(3, kmax + 1):
            c = Ctx(direction, k)
            for slot in (0, 1, 2):
                ms = c.mods()
                for _ in range(8):
                    u1, u2 = rng.choice(ms), rng.choice(ms)
                    bad += (c.coords(c.dbar_atom(u1 + u2, slot, T), k, "chk") !=
                            (c.coords(c.dbar_atom(u1, slot, T), k, "chk") ^
                             c.coords(c.dbar_atom(u2, slot, T), k, "chk")))
            base = c.digits(T, k)
            eff = [tuple(a ^ b for a, b in zip(c.digits(mul_triple(T, mv), k), base))
                   for mv in c.digit_moves(T)]
            zero = [c.dbar_coords(T, mv) == 0 for mv in c.digit_moves(T)]
            print(f"  dir{direction} k={k}: additivity mismatches {bad}; "
                  f"SL2 move effects {eff}; dbar(move)=0 {zero}")
            if k < kmax:
                T, _ = climb(c, T, (0, 0))


# -------------------------------------------------------------------------- census
def census():
    for direction in (1, 2):
        print()
        rows = seed_census(direction, verbose=True)
        c = Ctx(direction, 3)
        cols, ad = column_pair(c)
        p, q = c.tail_slots
        print(f"  k=3 pinning table (columns {[c.column_name(z, ad) for z, _ in cols]}):")
        for m, T, _, _ in rows:
            e = chi_digits_top(c, T)
            (ca, cb), phi, _ = coker_coords(c, T)
            sol = c.base_span(T)
            rem, _ = sol.reduce(c.delta_coords(T))
            kills = all(bin(col & c.in_pbw(v)).count("1") % 2 == 0
                        for v, _ in sol.rows for _, col in cols)
            pred = (e[q], e[p])
            print(f"    {str(m):>10} T={str(T):<22} e={tuple(e)} phi_cols={phi} "
                  f"coker=({ca},{cb}) cross=({pred[0]},{pred[1]}) "
                  f"{'OK' if (ca, cb) == pred else 'MISMATCH'} "
                  f"in-span={rem == 0} cols-kill-base={kills}")


# ---------------------------------------------------------------------------- funs
def funs(kmax=5):
    for direction in (1, 2):
        for si, T0 in enumerate(good_seeds(direction)):
            T = T0
            c0 = Ctx(direction, 3)
            print(f"\n### dir{direction} class{si} seed={T0} tower letters=({c0.letters})")
            for k in range(3, kmax + 1):
                c = Ctx(direction, k)
                pa, pb = c.coker_functionals(T)
                span = {pa, pb, pa ^ pb}
                cols, ad = column_pair(c)
                tp = [c.in_pbw(v) for v in c.tail_coords(T)]
                inside = all(col in span for _, col in cols)
                exact = inside and len({cols[0][1], cols[1][1]}) == 2
                print(f"  k={k} sP={c.is_sP(T)[0]} coker-dual = span of the two columns: "
                      f"{exact}   delta-coker-coords={coker_coords(c, T)[0]}")
                for z, col in cols:
                    pr = [bin(col & t).count("1") % 2 for t in tp]
                    ab = [(abel2(T[i]) >> z) & 1 for i in c.tail_slots]
                    print(f"    {c.column_name(z, ad):18s} = {c.supp_names(col)}")
                    print(f"      {'pairing with tails':22s} {pr}  "
                          f"= mod-2 abelianization coefficients {ab}: {pr == ab}")
                if not exact:
                    print(f"    RAW dual basis: {c.supp_names(pa)} | {c.supp_names(pb)}")
                if k < kmax:
                    T, info = climb(c, T, (0, 0))
                    assert T is not None, info


# ------------------------------------------------------------------------- regress
def check_identity(c, T, tag, verbose=True):
    """The full per-triple check: chi-depth >= k-1, auto-slot digit 0, columns kill the
    base, the cross identity, the reachability dichotomy."""
    e = chi_digits_top(c, T)
    p, q = c.tail_slots
    assert e[c.auto_slot] == 0, f"{tag}: AUTO-SLOT DIGIT NONZERO e={e}"
    (ca, cb), phi, _ = coker_coords(c, T)
    cols, _ = column_pair(c)
    dp = c.in_pbw(c.delta_coords(T))
    sol = c.base_span(T)
    for z, col in cols:
        for v, _ in sol.rows:
            assert bin(col & c.in_pbw(v)).count("1") % 2 == 0, f"{tag}: column hits base"
        # explicit, T-independent form of the identity
        lhs = bin(col & dp).count("1") % 2
        rhs = (e[p] * ((abel2(T[q]) >> z) & 1) ^ e[q] * ((abel2(T[p]) >> z) & 1)) & 1
        assert lhs == rhs, f"{tag}: explicit identity fails at z={z} (e={e})"
    rem, _ = sol.reduce(c.delta_coords(T))
    inspan = rem == 0
    ok = (ca, cb) == (e[q], e[p])
    assert inspan == (e[p] == 0 and e[q] == 0), f"{tag}: dichotomy broken"
    if verbose:
        print(f"   {tag:24s} e={tuple(e)} phi_cols={phi} coker=({ca},{cb}) "
              f"cross-pred=({e[q]},{e[p]}) {'OK' if ok else '** MISMATCH **'} "
              f"delta-in-span={inspan}")
    return ok, tuple(e)


def regress(kmax=5):
    allok = True
    for direction in (1, 2):
        for si, T0 in enumerate(good_seeds(direction)):
            T = T0
            for k in range(3, kmax):
                c, nxt = Ctx(direction, k), Ctx(direction, k + 1)
                print(f"\n dir{direction} class{si}: {k} -> {k+1} "
                      f"(tail slots {c.tail_slots}, auto slot {c.auto_slot})")
                for want in ((0, 0), (0, 1), (1, 0), (1, 1)):
                    T2, info = climb(c, T, want)
                    assert T2 is not None, info
                    ok, _ = check_identity(nxt, T2, f"want={want}")
                    allok &= ok
                    if want == (0, 0):
                        good = T2
                T = good
    print(f"\nCROSS IDENTITY HOLDS ON EVERY CONTROLLED INSTALL: {allok}")


# -------------------------------------------------------------------------- sample
def sample(kmax=5, nsamp=25):
    n = bad = 0
    seen = {}
    t0 = time.time()
    for direction in (1, 2):
        for si, T0 in enumerate(good_seeds(direction)):
            T, prev = T0, None
            for k in range(3, kmax + 1):
                c = Ctx(direction, k)
                rng = random.Random(7 * k + 31 * direction + si)
                pool = [(T, "good")]
                # (a) S^P_k-orbit: any lambda_{k-1}-move keeps all three clauses
                for i in range(nsamp):
                    T2 = mul_triple(T, rand_lambda_move(c, k - 1, rng))
                    okmem, why = c.is_sP(T2)
                    assert okmem, f"lambda_{k-1}-move broke membership ({why})"
                    pool.append((T2, f"orbit{i}"))
                # (b) different SL1 solutions at level k-1 (kernel offsets)
                if prev is not None:
                    cp = Ctx(direction, k - 1)
                    gens, ker, nR = move_kernel(direction, prev, k - 2, k - 1)
                    for i in range(nsamp):
                        combo = 0
                        for kb in ker:
                            if rng.random() < 0.5:
                                combo ^= kb
                        T2, info = climb(cp, prev, (0, 0),
                                         extra_kernel=combo_to_move(gens, nR, combo))
                        assert T2 is not None, info
                        assert c.is_sP(T2)[0], "alternative refinement left S^P"
                        pool.append((T2, f"alt-solve{i}"))
                    # (c) mid-depth deviation moves (lambda_{k-2}, relator-preserving)
                    gens, ker, nR = move_kernel(direction, T, k - 2, k - 1)
                    got = 0
                    for i in range(nsamp * 4):
                        combo = 0
                        for kb in ker:
                            if rng.random() < 0.5:
                                combo ^= kb
                        w = combo_to_move(gens, nR, combo)
                        if not any(w):
                            continue
                        T2 = mul_triple(T, w)
                        if not c.relator_ok(T2, k):
                            continue
                        pool.append((T2, f"dev{i}"))
                        got += 1
                        if got >= nsamp:
                            break
                for T2, tag in pool:
                    ok, e = check_identity(c, T2, tag, verbose=False)
                    n += 1
                    bad += not ok
                    seen[(direction, k, e)] = seen.get((direction, k, e), 0) + 1
                print(f" dir{direction} class{si} k={k}: {len(pool)} triples "
                      f"({round(time.time() - t0, 1)} s)", flush=True)
                if k < kmax:
                    prev = T
                    T, info = climb(c, T, (0, 0))
                    assert T is not None, info
    print(f"\nchecked {n} triples, {bad} mismatches")
    print("e-patterns realized (direction, k, e) -> count:")
    for key in sorted(seen):
        print("   ", key, seen[key])


# ------------------------------------------------------------------------- witness
def witness(kmax=5):
    """The 2^{k-3} witnesses: the SL2 move family one power lower.  They kill their own
    dbar-bracket, flip a TOP chi digit, and shift delta by exactly the crossed tail."""
    for direction in (1, 2):
        for si, T0 in enumerate(good_seeds(direction)):
            T = T0
            for k in range(3, kmax + 1):
                c = Ctx(direction, k)
                if k > 3:
                    m = k - 3
                    if direction == 1:
                        v = pw2(list(T[1]) + list(T[2]), m)
                        ws = [("slot1 <- T2^{2^(k-3)}", [[], pw2(list(T[2]), m), []]),
                              ("slots1,2 <- (T1T2)^{2^(k-3)}", [[], v, v])]
                    else:
                        ws = [("slot0 <- T1^{2^(k-3)}", [pw2(list(T[1]), m), [], []]),
                              ("slot1 <- T0^{2^(k-3)}", [[], pw2(list(T[0]), m), []])]
                    print(f"\n dir{direction} class{si} k={k} tail slots {c.tail_slots}")
                    for name, w in ws:
                        T2 = mul_triple(T, w)
                        if not c.relator_ok(T2, k):
                            print(f"   {name:30s} RELATOR CLAUSE BROKEN")
                            continue
                        check_identity(c, T2, name)
                if k < kmax:
                    T, info = climb(c, T, (0, 0))
                    assert T is not None, info


# --------------------------------------------------------------------------- cross
def cross(kmax=5):
    """The column functional in closed form: phi^z = digit_{k-1} of the theta-crossed
    derivation D_z (theta: ad-letter -> -1, others -> 1; D_z(z) = 1, D_z(rest) = 0)."""
    ok = True
    for direction in (1, 2):
        c0 = Ctx(direction, 3)
        (r1, r2), ad = roots_and_addir(direction)
        for z in (r1, r2):
            th, Dv = theta_D(c0.rword, z, ad, c0.M)
            print(f"  dir{direction} root={c0.letters[z]}: theta(presenting relator)="
                  f"{th % c0.M}  D(presenting relator)={Dv % c0.M}")
        T = good_seeds(direction)[0]
        for k in range(3, kmax + 1):
            c = Ctx(direction, k)
            cols, _ = column_pair(c)
            for z, col in cols:
                got = 0
                for i, l in enumerate(c.lyn):
                    if crossed_digit(c, pw2(bracketing(l), k - len(l)), z):
                        got |= 1 << i
                ok &= got == col
                if got != col:
                    print(f"   dir{direction} k={k} z={c.letters[z]}: DIFFERS by "
                          f"{c.supp_names(got ^ col)}")
                dp = c.in_pbw(c.delta_coords(T))
                assert crossed_digit(c, c.delta(T), z) == bin(col & dp).count("1") % 2
                for a in c.ratoms(k):
                    assert crossed_digit(c, a, z) == 0, "hits the relator layer"
                for u in c.mods():
                    for slot in (0, 1, 2):
                        assert crossed_digit(c, c.dbar_atom(u, slot, T), z) == 0, \
                            "hits Im dbar"
                for slot in c.tail_slots:
                    assert crossed_digit(c, pw2(list(T[slot]), k - 1), z) == \
                        ((abel2(T[slot]) >> z) & 1)
                # closed form of D on the (uncorrected) tested relator word
                Dt = theta_D(c.tested(list(T)), z, roots_and_addir(direction)[1], c.M)[1]
                pred = (4 * theta_D(list(T[1]), z, ad, c.M)[1]) % c.M if direction == 1 \
                    else (4 * (theta_D(list(T[0]), z, ad, c.M)[1]
                               - theta_D(list(T[1]), z, ad, c.M)[1])) % c.M
                assert Dt % c.M == pred, "closed form of D(tested relator) fails"
            print(f"  dir{direction} k={k}: phi^z = digit_(k-1) o D_z on the PBW basis; "
                  f"kills R_k and Im dbar; reads tails; D(tested word) closed form OK")
            if k < kmax:
                T, info = climb(c, T, (0, 0))
                assert T is not None, info
    print("\nCLOSED-FORM (CROSSED-DERIVATION) DESCRIPTION VALID:", ok)


if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    kmax = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    t0 = time.time()
    for name, fn in (("calib", calib), ("census", lambda kmax=None: census()),
                     ("funs", funs), ("cross", cross), ("regress", regress),
                     ("sample", sample), ("witness", witness)):
        if what in ("all", name):
            print(f"\n{'=' * 78}\n== {name}\n{'=' * 78}")
            fn(kmax)
    print(f"\n[{round(time.time() - t0, 1)} s]")
