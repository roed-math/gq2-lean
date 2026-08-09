#!/usr/bin/env python3
"""W52-LIFT step 3: the honest two-row stage-3 system and stage-4 containment.

Stage 3 in U5 = rows h AND i (left and right class-3 functionals).
gamma-2 moves z3 (U-slot), z4 (V-slot), (e,f,g)-parts in the lattice Lam5:
  h-inc = z3.e*(mV).c - z3.f*(mV).a + (mU).a*z4.f - (mU).c*z4.e
  i-inc = z3.f*(mV).d - z3.g*(mV).b + (mU).b*z4.g - (mU).d*z4.f
Plus exponent-slot gamma-3 moves w1,w2 ((h,i) free): -4*w.hi + 2*w.hi => all even PAIRS.
Questions:
 S3a: is (h-res, i-res) of the witness always in the stage-3 increment group J3?
 S3b: classify J3 by parity class.
 S4:  after solving stage 3, is the j-residue in J4 (class-4 increments)?  J4 classes?
 S4b: mod-2 collapse of both J3 and J4 and of the verdicts.
"""
from sweep_u5 import (M, IDX, ONE, mul, inv, commP, power, sqRelWord, U5,
                      binder_points, letters, lam5_gens, lam3_gens, span2,
                      increment_set, witness_tuple, classify_J)
import itertools, random

random.seed(2)


def span_pairs(gens):
    S = {(0, 0)}
    frontier = [(0, 0)]
    while frontier:
        x = frontier.pop()
        for g in gens:
            y = ((x[0] + g[0]) % M, (x[1] + g[1]) % M)
            if y not in S:
                S.add(y)
                frontier.append(y)
    return S


def stage3_pair_gens(pt, m):
    """(h,i)-increment pair generators from lattice gamma-2 moves on U/V slots."""
    mU, mV = m[3], m[4]
    gens = [(2, 0), (0, 2)]  # exponent-slot gamma-3 dressings, each row separately
    for (ze, zf, zg) in lam5_gens(pt):
        gens.append(((ze * mV[IDX['c']] - zf * mV[IDX['a']]) % M,
                     (zf * mV[IDX['d']] - zg * mV[IDX['b']]) % M))
        gens.append(((mU[IDX['a']] * zf - mU[IDX['c']] * ze) % M,
                     (mU[IDX['b']] * zg - mU[IDX['d']] * zf) % M))
    return gens


def solve_stage3(pt, m):
    """Find lattice gamma-2 moves (z3,z4) + gamma-3 (w1,w2) killing rows h,i.
    Search: coefficients on the 4 lattice gens for each slot, plus exact even fix."""
    rows = sqRelWord(m)
    target = (rows[7], rows[8])
    L5 = lam5_gens(pt)
    # brute force small coefficient vectors (r1..r4 for z3, s1..s4 for z4) mod M
    # to keep cost down: use meet-in-middle via dict of z3-effects
    eff3 = {}
    for coef in itertools.product(range(M), repeat=2):
        for pick in itertools.combinations(range(4), 2):
            ze = sum(coef[k] * L5[pick[k]][0] for k in range(2)) % M
            zf = sum(coef[k] * L5[pick[k]][1] for k in range(2)) % M
            zg = sum(coef[k] * L5[pick[k]][2] for k in range(2)) % M
            z3 = U5(e=ze, f=zf, g=zg)
            m2 = list(m)
            m2[3] = mul(m2[3], z3)
            r2 = sqRelWord(m2)
            key = (r2[7] % 2, r2[8] % 2)  # parity of both rows
            if key == (0, 0):
                # even rows: finish with exponent-slot gamma-3 (2*w kills evens)
                w2v = [w for w in range(M) if (2 * w + r2[7]) % M == 0][0]
                w2i = [w for w in range(M) if (2 * w + r2[8]) % M == 0][0]
                m3 = list(m2)
                m3[2] = mul(m3[2], U5(h=w2v, i=w2i))
                r3 = sqRelWord(m3)
                if all(r3[k] == 0 for k in range(9)):
                    return m3, r3
    return None, None


def main():
    print("== stage-3 two-row system + stage-4 containment, by type")
    for tys in [(0, 1), (1, 0), (1, 1)]:
        pts = binder_points(40, types={tys})
        agg = {}
        for pt in pts:
            m, rows, need = witness_tuple(pt)
            J3 = span_pairs(stage3_pair_gens(pt, m))
            hin = (rows[7], rows[8]) in J3
            n3 = len(J3)
            m3, r3 = solve_stage3(pt, m)
            if m3 is None:
                key = (f"J3size{n3}", 'hi-in-J3' if hin else 'HI-NOT-IN-J3',
                       'stage3-unsolved')
                agg.setdefault(key, [0, 0])[0] += 1
                continue
            J4 = increment_set(pt, m3[3], m3[4])
            jin = r3[9] in J4
            key = (f"J3size{n3}", 'hi-in-J3' if hin else 'HI-NOT-IN-J3',
                   f"J4={classify_J(J4)}", 'j-in-J4' if jin else 'J-NOT-IN-J4')
            agg.setdefault(key, [0, 0])[0] += 1
        print(f"  type {tys}:")
        for k, v in sorted(agg.items(), key=str):
            print(f"    {k}: {v[0]}")

    print("== mod-2 collapse of (J3, J4, verdicts)")
    seen = {}
    mism = 0
    for pt in binder_points(300):
        par = tuple(x % 2 for x in pt[:8])
        m, rows, need = witness_tuple(pt)
        J3 = frozenset(span_pairs(stage3_pair_gens(pt, m)))
        J4 = frozenset(increment_set(pt, m[3], m[4]))
        if par in seen and seen[par] != (J3, J4):
            mism += 1
        seen.setdefault(par, (J3, J4))
    print(f"  parity classes: {len(seen)}, mismatches: {mism}")
    from collections import Counter
    cnt = Counter((len(J3), classify_J(set(J4))) for (J3, J4) in seen.values())
    for k, v in sorted(cnt.items(), key=str):
        print(f"  (|J3|, J4) = {k}: {v} classes")


if __name__ == "__main__":
    main()
