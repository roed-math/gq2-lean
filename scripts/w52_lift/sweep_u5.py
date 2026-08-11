#!/usr/bin/env python3
"""sweep_u5.py.

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

"""sweep_u5.py.
"""

"""sweep_u5.py.
"""

"""sweep_u5.py.
"""

"""sweep_u5.py.
"""

"""W52-LIFT step 2: end-to-end Z/8 sweep of the class-4 engine claims.

Binder: weights A B C D (chi_a, chi_c on U,V), E F (chi_d), rows T S (nu'),
x1 class-2 coords P Q R, new half W2, subject to
  hd: 2P + (A*S - B*T) = 0        he: 2Q + (T*D - S*C) = 0
  hg: 2R + (C*F - D*E) = 0        hb: 2W2 + (E*S - F*T) = 0
Uncleared: T or S odd.

Claims to validate:
 C1 row invariance + translation identity of the lift refinement (gamma-3 on handles,
    gamma-4 on exp slots): Delta_j = -4w1.j + 2w2.j + (z3.h*(mV).d - z3.i*(mV).a)
    + ((mU).a*z4.i - (mU).d*z4.h).
 C2 the witness tuple (lift of selConWit + solved deep coords) kills rows a..g
    and rows h,i (h-row: even class-3 residue killed by the committed completion move
    on the (e,f)-coords -- the stage-3 refinement; i-row analogous?  MEASURE).
 C3 increment lattice J of the class-4 action: classify per binder point; check
    mod-2 collapse (J depends only on parities of (A..F,T,S)).
 C4 containment: class-4 residue of the stage-3 survivor lies in J.
"""
import itertools, random

M = 8
random.seed(1)

# U5 coords index: 0..9 = a b c d e f g h i j
IDX = {n: k for k, n in enumerate("abcdefghij")}
ONE = (0,) * 10


def mul(x, y):
    a, b, c, d, e, f, g, h, i, j = [(x[k] + y[k]) % M for k in range(10)]
    e = (e + x[0] * y[1]) % M
    f = (f + x[1] * y[2]) % M
    g = (g + x[2] * y[3]) % M
    h = (h + x[0] * y[5] + x[4] * y[2]) % M
    i = (i + x[1] * y[6] + x[5] * y[3]) % M
    j = (j + x[0] * y[8] + x[4] * y[6] + x[7] * y[3]) % M
    return (a, b, c, d, e, f, g, h, i, j)


def inv(x):
    r = ONE
    # inverse by solving mul(x, r) = 1 greedily coordinate by coordinate:
    y = list(ONE)
    for k in [0, 1, 2, 3]:
        y[k] = (-x[k]) % M
    for k in [4, 5, 6, 7, 8, 9]:
        cur = mul(x, tuple(y))
        y[k] = (-cur[k]) % M
    assert mul(x, tuple(y)) == ONE
    return tuple(y)


def conjP(p, gg):
    return mul(mul(inv(gg), p), gg)


def commP(p, q):
    return mul(mul(inv(p), inv(q)), mul(p, q))


def power(x, n):
    r = ONE
    if n < 0:
        x, n = inv(x), -n
    for _ in range(n):
        r = mul(r, x)
    return r


def sqWord(s, x, y):
    return mul(mul(mul(inv(conjP(x, s)), inv(power(x, 3))), power(y, 2)),
               commP(y, conjP(y, s)))


def sqRelWord(m):
    # m: list of sqRank(h) slot values, h handles
    hh = (len(m) - 3) // 2
    w = sqWord(m[0], m[1], m[2])
    for jj in range(hh):
        w = mul(w, commP(m[3 + 2 * jj], m[4 + 2 * jj]))
    return w


def U5(**kw):
    v = [0] * 10
    for n, val in kw.items():
        v[IDX[n]] = val % M
    return tuple(v)


def binder_points(n, types=None):
    """Sample n random binder points (A..F,T,S,P,Q,R,W2) satisfying parities."""
    pts = []
    while len(pts) < n:
        A, B, C, D, E, F = [random.randrange(M) for _ in range(6)]
        T, S = random.randrange(M), random.randrange(M)
        if T % 2 == 0 and S % 2 == 0:
            continue
        if types and (T % 2, S % 2) not in types:
            continue
        rows = [A * S - B * T, T * D - S * C, C * F - D * E, E * S - F * T]
        if any(r % 2 for r in rows):
            continue
        P, Q, R, W2 = [(-r // 2) % M for r in rows]
        # halves are defined mod 4; randomize the mod-4 lift
        P = (P + 4 * random.randrange(2)) % M
        Q = (Q + 4 * random.randrange(2)) % M
        R = (R + 4 * random.randrange(2)) % M
        W2 = (W2 + 4 * random.randrange(2)) % M
        pts.append((A, B, C, D, E, F, T, S, P, Q, R, W2))
    return pts


def letters(pt):
    A, B, C, D, E, F, T, S, P, Q, R, W2 = pt
    sig = U5(b=1)
    Ub = U5(a=A, c=C, d=E, f=-(T * C))
    Vb = U5(a=B, c=D, d=F, e=-(B * S))
    X1 = U5(e=P, f=Q, g=R, h=-((A + B) * Q))
    return sig, Ub, Vb, X1


def lam5_gens(pt):
    """gamma-2 image lattice generators (e,f,g)."""
    A, B, C, D, E, F, T, S, P, Q, R, W2 = pt
    return [(-A % M, C, 0), ((-B) % M, D, 0),
            ((-2 * P) % M, (-2 * Q) % M, (-2 * R) % M), (0, 0, (-2 * R) % M)]


def lam3_gens(pt):
    """gamma-3 image lattice generators (h,i): pairings [z,L], L in {sigma,u,v}."""
    A, B, C, D, E, F, T, S, P, Q, R, W2 = pt
    Ls = [(0, 1, 0, 0), (A, T, C, E), (B, S, D, F)]
    out = []
    for (ze, zf, zg) in lam5_gens(pt):
        for (La, Lb, Lc, Ld) in Ls:
            out.append(((ze * Lc - zf * La) % M, (zf * Ld - zg * Lb) % M))
    return out


def span2(gens):
    """subgroup of (Z/8)^2 generated."""
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


def increment_set(pt, mU, mV):
    """achievable class-4 increments: z3 on U-slot, z4 on V-slot + even part."""
    inc = set()
    for (zh, zi) in span2(lam3_gens(pt)):
        inc.add((zh * mV[IDX['d']] - zi * mV[IDX['a']]) % M)
        inc.add((mU[IDX['a']] * zi - mU[IDX['d']] * zh) % M)
    # exponent-slot gamma-4: -4w + 2w' : all even multiples reachable
    base = set()
    for x in inc:
        for k in range(M):
            base.add((x + 2 * k) % M)
    # close under addition
    J = {0}
    frontier = [0]
    allg = list(base)
    while frontier:
        x = frontier.pop()
        for g in allg:
            y = (x + g) % M
            if y not in J:
                J.add(y)
                frontier.append(y)
    return J


def witness_tuple(pt, h=1, jj=0, solve_deep=True):
    """U5 lift of selConWit: slot1 = forced dressing value, deep coords solved to
    kill rows d,g (and record what h,i,j rows need)."""
    A, B, C, D, E, F, T, S, P, Q, R, W2 = pt
    sig, Ub, Vb, X1 = letters(pt)
    # slot1 committed U4 value lifted: a=BT-AS, c=DT-CS, d(new)=FT-ES,
    # e=-2TSB, f=STC+TSD, deep g,h,i,j to be solved.
    s1 = [(B * T - A * S) % M, 0, (D * T - C * S) % M, (F * T - E * S) % M,
          (-2 * (T * S * B)) % M, (S * (T * C) + T * S * D) % M, 0, 0, 0, 0]
    m = [sig, tuple(s1), X1] + [Ub, Vb] * h
    m = [list(v) for v in m]
    rows = sqRelWord([tuple(v) for v in m])
    need = {}
    if solve_deep:
        # row d: -4*s1.d + 2*X1.d = -4*(FT-ES): must vanish given hb (FT-ES = 2*W2
        # so -4*2W2 = -8W2 = 0). Check:
        assert rows[3] == 0, (pt, rows)
        # row g: -4*s1.g + 2*R + core + hw.g: solve s1.g (coefficient -4: need rhs in 4Z)
        # instead solve via s1.g over Z/8: -4*s1.g + rest = 0.
        rest = (rows[6] + 4 * m[1][6]) % M  # remove current -4*s1.g contribution
        sols = [gv for gv in range(M) if (-4 * gv + rest) % M == 0]
        if not sols:
            need['g'] = rest
        else:
            m[1][6] = sols[0]
        rows = sqRelWord([tuple(v) for v in m])
    return [tuple(v) for v in m], rows, need


def stage3_completion(pt, m):
    """Apply the committed class-3 completion on the (e,f)-coords: U-slot gamma-2
    move with (e,f) = rr*res*(-B, D), g chosen to also fix... MEASURE what happens."""
    A, B, C, D, E, F, T, S, P, Q, R, W2 = pt
    rows = sqRelWord(m)
    # class-3 residue on h-row (left-U4 f-row): rows[7]; must be even
    if rows[7] % 2:
        return None, 'odd-h'
    res = (rows[7] // 2) % M  # want 2*res... careful: rows[7] = 2*res mod 8
    res = None
    for r0 in range(M):
        if (2 * r0) % M == rows[7]:
            res = r0
            break
    pairing = (B * m[4][IDX['c']] + D * m[4][IDX['a']]) % M
    rr = None
    for r in range(M):
        if (r * pairing) % M == 2:
            rr = r
            break
    if rr is None:
        return None, 'no-live'
    z3 = U5(e=(-(rr * res * B)) % M, f=(rr * res * D) % M)
    m2 = list(m)
    m2[3] = mul(m2[3], z3)
    return m2, sqRelWord(m2)


def classify_J(J):
    if any(x % 2 for x in J):
        return 'full' if len(J) == M else f'odd:{sorted(J)}'
    return {8: 'full', 4: '2Z', 2: '4Z', 1: '0'}[len(J)]


def main():
    print("== C1: translation identity, 200 random checks")
    bad = 0
    for _ in range(200):
        pt = binder_points(1)[0]
        m, rows, need = witness_tuple(pt)
        # random tuple perturbation to make it generic:
        mm = [mul(v, U5(**{n: random.randrange(M) for n in "efghij"})) for v in m]
        w1 = U5(j=random.randrange(M))
        w2 = U5(j=random.randrange(M))
        z3 = U5(h=random.randrange(M), i=random.randrange(M), j=random.randrange(M))
        z4 = U5(h=random.randrange(M), i=random.randrange(M), j=random.randrange(M))
        ref = list(mm)
        ref[1] = mul(ref[1], w1)
        ref[2] = mul(ref[2], w2)
        ref[3] = mul(ref[3], z3)
        ref[4] = mul(ref[4], z4)
        r0, r1 = sqRelWord(mm), sqRelWord(ref)
        delta = (-4 * w1[9] + 2 * w2[9]
                 + z3[7] * mm[4][3] - z3[8] * mm[4][0]
                 + mm[3][0] * z4[8] - mm[3][3] * z4[7]) % M
        ok = all(r0[k] == r1[k] for k in range(9)) and (r1[9] - r0[9]) % M == delta
        bad += 0 if ok else 1
    print(f"  failures: {bad}/200")

    print("== C2/C3/C4: per-parity-class study")
    for tys in [(0, 1), (1, 0), (1, 1)]:
        pts = binder_points(60, types={tys})
        stats = {}
        for pt in pts:
            m, rows, need = witness_tuple(pt)
            if need:
                stats.setdefault('g-unsolvable', []).append((pt, need))
                continue
            # rows a..g should now be dead:
            low = all(rows[k] == 0 for k in range(7))
            m2, r2 = stage3_completion(pt, m)
            J = increment_set(pt, m[3], m[4])
            cls = classify_J(J)
            key = (low, 'none' if m2 is None else 'done', cls)
            stats.setdefault(key, [0, 0, 0])[0] += 1
            if m2 is not None and not isinstance(r2, str):
                # r2: rows after stage-3 completion; h-row dead?
                stats[key][1] += (1 if all(r2[k] == 0 for k in range(8)) else 0)
                # i-row status and j-residue containment:
                irow = r2[8]
                jres = r2[9]
                stats[key][2] += (1 if (irow == 0 and jres % M in J) else 0)
        print(f"  type {tys}:")
        for k, v in sorted(stats.items(), key=str):
            print(f"    {k}: {v}")

    print("== C3b: mod-2 collapse of J")
    seen = {}
    for pt in binder_points(400):
        par = tuple(x % 2 for x in pt[:8])
        m, rows, need = witness_tuple(pt)
        J = frozenset(increment_set(pt, m[3], m[4]))
        if par in seen and seen[par] != J:
            print(f"  COLLAPSE FAILS at parity {par}: {sorted(J)} vs {sorted(seen[par])}")
        seen[par] = J
    summary = {}
    for par, J in seen.items():
        summary.setdefault(classify_J(set(J)), []).append(par)
    for cls, pars in sorted(summary.items()):
        print(f"  J = {cls}: {len(pars)} parity classes")


if __name__ == "__main__":
    main()
