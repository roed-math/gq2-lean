"""W64-CENSUS5 shared machinery: the sigma-slot kill, decided EXACTLY at a binder point.

Layered on `scripts/w63_central2/centrallib.py` (the gamma_2 shift read off the relator, and the
polycyclic sift) and `scripts/w60_stage4/pointlib.py` (the layered solve that enumerates live
binder points).  Nothing is transcribed from a Lean file.

W63-CENTRAL2 swept wave 60's own sigma slot by brute force, `262144` dressings.  That is far too
slow for a census over many points, so this module decides the same question EXACTLY and in
milliseconds, using four structural facts about the sigma-slot shift

    Phi(w) = sqRelWord(fiveTuple(S, X, Y, U, V))^{-1} * sqRelWord(fiveTuple(S w, X, Y, U, V)),

each of which `derive_census.py` section 1 certifies against honest 6 x 6 collection:

  A. for `w` in gamma_2 the shift's class-three rows `(j, k, l)` depend only on `w`'s class-two
     part;
  B. its class-four rows `(m, n)` depend only on `w`'s class-two and class-three parts;
  C. the whole shift ignores `w.o`;
  D. the shift is MULTIPLICATIVE in a gamma_3-shaped right factor: `Phi(w r) = Phi(w) Phi(r)`
     whenever `r` is gamma_3-shaped, and a gamma_3-shaped `r` has `Phi(r)` supported on
     `(m, n, o)` alone, where the group law is coordinatewise addition.  In particular a
     class-four-shaped `r` contributes exactly `r.m * X.e - r.n * X.a` on the class-five row.

Because the polycyclic sift lists its rows in COORDINATE order, every element of the achievable
lattice `L = [H, H]` is a product `p2 * p3 * p4 * p5` of sub-products drawn from the rows whose
leading coordinate has class 2, 3, 4, 5 respectively.  A + B + C then say the search prunes class
by class, and D collapses the last three stages to linear algebra over `Z/8`: only the class-two
layer needs brute force, so one point costs `2^(#class-two rows)` relator evaluations instead of
the whole lattice.

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
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w63_central2"))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w60_stage4"))

import centrallib as C                                            # noqa: E402
import pointlib as P                                              # noqa: E402
import u6mat as M                                                 # noqa: E402

N = 8
ONE = M.ONE
IDX = C.IDX
SIG = M.sigFiveMark
INV8 = {1: 1, 3: 3, 5: 5, 7: 7}


def co(z, c):
    return z[IDX[c]]


def frame(S, X, Y, U, V, h=1, jj=0):
    """The one-handle-live marking with sigma letter `S`."""
    return P.mirTuple(h, jj, S, X, Y, U, V)


def rel(S, X, Y, U, V, h=1, jj=0):
    return M.sqRelWord(frame(S, X, Y, U, V, h, jj))


def mknob(t):
    """`<m = t>`: the class-four coordinate alone, the knob W63-CENTRAL2's kill turns."""
    return M.named(m=t)


def sig_shift(S, X, Y, U, V, w, h=1, jj=0, binv=None):
    """`Phi(w)`, read off the relator and never from an emitted closed form."""
    if binv is None:
        binv = M.inv(rel(S, X, Y, U, V, h, jj))
    return M.mul(binv, rel(M.mul(S, w), X, Y, U, V, h, jj))


# ---- live binder points -------------------------------------------------------------------


def is_stageN1(z):
    return co(z, "a") % 2 == 0 and co(z, "c") % 2 == 0


def live_points(X, U, V, h=1, jj=0, limit=None):
    """Every `Y` making `(X, Y, U, V)` a LIVE binder point at the mark `sigFiveMark`.

    Live means: every letter is `stageN1`; the undressed frame kills the relator; and the
    `a0 = a1` frame - the sigma slot multiplied by `x0` - is a central translation with an ODD
    class-five residue.  That is exactly wave 62's census condition.
    """
    if not (is_stageN1(X) and is_stageN1(U) and is_stageN1(V)):
        return []
    out = []
    for Y in P.solve_y_central(SIG, X, U, V, h, jj, limit=limit):
        if not is_stageN1(Y):
            continue
        r0 = rel(SIG, X, Y, U, V, h, jj)
        r1 = rel(M.mul(SIG, X), X, Y, U, V, h, jj)
        if r0 != ONE:
            continue
        if any(r1[k] for k in range(14)) or r1[14] % 2 == 0:
            continue
        out.append(Y)
    return out


def residue(X, Y, U, V, h=1, jj=0):
    """The class-five residue of the `a0 = a1` frame."""
    return rel(M.mul(SIG, X), X, Y, U, V, h, jj)[14]


CLS = {c: [k for k in range(15) if M.cls(k) == c] for c in range(1, 6)}


def sample_live(X, U, V, rng, want, h=1, jj=0, tries=None):
    """A RANDOMISED sample of live `x1` slots for the triple `(X, U, V)`.

    `pointlib.solve_y_central` is depth-first with a fixed lift order, so its first `n`
    solutions are structurally alike and a prefix is a biased sample.  This is the same cascade
    with the two lifts pushed in random order and the coordinate branches shuffled, so the
    sample spreads over the whole solution set.
    """
    out = []
    tries = tries if tries is not None else 40 * want + 200
    steps = 0
    stack = [(ONE, 1)]
    while stack and len(out) < want and steps < tries:
        Y, c = stack.pop()
        steps += 1
        if c == 5:
            r0 = rel(SIG, X, Y, U, V, h, jj)
            r1 = rel(M.mul(SIG, X), X, Y, U, V, h, jj)
            if r0[14] % 2 or (r1[14] - r0[14]) % 2 == 0:
                continue
            base = (-(r0[14] // 2)) % 4
            for lift in rng.sample([base, base + 4], 2):
                cand = tuple(lift if k == 14 else Y[k] for k in range(15))
                if is_stageN1(cand):
                    out.append(cand)
            continue
        cand = [Y]
        for k in CLS[c]:
            nxt = []
            for Yp in cand:
                r0 = rel(SIG, X, Yp, U, V, h, jj)
                r1 = rel(M.mul(SIG, X), X, Yp, U, V, h, jj)
                if r0[k] % 2 or r0[k] != r1[k]:
                    continue
                base = (-(r0[k] // 2)) % 4
                for lift in rng.sample([base, base + 4], 2):
                    nxt.append(tuple(lift if kk == k else Yp[kk] for kk in range(15)))
            rng.shuffle(nxt)
            cand = nxt[:8]
        for Yp in cand:
            stack.append((Yp, c + 1))
        rng.shuffle(stack)
    return out


# ---- the achievable lattice, split by class ------------------------------------------------


def lattice(S, X, Y, U, V):
    """`forceLcs H 1 = [H, H]` for `H` the image of the frame, as a polycyclic sift."""
    return C.derived_of([S, X, Y, U, V])


def rows_by_class(L):
    """The sift's rows, bucketed by the class of their leading coordinate."""
    buckets = {2: [], 3: [], 4: [], 5: []}
    for key in sorted(L.table):
        k = key[0]
        buckets[M.cls(k)].append(L.table[key])
    return buckets


def subset_products(rows):
    """Every ordered sub-product of `rows`, which is every element of the layer they span."""
    out = [ONE]
    for r in reversed(rows):
        out = [M.mul(r, x) for x in out] + out
    return out


def mno_sums(steps):
    """Every subset sum of a list of `(m, n, o)` steps, with multiplicities."""
    counts = {(0, 0, 0): 1}
    for s in steps:
        nxt = dict(counts)
        for v, c in counts.items():
            w = ((v[0] + s[0]) % N, (v[1] + s[1]) % N, (v[2] + s[2]) % N)
            nxt[w] = nxt.get(w, 0) + c
        counts = nxt
    return counts


# ---- the exact sigma-slot decision ---------------------------------------------------------


def sigma_kill_census(S, X, Y, U, V, h=1, jj=0, L=None, want_examples=1):
    """Does ANY achievable gamma_2-dressing of the SIGMA SLOT kill the dressed frame?

    Returns a dict with the verdict, the exact number of killing dressings inside the
    achievable lattice, and up to `want_examples` witnesses.  Structural facts A to D make the
    class-three, class-four and class-five layers linear, so only the class-two layer is swept.
    """
    if L is None:
        L = lattice(S, X, Y, U, V)
    buckets = rows_by_class(L)
    base = rel(S, X, Y, U, V, h, jj)
    binv = M.inv(base)
    res = base[14]
    deep = mno_sums([tuple(sig_shift(S, X, Y, U, V, r, h, jj, binv)[k] for k in (12, 13, 14))
                     for r in buckets[3] + buckets[4]])
    free5 = 1 << len(buckets[5])
    # the class-three rows are ADDITIVE over the class-two layer, so the layer's kernel is
    # found by subset sums of the per-row triples and only the kernel is ever evaluated.
    jkl = [tuple(sig_shift(S, X, Y, U, V, r, h, jj, binv)[k] for k in (9, 10, 11))
           for r in buckets[2]]
    kernel = []
    for mask in range(1 << len(buckets[2])):
        acc = [0, 0, 0]
        for b in range(len(buckets[2])):
            if mask >> b & 1:
                for c in range(3):
                    acc[c] = (acc[c] + jkl[b][c]) % N
        if acc == [0, 0, 0]:
            kernel.append(mask)
    kills = 0
    examples = []
    for mask in kernel:
        p2 = ONE
        for b in range(len(buckets[2])):
            if mask >> b & 1:
                p2 = M.mul(p2, buckets[2][b])
        s2 = sig_shift(S, X, Y, U, V, p2, h, jj, binv)
        assert not (s2[9] or s2[10] or s2[11])
        want = ((-s2[12]) % N, (-s2[13]) % N, (-res - s2[14]) % N)
        if want in deep:
            kills += deep[want] * free5
            if len(examples) < want_examples:
                for q in subset_products(buckets[3] + buckets[4]):
                    cand = M.mul(p2, q)
                    if rel(M.mul(S, cand), X, Y, U, V, h, jj) == ONE:
                        examples.append(cand)
                        break
    return dict(res=res, kills=kills, order_log2=L.order_log2(), examples=examples,
                stageA=len(kernel), rows=[len(buckets[c]) for c in (2, 3, 4, 5)])


def slot_dress(w, slot, h=1, jj=0):
    """The five-slot dressing carrying `w` on `slot` and `1` everywhere else.

    Slots `3` and `4` are the LIVE handle pair, which sits at tuple indices `3 + 2 j` and
    `4 + 2 j`, not at `3` and `4`.
    """
    n = 3 + 2 * h
    idx = slot if slot < 3 else (slot + 2 * jj)
    return [w if k == idx else ONE for k in range(n)]


def slot_shift(S, X, Y, U, V, w, slot, h=1, jj=0, binv=None):
    """`SqU6.gaTwoShift h m z` for the single-slot dressing `z`, read off the relator."""
    m = frame(S, X, Y, U, V, h, jj)
    if binv is None:
        binv = M.inv(M.sqRelWord(m))
    d = [M.mul(m[k], z) for k, z in enumerate(slot_dress(w, slot, h, jj))]
    return M.mul(binv, M.sqRelWord(d))


FAST_SLOTS = (0, 3, 4)


def slot_kill_exact(S, X, Y, U, V, slot, h=1, jj=0, L=None, want_examples=1, cap=400000):
    """Does ANY achievable gamma_2-dressing of ONE slot kill the dressed frame?  EVERY slot.

    A nested sweep of the sift's four layers, valid at every slot because the shift's class-`c`
    rows read only the dressing's class-`<= c` part (`derive_census.py` section 2, exceptionless
    at all five slots).  The base relator must be CENTRAL, which is what a binder point supplies:
    then killing the dressed frame is exactly "the shift's fourteen lower rows vanish and its
    class-five row is `-res`", layer by layer.

    Slower than `slot_kill_census` by the size of the deeper layers, and used where that one is
    not licensed: the two CORE slots, at which the stronger facts fail.
    """
    if L is None:
        L = lattice(S, X, Y, U, V)
    buckets = rows_by_class(L)
    base = rel(S, X, Y, U, V, h, jj)
    assert all(base[k] == 0 for k in range(14)), "the base relator is not central"
    binv = M.inv(base)
    res = base[14]
    layers = [buckets[2], buckets[3], buckets[4], buckets[5]]
    rowsets = [(5, 6, 7, 8), (9, 10, 11), (12, 13), (14,)]
    frontier = [ONE]
    evals = 0
    for li in range(4):
        nxt = []
        block = subset_products(layers[li])
        if len(frontier) * len(block) > cap:
            return dict(res=res, kills=None, order_log2=L.order_log2(), examples=[],
                        evals=evals, capped=True)
        for p in frontier:
            for q in block:
                w = M.mul(p, q)
                sh = slot_shift(S, X, Y, U, V, w, slot, h, jj, binv)
                evals += 1
                if li < 3:
                    if any(sh[k] for k in rowsets[li]):
                        continue
                elif sh[14] != (-res) % N:
                    continue
                nxt.append(w)
        frontier = nxt
    return dict(res=res, kills=len(frontier), order_log2=L.order_log2(),
                examples=frontier[:want_examples], evals=evals, capped=False)


def slot_kill_census(S, X, Y, U, V, slot, h=1, jj=0, L=None, want_examples=1):
    """The FAST exact decision, licensed at the sigma slot and the two handle slots only.

    The sift's class-two layer is swept by brute force and the class-three, class-four and
    class-five layers are linear, because the shift is multiplicative in a gamma_3-shaped right
    factor and gamma_3-shaped elements multiply coordinatewise.  `derive_census.py` section 2
    certifies both at slots `0`, `3`, `4` and shows they FAIL at the two core slots, where the
    dressing enters through the powers `x^3` and `y^2`; use `slot_kill_exact` there.
    """
    assert slot in FAST_SLOTS, "the fast census is not licensed at slot %d" % slot
    if L is None:
        L = lattice(S, X, Y, U, V)
    buckets = rows_by_class(L)
    base = rel(S, X, Y, U, V, h, jj)
    assert all(base[k] == 0 for k in range(14)), "the base relator is not central"
    binv = M.inv(base)
    res = base[14]
    deeprows = buckets[3] + buckets[4] + buckets[5]
    steps = [tuple(slot_shift(S, X, Y, U, V, r, slot, h, jj, binv)[k] for k in range(9, 15))
             for r in deeprows]
    deep = {(0,) * 6: 1}
    for s in steps:
        nxt = dict(deep)
        for v, c in deep.items():
            w = tuple((v[k] + s[k]) % N for k in range(6))
            nxt[w] = nxt.get(w, 0) + c
        deep = nxt
    kills = 0
    examples = []
    swept = 0
    for p2 in subset_products(buckets[2]):
        s2 = slot_shift(S, X, Y, U, V, p2, slot, h, jj, binv)
        if any(s2[k] for k in range(5, 9)):
            continue                                # the class-two rows must not move
        swept += 1
        want = tuple((-s2[k]) % N for k in range(9, 14)) + (((-res - s2[14]) % N),)
        if want in deep:
            kills += deep[want]
            if len(examples) < want_examples:
                for q in subset_products(deeprows):
                    cand = M.mul(p2, q)
                    d = [M.mul(g, z) for g, z in
                         zip(frame(S, X, Y, U, V, h, jj), slot_dress(cand, slot, h, jj))]
                    if M.sqRelWord(d) == ONE:
                        examples.append(cand)
                        break
    return dict(res=res, kills=kills, order_log2=L.order_log2(), examples=examples,
                swept=swept, rows=[len(buckets[c]) for c in (2, 3, 4, 5)])


def random_multi_kill(S, X, Y, U, V, rng, trials, h=1, jj=0, L=None):
    """A random search over FIVE-slot achievable dressings, which no exhaustive method reaches.

    `|L|^5` is far beyond enumeration, so this is evidence and not a decision.  Each trial draws
    an independent uniform element of `L` for every slot.
    """
    if L is None:
        L = lattice(S, X, Y, U, V)
    rows = [L.table[k] for k in sorted(L.table)]
    m = frame(S, X, Y, U, V, h, jj)
    hits = 0
    for _ in range(trials):
        z = []
        for _ in range(5):
            g = ONE
            for r in rows:
                if rng.getrandbits(1):
                    g = M.mul(g, r)
            z.append(g)
        d = list(m)
        for k in range(3):
            d[k] = M.mul(d[k], z[k])
        d[3 + 2 * jj] = M.mul(d[3 + 2 * jj], z[3])
        d[4 + 2 * jj] = M.mul(d[4 + 2 * jj], z[4])
        if M.sqRelWord(d) == ONE:
            hits += 1
    return hits


def knob_report(S, X, Y, U, V, h=1, jj=0, L=None):
    """W63-CENTRAL2's own route: the `<m = t>` knob, and whether it is achievable."""
    if L is None:
        L = lattice(S, X, Y, U, V)
    res = rel(S, X, Y, U, V, h, jj)[14]
    xe = co(X, "e")
    if xe % 2 == 0:
        return dict(xe=xe, t=None, achievable=None, kills=None)
    t = (-res * INV8[xe % N]) % N
    w = mknob(t)
    return dict(xe=xe, t=t, achievable=L.contains(w),
                kills=rel(M.mul(S, w), X, Y, U, V, h, jj) == ONE)


def comm_m_parities(letters):
    """The parity of `[p, q].m` over the ten pairwise commutators, and whether any is odd.

    W62's `SqU6.commP_m_parity` makes this parity the bilinear form
    `p.j q.d + p.d q.j + p.f q.h + p.h q.f` on `stageN1` letters, and W62 also certifies that
    `(m, i, l) mod 2` is a homomorphism on the achievable lattice killing gamma_3, so "the
    lattice has an odd class-four coordinate" IS "some pairwise commutator does".
    """
    out = {}
    n = len(letters)
    for i in range(n):
        for j in range(i + 1, n):
            out[(i, j)] = co(M.commP(letters[i], letters[j]), "m") % 2
    return out


def bform(p, q):
    """W62's parity form for `[p, q].m` at `stageN1` letters."""
    return (co(p, "j") * co(q, "d") + co(p, "d") * co(q, "j")
            + co(p, "f") * co(q, "h") + co(p, "h") * co(q, "f")) % 2


def w58_bit(X, Y):
    """Wave 58's closed form for the class-five separation bit."""
    return (co(X, "a") * co(Y, "g") * co(Y, "i") + co(X, "e") * co(Y, "f") * co(Y, "h")) % 2


def show(p):
    return M.show(p)
