"""W64-CENSUS5 step 1: certify the knob identity and the machinery the census runs on.

Five sections, each a list of NAMED checks with a pass/fail count.  Everything is on the honest
6 x 6 matrices of `scripts/w59_force5/u6mat.py`; section 1 additionally rebuilds the group law
over eight different moduli so the ring-generic claim is tested and not asserted.

  1. THE KNOB IDENTITY.  Dressing one slot by `<m = t>` translates the relator's class-five row
     by `gearing * t` and by nothing else, where the gearing is the `(5,6)`-column of the
     Fox-permuted letter of that slot.  At the sigma slot and both handle slots the whole shift
     is that central translation; at the two core slots it is not.
  2. THE FAST CENSUS.  The four structural facts that let `censuslib.slot_kill_census` decide a
     slot exactly in `2^(#class-two rows)` relator evaluations instead of enumerating `[H, H]`.
  3. CROSS-CHECKS.  The fast census against W63-CENTRAL2's own exhaustive sweep, and against
     honest brute force over a whole small lattice.
  4. THE CLASS-FOUR PARITY.  W62's bilinear form for `[p, q].m`, re-measured; and that the
     lattice's class-four parity is decided by the ten pairwise commutators.
  5. LIVENESS AND `x0.e`.  The measured half of the census criterion: at a point whose undressed
     frame kills and whose `a0 = a1` frame is central, an EVEN `x0.e` forces an EVEN residue.

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

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import censuslib as CE                                            # noqa: E402
import centrallib as C                                            # noqa: E402
import u6mat as M                                                 # noqa: E402

FAIL = [0]
NCHK = [0]


def check(name, cond, extra=""):
    NCHK[0] += 1
    if not cond:
        FAIL[0] += 1
    print("   [%s] %-72s %s" % ("ok " if cond else "FAIL", name, extra))


def head(t):
    print()
    print("=" * 98)
    print("== " + t)
    print("=" * 98)
    print()


# ---- a modulus-parametrised rebuild of the group law, for the ring-generic claim ------------

POS = [(1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (1, 3), (2, 4), (3, 5), (4, 6),
       (1, 4), (2, 5), (3, 6), (1, 5), (2, 6), (1, 6)]


def ring(N):
    ONE = (0,) * 15

    def mat(p):
        A = [[1 if r == c else 0 for c in range(6)] for r in range(6)]
        for k, (i, j) in enumerate(POS):
            A[i - 1][j - 1] = p[k] % N
        return A

    def tup(A):
        return tuple(A[i - 1][j - 1] % N for (i, j) in POS)

    def mmul(A, B):
        return [[sum(A[i][k] * B[k][j] for k in range(6)) % N for j in range(6)]
                for i in range(6)]

    def minv(A):
        X = [[0] * 6 for _ in range(6)]
        for j in range(6):
            for i in range(j, -1, -1):
                X[i][j] = ((1 if i == j else 0)
                           - sum(A[i][k] * X[k][j] for k in range(i + 1, 6))) % N
        return X

    def mul(p, q):
        return tup(mmul(mat(p), mat(q)))

    def inv(p):
        return tup(minv(mat(p)))

    def pw(p, k):
        r = ONE
        for _ in range(k):
            r = mul(r, p)
        return r

    def conj(p, g):
        return mul(mul(inv(g), p), g)

    def comm(p, q):
        return mul(mul(inv(p), inv(q)), mul(p, q))

    def sqWord(s, x, y):
        return mul(mul(mul(inv(conj(x, s)), inv(pw(x, 3))), pw(y, 2)), comm(y, conj(y, s)))

    def relword(m):
        r = sqWord(m[0], m[1], m[2])
        for k in range((len(m) - 3) // 2):
            r = mul(r, comm(m[3 + 2 * k], m[4 + 2 * k]))
        return r

    return dict(ONE=ONE, mul=mul, inv=inv, rel=relword, N=N)


def section1(rng):
    head("1  THE KNOB IDENTITY: one class-four coordinate, one gearing")
    print("   Dressing slot `i` by `<m = t>` and reading the shift off the relator, never from")
    print("   an emitted closed form.  The five gearings are the `(5,6)`-columns of the")
    print("   Fox-permuted letters `(x0, 10 x0 - sigma - 8 x1, x1, v_j, -u_j)`.")
    print()

    def fox(s, x, y):
        return tuple((10 * x[k] - s[k] - 8 * y[k]) % 8 for k in range(15))

    names = ["sigma slot   (gearing x0.e )", "x0 slot      (gearing fox.e)",
             "x1 slot      (gearing x1.e )", "u-handle slot(gearing v.e  )",
             "v-handle slot(gearing -u.e )"]
    badrow = [0] * 5
    badcen = [0] * 5
    n = 400
    for _ in range(n):
        h = 1 + rng.randrange(3)
        jj = rng.randrange(h)
        L = [M.named(**{k: rng.randrange(8) for k in M.COORDS}) for _ in range(5)]
        S, X, Y, U, V = L
        t = rng.randrange(8)
        gear = [X[4], fox(S, X, Y)[4], Y[4], V[4], (-U[4]) % 8]
        for s in range(5):
            sh = CE.slot_shift(S, X, Y, U, V, M.named(m=t), s, h, jj)
            if sh[14] != (gear[s] * t) % 8:
                badrow[s] += 1
            if sh != M.liftC(gear[s] * t):
                badcen[s] += 1
    for s in range(5):
        check("class-five row moves by gearing * t: %s" % names[s], badrow[s] == 0,
              "%d/%d exceptions" % (badrow[s], n))
    for s in (0, 3, 4):
        check("whole shift IS that central translation: %s" % names[s], badcen[s] == 0,
              "%d/%d exceptions" % (badcen[s], n))
    check("the two core slots are NOT central (so they carry no knob of this kind)",
          badcen[1] > 0 and badcen[2] > 0,
          "x0 slot %d/%d, x1 slot %d/%d non-central" % (badcen[1], n, badcen[2], n))

    print()
    print("   The same three central identities over eight moduli, which is the ring-generic")
    print("   claim the Lean statements make.")
    print()
    for N in (3, 4, 5, 7, 8, 9, 16, 32):
        R = ring(N)
        bad = 0
        for _ in range(120):
            h = 1 + rng.randrange(2)
            jj = rng.randrange(h)
            S, X, Y, U, V = [tuple(rng.randrange(N) for _ in range(15)) for _ in range(5)]
            t = rng.randrange(N)
            knob = tuple(t if k == 12 else 0 for k in range(15))
            m = [S, X, Y]
            for k in range(h):
                m += [U, V] if k == jj else [R["ONE"]] * 2
            base = R["rel"](m)
            for slot, gear in ((0, X[4]), (3 + 2 * jj, V[4]), (4 + 2 * jj, (-U[4]) % N)):
                d = list(m)
                d[slot] = R["mul"](d[slot], knob)
                lift = tuple((gear * t) % N if k == 14 else 0 for k in range(15))
                if R["rel"](d) != R["mul"](base, lift):
                    bad += 1
        check("sigma and both handle knobs over Z/%d" % N, bad == 0,
              "%d/%d exceptions" % (bad, 360))


def section2(rng):
    head("2  THE CENSUS MACHINERY: which structural facts hold, and where")
    print("   `Phi_i(w)` is the shift of a single-slot gamma_2 dressing on slot `i`, read off")
    print("   the relator.  The WEAK fact licenses the nested sweep `slot_kill_exact` at every")
    print("   slot; the four STRONG facts license the fast `slot_kill_census`, and they hold at")
    print("   the sigma slot and both handle slots and FAIL at the two core slots, where the")
    print("   dressing enters through the powers `x^3` and `y^2`.")
    print()
    CLSC = {2: "fghi", 3: "jkl", 4: "mn", 5: "o"}
    ROWS = {2: (5, 6, 7, 8), 3: (9, 10, 11), 4: (12, 13), 5: (14,)}
    n = 200
    badW = [[0] * 4 for _ in range(5)]
    badA = [0] * 5
    badB = [0] * 5
    badC = [0] * 5
    badD = [0] * 5
    for _ in range(n):
        h = 1 + rng.randrange(2)
        jj = rng.randrange(h)
        S, X, Y, U, V = [M.named(**{k: rng.randrange(8) for k in M.COORDS}) for _ in range(5)]

        def g2(keep=""):
            return M.named(**{k: (w[CE.IDX[k]] if k in keep else rng.randrange(8))
                              for k in "fghijklmno"})
        w = M.named(**{k: rng.randrange(8) for k in "fghijklmno"})
        r3 = M.named(**{k: rng.randrange(8) for k in "jklmno"})
        for s in range(5):
            base = CE.slot_shift(S, X, Y, U, V, w, s, h, jj)
            for ci, c in enumerate((2, 3, 4, 5)):
                keep = "".join(CLSC[d] for d in range(2, c + 1))
                other = CE.slot_shift(S, X, Y, U, V, g2(keep), s, h, jj)
                if tuple(base[k] for k in ROWS[c]) != tuple(other[k] for k in ROWS[c]):
                    badW[s][ci] += 1
            if tuple(base[k] for k in ROWS[3]) != \
                    tuple(CE.slot_shift(S, X, Y, U, V, g2("fghi"), s, h, jj)[k] for k in ROWS[3]):
                badA[s] += 1
            if tuple(base[k] for k in ROWS[4]) != \
                    tuple(CE.slot_shift(S, X, Y, U, V, g2("fghijkl"), s, h, jj)[k]
                          for k in ROWS[4]):
                badB[s] += 1
            if base != CE.slot_shift(S, X, Y, U, V, g2("fghijklmn"), s, h, jj):
                badC[s] += 1
            if CE.slot_shift(S, X, Y, U, V, M.mul(w, r3), s, h, jj) != \
                    M.mul(base, CE.slot_shift(S, X, Y, U, V, r3, s, h, jj)):
                badD[s] += 1
    for s in range(5):
        check("WEAK, slot %d: class-c rows read only the dressing's class-<=c part" % s,
              sum(badW[s]) == 0, "exceptions per c=2,3,4,5: %s of %d" % (badW[s], n))
    for s in CE.FAST_SLOTS:
        check("STRONG A, slot %d: class-three rows read only the class-two part" % s,
              badA[s] == 0, "%d/%d" % (badA[s], n))
        check("STRONG B, slot %d: class-four rows read only the class-<=3 part" % s,
              badB[s] == 0, "%d/%d" % (badB[s], n))
        check("STRONG C, slot %d: the shift ignores w.o" % s, badC[s] == 0,
              "%d/%d" % (badC[s], n))
        check("STRONG D, slot %d: Phi(w r) = Phi(w) Phi(r), r gamma_3-shaped" % s,
              badD[s] == 0, "%d/%d" % (badD[s], n))
    check("the strong facts FAIL at both core slots, so the fast census is not run there",
          min(badA[1], badA[2], badD[1], badD[2]) > 0,
          "A: %d, %d of %d; D: %d, %d of %d" % (badA[1], badA[2], n, badD[1], badD[2], n))
    bad = 0
    for _ in range(400):
        p = M.named(**{k: rng.randrange(8) for k in "jklmno"})
        q = M.named(**{k: rng.randrange(8) for k in "jklmno"})
        if M.mul(p, q) != tuple((p[k] + q[k]) % 8 for k in range(15)):
            bad += 1
    check("gamma_3-shaped elements multiply COORDINATEWISE (so the deep layers are linear)",
          bad == 0, "%d/400" % bad)


def section3(rng):
    head("3  CROSS-CHECKS of the census")
    S = M.mul(CE.SIG, C.stageX)
    L = CE.lattice(S, C.stageX, C.stageY, C.stageU, C.stageV)
    check("wave 60's achievable gamma_2 lattice has order 2^26 (W63-CENTRAL2's count)",
          L.order_log2() == 26, "2^%d" % L.order_log2())
    r0 = CE.sigma_kill_census(S, C.stageX, C.stageY, C.stageU, C.stageV, L=L, want_examples=0)
    r1 = CE.slot_kill_census(S, C.stageX, C.stageY, C.stageU, C.stageV, 0, L=L, want_examples=0)
    check("sigma-slot kill count is W63-CENTRAL2's 131072", r0["kills"] == 131072,
          "%d" % r0["kills"])
    check("the generic per-slot census agrees with the sigma-only one at slot 0",
          r0["kills"] == r1["kills"], "%d vs %d" % (r0["kills"], r1["kills"]))
    ex = CE.sigma_kill_census(S, C.stageX, C.stageY, C.stageU, C.stageV, L=L,
                              want_examples=1)["examples"]
    ok = all(CE.rel(M.mul(S, w), C.stageX, C.stageY, C.stageU, C.stageV) == M.ONE and
             L.contains(w) for w in ex)
    check("every exhibited killer is achievable AND kills, by direct evaluation", ok,
          "witness %s" % (M.show(ex[0]) if ex else "none"))
    check("W63-CENTRAL2's own killer <m=3> is in the lattice and kills",
          L.contains(M.named(m=3)) and
          CE.rel(M.mul(S, M.named(m=3)), C.stageX, C.stageY, C.stageU, C.stageV) == M.ONE)

    print()
    print("   Three independent routes on SUB-LATTICES of wave 60's achievable lattice, small")
    print("   enough to enumerate outright: the fast census, the nested sweep, and honest")
    print("   brute force over every element.  The base relator is central at this point, so")
    print("   all three decide the same question.")
    print()
    rows = [L.table[k] for k in sorted(L.table)]
    for slot in range(5):
        badf = badb = tested = 0
        for _ in range(60):
            sub = C.Sift()
            for r in rng.sample(rows, 10):
                sub.add(r)
            if sub.order_log2() > 11:
                continue
            tested += 1
            ex = CE.slot_kill_exact(S, C.stageX, C.stageY, C.stageU, C.stageV, slot, L=sub,
                                    want_examples=0)
            brute = 0
            for w in sub.elements():
                d = [M.mul(g, z) for g, z in
                     zip(CE.frame(S, C.stageX, C.stageY, C.stageU, C.stageV),
                         CE.slot_dress(w, slot))]
                if M.sqRelWord(d) == M.ONE:
                    brute += 1
            if brute != ex["kills"]:
                badb += 1
            if slot in CE.FAST_SLOTS:
                fast = CE.slot_kill_census(S, C.stageX, C.stageY, C.stageU, C.stageV, slot,
                                           L=sub, want_examples=0)
                if fast["kills"] != brute:
                    badf += 1
            if tested >= 12:
                break
        check("slot %d: the nested sweep equals brute force on %d sub-lattices"
              % (slot, tested), badb == 0, "%d mismatches" % badb)
        if slot in CE.FAST_SLOTS:
            check("slot %d: the FAST census equals brute force on the same sub-lattices" % slot,
                  badf == 0, "%d mismatches" % badf)


def section4(rng):
    head("4  THE CLASS-FOUR PARITY: W62's form, and what the lattice can reach")
    bad = 0
    n = 3000
    for _ in range(n):
        def st():
            d = {k: rng.randrange(8) for k in M.COORDS}
            d["a"] = rng.randrange(0, 8, 2)
            d["c"] = rng.randrange(0, 8, 2)
            return M.named(**d)
        p, q = st(), st()
        if CE.co(M.commP(p, q), "m") % 2 != CE.bform(p, q):
            bad += 1
    check("W62 `commP_m_parity`: [p,q].m = p.j q.d + p.d q.j + p.f q.h + p.h q.f (mod 2)",
          bad == 0, "%d/%d exceptions on stageN1 pairs" % (bad, n))
    S = M.mul(CE.SIG, C.stageX)
    L = CE.lattice(S, C.stageX, C.stageY, C.stageU, C.stageV)
    letters = [S, C.stageX, C.stageY, C.stageU, C.stageV]
    pars = CE.comm_m_parities(letters)
    odd = sum(1 for v in pars.values() if v)
    latodd = any(L.table[k][12] % 2 for k in L.table)
    check("at wave 60's point the ten pairwise commutators give an odd class-four coordinate",
          odd > 0 and latodd, "%d of 10 odd" % odd)
    bad = 0
    rows = [L.table[k] for k in sorted(L.table)]
    for _ in range(2000):
        a = M.ONE
        b = M.ONE
        for r in rows:
            if rng.getrandbits(1):
                a = M.mul(a, r)
            if rng.getrandbits(1):
                b = M.mul(b, r)
        if CE.co(M.mul(a, b), "m") % 2 != (CE.co(a, "m") + CE.co(b, "m")) % 2:
            bad += 1
    check("the class-four parity is a HOMOMORPHISM on the achievable lattice", bad == 0,
          "%d/2000 exceptions" % bad)


def section5(rng):
    head("5  LIVENESS AND `x0.e`: the measured half of the census criterion")
    print("   The `a0 = a1` residue is `sqWord(sigma x0, x0, x1) * sqWord(sigma, x0, x1)^{-1}`")
    print("   whenever the undressed frame kills, so the liveness condition DECOUPLES from the")
    print("   handle letters and can be swept far more widely than whole binder points.  The")
    print("   `x1` slot's abelian columns are pinned by the relator's own rows")
    print("   (`sqRelWord_lower_x1_even`), which is imposed here.")
    print()

    def D(X, Y):
        return M.mul(M.sqWord(M.mul(CE.SIG, X), X, Y), M.inv(M.sqWord(CE.SIG, X, Y)))

    def randX(par):
        d = {k: rng.randrange(8) for k in M.COORDS}
        d["a"] = rng.randrange(0, 8, 2)
        d["c"] = rng.randrange(0, 8, 2)
        d["e"] = rng.randrange(par, 8, 2)
        return M.named(**d)

    def randY(X):
        d = {k: rng.randrange(8) for k in M.COORDS}
        for k in "abcde":
            d[k] = (2 * X[CE.IDX[k]]) % 4 + 4 * rng.randrange(2)
        return M.named(**d)

    n = 60000
    tab = {}
    for par in (0, 1):
        cen = odd = 0
        for _ in range(n):
            X = randX(par)
            Y = randY(X)
            d = D(X, Y)
            if all(d[k] == 0 for k in range(14)):
                cen += 1
                if d[14] % 2:
                    odd += 1
        tab[par] = (cen, odd)
        print("   x0.e %-4s : %6d of %d have a CENTRAL residue, %6d of those are ODD"
              % ("EVEN" if par == 0 else "ODD", cen, n, odd))
    print()
    check("an EVEN `x0.e` never produces an odd residue (the incompatibility)",
          tab[0][1] == 0, "%d of %d central cases" % (tab[0][1], tab[0][0]))
    check("an ODD `x0.e` produces them in quantity (so the horn is not vacuous)",
          tab[1][1] > 0, "%d of %d central cases" % (tab[1][1], tab[1][0]))

    print()
    print("   And wave 58's closed form for the bit, on the same sample.")
    print()
    bad = tot = 0
    for _ in range(20000):
        X = randX(rng.randrange(2))
        Y = randY(X)
        d = D(X, Y)
        tot += 1
        if d[14] % 2 != CE.w58_bit(X, Y):
            bad += 1
    check("wave 58's form `x0.a x1.g x1.i + x0.e x1.f x1.h` IS the bit, mod two", bad == 0,
          "%d/%d exceptions" % (bad, tot))


def main():
    rng = random.Random(64005)
    print("=" * 98)
    print("== W64-CENSUS5: the knob identity, the census machinery, and the parity horn ==")
    print("=" * 98)
    section1(rng)
    section2(rng)
    section3(rng)
    section4(rng)
    section5(rng)
    print()
    print("=" * 98)
    print("== %d named checks, %d failures ==" % (NCHK[0], FAIL[0]))
    print("=" * 98)


if __name__ == "__main__":
    main()
