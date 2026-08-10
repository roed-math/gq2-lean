"""Exact SqU5 = U_5(Z/8) arithmetic, transcribed from GQ2/Dyadic/SqCore/GradedFour.lean.

Coordinates (a, b, c, d, e, f, g, h, i, j) = (x12, x23, x34, x45, x13, x24, x35, x14, x25, x15).
All arithmetic is plain Python integers reduced mod N (default 8); no external packages.
"""

N = 8

ONE = (0,) * 10


def red(p, n=N):
    return tuple(x % n for x in p)


def mul(p, q, n=N):
    (pa, pb, pc, pd, pe, pf, pg, ph, pi, pj) = p
    (qa, qb, qc, qd, qe, qf, qg, qh, qi, qj) = q
    return red((
        pa + qa,
        pb + qb,
        pc + qc,
        pd + qd,
        pe + qe + pa * qb,
        pf + qf + pb * qc,
        pg + qg + pc * qd,
        ph + qh + pa * qf + pe * qc,
        pi + qi + pb * qg + pf * qd,
        pj + qj + pa * qi + pe * qg + ph * qd,
    ), n)


def inv(p, n=N):
    (pa, pb, pc, pd, pe, pf, pg, ph, pi, pj) = p
    return red((
        -pa, -pb, -pc, -pd,
        pa * pb - pe,
        pb * pc - pf,
        pc * pd - pg,
        -(pa * pb * pc) + pa * pf + pc * pe - ph,
        -(pb * pc * pd) + pb * pg + pd * pf - pi,
        pa * pb * pc * pd - pa * pb * pg - pa * pd * pf + pa * pi
        - pc * pd * pe + pd * ph + pe * pg - pj,
    ), n)


def power(p, k, n=N):
    r = ONE
    for _ in range(k):
        r = mul(r, p, n)
    return r


def conjP(p, g, n=N):
    """x ^ g = g^{-1} x g, the repo convention."""
    return mul(mul(inv(g, n), p, n), g, n)


def commP(p, q, n=N):
    """[p, q] = p^{-1} q^{-1} p q, the repo convention."""
    return mul(mul(inv(p, n), inv(q, n), n), mul(p, q, n), n)


def sqWord(s, x, y, n=N):
    """(x^s)^{-1} * (x^3)^{-1} * y^2 * [y, y^s]."""
    return mul(mul(mul(inv(conjP(x, s, n), n), inv(power(x, 3, n), n), n),
                   power(y, 2, n), n),
               commP(y, conjP(y, s, n), n), n)


def handleWord(us, vs, n=N):
    r = ONE
    for u, v in zip(us, vs):
        r = mul(r, commP(u, v, n), n)
    return r


def sqRelWord(m, n=N):
    """m is the tuple (slot0=sigma, slot1=x0, slot2=x1, then handle pairs u_0, v_0, ...)."""
    h = (len(m) - 3) // 2
    us = [m[3 + 2 * k] for k in range(h)]
    vs = [m[4 + 2 * k] for k in range(h)]
    return mul(sqWord(m[0], m[1], m[2], n), handleWord(us, vs, n), n)


def liftC(w, n=N):
    return red((0, 0, 0, 0, 0, 0, 0, 0, 0, w), n)


def is_ga_two(p):
    return p[0] == 0 and p[1] == 0 and p[2] == 0 and p[3] == 0


def is_ga_three(p):
    return is_ga_two(p) and p[4] == 0 and p[5] == 0 and p[6] == 0


def is_ga_four(p):
    return is_ga_three(p) and p[7] == 0 and p[8] == 0


def selPar(x):
    return x % 2


# ---- committed objects, transcribed from GradedSigmaFour.lean -------------------

sigFourMark = (0, 1, 0, 0, 0, 0, 0, 0, 0, 0)
sigFourU = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
sigFourV = (2, 0, 0, 0, 0, 0, 0, 0, 0, 0)
sigFourX = (2, 0, 0, 0, 0, 0, 0, 0, 1, 0)
sigFourY = (0, 0, 0, 0, 1, 0, 4, 0, 2, 0)


def sigFourWit(v, n=N):
    return [mul(sigFourMark, v, n), sigFourX, sigFourY, sigFourU, sigFourV]


def sigFourRead(v, x, y, n=N):
    return (
        v[0] * (4 * (x[2] * x[3]) - 2 * (x[2] * y[3]) - 4 * (x[3] * x[5])
                + 2 * (x[5] * y[3]) - x[6] + x[8] - y[2] * y[3] + y[3] * y[5])
        + v[2] * (3 * (x[0] * x[3]) - 2 * (x[0] * y[3]) + 3 * (x[3] * x[4])
                  - 2 * (x[4] * y[3]) - y[0] * y[3] - 2 * (y[3] * y[4]))
        + v[3] * (x[0] * x[5] + x[2] * x[4] - x[7] - y[0] * y[2] + y[0] * y[5] + y[2] * y[4])
        + v[4] * (-4 * (x[2] * x[3]) + 2 * (x[2] * y[3]) + x[6] + y[2] * y[3])
        + v[5] * (3 * (x[0] * x[3]) - 2 * (x[0] * y[3]) - 2 * (y[0] * y[3]))
        + v[6] * (-x[0] - x[4])
        + v[7] * x[3] - v[8] * x[0]
        + (v[0] * v[3] * (x[5] - x[2]) - v[0] * v[5] * x[3]
           - v[2] * v[4] * x[3] + v[3] * v[4] * x[2])
    ) % n


def sigFourG(v, x, n=N):
    return (v[2] * x[3] - v[3] * x[2]) % n


def sigFourH(v, x, n=N):
    return (v[0] * (x[5] - x[2]) - v[2] * (x[0] + x[4]) + v[4] * x[2] - v[5] * x[0]) % n


def sigFourI(v, x, n=N):
    return (v[3] * (x[2] - x[5]) + v[5] * x[3]) % n


def sigLift(m, z0, w1, w2, z3, z4, n=N):
    """Five-slot class-four refinement at handle j = 0, h = 1."""
    return [mul(m[0], z0, n), mul(m[1], w1, n), mul(m[2], w2, n),
            mul(m[3], z3, n), mul(m[4], z4, n)]


# ---- general handle count -------------------------------------------------------------

def mirTuple(h, j, s, x, y, u, v, n=N):
    """GradedFourMirror.mirTuple: core slots, the j-th handle pair (u, v), the rest trivial."""
    m = [s, x, y]
    for k in range(h):
        m += [u, v] if k == j else [ONE, ONE]
    return m


def cwWit(h, j, y, U, V, v, n=N):
    """The witness shape with a FREE x1-slot `y`: sigma slot sigFourMark*v, x0 slot sigFourX,
    x1 slot `y`, the j-th handle pair (U, V), every other handle letter trivial.  With
    y = sigFourY this is GradedFourMirror.mirWit."""
    return mirTuple(h, j, mul(sigFourMark, v, n), sigFourX, y, U, V, n)


def sigLift_at(h, j, m, z0, w1, w2, z3, z4, n=N):
    """The five-slot refinement at handle j and handle count h."""
    m = list(m)
    m[0] = mul(m[0], z0, n)
    m[1] = mul(m[1], w1, n)
    m[2] = mul(m[2], w2, n)
    m[3 + 2 * j] = mul(m[3 + 2 * j], z3, n)
    m[4 + 2 * j] = mul(m[4 + 2 * j], z4, n)
    return m


def toU4L(p):
    return (p[0], p[1], p[2], p[4], p[5], p[7])


def toU4R(p):
    return (p[1], p[2], p[3], p[5], p[6], p[8])


def rowPivotVal(c, n=N):
    """GradedFourRow.rowPivotVal, the pivot image at every point of this family."""
    return red((-(2 * c), 1, 0, 0, 0, 0, 0, 0, -c, c * c + c), n)


# ---- the W57 points --------------------------------------------------------------------

# (a) the CLEARED row at general handle count: the committed letters, unchanged.
clrFourU = sigFourU              # (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
clrFourV = sigFourV              # (2, 0, 0, 0, 0, 0, 0, 0, 0, 0)

# (b) the LIVE-HANDLE-BLOCK point: the committed x1-slot with class-three coordinate 3, and
#     the committed v-letter with second class-two coordinate 2.
liveFourY = (0, 0, 0, 0, 1, 0, 4, 3, 2, 0)
liveFourU = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
liveFourV = (2, 0, 0, 0, 0, 2, 0, 0, 0, 0)


def in_live_frame(p):
    """liveFrameSub: vanishing third abelian column, EVEN second and third class-two ones."""
    return p[2] == 0 and p[5] % 2 == 0 and p[6] % 2 == 0


def in_row_frame(p):
    """GradedFourRow.rowFrameSub: c = 0, f = 0, g even - strictly inside liveFrameSub."""
    return p[2] == 0 and p[5] == 0 and p[6] % 2 == 0


# ---- the W56 committed displaced-row letters -------------------------------------------

mirFourU = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
mirFourV = (0, 0, 0, 1, 0, 0, 0, 0, 0, 0)
rowFourU = (0, 0, 0, 1, 0, 0, 0, 0, 0, 0)
rowFourV = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)

# ---- the W58 points --------------------------------------------------------------------

# (1) the MIRROR row (t, s) = (1, 0): left displacement, the block is inert under it.
mirLiveU = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)       # = mirFourU, the CLEAN open dressing
mirLiveV = (0, 0, 0, 1, 0, 4, 0, 0, 0, 0)       # mirFourV with f = 4
liveRowY = (0, 0, 0, 0, 1, 0, 4, 2, 2, 0)       # the shared x1-slot of the three rows
mirLiveY = liveRowY

# (2) the UNCLEARED-v row (t, s) = (0, 1): right displacement, the block is conjugated.
rowLiveU = (0, 0, 0, 1, 0, 4, 0, 0, 0, 0)       # rowFourU with f = 4
rowLiveV = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)       # = rowFourV, the CLEAN open dressing
rowLiveY = liveRowY

# (3) the DOUBLY uncleared row (t, s) = (1, 1): both displacements.
dblLiveU = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)       # = mirFourU
dblLiveV = (1, 0, 0, 0, 0, 4, 0, 0, 0, 0)       # rowFourV with f = 4
dblLiveY = liveRowY

# (4) the TWO-LIVE-HANDLE point at the cleared row: the COMMITTED core slots, the pair
#     (U, V) at one handle and the SWAPPED pair (V, U) at another.
twoLiveU = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)       # = sigFourU
twoLiveV = (2, 0, 0, 0, 0, 2, 0, 0, 0, 0)       # = W57's liveFourV

# (5) the two-live marking whose blocks are individually ODD in class three.
oddLiveU = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)       # = sigFourU
oddLiveV = (2, 0, 0, 1, 0, 1, 0, 0, 0, 0)       # f = 1 ODD, d = 1

# (6) the HIGHER pivot power row (t, s) = (2, 0).
hiLiveU = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)        # = sigFourU
hiLiveV = (0, 0, 0, 1, 0, 2, 0, 0, 0, 0)
hiLiveY = (0, 0, 0, 0, 1, 0, 4, 3, 2, 0)        # = W57's liveFourY

liveFourY = (0, 0, 0, 0, 1, 0, 4, 3, 2, 0)
liveFourU = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
liveFourV = (2, 0, 0, 0, 0, 2, 0, 0, 0, 0)


def twoTuple(h, j1, j2, s, x, y, u1, v1, u2, v2, n=N):
    """Core slots, the j1-th handle pair (u1, v1), the j2-th (u2, v2), the rest trivial."""
    m = [s, x, y]
    for k in range(h):
        if k == j1:
            m += [u1, v1]
        elif k == j2:
            m += [u2, v2]
        else:
            m += [ONE, ONE]
    return m


# ================================================================================
# W59-INVARIANT additions: the increment pairing, the derived subgroup, and the two
# markings that separate `liveFrameSub` from the sharp line.
# ================================================================================


def sigIncrPair(mU, mV, z3, z4, n=N):
    """The handle part of the five-slot increment of `sqRelWord_sigLift`:

        (z3.h * V.d - z3.i * V.a) + (U.a * z4.i - U.d * z4.h)

    with `U = m (sqHandleIdxU j)` and `V = m (sqHandleIdxV j)`.  This is the ONLY part of
    the increment that is not automatically even over the committed `x0`-gauge."""
    return (z3[7] * mV[3] - z3[8] * mV[0] + mU[0] * z4[8] - mU[3] * z4[7]) % n


def sigIncrFull(m, j, z0, w1, w2, z3, z4, n=N):
    """The full increment of `GradedSigmaFour.sqRelWord_sigLift` at handle `j`."""
    m1 = m[1]
    mU = m[3 + 2 * j]
    mV = m[4 + 2 * j]
    return ((z0[7] * m1[3] - z0[8] * m1[0]) + (-4 * w1[9] + 2 * w2[9])
            + (z3[7] * mV[3] - z3[8] * mV[0])
            + (mU[0] * z4[8] - mU[3] * z4[7])) % n


def subgroup_closure(gens, n=N, cap=1 << 22):
    """The subgroup of SqU5(Z/n) generated by `gens`, by orbit BFS."""
    seen = {ONE}
    frontier = [ONE]
    gg = list(gens) + [inv(g, n) for g in gens]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gg:
                y = mul(x, g, n)
                if y not in seen:
                    seen.add(y)
                    if len(seen) > cap:
                        raise RuntimeError("subgroup closure exceeded cap")
                    nxt.append(y)
        frontier = nxt
    return seen


def basic_commutators(gens, cls=4, n=N):
    """Weight-2..cls basic commutators in `gens`.  In a nilpotent group of class `cls` these
    generate the derived subgroup of the subgroup generated by `gens`."""
    out = set()
    level = [commP(p, q, n) for p in gens for q in gens]
    out.update(level)
    for _ in range(cls - 2):
        nxt = [commP(x, g, n) for x in level for g in gens]
        out.update(nxt)
        level = nxt
    return [x for x in out if x != ONE]


def derived_subgroup(gens, n=N):
    """gamma_2 of the subgroup generated by `gens` = `rowGaTwoOf (closure (range m))`."""
    return subgroup_closure(basic_commutators(gens, 4, n), n)


def gaThree_part(S):
    """The gamma_3-shaped elements of a set: the ones a five-slot handle move may be."""
    return sorted(z for z in S if is_ga_three(z))


def hi_parities(S):
    """The subgroup of F_2^2 realised by the (h, i)-coordinates of the gamma_3-shaped part."""
    return sorted({(z[7] % 2, z[8] % 2) for z in gaThree_part(S)})


def frame_orth(m, j, n=N):
    """THE SHARP LINE.  `True` iff every achievable gamma_3-shaped handle move pairs EVENLY
    against the two handle slots' outer columns, i.e. iff both mod-2 covectors (V.d, V.a) and
    (U.d, U.a) annihilate the class-three parity image of gamma_2 of the marking's image."""
    mU = m[3 + 2 * j]
    mV = m[4 + 2 * j]
    A = derived_subgroup(m, n)
    for z in gaThree_part(A):
        if (z[7] * mV[3] - z[8] * mV[0]) % 2 != 0:
            return False
        if (mU[0] * z[8] - mU[3] * z[7]) % 2 != 0:
            return False
    return True


def in_live_gaTwo(p):
    """liveGaTwoSub: the target of `commP_mem_liveGaTwoSub`."""
    return (p[0] == 0 and p[1] == 0 and p[2] == 0 and p[3] == 0 and p[5] == 0 and p[6] == 0
            and p[7] % 2 == 0 and p[8] % 2 == 0)


def in_half_frame(p):
    """halfFrameSub (W59): even fourth abelian column, even third class-two coordinate.  The
    invariant of the MIXED point, incomparable with `liveFrameSub`."""
    return p[3] % 2 == 0 and p[6] % 2 == 0


def in_half_gaTwo(p):
    """halfGaTwoSub (W59): the target of the mixed point's commutator lemma."""
    return p[3] % 2 == 0 and p[6] % 2 == 0 and p[8] % 2 == 0


# ---- the W59 points --------------------------------------------------------------------

# (A) the ORTHOGONAL point: BOTH handle covectors vanish, so the pairing is identically zero
#     and the forcing holds with NO achievability hypothesis at all - yet the block is ODD in
#     class three and the v-letter has a NONZERO c-column, so the marking is far outside
#     `liveFrameSub`.
orthU = (0, 0, 0, 0, 1, 0, 0, 0, 0, 0)          # e = 1
orthV = (0, 0, 1, 0, 0, 0, 0, 0, 0, 0)          # c = 1: outside liveFrameSub

# (B) the MIXED point: the committed odd-character letter `sigFourU` at the u-slot, so the
#     u-covector is (0, 1) and achievability IS load-bearing; the v-letter has ODD f, so the
#     block is odd in class three and the marking is outside `liveFrameSub`; but d and g stay
#     even everywhere, so every achievable move has EVEN second class-three coordinate and the
#     pairing still vanishes.
mixU = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)           # = sigFourU
mixV = (0, 0, 0, 0, 0, 1, 0, 0, 0, 0)           # f = 1 ODD: outside liveFrameSub


def twoSwapMark(h, j1, j2, U, V, n=N):
    """The W58 two-live-handle marking at the committed core slots: the pair (U, V) at handle
    j1 and the SWAPPED pair (V, U) at j2.  Kills the relator for ARBITRARY U, V."""
    return twoTuple(h, j1, j2, sigFourMark, sigFourX, sigFourY, U, V, V, U, n)


def twoSwapWit(h, j1, j2, U, V, v, n=N):
    """...with the sigma slot dressed by `v`."""
    return twoTuple(h, j1, j2, mul(sigFourMark, v, n), sigFourX, sigFourY, U, V, V, U, n)


def sigFourDress_at(m, v, n=N):
    """GradedSigmaFour.sigFourDress: the marking with the sigma slot multiplied by `v` on the
    right and every other slot untouched."""
    m = list(m)
    m[0] = mul(m[0], v, n)
    return m


# ================================================================================
# An exact, fast subgroup engine: induced polycyclic generating sequences.
#
# The coordinate order (a, b, c, d, e, f, g, h, i, j) filters SqU5 by SUBGROUPS
#   G_k = {p | p_0 = ... = p_{k-1} = 0},
# and on each `G_k` the k-th coordinate is a homomorphism to Z/8 (checked in
# `derive_necessity.py`).  So a subgroup S has an induced polycyclic generating sequence
# `piv[0..9]` with `S cap G_k = <piv[k], ..., piv[9]>`, computed by sifting.  In particular
#   S cap gamma_3 = <piv[7], piv[8], piv[9]>,
# which is the ONLY part of S the class-four forcing reads.
# ================================================================================


def _val2(x, n=N):
    """2-adic valuation of x in Z/n; the zero class gets the top valuation."""
    x %= n
    if x == 0:
        return n.bit_length() - 1
    v = 0
    while x % 2 == 0:
        x //= 2
        v += 1
    return v


def _first_nonzero(p, n=N):
    for k in range(10):
        if p[k] % n != 0:
            return k
    return None


def pc_sift(piv, x, n=N):
    """Reduce x by the pivots; return (k, y) with y the residue stuck at position k, or
    (None, ONE) if x reduces to the identity."""
    while True:
        k = _first_nonzero(x, n)
        if k is None:
            return (None, ONE)
        p = piv[k]
        if p is None:
            return (k, x)
        e = _val2(p[k], n)
        ex = _val2(x[k], n)
        if ex < e:
            return (k, x)
        m = n >> e
        t = ((x[k] % n) >> e) * pow((p[k] % n) >> e, -1, m) % m
        x = mul(power(inv(p, n), t, n), x, n)


def pc_closure(gens, n=N):
    """The induced polycyclic generating sequence of the subgroup generated by `gens`."""
    piv = [None] * 10
    pending = list(gens)
    while pending:
        x = pending.pop()
        k, y = pc_sift(piv, x, n)
        if k is None:
            continue
        old = piv[k]
        piv[k] = y
        if old is not None:
            pending.append(old)
        e = _val2(y[k], n)
        pending.append(power(y, 1 << ((n.bit_length() - 1) - e), n))
        for l in range(10):
            if piv[l] is not None and l != k:
                pending.append(commP(piv[l], y, n))
                pending.append(commP(y, piv[l], n))
    return piv


def pc_order(piv, n=N):
    o = 1
    for k in range(10):
        if piv[k] is not None:
            o *= 1 << ((n.bit_length() - 1) - _val2(piv[k][k], n))
    return o


def pc_gaThree(piv, n=N):
    """S cap gamma_3, enumerated: the tail <piv[7], piv[8], piv[9]> of the induced sequence."""
    out = [ONE]
    for k in (7, 8, 9):
        p = piv[k]
        if p is None:
            continue
        ordk = 1 << ((n.bit_length() - 1) - _val2(p[k], n))
        out = [mul(x, power(p, t, n), n) for x in out for t in range(ordk)]
    return sorted(set(out))


def derived_gaThree(m, n=N):
    """The achievable gamma_3-shaped handle moves of a marking: gamma_2 of its image, cut down
    to gamma_3.  Exact, and independent of any enumeration of the image."""
    return pc_gaThree(pc_closure(basic_commutators(list(m), 4, n), n), n)
