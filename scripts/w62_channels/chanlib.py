"""W62-CHANNELS shared machinery: the three-channel functional and the parity triple.

The transport `SqU6.sqRelWord_gaTwoDress_o_channel` (wave 61, committed) says that on the
achievable lattice the class-five row of a `gamma_2`-dressed frame moves by

    chan(z, L) = z.m * L.e + z.i * L.j + z.l * L.f

summed over the slots against the permuted letters, and by nothing else mod two.  A
`gamma_2`-level exclusion therefore needs a binder point at which that functional is EVEN for
every achievable dressing.  This module supplies the two objects the search needs:

* `parity3(z) = (z.m % 2, z.i % 2, z.l % 2)`, which on the achievable lattice is a group
  HOMOMORPHISM to `F_2^3` (`derive_channels.py` section 1 certifies both that and the fact
  that gamma_3 of the image dies under it), so the whole functional is decided by the ten
  pairwise commutators of the point's letters;
* `covector(L) = (L.e % 2, L.j % 2, L.f % 2)`, the letter's side of the pairing.

Group law: `w59_force5/u6mat.py`, honest 6 x 6 matrices over Z/8.  Nothing is read from Lean.
"""
import sys
import os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w60_stage4"))

import u6mat as M                                               # noqa: E402
import pointlib as P                                            # noqa: E402

N = 8
ONE = M.ONE
IDX = {c: k for k, c in enumerate(M.COORDS)}
SIG = M.sigFiveMark

SLOT = ["sigma", "x0", "x1", "U", "V"]


def co(z, c):
    return z[IDX[c]]


def parity3(z):
    """(m, i, l) mod two: the dressing's side of the three channels."""
    return (co(z, "m") % 2, co(z, "i") % 2, co(z, "l") % 2)


def covector(L):
    """(e, j, f) mod two: the letter's side of the three channels."""
    return (co(L, "e") % 2, co(L, "j") % 2, co(L, "f") % 2)


def chan(z, L):
    """`SqU6.gaTwoChannel z L`, over Z/8."""
    return (co(z, "m") * co(L, "e") + co(z, "i") * co(L, "j")
            + co(z, "l") * co(L, "f")) % N


def pair2(u, v):
    return (u[0] * v[0] + u[1] * v[1] + u[2] * v[2]) % 2


def fox(s, x, y):
    """`sqFoxX6 s x y = 10 x - s - 8 y`, columnwise."""
    return tuple((10 * x[k] - s[k] - 8 * y[k]) % N for k in range(15))


def marking(S, X, Y, U, V, h=1, jj=0):
    """The five-letter one-handle-live marking tuple (sigma slot ALREADY dressed)."""
    return P.mirTuple(h, jj, S, X, Y, U, V)


def letters_of(S, X, Y, U, V):
    """The generators of the image subgroup H at the dressed marking."""
    return [S, X, Y, U, V]


def beta_of(S, X, Y, U, V):
    """The permuted letters, slot by slot: `SqU6.gaTwoShiftChan`'s right-hand arguments.

    Slot 0 (sigma) reads `m 1 = x0`; slot 1 (x0) reads the Fox letter of the marking; slot 2
    (x1) reads `m 2 = x1`; the two handle slots read each other's letter.
    """
    return [X, fox(S, X, Y), Y, V, U]


def comm_gens(letters):
    """The pairwise commutators of the letters: achievable gamma_2-dressings by definition."""
    out = {}
    n = len(letters)
    for i in range(n):
        for j in range(i + 1, n):
            c = M.commP(letters[i], letters[j])
            if c != ONE:
                out[(i, j)] = c
    return out


def channel_span(letters):
    """The F_2-span W of the parity triples of the pairwise commutators.

    `derive_channels.py` certifies that this is the FULL image of the achievable lattice
    `forceLcs H 1 = [H, H]` under `parity3`, whenever the letters have even (1,2)- and
    (3,4)-columns: parity3 is then a homomorphism on the lattice, and every deeper commutator
    dies under it.
    """
    basis = []
    for c in comm_gens(letters).values():
        v = parity3(c)
        for b in basis:
            w = tuple((v[k] ^ b[k]) for k in range(3))
            if sum(w) < sum(v):
                v = w
        if any(v):
            basis.append(v)
            basis = reduce_basis(basis)
    return span_of(basis)


def reduce_basis(vs):
    """Row reduction over F_2 on 3-vectors."""
    basis = []
    for v in vs:
        cur = v
        for b in basis:
            lead = min(k for k in range(3) if b[k])
            if cur[lead]:
                cur = tuple(cur[k] ^ b[k] for k in range(3))
        if any(cur):
            basis.append(cur)
    return basis


def span_of(basis):
    out = {(0, 0, 0)}
    for b in basis:
        out |= {tuple(x[k] ^ b[k] for k in range(3)) for x in out}
    return out


def channels_even(S, X, Y, U, V):
    """Is the three-channel functional EVEN for every achievable dressing of every slot?

    Returns (verdict, offenders): an offender is (slot, (i, j), value) with `(i, j)` the index
    pair of the letter commutator whose channel against that slot's permuted letter is odd.
    """
    letters = letters_of(S, X, Y, U, V)
    beta = beta_of(S, X, Y, U, V)
    gens = comm_gens(letters)
    bad = []
    for key, z in gens.items():
        for s in range(5):
            if chan(z, beta[s]) % 2:
                bad.append((s, key, chan(z, beta[s])))
    return (not bad), bad


def lattice_closure(letters, cap=None):
    """The honest achievable lattice [H, H], by closure under products and conjugation."""
    seeds = [M.commP(a, b) for a in letters for b in letters]
    seen = {ONE}
    gens = []
    for s in sorted({t for t in seeds if t != ONE}):
        gens.append(s)
        gens.append(M.inv(s))
    changed = True
    while changed:
        changed = False
        for p in list(seen):
            for g in gens:
                q = M.mul(p, g)
                if q not in seen:
                    seen.add(q)
                    changed = True
            for c in letters:
                q = M.conjP(p, c)
                if q not in seen:
                    seen.add(q)
                    changed = True
        if cap is not None and len(seen) > cap:
            raise RuntimeError("lattice larger than cap %d" % cap)
    return seen


def residue(S, X, Y, U, V, h=1, jj=0):
    return M.sqRelWord(marking(S, X, Y, U, V, h, jj))


def stageN1(z):
    return co(z, "a") % 2 == 0 and co(z, "c") % 2 == 0


def gauge_x(X):
    """The committed class-two-forced gauge on the `x0` slot (GradedSigmaFour.sigFourRead_gauge
    read through `toU5L`): a, c, d, f, g even and b = 0."""
    return (co(X, "a") % 2 == 0 and co(X, "c") % 2 == 0 and co(X, "d") % 2 == 0
            and co(X, "f") % 2 == 0 and co(X, "g") % 2 == 0 and co(X, "b") == 0)


def gauge_y(Y):
    """…and on the `x1` slot: a, c, d even."""
    return (co(Y, "a") % 2 == 0 and co(Y, "c") % 2 == 0 and co(Y, "d") % 2 == 0)


def class_four_blind(S, X, Y, U, V, h=1, jj=0):
    """Do both `U_5`-quotients kill the class-four relator at this marking?

    `SqU6.toU5L_sqRelWord` (committed) makes `toU5L` a homomorphism intertwining the two
    relators, so this is the quotient of the class-five relator and needs no second engine.
    """
    r = residue(S, X, Y, U, V, h, jj)
    return M.toU5L(r) == (0,) * 10 and M.toU5R(r) == (0,) * 10
