"""W63-CENTRAL2 shared machinery: the gamma_2 shift, and subgroups by polycyclic sifting.

Everything is taken on the honest `6 x 6` matrices of `scripts/w59_force5/u6mat.py` over `Z/8`.
Nothing is transcribed from the Lean file: the gamma_2 shift is not evaluated from
`SqU6.gaTwoShift`'s fifty-two-term closed form, it is READ OFF the relator,

    gaTwoShift(m, z) = sqRelWord(m)^{-1} * sqRelWord(conFiveDress(m, z)),

which is `SqU6.sqRelWord_gaTwoDress` solved for the shift.  So the measurements below are
independent of every emitted form in `GradedFiveGammaTwo`.

The second half is a polycyclic sift for subgroups of `U_6(Z/8)`.  The coordinate order is by
class (a b c d e | f g h i | j k l | m n | o), so an element that vanishes in every coordinate
before position `k` adds exactly at position `k`: within one class the group law is addition.
That makes the standard induced-polycyclic-sequence algorithm exact, with one table row per
(coordinate, 2-valuation) pair, hence at most 45 rows and a subgroup order of `2^(#rows)`.

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
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))

import u6mat as M                                               # noqa: E402

N = 8
COORDS = M.COORDS
IDX = {c: k for k, c in enumerate(COORDS)}
ONE = M.ONE

# ---- wave 60's binder point ---------------------------------------------------------------

stageX = M.named(a=2, e=5)
stageY = M.named(e=2, f=1, g=1, h=1, m=3, n=3)
stageU = M.named(a=6, b=7, c=4, d=1, e=3, g=5, h=5)
stageV = M.named(a=6, b=7, c=6, d=1, e=3, f=5, g=3, h=3, i=4)
sigMark = M.sigFiveMark


def stage_wit(v, h=1, jj=0):
    """`stageWit h j v`: the sigma slot is `fiveSigMark * v`."""
    return M.mirTuple(h, jj, M.mul(sigMark, v), stageX, stageY, stageU, stageV)


def co(z, c):
    return z[IDX[c]]


def dress(m, z):
    return [M.mul(m[i], z[i]) for i in range(len(m))]


def shift(m, z):
    """`SqU6.gaTwoShift h m z`, read off the translation identity."""
    return M.mul(M.inv(M.sqRelWord(m)), M.sqRelWord(dress(m, z)))


def is_central(p):
    """`p = SqU6.liftO w` for some `w`: every one of the fourteen lower rows vanishes."""
    return all(p[k] == 0 for k in range(14))


def slot(i, g, n=5):
    return [g if k == i else ONE for k in range(n)]


def fox(s, x, y):
    """`sqFoxX6 s x y`, which GradedFiveStageFour defines columnwise."""
    return tuple((10 * x[k] - s[k] - 8 * y[k]) % N for k in range(15))


def chan_pair(z, L):
    """`SqU6.gaTwoChannel z L = z.m * L.e + z.i * L.j + z.l * L.f`."""
    return (co(z, "m") * co(L, "e") + co(z, "i") * co(L, "j") + co(z, "l") * co(L, "f")) % N


def shift_chan(m, z, h=1, jj=0):
    """`SqU6.gaTwoShiftChan h m z`, the three-channel functional."""
    tot = chan_pair(z[0], m[1]) + chan_pair(z[1], fox(m[0], m[1], m[2])) + chan_pair(z[2], m[2])
    for k in range(h):
        tot += chan_pair(z[3 + 2 * k], m[4 + 2 * k]) - chan_pair(z[4 + 2 * k], m[3 + 2 * k])
    return tot % N


# ---- polycyclic sifting -------------------------------------------------------------------


def val2(x):
    """2-adic valuation of `x` in `Z/8`, with `val2(0) = 3`."""
    x %= N
    if x == 0:
        return 3
    v = 0
    while x % 2 == 0:
        x //= 2
        v += 1
    return v


def leading(g):
    for k in range(15):
        if g[k] % N:
            return (k, val2(g[k]))
    return None


INV8 = {1: 1, 3: 3, 5: 5, 7: 7}


class Sift:
    """An induced polycyclic sequence for a subgroup of `U_6(Z/8)`."""

    def __init__(self):
        self.table = {}                     # (coordinate, valuation) -> group element

    def reduce(self, g):
        """Sift `g` down; returns the residue, `ONE` exactly when `g` is in the subgroup."""
        while True:
            lead = leading(g)
            if lead is None:
                return g
            k, v = lead
            row = self.table.get(lead)
            if row is None:
                return g
            u1 = (g[k] // (1 << v)) % N          # odd, since v = val2(g[k])
            u2 = (row[k] // (1 << v)) % N        # odd, since the row sits at the same valuation
            t = (u1 * INV8[u2 % 8]) % N
            g = M.mul(g, M.inv(M.power(row, t)))

    def add(self, g):
        """Insert `g`; returns the newly seated element, or None if `g` was already inside."""
        r = self.reduce(g)
        if leading(r) is None:
            return None
        self.table[leading(r)] = r
        return r

    def order_log2(self):
        return len(self.table)

    def elements(self):
        """Every element, as products of the table rows in coordinate order."""
        rows = [self.table[k] for k in sorted(self.table)]
        out = [ONE]
        for r in reversed(rows):
            out = [M.mul(r, x) for x in out] + out
        return out

    def contains(self, g):
        return leading(self.reduce(g)) is None


def subgroup(gens, extra_normalisers=()):
    """The subgroup generated by `gens`, closed under squares and commutators.

    `extra_normalisers` are further elements to commute new rows against, which is how the
    NORMAL closure (needed for `[H, H]` inside `H`) is obtained.
    """
    S = Sift()
    todo = []
    for g in gens:
        r = S.add(g)
        if r is not None:
            todo.append(r)
    others = list(extra_normalisers)
    while todo:
        x = todo.pop()
        cands = [M.mul(x, x)]
        for y in list(S.table.values()) + others:
            cands.append(M.commP(x, y))
        for c in cands:
            r = S.add(c)
            if r is not None:
                todo.append(r)
    return S


def image_group(m):
    """`H = Subgroup.closure (Set.range m)`, the image of the marking."""
    gens = [g for g in m if g != ONE]
    return subgroup(gens)


def derived_of(gens):
    """`forceLcs H 1 = [H, H]`: the normal closure in `H` of the pairwise commutators."""
    comms = []
    gg = [g for g in gens if g != ONE]
    for i in range(len(gg)):
        for j in range(i + 1, len(gg)):
            comms.append(M.commP(gg[i], gg[j]))
    return subgroup(comms, extra_normalisers=gg)
