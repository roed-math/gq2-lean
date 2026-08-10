"""W61-BLOCK: mod-8 `U_6` arithmetic, the relator, and the layered solve.

Nothing is retyped: the coordinate law, the inverse, `conjP`, `commP` and `sqWord` are
imported from `scripts/w59_blind5/u6lib.py`, which certifies them against honest `6 x 6`
matrix arithmetic.  This module adds only

* reduction mod `8` (`gr3R = ZMod 8`);
* the relator `sqRelWord m = sqWord(m0, m1, m2) * prod_j [u_j, v_j]`, at any handle count;
* the **layered solve**: given a sigma slot `s`, an `x0` slot `x` and a target `T` in
  `gamma_2`, produce every `x1` slot `y` with `sqWord(s, x, y) = T`, class layer by class
  layer.  The solve is deliberately written WITHOUT the block equation it is used to test:
  at each of the fifteen rows it simply asks whether the residual is even, and reports the
  first row at which it is not.  Row `i` failing IS the block equation failing.

Coordinate naming is the campaign's (`GQ2/Dyadic/SqCore/GradedFive.lean`):

    index  0  1  2  3  4   5  6  7  8   9 10 11  12 13  14
    name   a  b  c  d  e   f  g  h  i   j  k  l   m  n   o
    entry 12 23 34 45 56  13 24 35 46  14 25 36  15 26  16
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "w59_blind5"))

from u6lib import NAMES, U6, commP, conjP, inv, mul, sqWord  # noqa: E402

M = 8

# The five class layers, in the order the layered solve must use them: setting a coordinate
# of one layer never disturbs a row of a strictly lower layer.
LAYERS = [["a", "b", "c", "d", "e"], ["f", "g", "h", "i"], ["j", "k", "l"], ["m", "n"], ["o"]]


def red(p):
    """Reduce a `U_6` element mod 8."""
    return U6({k: p.co[k] % M for k in NAMES})


def rand(rng, keys=NAMES):
    return U6({k: rng.randrange(M) for k in keys})


def eq(p, q):
    return all((p.co[k] - q.co[k]) % M == 0 for k in NAMES)


def is_one(p):
    return all(p.co[k] % M == 0 for k in NAMES)


def rmul(p, q):
    return red(mul(p, q))


def rinv(p):
    return red(inv(p))


def rsqWord(s, x, y):
    return red(sqWord(s, x, y))


def handle_word(us, vs):
    """`handleWord u v = prod_{j < h} [u_j, v_j]`, mod 8, in the campaign's order."""
    out = U6()
    for u, v in zip(us, vs):
        out = rmul(out, red(commP(u, v)))
    return out


def rel_word(s, x, y, us, vs):
    """`sqRelWord`, mod 8, at handle count `h = len(us)`."""
    return rmul(rsqWord(s, x, y), handle_word(us, vs))


# --------------------------------------------------------------------------------------
# The two functionals this lane is about.


def block_read(s, x):
    """⭐ **The block reading** `s_45 * x_56 - s_56 * x_45`, mod 8."""
    return (s.d * x.e - s.e * x.d) % M


def coupling(v, s, x):
    """The class-three sigma response `GradedFive.SqU6.sqWord_j_dress` produces, mod 8."""
    return (v.a * x.g - v.g * x.a + v.f * x.c - v.c * x.f
            - s.b * (v.a * x.c + v.c * x.a)) % M


def handle_minor(u, v):
    """The `j`-th handle's contribution to the block coordinate: `u_45 v_56 - u_56 v_45`."""
    return (u.d * v.e - u.e * v.d) % M


def par(z):
    return z % 2


# --------------------------------------------------------------------------------------
# The layered solve.


def solve_x1(s, x, target, rng, branch=None):
    """Find `y` with `sqWord(s, x, y) = target` mod 8, layer by layer.

    Returns `(y, None)` on success and `(None, row)` on failure, where `row` is the first
    coordinate whose residual came out ODD.  No parity fact is assumed anywhere: the solve
    computes `sqWord` honestly at every step and only ever asks `residual % 2 == 0`.
    """
    y = U6()
    picks = iter(branch) if branch is not None else None
    for layer in LAYERS:
        for row in layer:
            w = rsqWord(s, x, y)
            resid = (target.co[row] - w.co[row]) % M
            if resid % 2 != 0:
                return None, row
            half = (resid // 2) % 4
            bit = next(picks) if picks is not None else rng.randrange(2)
            y.co[row] = (y.co[row] + half + 4 * bit) % M
    if not eq(rsqWord(s, x, y), target):
        return None, "VERIFY"
    return y, None


def random_relator_marking(rng, h, tries=200, slot=None):
    """A relator-killing marking at handle count `h`, or `None`.

    Built the honest way round: random handle letters first, then the layered solve for the
    `x1` slot against the target `handleWord^{-1}`.  `slot` optionally pins the sigma slot.
    """
    for _ in range(tries):
        us = [rand(rng) for _ in range(h)]
        vs = [rand(rng) for _ in range(h)]
        hw = handle_word(us, vs)
        s = rand(rng) if slot is None else slot
        x = rand(rng)
        y, bad = solve_x1(s, x, rinv(hw), rng)
        if y is not None:
            return dict(s=s, x=x, y=y, us=us, vs=vs, h=h)
    return None


def sig_dress(mark, v):
    """`sigFiveDress`: multiply the sigma slot on the right by `v`, leave everything else."""
    out = dict(mark)
    out["s"] = rmul(mark["s"], v)
    return out


def rel_of(mark):
    return rel_word(mark["s"], mark["x"], mark["y"], mark["us"], mark["vs"])
