"""W63-SECOND: the four class-two block readings of `U_6`, and the pair of them.

Layered on `scripts/w61_block/blocklib.py`, which is layered on the independently certified
`scripts/w59_blind5/u6lib.py`.  Nothing about the group law, the relator or the layered solve is
retyped here.

The campaign's coordinate naming (`GQ2/Dyadic/SqCore/GradedFive.lean`):

    index  0  1  2  3  4   5  6  7  8   9 10 11  12 13  14
    name   a  b  c  d  e   f  g  h  i   j  k  l   m  n   o
    entry 12 23 34 45 56  13 24 35 46  14 25 36  15 26  16

`U_6` has four class-two coordinates `f, g, h, i` at rows `(1,3), (2,4), (3,5), (4,6)`, and each
is the wedge of the two abelian columns beneath it:

    row  f = (1,3)   columns (a, b) = ((1,2), (2,3))
    row  g = (2,4)   columns (b, c) = ((2,3), (3,4))
    row  h = (3,5)   columns (c, d) = ((3,4), (4,5))
    row  i = (4,6)   columns (d, e) = ((4,5), (5,6))

Wave 61 committed the `i` one as `SqU6.blockRead s x = s.d * x.e - s.e * x.d`.  This lane is
about the `h` one, `s.c * x.d - s.d * x.c`, which `docs/dyadic/w61-block-note.md` section 6.3
called the second block reading, and about the pair.

`ROWS` below is the single place the four readings are named; every measurement in this
directory is written against it, so no reading is special-cased anywhere.

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "w61_block"))
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "w59_blind5"))

from blocklib import (  # noqa: E402
    LAYERS, M, eq, handle_word, is_one, par, rand, red, rel_of, rel_word, rinv, rmul,
    rsqWord, sig_dress, solve_x1,
)
from u6lib import NAMES, U6, commP, conjP, inv, mul, sqWord  # noqa: E402

# The four class-two rows, each with the pair of abelian columns it is the wedge of.
# `de` is wave 61's committed `blockRead`; `cd` is this lane's second reading.
ROWS = {
    "f": ("a", "b"),
    "g": ("b", "c"),
    "h": ("c", "d"),
    "i": ("d", "e"),
}

# The two readings the brief is about, by the name of their column pair.
FIRST = "i"    # blockRead   = s.d * x.e - s.e * x.d,  the (4,6) row
SECOND = "h"   # blockReadCD = s.c * x.d - s.d * x.c,  the (3,5) row

ROW_ENTRY = {"f": "(1,3)", "g": "(2,4)", "h": "(3,5)", "i": "(4,6)"}
COL_ENTRY = {"a": "(1,2)", "b": "(2,3)", "c": "(3,4)", "d": "(4,5)", "e": "(5,6)"}


def wedge(p, q, row):
    """The `row`-reading of the ordered pair `(p, q)`, mod `8`.

    For `row = "i"` this is exactly `blocklib.block_read`; for `row = "h"` it is the second
    block reading `s_34 x_45 - s_45 x_34`.
    """
    lo, hi = ROWS[row]
    return (p.co[lo] * q.co[hi] - p.co[hi] * q.co[lo]) % M


def wedge_par(p, q, row):
    return wedge(p, q, row) % 2


def block_read_cd(s, x):
    """The second block reading, spelled out: `s_34 * x_45 - s_45 * x_34`."""
    return (s.c * x.d - s.d * x.c) % M


def handle_block(mark, row):
    """The handle block's `row` coordinate, mod `8`, computed honestly."""
    return handle_word(mark["us"], mark["vs"]).co[row] % M


def minor_sum(mark, row):
    """The sum of the handles' `row`-wedges: the right side of the symplectic identity."""
    return sum(wedge(u, v, row) for u, v in zip(mark["us"], mark["vs"])) % M


# --------------------------------------------------------------------------------------
# Markings as homomorphisms.
#
# `sqU6Hom` turns a relator-killing marking into a continuous homomorphism `D_sq h -> U_6(Z/8)`
# sending the i-th generator to the i-th slot, so a marking IS a homomorphism and the generator
# images are the slots.  The generator order is the campaign's: 0 = sigma, 1 = x0, 2 = x1, then
# u_0, v_0, u_1, v_1, ...  (`sqHandleIdxU j = 3 + 2j`, `sqHandleIdxV j = 4 + 2j`).


def gens(mark):
    """The images of the generators of `D_sq h`, in the campaign's index order."""
    out = [mark["s"], mark["x"], mark["y"]]
    for u, v in zip(mark["us"], mark["vs"]):
        out.append(u)
        out.append(v)
    return out


def gen_names(mark):
    out = ["sigma", "x0", "x1"]
    for j in range(mark["h"]):
        out.append(f"u{j}")
        out.append(f"v{j}")
    return out


def word_image(mark, exps):
    """The image of a word in the generators, given exponents (an integer per generator)."""
    g = U6()
    for p, n in zip(gens(mark), exps):
        if n >= 0:
            for _ in range(n):
                g = rmul(g, p)
        else:
            pi = rinv(p)
            for _ in range(-n):
                g = rmul(g, pi)
    return g


def live_pairs(mark, row):
    """Every ordered generator pair on which the `row`-form is odd."""
    gs, ns = gens(mark), gen_names(mark)
    return [(ns[a], ns[b]) for a in range(len(gs)) for b in range(len(gs))
            if wedge_par(gs[a], gs[b], row) == 1]


def form_is_live(mark, row):
    """Is the `row`-form odd on SOME pair of group elements?

    The form is bi-additive and kills commutators, so it is determined by its values on
    generator pairs; it is live on the group exactly when it is live on one of those.
    """
    gs = gens(mark)
    for a in range(len(gs)):
        for b in range(a + 1, len(gs)):
            if wedge_par(gs[a], gs[b], row) == 1:
                return True
    return False


def core_par(mark, row):
    """The `row`-form on the core pair `(sigma, x0)`, mod `2`."""
    return wedge_par(mark["s"], mark["x"], row)


# --------------------------------------------------------------------------------------
# Collecting relator-killing markings, honestly: random letters first, then the layered solve.


def collect(rng, h, want, tries=400, slot=None, x0=None, letters=None):
    """`want` relator-killing markings at handle count `h`, or as many as `tries` allows.

    Every marking is verified by recomputing `sqRelWord` from the letters, so nothing here
    depends on the solve being correct.
    """
    out = []
    for _ in range(tries):
        if len(out) >= want:
            break
        if letters is not None:
            us, vs = [U6(dict(u.co)) for u in letters[0]], [U6(dict(v.co)) for v in letters[1]]
        else:
            us = [rand(rng) for _ in range(h)]
            vs = [rand(rng) for _ in range(h)]
        hw = handle_word(us, vs)
        s = rand(rng) if slot is None else U6(dict(slot.co))
        x = rand(rng) if x0 is None else U6(dict(x0.co))
        y, _bad = solve_x1(s, x, rinv(hw), rng)
        if y is None:
            continue
        mark = dict(s=s, x=x, y=y, us=us, vs=vs, h=h)
        if is_one(rel_of(mark)):
            out.append(mark)
    return out


def show(p):
    """A `U_6` element in the campaign's angle-bracket notation."""
    body = ", ".join(f"{k}={p.co[k] % M}" for k in NAMES if p.co[k] % M)
    return "<" + body + ">" if body else "<1>"


def tuple15(p):
    return "⟨" + ", ".join(str(p.co[k] % M) for k in NAMES) + "⟩"
