"""W60-STAGE4: `gamma_3` of an image subgroup as a Z/8-module, and the single-slot kill test.

Two things this file provides, both validated in `sanity_mod.py` against `pointlib`'s honest
element-by-element closure at the wave-59 point:

* `gamma3_module(letters)`: a Howell basis of `gamma_3(im)` inside `(Z/8)^6`, and
  `gaFourShaped(...)`: the submodule of `gamma_4`-SHAPED members, i.e. the object the wave-59
  hole is about;
* `slot_increment(...)`: the exact motion of the relator when one slot is dressed by a
  `gamma_4`-shaped element, read off honestly (not from a transcribed formula) by evaluating
  the relator, so no derivation is trusted here.
"""
import sys
import os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))

import u6mat as M                                             # noqa: E402
import modlib as MD                                           # noqa: E402

G3IDX = [9, 10, 11, 12, 13, 14]                               # j, k, l, m, n, o


def vec(z):
    """The (j,k,l,m,n,o)-vector of a gamma_3-shaped carrier element."""
    return tuple(z[k] % 8 for k in G3IDX)


def elt(v):
    """…and back."""
    t = [0] * 15
    for i, k in enumerate(G3IDX):
        t[k] = v[i] % 8
    return tuple(t)


def gamma3_gens(letters):
    """Generators of gamma_3(im) as a Z/8-module of (Z/8)^6."""
    t3 = {M.commP(M.commP(a, b), c) for a in letters for b in letters for c in letters}
    t4 = {M.commP(z, c) for z in t3 for c in letters}
    t5 = {M.commP(z, c) for z in t4 for c in letters}
    gens = t3 | t4 | t5
    assert all(all(z[k] == 0 for k in range(9)) for z in gens), "not gamma_3-shaped"
    return [vec(z) for z in gens]


def gamma3_module(letters):
    return MD.howell(gamma3_gens(letters), 6)


def gamma4_gens(letters):
    t3 = {M.commP(M.commP(a, b), c) for a in letters for b in letters for c in letters}
    t4 = {M.commP(z, c) for z in t3 for c in letters}
    t5 = {M.commP(z, c) for z in t4 for c in letters}
    return [vec(z) for z in (t4 | t5)]


def gamma4_module(letters):
    return MD.howell(gamma4_gens(letters), 6)


def ga4_shaped_basis(basis):
    """A basis of the gamma_4-SHAPED submodule: first three coordinates (j,k,l) zero."""
    return MD.sub_zero_prefix(basis, 3)


def ga4_shaped_elements(basis):
    rows = [(r[3], r[4], r[5]) for r in ga4_shaped_basis(basis)]
    return MD.members(MD.howell(rows, 3), 3) if rows else {(0, 0, 0)}


def mn_parities(basis):
    """Which (m, n) parity classes occur among the gamma_4-shaped members."""
    return {(z[0] % 2, z[1] % 2) for z in ga4_shaped_elements(basis)}
