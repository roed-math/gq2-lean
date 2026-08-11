"""W62-SEPARATE: is the achievability the four gap markings consume a MOD-2 LINEAR condition?

`diagnose.py` shows no per-coordinate evenness condition that holds on the achievable lattice
forces "central shift => even class-five row" at the four.  The next-coarsest Lean-provable
shape is a mod-2 LINEAR condition: the dressing's `(j, k, l, m, n, o)` reduced mod 2 lies in a
fixed subspace of `F_2^6`.  Any such condition defines a subgroup of `gamma_3` (gamma_3
elements multiply coordinatewise), so a two-step commutator chain could deliver it.

This script computes, at each gap marking:
  * the mod-2 image `V2` of the achievable lattice and the functionals killing it;
  * whether restricting the tuple lattice to `{v : v mod 2 in V2}` forces the implication;
  * the same for the mod-4 image, the next shape up.
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w61_sharp4"))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w60_stage4"))

import sharp4lib as L                                                  # noqa: E402
import modlib as MD                                                    # noqa: E402
import u6mat as M                                                      # noqa: E402

COORD = "jklmno"


def f2_span(vecs):
    """Row-reduce mod 2; returns the reduced basis."""
    rows = [list(v) for v in vecs]
    basis = []
    for r in rows:
        r = [x % 2 for x in r]
        for b in basis:
            p = next(i for i in range(6) if b[i])
            if r[p]:
                r = [(r[i] + b[i]) % 2 for i in range(6)]
        if any(r):
            basis.append(r)
            basis.sort(key=lambda b: next(i for i in range(6) if b[i]))
    return basis


def f2_dual(basis):
    """All functionals on F_2^6 killing the span."""
    out = []
    for mask in range(1, 64):
        c = [(mask >> i) & 1 for i in range(6)]
        if all(sum(c[i] * b[i] for i in range(6)) % 2 == 0 for b in basis):
            out.append(tuple(c))
    return out


def lattice_of_congruence(basis2, mod=2):
    """Generators of `{v in (Z/8)^6 : v mod `mod` in the span of basis2}`."""
    gens = [tuple(mod if s == t else 0 for s in range(6)) for t in range(6)]
    gens += [tuple(x % 8 for x in b) for b in basis2]
    return MD.howell(gens, 6)


def implication_holds(m, lat):
    """With every slot's dressing drawn from the lattice `lat`, does a central shift force an
    even class-five row?"""
    rows = []
    for i in range(len(m)):
        mat = L.slot_matrix(m, i)
        for g in lat:
            rows.append(L.apply_matrix(mat, g))
    d = len(rows)
    aug = [tuple(list(rows[t][:5]) + [1 if s == t else 0 for s in range(d)]) for t in range(d)]
    basis = MD.howell(aug, 5 + d)
    for r in MD.sub_zero_prefix(basis, 5):
        v = r[5:]
        if sum(v[t] * rows[t][5] for t in range(d)) % 2:
            return False
    return True


def report(name, m):
    print("== %s" % name)
    B = L.gamma3_basis(m)
    b2 = f2_span(B)
    print("   mod-2 image of the achievable lattice: dim %d, basis %s" % (len(b2), b2))
    duals = f2_dual(b2)
    print("   functionals killing it: %s"
          % ["+".join(COORD[i] for i in range(6) if c[i]) for c in duals])
    lat2 = lattice_of_congruence(b2, 2)
    print("   implication under the mod-2 condition alone: %s" % implication_holds(m, lat2))
    b4 = MD.howell([tuple(x % 8 for x in g) for g in B] + [(0,) * 6], 6)
    gens4 = MD.howell([tuple(4 if s == t else 0 for s in range(6)) for t in range(6)]
                      + [tuple(x % 8 for x in g) for g in B], 6)
    print("   |lattice + 4Z^6| %d vs |achievable| %d" % (MD.card(gens4, 6), MD.card(b4, 6)))
    print("   implication under the mod-4 condition alone: %s" % implication_holds(m, gens4))
    print("   implication on the honest achievable lattice: %s" % implication_holds(m, B))
    print()


if __name__ == "__main__":
    from inspect_four import FOUR
    for (name, m) in FOUR:
        report(name, m)
