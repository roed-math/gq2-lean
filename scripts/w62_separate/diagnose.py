"""W62-SEPARATE: what exactly does the central half of the sharp line CONSUME at a marking?

`inspect_four.py` shows the wave-61 gap markings are real, but that `orth_central_unrestricted`
is FALSE at all four: some `gamma_3`-tuple that is not achievable acts centrally with an odd
class-five row.  So a Lean proof of `StageCentral` there has to consume achievability.  This
script measures HOW MUCH: for each of the 32 congruence conditions "coordinate c of every
dressing slot is even", it asks whether restricting the tuple lattice to that condition makes
"central shift => even class-five row" TRUE.  A condition that works and that holds on the
achievable lattice is a candidate for a Lean-provable subgroup.
"""

import itertools
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


def slot_matrices(m):
    return [L.slot_matrix(m, i) for i in range(len(m))]


def print_matrices(m):
    for i in range(len(m)):
        mat = L.slot_matrix(m, i)
        print("   slot %-6s" % L.SLOT[i])
        for s in range(6):
            print("      d%s -> %s" % (COORD[s], mat[s]))


def central_odd_witness(m, even_set):
    """A gamma_3-tuple, with the named coordinates forced even at every slot, whose shift is
    central and whose class-five row is odd.  `None` if the implication holds."""
    rows = L.total_matrix(m)                       # 6 * nslots rows, indexed (slot, coord)
    d = len(rows)
    # generators of the restricted tuple lattice: e_t for a free coordinate, 2 e_t otherwise
    gens = []
    for t in range(d):
        c = t % 6
        scale = 2 if c in even_set else 1
        gens.append(tuple(scale if s == t else 0 for s in range(d)))
    # kernel of the five class-<=four rows inside that lattice
    aug = [tuple([sum(g[t] * rows[t][k] for t in range(d)) % 8 for k in range(5)] + list(g))
           for g in gens]
    basis = MD.howell(aug, 5 + d)
    for r in MD.sub_zero_prefix(basis, 5):
        v = r[5:]
        if sum(v[t] * rows[t][5] for t in range(d)) % 2:
            return v
    return None


def lattice_even(basis, c):
    """Is coordinate `c` even on the whole achievable lattice?"""
    return all(r[c] % 2 == 0 for r in basis)


def report(name, m):
    print("== %s" % name)
    print("   letters: %s" % " | ".join(M.show(g) for g in m))
    B = L.gamma3_basis(m)
    even_on_lattice = {c for c in range(6) if lattice_even(B, c)}
    print("   achievable lattice: even coordinates %s"
          % "".join(COORD[c] for c in sorted(even_on_lattice)))
    print_matrices(m)
    w = central_odd_witness(m, set())
    print("   unrestricted central-odd witness: %s" % (w,))
    if w is not None:
        for i in range(len(m)):
            part = w[6 * i:6 * i + 6]
            if any(part):
                print("      slot %-6s %s" % (L.SLOT[i], part))
    good = []
    for r in range(1, 7):
        for sub in itertools.combinations(range(6), r):
            if central_odd_witness(m, set(sub)) is None:
                good.append(sub)
    minimal = [s for s in good if not any(set(t) < set(s) for t in good)]
    print("   MINIMAL even-coordinate conditions that force the implication:")
    for s in minimal:
        holds = set(s) <= even_on_lattice
        print("      %-6s  holds on the achievable lattice: %s"
              % ("".join(COORD[c] for c in s), holds))
    print()


if __name__ == "__main__":
    from inspect_four import FOUR
    for (name, m) in FOUR:
        report(name, m)
