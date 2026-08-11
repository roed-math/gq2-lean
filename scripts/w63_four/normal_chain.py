"""W63-FOUR, step 2: the chain sharpened by NORMALITY, which is what makes the four reachable.

`chain_bound.py` measures the chain a Lean file gets from `Subgroup.commutator_le` alone, with
`K0` a filtered congruence subgroup containing the letters: it loses a factor of `8` at gap-1
and `4` at gap-2 and no separating character survives.  The loss is entirely in `K0`: the
letters' higher levels are correlated with their class-one rows and a graded `K0` forgets that.

There is a standard way not to name `K0` at all.  If `K` is a NORMAL subgroup then

    C(K, A) = {g : for every a in A, [a, g] in K}

is a subgroup (because `[a, gh] = [a, h] * [a, g]^h`), so `[A, closure S] <= K` follows from the
generators `S` alone; and symmetrically on the left.  Applied twice this replaces the chain by

    K1 := a normal subgroup containing the 25 letter commutators [s, t]
    K2 := a normal subgroup of gamma_3 containing [p, s] for p in K1 and s a letter

and `forceLcs H 2 <= K2`.  `K1` still has to be named, but it lives inside `gamma_2`, where the
letters contribute nothing but their commutators, so the graded loss is far smaller.

This script measures three bounds at each of the four markings and asks, for each, whether a
separating character of the shift image survives:

  * `NORMAL-G`   : `K1`, `K2` graded and normal in the whole carrier (the cheapest Lean lemma);
  * `NORMAL-H`   : `K1`, `K2` graded and normalised by the image only (needs the normaliser
                   refinement of the same lemma);
  * `EXACT`      : `gamma_3(H)` itself, the wave-61 lattice, which is the ceiling.
"""

import fourlib as F


def separating(d):
    B = F.image_span(d["mats"], d["Av"])
    return B, [c for c in F.characters(B) if c[5] % 8]


def survives(d, sep, K2):
    """Which separating characters kill the bound `K2` on every slot."""
    out = []
    for c in sep:
        lam = [tuple(F.dot(c, d["mats"][i][s]) for s in range(6)) for i in range(len(d["mats"]))]
        if all(F.dot(lam[i], v) == 0 for i in range(len(lam)) for v in K2):
            out.append((c, lam))
    return out


def bound(m, conj):
    """`K1` and `K2` of the normal chain, with conjugation by `conj`."""
    T2 = [F.M.commP(s, t) for s in m for t in m]
    V1 = F.graded_hull(T2, conj)
    K1gens = F.hull_gens(V1)
    K2 = F.comm_span(K1gens, list(m), conj)
    return V1, K1gens, K2


def report(name, m):
    print("== %s" % name)
    print("   letters: %s" % " | ".join(F.M.show(g) for g in m))
    d = F.marking_data(m)
    B, sep = separating(d)
    print("   |forceLcs H 2| %d   |B| %d   separating characters %d"
          % (len(d["Av"]), F.MD.card(B, 6), len(sep)))

    for tag, conj in (("NORMAL-G", F.UNITS), ("NORMAL-H", list(m))):
        V1, _, K2 = bound(m, conj)
        lv = " ".join("L%d:%d" % (r + 2, F.MD.card(V1[r + 1], F.LEVDIM[r + 1]))
                      for r in range(4))
        ok = survives(d, sep, K2)
        print("   %-9s |K1| levels %s   |K2| %d   surviving characters %d"
              % (tag, lv, F.MD.card(K2, 6), len(ok)))
        for (c, lam) in ok[:3]:
            print("      psi = %-22s  pullbacks %s"
                  % (F.show_char(c), " | ".join(F.show_char(v) for v in lam)))

    okE = survives(d, sep, d["Abasis"])
    print("   %-9s |K2| %d   surviving characters %d" % ("EXACT", len(d["Av"]), len(okE)))
    print()


if __name__ == "__main__":
    for (nm, mm) in F.FOUR:
        report(nm, mm)
