"""W60-SHARP5: the five slot-column conditions, EXHAUSTIVELY.

Which of the five abelian columns, required even at every slot of a marking, forces which of
the two class-four coordinates of every achievable class-four dressing even?

Modulo `2` the whole question depends only on the `F_2`-span `Q` of the letters' abelian
columns, because `pair2`, `pair3` and `pair4` are bilinear and reduction is a ring map.  So
the sweep is EXHAUSTIVE rather than sampled: it runs over every `F_2`-subspace of the
hyperplane `{x_idx = 0}` of `F_2^5`, enumerated by closing the zero subspace under adjoining
one nonzero vector at a time until nothing new appears.  There are `67` subspaces of each
hyperplane and `374` of `F_2^5`.

The output is the table in the file docstring of `GQ2/Dyadic/SqCore/GradedFiveNecessity.lean`;
the `c`-row is `GradedFiveForce.forceLcs_three_le_forceN4` and the `e`-row is
`GradedFiveNecessity.forceLcs_three_le_fiveEvenN`, both theorems.  The other three rows are
this computation and nothing else.

BRACKET CONVENTION.  [NONE]
This script computes no commutators, so the convention does not arise.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

import itertools

OUT = []


def say(s=""):
    print(s)
    OUT.append(s)


def f2span(vecs, dim):
    seen = {tuple([0] * dim)}
    frontier = [tuple([0] * dim)]
    gens = [v for v in vecs if any(v)]
    while frontier:
        nxt = []
        for p in frontier:
            for g in gens:
                q = tuple((p[k] + g[k]) % 2 for k in range(dim))
                if q not in seen:
                    seen.add(q)
                    nxt.append(q)
        frontier = nxt
    return seen


def p2(p, q):
    return ((p[0] * q[1] + p[1] * q[0]) % 2, (p[1] * q[2] + p[2] * q[1]) % 2,
            (p[2] * q[3] + p[3] * q[2]) % 2, (p[3] * q[4] + p[4] * q[3]) % 2)


def p3(w, v):
    return ((w[1] * v[0] + w[0] * v[2]) % 2, (w[2] * v[1] + w[1] * v[3]) % 2,
            (w[3] * v[2] + w[2] * v[4]) % 2)


def p4(z, v):
    return ((z[0] * v[3] + z[1] * v[0]) % 2, (z[1] * v[4] + z[2] * v[1]) % 2)


def lam4(Q):
    L2 = f2span([p2(p, q) for p in Q for q in Q], 4)
    L3 = f2span([p3(w, v) for w in L2 for v in Q], 3)
    return f2span([p4(z, v) for z in L3 for v in Q], 2)


def subspaces(dim, restrict=None):
    """Every `F_2`-subspace of `F_2^dim`, as a frozenset of its elements."""
    vecs = [v for v in itertools.product([0, 1], repeat=dim)
            if any(v) and (restrict is None or v[restrict] == 0)]
    out = {frozenset([tuple([0] * dim)])}
    frontier = list(out)
    while frontier:
        nxt = []
        for S in frontier:
            for v in vecs:
                if v in S:
                    continue
                T = frozenset(f2span(list(S) + [v], dim))
                if T not in out:
                    out.add(T)
                    nxt.append(T)
        frontier = nxt
    return out


if __name__ == "__main__":
    say("== the five slot-column conditions, over EVERY abelian parity subspace ==")
    say()
    say("  every slot even in     x_{15} always even   x_{26} always even   subspaces swept")
    names = ["a = x_{12}", "b = x_{23}", "c = x_{34}", "d = x_{45}", "e = x_{56}"]
    rows = []
    for idx in range(5):
        subs = subspaces(5, restrict=idx)
        modd = nodd = 0
        for Q in subs:
            L4 = lam4(sorted(Q))
            if any(mm for (mm, _) in L4):
                modd += 1
            if any(nn for (_, nn) in L4):
                nodd += 1
        rows.append((names[idx], modd == 0, nodd == 0, len(subs)))
        say("  %-20s %-20s %-20s %d"
            % (names[idx], modd == 0, nodd == 0, len(subs)))
    say()
    say("  (the c-row is GradedFiveForce.forceLcs_three_le_forceN4, a theorem;")
    say("   the e-row is GradedFiveNecessity.forceLcs_three_le_fiveEvenN, a theorem;")
    say("   the a-, b- and d-rows are this computation.)")
    say()
    allsub = subspaces(5)
    both = sum(1 for Q in subspaces(5)
               if not any(mm for (mm, _) in lam4(sorted(Q)))
               and not any(nn for (_, nn) in lam4(sorted(Q))))
    say("  with NO column condition: %d subspaces of F_2^5 in all, %d of which force both"
        % (len(allsub), both))
    want = [("a = x_{12}", True, False), ("b = x_{23}", True, True),
            ("c = x_{34}", True, True), ("d = x_{45}", True, True),
            ("e = x_{56}", False, True)]
    got = [(r[0], r[1], r[2]) for r in rows]
    say()
    say("  [%s] the table is exactly the one the Lean docstring carries"
        % ("PASS" if got == want else "FAIL"))
    with open("results/column_table.txt", "w") as fh:
        fh.write("\n".join(OUT) + "\n")
