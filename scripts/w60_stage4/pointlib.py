"""W60-STAGE4 shared machinery: the layered solve for a class-five sigma-witness point, and
the two censuses that decide whether a point has the wave-59 hole.

Nothing here is transcribed from a Lean file.  The group law comes from `w59_force5/u6mat.py`
(honest 6 x 6 matrices, Gaussian back-substitution inverse), which `verify_stage4.py` section 0
re-checks against wave 58's independent coordinate library before any measurement is taken.

The objects:

* `solve_y(sigma, X, U, V, h, jj)` enumerates every `x1`-slot value `Y` for which the
  UNDRESSED frame kills the relator.  The relator's class-`c` row is affine in `Y`'s class-`c`
  coordinates with slope `2` (the `y^2` of the core word) and blind to `Y`'s deeper ones, so
  the solve cascades class by class with two lifts per coordinate and a parity gate.
* `gamma_series(letters)` computes gamma_3, gamma_4, gamma_5 of the image subgroup by honest
  closure (normal closure of the iterated commutators of the letters).
* `hole_report(...)` measures which achievable gamma_3-dressings kill the DRESSED frame, i.e.
  exactly the wave-59 scope finding, and the same at the gamma_4 level.
"""
import sys
import os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w58_sigma5"))

import u6mat as M                                             # noqa: E402

N = 8
ONE = M.ONE
COORDS = M.COORDS

# class -> the coordinate indices of that class
CLS = {c: [k for k in range(15) if M.cls(k) == c] for c in range(1, 6)}


def mirTuple(h, jj, s, x, y, u, v):
    """The one-handle-live marking tuple: (sigma, x0, x1, u_0, v_0, ...)."""
    m = [s, x, y]
    for k in range(h):
        m += [u, v] if k == jj else [ONE, ONE]
    return m


def setc(p, k, val):
    q = list(p)
    q[k] = val % N
    return tuple(q)


def solve_y(sigma, X, U, V, h=1, jj=0, limit=None):
    """Every `Y` with sqRelWord(sigma, X, Y, U, V) = 1, by the class-by-class cascade.

    The relator's class-`c` row is `(row at Y_c = 0) + 2 * Y_c`, so each coordinate is
    solvable exactly when that row is even, and then has two lifts differing by 4.
    """
    out = []
    stack = [(ONE, 1)]
    while stack:
        Y, c = stack.pop()
        if c > 5:
            out.append(Y)
            if limit is not None and len(out) >= limit:
                return out
            continue
        cand = [Y]
        for k in CLS[c]:
            nxt = []
            for Yp in cand:
                r = M.sqRelWord(mirTuple(h, jj, sigma, X, Yp, U, V))
                if r[k] % 2:
                    continue                       # this branch cannot be solved at row k
                base = (-(r[k] // 2)) % 4
                nxt.append(setc(Yp, k, base))
                nxt.append(setc(Yp, k, base + 4))
            cand = nxt
        for Yp in cand:
            stack.append((Yp, c + 1))
    return out


def solve_y_central(sigma, X, U, V, h=1, jj=0, limit=None):
    """Every `Y` for which the UNDRESSED frame kills the relator AND the `a0 = a1`-dressed
    frame is central with an ODD class-five residue: the two conditions that make a point a
    class-five sigma witness at all.

    Both relators are affine in `Y`'s class-`c` coordinates with the same slope `2`, so at each
    coordinate the two equations are compatible exactly when the two rows AGREE and are even,
    and then they have the same two lifts.  At class five the two rows must instead DIFFER by
    an odd amount, which is the residue and is independent of `Y.o`.
    """
    out = []
    stack = [(ONE, 1)]
    while stack:
        Y, c = stack.pop()
        if c == 5:
            r0 = M.sqRelWord(mirTuple(h, jj, sigma, X, Y, U, V))
            r1 = M.sqRelWord(mirTuple(h, jj, M.mul(sigma, X), X, Y, U, V))
            if r0[14] % 2 or (r1[14] - r0[14]) % 2 == 0:
                continue
            base = (-(r0[14] // 2)) % 4
            for lift in (base, base + 4):
                out.append(setc(Y, 14, lift))
                if limit is not None and len(out) >= limit:
                    return out
            continue
        cand = [Y]
        for k in CLS[c]:
            nxt = []
            for Yp in cand:
                r0 = M.sqRelWord(mirTuple(h, jj, sigma, X, Yp, U, V))
                r1 = M.sqRelWord(mirTuple(h, jj, M.mul(sigma, X), X, Yp, U, V))
                if r0[k] % 2 or r0[k] != r1[k]:
                    continue
                base = (-(r0[k] // 2)) % 4
                nxt.append(setc(Yp, k, base + 4))
                nxt.append(setc(Yp, k, base))       # LIFO: the sparser lift is explored first
            cand = nxt
        for Yp in cand:
            stack.append((Yp, c + 1))
    return out


def residue(sigma, X, Y, U, V, h=1, jj=0):
    """The relator of the `a0 = a1`-dressed frame: sigma slot multiplied by the `x0` value."""
    return M.sqRelWord(mirTuple(h, jj, M.mul(sigma, X), X, Y, U, V))


def subgroup(seeds, conj_gens):
    """The smallest conjugation-closed subgroup containing `seeds`."""
    seen = {ONE}
    gens = []
    for s in sorted({t for t in seeds if t != ONE}):
        if s in seen:
            continue
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
                for c in conj_gens:
                    q = M.conjP(p, c)
                    if q not in seen:
                        seen.add(q)
                        changed = True
    return seen


def gamma_series(letters):
    """gamma_3, gamma_4, gamma_5 of the subgroup generated by `letters`, by honest closure."""
    g3 = subgroup([M.commP(M.commP(a, b), c)
                   for a in letters for b in letters for c in letters], letters)
    g4 = subgroup([M.commP(z, g) for z in g3 for g in letters], letters)
    g5 = subgroup([M.commP(z, g) for z in g4 for g in letters], letters)
    return g3, g4, g5


def kills(base, i, z):
    """Does dressing slot `i` of the marking `base` by `z` kill the relator?"""
    m = list(base)
    m[i] = M.mul(m[i], z)
    return M.sqRelWord(m) == ONE


SLOT = ["sigma", "x0", "x1", "U", "V"]


def hole_report(sigma, X, Y, U, V, g3=None, g4=None):
    """Single-slot kill counts of the DRESSED frame at the gamma_3 and gamma_4 levels.

    Returns (counts3, counts4, examples3, sizes).  The wave-59 hole is `sum(counts3) > 0`
    with `sum(counts4) = 0`.
    """
    letters = [sigma, X, Y, U, V]
    if g3 is None:
        g3, g4, _ = gamma_series(letters)
    base = [M.mul(sigma, X), X, Y, U, V]
    c3, c4, ex = [], [], []
    for i in range(5):
        k3 = [z for z in sorted(g3) if kills(base, i, z)]
        k4 = [z for z in sorted(g4) if kills(base, i, z)]
        c3.append(len(k3))
        c4.append(len(k4))
        ex.append(k3[:3])
    return c3, c4, ex, (len(g3), len(g4))


def gaFour_shaped(S):
    """The gamma_4-shaped members of a set of carrier elements."""
    return [z for z in S if all(z[k] == 0 for k in range(12))]


def show(p):
    return M.show(p)
