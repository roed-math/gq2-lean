#!/usr/bin/env python3
"""W58-FIVE step 1: derive the SqU6 (= U_6) closed forms symbolically over Z.

U6(R) is carried on the fifteen strictly-upper coordinates of a 6x6 unitriangular
matrix, named so that the class filtration reads off the letters:

    a=(1,2) b=(2,3) c=(3,4) d=(4,5) e=(5,6)      -- abelian
    f=(1,3) g=(2,4) h=(3,5) i=(4,6)              -- class two
    j=(1,4) k=(2,5) l=(3,6)                      -- class three
    m=(1,5) n=(2,6)                              -- class four
    o=(1,6)                                      -- class five

Repo conventions: conjP x g = g^-1 x g, commP x y = x^-1 y^-1 x y,
sqWord s x y = (conjP x s)^-1 * (x^3)^-1 * y^2 * commP y (conjP y s).

Everything below is exact integer polynomial arithmetic (sympy over ZZ); the numeric
cross-check against honest group collection lives in validate_u6.py.
"""
import sys
import sympy as sp

NAMES = "abcdefghijklmno"

# position of each coordinate in the 6x6 matrix (0-indexed)
POS = dict(a=(0, 1), b=(1, 2), c=(2, 3), d=(3, 4), e=(4, 5),
           f=(0, 2), g=(1, 3), h=(2, 4), i=(3, 5),
           j=(0, 3), k=(1, 4), l=(2, 5),
           m=(0, 4), n=(1, 5),
           o=(0, 5))


def mat(vals):
    M = sp.eye(6)
    for nm, (r, c) in POS.items():
        M[r, c] = vals[nm]
    return M


def M(pref):
    v = {n: sp.Symbol(f"{pref}{n}") for n in NAMES}
    return mat(v), v


def coords(m):
    return {n: sp.expand(m[POS[n]]) for n in NAMES}


inv = lambda m: m.inv()
conjP = lambda p, g: inv(g) * p * g
commP = lambda p, q: inv(p) * inv(q) * p * q


def lean(ex, pref_map=None):
    """Render a sympy polynomial as a Lean term, with x.a style field accesses."""
    s = str(sp.expand(ex))
    if pref_map:
        for src, dst in pref_map:
            for n in NAMES:
                s = s.replace(f"{src}{n}", f"{dst}.{n}")
    return s


def show(title, m, pref_map=None, only=None):
    print(f"== {title}")
    cs = coords(m)
    for n in NAMES:
        if only and n not in only:
            continue
        ex = sp.expand(cs[n])
        print(f"  .{n} = {lean(ex, pref_map)}    [{len(ex.as_ordered_terms())} terms]")
    print()


def main():
    x, xv = M("x")
    y, yv = M("y")

    PM = [("x", "p"), ("y", "q")]

    print("### 1. multiplication")
    show("(x*y)", x * y, PM)

    print("### 2. inverse")
    show("x^-1", inv(x), [("x", "p")])

    print("### 3. commutator  commP x y = x^-1 y^-1 x y")
    show("commP x y", commP(x, y), PM)

    print("### 4. conjugation  conjP x s = s^-1 x s")
    s, sv = M("s")
    show("conjP x s", conjP(x, s), [("x", "p"), ("s", "g")])

    print("### 5. power law: check g^n coefficients against binomials")
    n = sp.Symbol("n", integer=True, nonnegative=True)
    # symbolic guess: for each coordinate, express (x^k).coord for k = 0..7 and fit
    pows = [sp.eye(6)]
    for _ in range(8):
        pows.append(sp.expand(pows[-1] * x))
    binom = {d: sp.binomial(n, d) for d in range(1, 6)}
    # basis monomials per coordinate, in filtration order
    for nm in NAMES:
        vals = [sp.expand(pows[k][POS[nm]]) for k in range(8)]
        # collect: assume  (x^k).nm = sum_d C(k,d) * P_d  with P_d independent of k
        # solve greedily: P_1 = x.nm ; then subtract and divide by C(k,2) etc.
        rem = list(vals)
        Ps = {}
        for d in range(1, 6):
            # value at k = d determines P_d (all lower layers already subtracted)
            Pd = sp.expand(rem[d])
            Ps[d] = Pd
            for k in range(8):
                rem[k] = sp.expand(rem[k] - sp.binomial(k, d) * Pd)
        assert all(r == 0 for r in rem), (nm, rem)
        parts = [f"C(n,{d})*({Ps[d]})" for d in range(1, 6) if Ps[d] != 0]
        print(f"  (p^n).{nm} = " + " + ".join(parts))
    print()

    print("### 6. the two U5-quotients")
    print("  toU5L : (a,b,c,d | f,g,h | j,k | m)   -- forget the last column")
    print("  toU5R : (b,c,d,e | g,h,i | k,l | n)   -- forget the first row")
    # verify they are homs by comparing coordinates of the product
    p, pv = M("p")
    q, qv = M("q")
    pq = coords(p * q)
    L = dict(a="a", b="b", c="c", d="d", e="f", f="g", g="h", h="j", i="k", j="m")
    R = dict(a="b", b="c", c="d", d="e", e="g", f="h", g="i", h="k", i="l", j="n")
    for nmL, tag in [(L, "toU5L"), (R, "toU5R")]:
        ok = True
        for u5c, u6c in nmL.items():
            # U5 multiplication rule in coordinate u5c, applied to the images
            def im(vv, c5):
                return vv[nmL[c5]]
            lhs = pq[u6c]
            rule = {
                "a": im(pv, "a") + im(qv, "a"),
                "b": im(pv, "b") + im(qv, "b"),
                "c": im(pv, "c") + im(qv, "c"),
                "d": im(pv, "d") + im(qv, "d"),
                "e": im(pv, "e") + im(qv, "e") + im(pv, "a") * im(qv, "b"),
                "f": im(pv, "f") + im(qv, "f") + im(pv, "b") * im(qv, "c"),
                "g": im(pv, "g") + im(qv, "g") + im(pv, "c") * im(qv, "d"),
                "h": im(pv, "h") + im(qv, "h") + im(pv, "a") * im(qv, "f")
                     + im(pv, "e") * im(qv, "c"),
                "i": im(pv, "i") + im(qv, "i") + im(pv, "b") * im(qv, "g")
                     + im(pv, "f") * im(qv, "d"),
                "j": im(pv, "j") + im(qv, "j") + im(pv, "a") * im(qv, "i")
                     + im(pv, "e") * im(qv, "g") + im(pv, "h") * im(qv, "d"),
            }[u5c]
            if sp.expand(lhs - rule) != 0:
                ok = False
                print(f"  !! {tag} fails at U5 coordinate {u5c}")
        print(f"  {tag}: hom check {'OK' if ok else 'FAILED'}")
    print()

    print("### 7. gamma_2 products are coordinatewise-additive?  (centrality analysis)")
    # elements with vanishing abelian coordinates
    def ga(pref, kill):
        v = {n: sp.Symbol(f"{pref}{n}") for n in NAMES}
        for n in kill:
            v[n] = 0
        return mat(v), v
    p2, p2v = ga("P", "abcde")
    q2, q2v = ga("Q", "abcde")
    pq2 = coords(p2 * q2)
    for nm in NAMES:
        diff = sp.expand(pq2[nm] - (p2v[nm] + q2v[nm]))
        if diff != 0:
            print(f"  gamma2: (P*Q).{nm} - (P.{nm}+Q.{nm}) = {diff}")
    print("  (blank above = coordinatewise; any line = cross-coupling inside gamma_2)")
    print()

    print("### 8. the core word sqWord s x y, rows and the class-five row")
    w = inv(conjP(x, s)) * inv(x * x * x) * (y * y) * commP(y, conjP(y, s))
    cs = coords(w)
    lin = {nm: -4 * xv[nm] + 2 * yv[nm] for nm in NAMES}
    for nm in NAMES:
        if nm in "abcde":
            print(f"  (sqWord).{nm} = {lean(cs[nm], [('s','s'),('x','x'),('y','y')])}")
        else:
            core = sp.expand(cs[nm] - lin[nm])
            print(f"  (sqWord).{nm} - (-4*x.{nm} + 2*y.{nm}) : "
                  f"{len(core.as_ordered_terms())} terms")
    print()

    print("### 9. handle block: gamma_2-ness and the top row of a two-handle product")
    u1, _ = M("U")
    v1, _ = M("V")
    u2, _ = M("W")
    v2, _ = M("Z")
    c1 = coords(commP(u1, v1))
    print("  commP is in gamma_2:",
          all(c1[nm] == 0 for nm in "abcde"))
    hw = commP(u1, v1) * commP(u2, v2)
    c2 = coords(commP(u2, v2))
    hwc = coords(hw)
    for nm in NAMES:
        cross = sp.expand(hwc[nm] - c1[nm] - c2[nm])
        if cross != 0:
            print(f"  cross-handle at .{nm}: {cross}")
    print()


if __name__ == "__main__":
    main()
