#!/usr/bin/env python3
"""emit_lean.py.

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

"""emit_lean.py.
"""

"""emit_lean.py.
"""

"""emit_lean.py.
"""

"""emit_lean.py.
"""

"""W58-FIVE step 2: emit Lean-ready bodies for the SqU6 closed forms.

Every polynomial that goes into GQ2/Dyadic/SqCore/GradedFive.lean is printed here,
so no fifteen-coordinate closed form is transcribed by hand.  Coordinate names and
conventions are those of derive_u6.py.
"""
import sympy as sp

NAMES = "abcdefghijklmno"
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


def render(ex, pref_map, wrap=96, indent="    "):
    """Lean text for a polynomial, wrapped at `wrap` columns."""
    terms = sp.expand(ex).as_ordered_terms()
    if not terms:
        return "0"
    chunks = []
    for t in terms:
        s = str(t)
        for src, dst in pref_map:
            for n in NAMES:
                s = s.replace(f"{src}{n}", f"{dst}.{n}")
        s = s.replace("**", "^")
        if s.startswith("-"):
            chunks.append(("-", s[1:]))
        else:
            chunks.append(("+", s))
    out = []
    line = chunks[0][1] if chunks[0][0] == "+" else "-(" + chunks[0][1] + ")"
    for sign, body in chunks[1:]:
        piece = f" {sign} {body}"
        if len(line) + len(piece) > wrap:
            out.append(line)
            line = indent + piece.lstrip()
            if line.lstrip().startswith("+"):
                line = indent + piece.strip()
        else:
            line += piece
    out.append(line)
    # re-glue: continuation lines must start with the operator
    res = []
    for idx, ln in enumerate(out):
        res.append(ln)
    return "\n".join(res)


def render_wrapped(ex, pref_map, indent="    ", wrap=94):
    terms = sp.expand(ex).as_ordered_terms()
    parts = []
    for t in terms:
        s = str(t)
        for src, dst in pref_map:
            for n in NAMES:
                s = s.replace(f"{src}{n}", f"{dst}.{n}")
        s = s.replace("**", "^")
        if s.startswith("-"):
            parts.append("- " + s[1:])
        else:
            parts.append("+ " + s)
    # first term: drop a leading '+'
    if parts[0].startswith("+ "):
        parts[0] = parts[0][2:]
    else:
        parts[0] = "-" + parts[0][2:]
    lines, cur = [], indent
    for p in parts:
        add = (p if cur.strip() == "" else " " + p)
        if len(cur) + len(add) > wrap and cur.strip():
            lines.append(cur)
            cur = indent + "  " + p
        else:
            cur += add
    lines.append(cur)
    return "\n".join(lines)


def main():
    p, pv = M("p")
    q, qv = M("q")
    g, gv = M("g")
    PQ = [("p", "p"), ("q", "q")]
    PG = [("p", "p"), ("g", "g")]

    print("-- ############ mul ############")
    mc = coords(p * q)
    for n in NAMES:
        print(f"mul_{n}: {render_wrapped(mc[n], PQ)}")
    print()

    print("-- ############ inv ############")
    ic = coords(inv(p))
    for n in NAMES:
        print(f"inv_{n}:\n{render_wrapped(ic[n], PQ)}")
    print()

    print("-- ############ commP ############")
    cc = coords(commP(p, q))
    for n in NAMES:
        print(f"commP_{n}:\n{render_wrapped(cc[n], PQ)}")
    print()

    print("-- ############ conjP (conjP p g = g^-1 p g) ############")
    jc = coords(conjP(p, g))
    for n in NAMES:
        body = sp.expand(jc[n] - pv[n])
        print(f"conjP_{n}: p.{n} +\n{render_wrapped(body, PG)}")
    print()

    print("-- ############ power laws ############")
    pows = [sp.eye(6)]
    for _ in range(8):
        pows.append(sp.expand(pows[-1] * p))
    for nm in NAMES:
        vals = [sp.expand(pows[k][POS[nm]]) for k in range(8)]
        rem = list(vals)
        Ps = {}
        for d in range(1, 6):
            Pd = sp.expand(rem[d])
            Ps[d] = Pd
            for k in range(8):
                rem[k] = sp.expand(rem[k] - sp.binomial(k, d) * Pd)
        assert all(r == 0 for r in rem), (nm, rem)
        segs = []
        for d in range(1, 6):
            if Ps[d] != 0:
                body = render_wrapped(Ps[d], [("p", "p")], indent="", wrap=200).strip()
                segs.append(f"C(n,{d}) * ({body})")
        print(f"pow_{nm}: " + " + ".join(segs))
    print()

    print("-- ############ gamma-2 cross terms (P,Q with abelian coords 0) ############")
    def ga(pref):
        v = {n: sp.Symbol(f"{pref}{n}") for n in NAMES}
        for n in "abcde":
            v[n] = 0
        return mat(v), v
    P2, P2v = ga("p")
    Q2, Q2v = ga("q")
    c2 = coords(P2 * Q2)
    for nm in NAMES:
        d = sp.expand(c2[nm] - P2v[nm] - Q2v[nm])
        print(f"  gaTwo mul_{nm} extra: {render_wrapped(d, PQ, indent='', wrap=200).strip()}")
    print()

    print("-- ############ sqWord rows a..e and the f,j response rows ############")
    s, sv = M("s")
    x, xv = M("x")
    y, yv = M("y")
    w = inv(conjP(x, s)) * inv(x * x * x) * (y * y) * commP(y, conjP(y, s))
    wc = coords(w)
    SXY = [("s", "s"), ("x", "x"), ("y", "y")]
    for nm in "abcde":
        print(f"sqWord_{nm}: {render_wrapped(wc[nm], SXY, indent='', wrap=200).strip()}")
    for nm in "fghij":
        body = sp.expand(wc[nm] - (-4 * xv[nm] + 2 * yv[nm]))
        print(f"sqWord_{nm} - (-4*x.{nm} + 2*y.{nm}):\n{render_wrapped(body, SXY)}")
    print()

    print("-- ############ sigma response of the f- and j-rows of the core word ############")
    v6, vv = M("v")
    wd = inv(conjP(x, s * v6)) * inv(x * x * x) * (y * y) * commP(y, conjP(y, s * v6))
    wdc = coords(wd)
    SXYV = [("s", "s"), ("x", "x"), ("y", "y"), ("v", "v")]
    for nm in "afj":
        d = sp.expand(wdc[nm] - wc[nm])
        print(f"delta core .{nm} = {render_wrapped(d, SXYV, indent='', wrap=200).strip()}")
        # under the b-column gauge x.b = y.b = v.b = 0
        sub = {xv["b"]: 0, yv["b"]: 0, vv["b"]: 0}
        print(f"   under x.b=y.b=v.b=0: "
              f"{render_wrapped(sp.expand(d.subs(sub)), SXYV, indent='', wrap=200).strip()}")
    print()


if __name__ == "__main__":
    main()
