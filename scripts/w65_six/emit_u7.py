"""W65-SIX: emit the Lean coordinate law of `SqU7 = U_7` from honest matrix arithmetic.

Nothing here is hand-transcribed: the multiplication comes from `mmul` and the inverse from
back substitution (`minv`), both in `u7lib`, whose `n = 6` instance is certified against the
committed `SqU6` law in `derive_six.py` section 1.  So the emitted Lean is a printout of the
same arithmetic the campaign already trusts, one index wider.
"""

import sys

sys.path.insert(0, "/Users/roed/claude/cla/worktrees/w65-six/scripts/w65_six")

from u7lib import PolyRing, cells, eye, minv, mmul, p_var

N = 7

# Field name for each cell, in class order: e12 e23 ... e67, e13 ... e57, ..., e17.
FIELD = {(r, c): f"e{r + 1}{c + 1}" for (r, c) in cells(N)}
ORDER = cells(N)


def sym(prefix):
    a = eye(N, PolyRing)
    for rc in ORDER:
        a[rc[0]][rc[1]] = p_var(f"{prefix}.{FIELD[rc]}")
    return a


def lean_poly(p):
    """Render a `PolyRing` element as Lean source, in class-then-lex monomial order."""
    if not p:
        return "0"
    terms = sorted(p.items(), key=lambda kv: (len(kv[0]), kv[0]))
    out = []
    for mono, coeff in terms:
        body = " * ".join(mono) if mono else "1"
        neg = coeff < 0
        a = abs(coeff)
        if mono and a == 1:
            core = body
        elif not mono:
            core = str(a)
        else:
            core = f"{a} * {body}"
        if not out:
            out.append(f"-({core})" if neg else core)
        else:
            out.append(("- " if neg else "+ ") + (f"({core})" if neg and " " in core else core))
    return " ".join(out)


def main():
    P, Q = sym("p"), sym("q")
    prod = mmul(P, Q, PolyRing)
    invm = minv(P, PolyRing)

    print("-- ==== MUL ====")
    for rc in ORDER:
        f = FIELD[rc]
        print(f"MUL {f} :: {lean_poly(prod[rc[0]][rc[1]])}")
    print()
    print("-- ==== INV ====")
    for rc in ORDER:
        f = FIELD[rc]
        print(f"INV {f} :: {lean_poly(invm[rc[0]][rc[1]])}")
    print()
    print("-- ==== SIZES ====")
    for rc in ORDER:
        print(f"  {FIELD[rc]}: mul {len(prod[rc[0]][rc[1]])} monomials, "
              f"inv {len(invm[rc[0]][rc[1]])} monomials")


if __name__ == "__main__":
    main()
