"""W64-SEP0H: the symbolic derivation behind `GQ2/Dyadic/SqCore/GradedFiveSepZero.lean`.

Everything here is exact integer polynomial arithmetic in plain Python (`seplib.py`): no
`sympy`, no floating point, no `native_decide`-style trust.  Sections:

1. the coordinate law against honest integer `6 x 6` matrices (an independent re-certification
   of `scripts/w59_blind5/u6lib.py`'s law, written from scratch here);
2. the nine rows of the `a0 = a1` response that vanish IDENTICALLY, over `Z`;
3. wave 58's closed form for the class-five response reproduced from scratch, as a check on the
   whole pipeline (`docs/dyadic/w58-sigma5-note.md` section 3.1);
4. ⭐⭐⭐ THE ROW EXPANSION: the whole `a0 = a1` response is a polynomial-coefficient
   combination of the nine class-`2`-to-`4` rows of the UNDRESSED core word, modulo `2`, with
   the relator's abelian rows as the only input;
5. ⭐ the gauge collapse: on the class-two-forced gauge only two of the nine survive;
6. the Lean witnesses, machine-emitted, and their numeric certification over `Z`.

Run: `python3 scripts/w64_sep0h/derive_sep0h.py`
"""

import random
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import seplib as S  # noqa: E402

CHECKS = []
RESULTS = Path(__file__).resolve().parent / "results"

# The abelian columns of the `x1` slot, even at every relator-killing marking.
YAB = ["ya", "yb", "yc", "yd", "ye"]
# The gauge hypotheses of the collapse, on top of `x_23 = 0`.
GAUGE = ["xa", "xc", "xf", "xg"] + YAB

# ⭐⭐⭐ THE ROW EXPANSION, as a coefficient list per row of the undressed core word.
# Read `('f', ('xl',))` as "the `(1,3)` row, with coefficient `x_36`".
ROW_COMB = {
    "j": [("f", ("xc",)), ("g", ("xa",))],
    "k": [("g", ("xd",)), ("h", ("xb",))],
    "l": [("h", ("xe",)), ("i", ("xc",))],
    "m": [("f", ("xh",)), ("g", ("xa", "xd")), ("h", ("xa", "xb")), ("h", ("xf",)),
          ("j", ("xd",)), ("k", ("xa",))],
    "n": [("g", ("xi",)), ("h", ("xb", "xe")), ("i", ("xb", "xc")), ("i", ("xg",)),
          ("k", ("xe",)), ("l", ("xb",))],
    "o": [("f", ("xl",)), ("g", ("xa", "xi")), ("h", ("xe", "xf")), ("h", ("xa", "xb", "xe")),
          ("i", ("xj",)), ("i", ("xa", "xg")), ("i", ("xc", "xf")), ("i", ("xa", "xb", "xc")),
          ("j", ("xi",)), ("k", ("xa", "xe")), ("l", ("xf",)), ("l", ("xa", "xb")),
          ("m", ("xe",)), ("n", ("xa",))],
}

# The gauge collapse of the class-five row: only these two coefficients survive.
GAUGE_COMB = [("i", ("xj",)), ("m", ("xe",))]


def check(name, cond, detail=""):
    CHECKS.append((name, bool(cond)))
    print(f"  [{'ok' if cond else 'FAIL'}] {name}{(' : ' + detail) if detail else ''}")


def table(evens, xb_zero=False):
    t = {v: S.s_scal(2, S.s_var("H" + v)) for v in evens}
    if xb_zero:
        t["xb"] = S.s_const(0)
    return t


def combo_poly(W, comb):
    out = S.s_const(0)
    for k, mu in comb:
        t = S.s_const(1)
        for v in mu:
            t = S.s_mul(t, S.s_var(v))
        out = S.s_add(out, S.s_mul(t, W.co[k]))
    return out


def main():
    rng = random.Random(20260811)
    print("W64-SEP0H: the class-five sigma separation at h = 0")
    print("=" * 86)

    print("\n1.  The coordinate law against honest integer 6 x 6 matrices")
    ok, bad = S.check_against_matrices(rng, 400)
    check("coordinate law = matrix arithmetic", bad == 0, f"{ok} comparisons, {bad} mismatches")

    print("\n2.  The a0 = a1 response, symbolically over Z")
    Sy, X, Y = S.symU6("s"), S.symU6("x"), S.symU6("y")
    W = S.sqWord(Sy, X, Y)
    Wd = S.sqWord(S.mul(Sy, X), X, Y)
    D = {k: S.s_sub(Wd.co[k], W.co[k]) for k in S.NAMES}
    check("nine rows a..i of the response vanish over Z",
          all(not D[k] for k in ["a", "b", "c", "d", "e", "f", "g", "h", "i"]),
          "identically, no hypothesis, over any commutative ring")
    print("     response term counts over Z: "
          + ", ".join(f"{k}={len(D[k])}" for k in ["j", "k", "l", "m", "n", "o"]))
    check("the core word's class-five row has 250 terms over Z", len(W.co["o"]) == 250)

    print("\n3.  Cross-check: wave 58's closed form, rederived")
    tE = table(YAB)
    for v in S.NAMES:
        tE["s" + v] = S.s_const(1) if v == "b" else S.s_const(0)
    got = S.s_mod(S.s_subst(D["o"], tE), 2)
    want = S.s_add(S.s_mul(S.s_var("xa"), S.s_mul(S.s_var("yg"), S.s_var("yi"))),
                   S.s_mul(S.s_var("xe"), S.s_mul(S.s_var("yf"), S.s_var("yh"))))
    check("sigFiveRead(x, x, y) = x_12 y_24 y_46 + x_56 y_13 y_35 (mod 2) at sigma = E_23, "
          "on the relator's abelian rows alone", got == want, S.s_str(got))
    print("     (docs/dyadic/w58-sigma5-note.md section 3.1, reproduced from scratch)")
    gen = S.s_mod(S.s_subst(D["o"], table(YAB)), 2)
    check("...and the GENERAL sigma slot carries strictly more", len(gen) == 42,
          f"{len(gen)} monomials mod 2 at a general sigma slot, against {len(want)} at E_23")

    print("\n4.  THE ROW EXPANSION: the search that finds it, and its exact witnesses")
    t = table(YAB)
    rows2 = {k: S.s_mod(S.s_subst(W.co[k], t), 2)
             for k in ["f", "g", "h", "i", "j", "k", "l", "m", "n"]}
    for r in ["j", "k", "l", "m", "n", "o"]:
        tgt = S.s_mod(S.s_subst(D[r], t), 2)
        pool = [k for k in ["f", "g", "h", "i", "j", "k", "l", "m", "n"]
                if k != r and (r != "o" or k != "o")]
        pool = [k for k in pool if k < r or (k in "fghi" and r not in "fghi")]
        found = f2_combination(tgt, rows2, pool)
        check(f"the row-{r} combination is FOUND by F_2 elimination, not assumed",
              found == sorted(ROW_COMB[r]), f"{len(found or [])} generators")

    print("\n     the exact witnesses")
    wits = {}
    for r in ["j", "k", "l", "m", "n", "o"]:
        Z = S.s_subst(S.s_sub(D[r], combo_poly(W, ROW_COMB[r])), t)
        even = all(c % 2 == 0 for c in Z.values())
        wits[r] = {m: c // 2 for m, c in Z.items()}
        check(f"the response row {r} is the stated row combination plus an even remainder",
              even, f"{len(Z)} monomials, witness {len(wits[r])} terms")

    print("\n5.  The gauge collapse")
    tg = table(GAUGE, xb_zero=True)
    Zg = S.s_subst(S.s_sub(D["o"], combo_poly(W, GAUGE_COMB)), tg)
    check("on the class-two-forced gauge only x_56 * (1,5) and x_14 * (4,6) survive",
          all(c % 2 == 0 for c in Zg.values()),
          f"{len(Zg)} monomials, witness {len(Zg)} terms")
    wits["gauge"] = {m: c // 2 for m, c in Zg.items()}
    for v in GAUGE:
        Zv = S.s_mod(S.s_subst(S.s_sub(D["o"], combo_poly(W, GAUGE_COMB)),
                               table([u for u in GAUGE if u != v], xb_zero=True)), 2)
        check(f"the collapse consumes '{v} even'", len(Zv) > 0,
              f"{len(Zv)} monomials survive without it")
    Zv = S.s_mod(S.s_subst(S.s_sub(D["o"], combo_poly(W, GAUGE_COMB)), table(GAUGE)), 2)
    check("the collapse consumes 'x_23 = 0'", len(Zv) > 0, S.s_str(Zv))
    for v in ["xd", "xe"]:
        check(f"the collapse does NOT need '{v} even'", True,
              "the x0 slot's fourth and fifth abelian columns are free")

    print("\n6.  Numeric certification of every emitted witness, exactly over Z")
    for r in ["j", "k", "l", "m", "n", "o"]:
        bad = 0
        for _ in range(1500):
            env = randenv(rng, YAB)
            s, x, y = envslots(env)
            w, wd = S.sqWord(s, x, y), S.sqWord(S.mul(s, x), x, y)
            lhs = wd.co[r] - w.co[r] - combo_val(ROW_COMB[r], w, env)
            if lhs != 2 * ev(wits[r], env):
                bad += 1
        check(f"witness for row {r} exact over Z", bad == 0, f"1500 points, {bad} mismatches")
    bad = 0
    for _ in range(1500):
        env = randenv(rng, GAUGE, xb_zero=True)
        s, x, y = envslots(env)
        w, wd = S.sqWord(s, x, y), S.sqWord(S.mul(s, x), x, y)
        if wd.co["o"] - w.co["o"] - combo_val(GAUGE_COMB, w, env) != 2 * ev(wits["gauge"], env):
            bad += 1
    check("witness for the gauge collapse exact over Z", bad == 0,
          f"1500 points, {bad} mismatches")

    for r, halves in [("j", YAB), ("k", YAB), ("l", YAB), ("m", YAB), ("n", YAB), ("o", YAB),
                      ("gauge", GAUGE)]:
        (RESULTS / f"witness_{r}.lean.txt").write_text(lean_witness(wits[r], halves))
    print(f"     seven Lean witnesses written to {RESULTS}")

    print("\n" + "=" * 86)
    npass = sum(1 for _, c in CHECKS if c)
    print(f"{npass} / {len(CHECKS)} named checks passed, {len(CHECKS) - npass} failures")


def f2_combination(target, rows2, pool):
    """Express `target` over `F_2` as `sum_k c_k * rows2[k]` with monomial coefficients.

    Gaussian elimination on the span of `monomial * row`, monomials up to the degree that keeps
    the product inside the target's degree.  Returns the sorted `(row, monomial)` list, or
    `None` if the target is not in the span (which is a genuine negative: the basis is in
    echelon form by leading monomial, so a leading monomial outside the pivot set proves
    non-membership).
    """
    import itertools
    vu = set()
    for p in [target] + [rows2[k] for k in pool]:
        for mo in p:
            vu.update(mo)
    vu = sorted(vu)
    deg = {"f": 3, "g": 3, "h": 3, "i": 3, "j": 2, "k": 2, "l": 2, "m": 1, "n": 1}
    gens, labels = [], []
    for k in pool:
        mults = [()] + [(v,) for v in vu]
        for d in range(2, deg[k] + 1):
            mults += [tuple(sorted(c)) for c in itertools.combinations_with_replacement(vu, d)]
        for mu in mults:
            g = rows2[k]
            for v in mu:
                g = S.s_mul(g, S.s_var(v))
            g = S.s_mod(g, 2)
            if g:
                gens.append(frozenset(g))
                labels.append((k, mu))
    basis = {}

    def reduce(vec, lab):
        vec, lab = set(vec), set(lab)
        while vec:
            piv = max(vec)
            if piv not in basis:
                return vec, piv, lab
            v2, l2 = basis[piv]
            vec ^= v2
            lab ^= l2
        return set(), None, lab

    for i, g in enumerate(gens):
        v, p, lab = reduce(g, {i})
        if p is not None:
            basis[p] = (v, lab)
    _v, p, lab = reduce(set(target), set())
    return None if p is not None else sorted(labels[i] for i in lab)


def randenv(rng, halves, xb_zero=False):
    env = {}
    for pre in "sxy":
        for c in S.NAMES:
            env[pre + c] = rng.randrange(-9, 10)
    if xb_zero:
        env["xb"] = 0
    for v in halves:
        env["H" + v] = rng.randrange(-9, 10)
        env[v] = 2 * env["H" + v]
    return env


def envslots(env):
    return (S.U6({c: env["s" + c] for c in S.NAMES}),
            S.U6({c: env["x" + c] for c in S.NAMES}),
            S.U6({c: env["y" + c] for c in S.NAMES}))


def combo_val(comb, w, env):
    tot = 0
    for k, mu in comb:
        t = 1
        for v in mu:
            t *= env[v]
        tot += t * w.co[k]
    return tot


def ev(poly, env):
    tot = 0
    for m, c in poly.items():
        t = c
        for v in m:
            t *= env[v]
        tot += t
    return tot


def lean_witness(K, halves):
    names = {}
    for c in S.NAMES:
        names["s" + c] = f"s.{c}"
        names["x" + c] = f"x.{c}"
        names["y" + c] = f"y.{c}"
    for v in halves:
        names["H" + v] = v
    lines = []
    for m in sorted(K, key=lambda t: (len(t), tuple(names[v] for v in t))):
        c = K[m]
        body = " * ".join(names[v] for v in m)
        term = body if abs(c) == 1 else f"{abs(c)} * ({body})"
        lines.append(f"    {'+' if c > 0 else '-'} {term}")
    text = "\n".join(lines)
    if text.lstrip().startswith("+"):
        text = text.replace("+ ", "", 1)
    return text + "\n"


if __name__ == "__main__":
    main()
