#!/usr/bin/env python3
"""W58-FIVE step 4: a relator-killing class-five marking with a LIVE handle block.

Wave 57 built the first class-four point with a live handle block and proved the class-four
sigma forcing cannot see it.  This script builds the class-five analogue and measures what the
class-five top row sees there.  Everything is honest 6x6 matrix collection over Z/8 (the
routines come from validate_u6.py, which is itself validated against the closed forms).

The solve is staged: the relator rows are triangular in the filtration, so each deep coordinate
of the x1-slot is fixed by scanning its own row.
"""
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from validate_u6 import (NAMES, T, ONE, cf_mul, M_sqRelWord, sqRelWord,
                         handleWord, sqWord, w_comm)

N = 8
DEEP = ["f", "g", "h", "i", "j", "k", "l", "m", "n", "o"]


def elt(**kw):
    return tuple(kw.get(nm, 0) % N for nm in NAMES)


def show(tag, t):
    d = T(t)
    parts = [f"{nm}={d[nm]}" for nm in NAMES if d[nm]]
    print(f"  {tag:24s} = <{', '.join(parts) if parts else 'trivial'}>")


def solve_x1(sig, x0, U, V, seed):
    """Scan each deep coordinate of the x1-slot against its own relator row."""
    y = dict(zip(NAMES, seed))
    for row in DEEP:
        found = None
        for val in range(N):
            cand = dict(y)
            cand[row] = val
            t = tuple(cand[nm] for nm in NAMES)
            rel = M_sqRelWord([sig, x0, t, U, V], 1, N)
            if T(rel)[row] == 0:
                found = val
                break
        if found is None:
            return None, row
        y[row] = found
    return tuple(y[nm] for nm in NAMES), None


def main():
    print("## staged solve for a class-five point with a live handle block (h = 1)")
    sig = elt()                      # sigma slot: trivial
    x0 = elt(g=1)                    # x0 slot: second class-two column, so the class-three
                                     # sigma response is live
    U = elt(d=1)                     # handle u-letter
    V = elt(e=2)                     # handle v-letter
    seed = elt(g=2)                  # forced by the class-two g-row: -4*x0.g + 2*x1.g = 0
    x1, bad = solve_x1(sig, x0, U, V, seed)
    if x1 is None:
        print(f"  !! no solution at row {bad}")
        return 1
    mk = [sig, x0, x1, U, V]
    for tag, t in (("sigma", sig), ("x0", x0), ("x1 (solved)", x1), ("U", U), ("V", V)):
        show(tag, t)

    core = sqWord(sig, x0, x1, N)
    blk = w_comm(U, V, N)
    show("sqWord (core word)", core)
    show("commP U V (block)", blk)
    rel_cf = sqRelWord(mk, 1, N)
    rel_mat = M_sqRelWord(mk, 1, N)
    show("sqRelWord (closed form)", rel_cf)
    show("sqRelWord (matrix)", rel_mat)
    ok = rel_cf == ONE and rel_mat == ONE
    print(f"  RELATOR TRIVIAL (all fifteen rows): {ok}")
    print(f"  HANDLE BLOCK LIVE: {blk != ONE}, order "
          f"{min(k for k in range(1, 33) if _pow(blk, k) == ONE)}")
    H = handleWord([U], [V], N)
    print(f"  handleWord.i (the class-five invariant) = {T(H)['i']}")
    if not ok:
        return 1

    print()
    print("## the sigma response at that point")
    v = elt(a=1)                     # nu'-trivial dressing (b-column zero)
    show("dressing v", v)
    d = [cf_mul(sig, v, N), x0, x1, U, V]
    resp_o = (T(M_sqRelWord(d, 1, N))["o"] - T(M_sqRelWord(mk, 1, N))["o"]) % N
    resp_m = (T(M_sqRelWord(d, 1, N))["m"] - T(M_sqRelWord(mk, 1, N))["m"]) % N
    core_d = sqWord(cf_mul(sig, v, N), x0, x1, N)
    dj = (T(core_d)["j"] - T(core)["j"]) % N
    df = (T(core_d)["f"] - T(core)["f"]) % N
    do = (T(core_d)["o"] - T(core)["o"]) % N
    print(f"  class-three sigma response of the core word : {dj}")
    print(f"  class-two   sigma response of the core word : {df}  (0 on the nu'-gauge)")
    print(f"  class-five  sigma response of the core word : {do}")
    print(f"  HANDLE CONTRIBUTION  dj * H.i               : {(dj * T(H)['i']) % N}")
    print(f"  total class-five response (o-row)           : {resp_o}")
    print(f"  total class-four  response (m-row)          : {resp_m}")
    print(f"  split check resp_o == do + dj*H.i           : "
          f"{resp_o == (do + dj * T(H)['i']) % N}")

    print()
    print("## the same core slots with the block removed (that marking is NOT legal)")
    mk0 = [sig, x0, x1, ONE, ONE]
    d0 = [cf_mul(sig, v, N), x0, x1, ONE, ONE]
    resp_o0 = (T(M_sqRelWord(d0, 1, N))["o"] - T(M_sqRelWord(mk0, 1, N))["o"]) % N
    resp_m0 = (T(M_sqRelWord(d0, 1, N))["m"] - T(M_sqRelWord(mk0, 1, N))["m"]) % N
    print(f"  class-five response without the block : {resp_o0}")
    print(f"  class-four response without the block : {resp_m0}")
    print(f"  CLASS FIVE SEES THE BLOCK : {resp_o != resp_o0}")
    print(f"  class four is blind       : {resp_m == resp_m0}")

    print()
    print("## sweep: every single-column nu'-trivial dressing at the live point")
    seen = diff = 0
    for nm in NAMES:
        if nm == "b":
            continue
        for val in range(1, N):
            vv = elt(**{nm: val})
            dd = [cf_mul(sig, vv, N), x0, x1, U, V]
            dd0 = [cf_mul(sig, vv, N), x0, x1, ONE, ONE]
            r1 = (T(M_sqRelWord(dd, 1, N))["o"] - T(M_sqRelWord(mk, 1, N))["o"]) % N
            r0 = (T(M_sqRelWord(dd0, 1, N))["o"] - T(M_sqRelWord(mk0, 1, N))["o"]) % N
            q1 = (T(M_sqRelWord(dd, 1, N))["m"] - T(M_sqRelWord(mk, 1, N))["m"]) % N
            q0 = (T(M_sqRelWord(dd0, 1, N))["m"] - T(M_sqRelWord(mk0, 1, N))["m"]) % N
            seen += 1
            if r1 != r0:
                diff += 1
            assert q1 == q0, (nm, val, q1, q0)
    print(f"  dressings swept: {seen}")
    print(f"  class-five responses that see the block: {diff}")
    print(f"  class-four responses that see the block: 0 (asserted for all {seen})")

    print()
    print("## the point at every handle count h, with the extra pairs trivial")
    for hh in range(1, 5):
        mkh = [sig, x0, x1, U, V] + [ONE, ONE] * (hh - 1)
        print(f"  h = {hh}: relator trivial = {M_sqRelWord(mkh, hh, N) == ONE}, "
              f"handleWord.i = "
              f"{T(handleWord([U] + [ONE] * (hh - 1), [V] + [ONE] * (hh - 1), N))['i']}")

    print()
    print("## the strengthened powering base (section 4 of the Lean file)")
    base = elt(a=1, e=1, k=2)
    show("fivePowBase", base)
    b = T(base)
    obs = {
        "a*b": b["a"] * b["b"], "b*c": b["b"] * b["c"], "c*d": b["c"] * b["d"],
        "d*e": b["d"] * b["e"],
        "a*g+f*c": b["a"] * b["g"] + b["f"] * b["c"],
        "b*h+g*d": b["b"] * b["h"] + b["g"] * b["d"],
        "c*i+h*e": b["c"] * b["i"] + b["h"] * b["e"],
        "a*k+f*h+j*d": b["a"] * b["k"] + b["f"] * b["h"] + b["j"] * b["d"],
        "b*l+g*i+k*e": b["b"] * b["l"] + b["g"] * b["i"] + b["k"] * b["e"],
        "a*n+f*l+j*i+m*e": (b["a"] * b["n"] + b["f"] * b["l"] + b["j"] * b["i"]
                            + b["m"] * b["e"]),
    }
    for tag, val in obs.items():
        print(f"  obstruction {tag:20s} = {val % N}")
    X3 = (b["a"] * b["b"] * b["l"] + b["a"] * b["e"] * b["k"] + b["a"] * b["g"] * b["i"]
          + b["c"] * b["f"] * b["i"] + b["d"] * b["e"] * b["j"] + b["e"] * b["f"] * b["h"])
    print(f"  class-five C(n,3) layer = {X3 % N}  (nonzero: the flat lemmas do not apply)")
    from validate_u6 import cf_pow, binom
    bad = 0
    for n in range(0, 20):
        got = T(cf_pow(base, n, N))["o"]
        want = (n * b["o"] + (n * n - n) * 0 + (n ** 3 - 3 * n ** 2 + 2 * n) * 3) % N
        if got != want:
            bad += 1
            print(f"  !! n={n}: {got} != {want}")
    print(f"  powering polynomial (w2 = 0, w3 = 3) checked for n < 20, mismatches: {bad}")
    return 0


def _pow(t, k):
    r = ONE
    for _ in range(k):
        r = cf_mul(r, t, N)
    return r


if __name__ == "__main__":
    sys.exit(main())
