"""W59-DEFECT5, step 3: validate every closed form against honest 6 x 6 collection.

Nothing symbolic is trusted here.  Every marking is turned into honest
unitriangular 6 x 6 integer matrices, the relator word is collected by matrix
multiplication and back-substitution inverses, and the resulting `(1,6)` and
`(1,5)` entries are compared against the derived closed forms.  The comparison is
run over the exact integers and over `ZMod 8` and `ZMod 4` (the campaign's gate
rings), at handle counts 0 to 4, at random and at structured markings.

Writes `results/validate.txt`.  Zero mismatches is the bar.
"""

import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from u6poly import (COORDS, U6, commP, conjP, coords_of_mat, handleWord, mat_inv,
                    mat_mul, mat_of, padd, peval, pmul, pscale, psub, pvar,
                    sqRelWord, sqWord)

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(OUT, exist_ok=True)
LOG = []
COMPARISONS = 0
MISMATCH = 0


def say(msg=""):
    print(msg)
    LOG.append(msg)


# --------------------------------------------------- the derived closed forms

_s, _x, _y = U6.gen("s"), U6.gen("x"), U6.gen("y")
_W = sqWord(_s, _x, _y)
CORE4 = psub(_W.m, padd(pscale(-4, pvar("x_m")), pscale(2, pvar("y_m"))))
CORE5 = psub(_W.o, padd(pscale(-4, pvar("x_o")), pscale(2, pvar("y_o"))))


def env_of(vals, prefix):
    return {prefix + "_" + co: vals[co] for co in COORDS}


def closed_core(poly, sv, xv, yv, mod=None):
    env = {}
    env.update(env_of(sv, "s"))
    env.update(env_of(xv, "x"))
    env.update(env_of(yv, "y"))
    v = peval(poly, env)
    return v % mod if mod else v


# ------------------------------------------------------ honest matrix words


def hm_mul(*Ms, mod=None):
    out = Ms[0]
    for M in Ms[1:]:
        out = mat_mul(out, M, mod)
    return out


def hm_conj(P, G, mod=None):
    return hm_mul(mat_inv(G, mod), P, G, mod=mod)


def hm_comm(P, Q, mod=None):
    return hm_mul(mat_inv(P, mod), mat_inv(Q, mod), P, Q, mod=mod)


def hm_pow(P, n, mod=None):
    out = mat_of({co: 0 for co in COORDS})
    for _ in range(n):
        out = mat_mul(out, P, mod)
    return out


def hm_sqWord(S, X, Y, mod=None):
    return hm_mul(mat_inv(hm_conj(X, S, mod), mod),
                  mat_inv(hm_pow(X, 3, mod), mod),
                  hm_pow(Y, 2, mod),
                  hm_comm(Y, hm_conj(Y, S, mod), mod), mod=mod)


def hm_relWord(ms, h, mod=None):
    W = hm_sqWord(ms[0], ms[1], ms[2], mod)
    for j in range(h):
        W = mat_mul(W, hm_comm(ms[3 + 2 * j], ms[4 + 2 * j], mod), mod)
    return W


# ------------------------------------------------------ the assembled defect


def poly_of_vals(vals):
    return U6(**{co: {(): vals[co]} if vals[co] else {} for co in COORDS})


def defect_closed(ms, h, mod=None):
    """`sqU6Defect` and `sqU6Defect4`, evaluated from the derived closed forms."""
    sv, xv, yv = ms[0], ms[1], ms[2]
    core5 = closed_core(CORE5, sv, xv, yv)
    core4 = closed_core(CORE4, sv, xv, yv)
    us = [poly_of_vals(ms[3 + 2 * j]) for j in range(h)]
    vs = [poly_of_vals(ms[4 + 2 * j]) for j in range(h)]
    Cs = [commP(us[j], vs[j]) for j in range(h)]

    def val(c, co):
        p = getattr(c, co)
        return p.get((), 0)

    def tot(co):
        return sum(val(c, co) for c in Cs)

    def tri(co1, co2):
        return sum(sum(val(Cs[ss], co1) for ss in range(t)) * val(Cs[t], co2)
                   for t in range(h))

    Hi, Hl, Hk, Hh = tot("i"), tot("l"), tot("k"), tot("h")
    Hn = tot("n") + tri("g", "i")
    Ho = tot("o") + tri("f", "l") + tri("j", "i")
    Hm = tot("m") + tri("f", "h")
    Wa = -4 * xv["a"] + 2 * yv["a"]
    Wf = (-4 * xv["f"] + 2 * yv["f"] + sv["a"] * xv["b"] - sv["b"] * xv["a"]
          + 10 * xv["a"] * xv["b"] - 8 * xv["a"] * yv["b"] + yv["a"] * yv["b"])
    Wj = -4 * xv["j"] + 2 * yv["j"] + closed_core(CORE3J, sv, xv, yv)
    d5 = core5 + Wa * Hn + Wf * Hl + Wj * Hi + Ho
    d4 = core4 + Wa * Hk + Wf * Hh + Hm
    if mod:
        d5, d4 = d5 % mod, d4 % mod
    return d5, d4


CORE3J = psub(_W.j, padd(pscale(-4, pvar("x_j")), pscale(2, pvar("y_j"))))


# ------------------------------------------------------------------ sampling


def rand_vals(rng, bound):
    return {co: rng.randrange(-bound, bound + 1) for co in COORDS}


def run(tag, rng, h, trials, bound, mod=None, sparse=None):
    global COMPARISONS, MISMATCH
    bad = 0
    for _ in range(trials):
        ms = []
        for _slot in range(3 + 2 * h):
            v = rand_vals(rng, bound)
            if sparse is not None:
                live = rng.sample(COORDS, sparse)
                v = {co: (v[co] if co in live else 0) for co in COORDS}
            if mod:
                v = {co: v[co] % mod for co in COORDS}
            ms.append(v)
        Ms = [mat_of(v) for v in ms]
        Rw = hm_relWord(Ms, h, mod)
        got = coords_of_mat(Rw)
        d5, d4 = defect_closed(ms, h, mod)
        head5 = -4 * ms[1]["o"] + 2 * ms[2]["o"]
        head4 = -4 * ms[1]["m"] + 2 * ms[2]["m"]
        pred5 = head5 + d5
        pred4 = head4 + d4
        if mod:
            pred5, pred4 = pred5 % mod, pred4 % mod
        COMPARISONS += 2
        if pred5 != got["o"]:
            bad += 1
        if pred4 != got["m"]:
            bad += 1
    MISMATCH += bad
    say("  %-52s h=%d trials=%5d  mismatches=%d" % (tag, h, trials, bad))
    return bad


def run_allrows(tag, rng, h, trials, bound, mod=None):
    """Every one of the fifteen rows against honest collection, not only the top."""
    global COMPARISONS, MISMATCH
    bad = 0
    for _ in range(trials):
        ms = []
        for _slot in range(3 + 2 * h):
            v = rand_vals(rng, bound)
            if mod:
                v = {co: v[co] % mod for co in COORDS}
            ms.append(v)
        Ms = [mat_of(v) for v in ms]
        got = coords_of_mat(hm_relWord(Ms, h, mod))
        sym = sqRelWord([poly_of_vals(v) for v in ms], h)
        for co in COORDS:
            p = getattr(sym, co)
            v = p.get((), 0)
            if mod:
                v %= mod
            COMPARISONS += 1
            if v != got[co]:
                bad += 1
    MISMATCH += bad
    say("  %-52s h=%d trials=%5d  mismatches=%d" % (tag, h, trials, bad))
    return bad


say("=" * 78)
say("W59-DEFECT5 validation: closed forms against honest 6 x 6 group collection")
say("=" * 78)
say()
say("## A the group law itself: all fifteen relator rows, symbolic vs honest matrices")
rng = random.Random(20260810)
for h in range(0, 5):
    run_allrows("all fifteen rows over ZZ", rng, h, 40, 6)
for h in range(0, 5):
    run_allrows("all fifteen rows over ZMod 8", rng, h, 40, 8, mod=8)

say()
say("## B the class-five and class-four defect closed forms over ZZ")
for h in range(0, 5):
    run("sqU6Defect / sqU6Defect4 over ZZ, dense", rng, h, 300, 5)
for h in range(0, 5):
    run("sqU6Defect / sqU6Defect4 over ZZ, wide range", rng, h, 150, 40)

say()
say("## C over the campaign's gate rings")
for h in range(0, 5):
    run("sqU6Defect / sqU6Defect4 over ZMod 8", rng, h, 300, 8, mod=8)
for h in range(0, 5):
    run("sqU6Defect / sqU6Defect4 over ZMod 4", rng, h, 300, 4, mod=4)
for h in range(0, 5):
    run("sqU6Defect / sqU6Defect4 over ZMod 16", rng, h, 200, 16, mod=16)

say()
say("## D sparse markings (few live coordinates), where cancellations hide")
for k in (1, 2, 3, 5):
    for h in range(0, 4):
        run("sparse marking, %d live coordinates per slot" % k, rng, h, 200, 5,
            sparse=k)


def run_transport(tag, rng, h, trials, bound, mod=None):
    """The class-five translation identity against honest 6 x 6 collection."""
    global COMPARISONS, MISMATCH
    bad = 0
    for _ in range(trials):
        ms, zs = [], []
        for _slot in range(3 + 2 * h):
            v = rand_vals(rng, bound)
            z = {co: (rand_vals(rng, bound)[co] if co in ("m", "n", "o") else 0)
                 for co in COORDS}
            if mod:
                v = {co: v[co] % mod for co in COORDS}
                z = {co: z[co] % mod for co in COORDS}
            ms.append(v)
            zs.append(z)
        dressed = [coords_of_mat(mat_mul(mat_of(ms[i]), mat_of(zs[i]), mod))
                   for i in range(3 + 2 * h)]
        got = coords_of_mat(hm_relWord([mat_of(v) for v in dressed], h, mod))
        base = coords_of_mat(hm_relWord([mat_of(v) for v in ms], h, mod))

        def E(i, co):
            return ms[i][co]

        def Z(i, co):
            return zs[i][co]

        shift = ((E(1, "e") * Z(0, "m") - E(1, "a") * Z(0, "n"))
                 + ((10 * E(1, "e") - E(0, "e") - 8 * E(2, "e")) * Z(1, "m")
                    - (10 * E(1, "a") - E(0, "a") - 8 * E(2, "a")) * Z(1, "n"))
                 + (E(2, "e") * Z(2, "m") - E(2, "a") * Z(2, "n")))
        for j in range(h):
            iu, iv = 3 + 2 * j, 4 + 2 * j
            shift += ((Z(iu, "m") * E(iv, "e") - Z(iu, "n") * E(iv, "a"))
                      + (E(iu, "a") * Z(iv, "n") - E(iu, "e") * Z(iv, "m")))
        fm = -4 * Z(1, "m") + 2 * Z(2, "m")
        fn = -4 * Z(1, "n") + 2 * Z(2, "n")
        fo = -4 * Z(1, "o") + 2 * Z(2, "o")
        pred_m = base["m"] + fm
        pred_n = base["n"] + fn
        pred_o = base["o"] + fo + shift + base["a"] * fn
        if mod:
            pred_m, pred_n, pred_o = pred_m % mod, pred_n % mod, pred_o % mod
        COMPARISONS += 3
        for pred, co in ((pred_m, "m"), (pred_n, "n"), (pred_o, "o")):
            if pred != got[co]:
                bad += 1
        # the class-<= 3 rows must be untouched
        for co in COORDS[:12]:
            COMPARISONS += 1
            if got[co] != base[co]:
                bad += 1
    MISMATCH += bad
    say("  %-52s h=%d trials=%5d  mismatches=%d" % (tag, h, trials, bad))
    return bad


say()
say("## E the class-five gamma_4 translation identity")
for h in range(0, 5):
    run_transport("conFiveDress transport over ZZ", rng, h, 200, 5)
for h in range(0, 5):
    run_transport("conFiveDress transport over ZMod 8", rng, h, 200, 8, mod=8)
for h in range(0, 3):
    run_transport("conFiveDress transport over ZZ, wide range", rng, h, 100, 40)

say()
say("=" * 78)
say("TOTAL COMPARISONS: %d" % COMPARISONS)
say("TOTAL MISMATCHES : %d" % MISMATCH)
say("=" * 78)

with open(os.path.join(OUT, "validate.txt"), "w") as fh:
    fh.write("\n".join(LOG) + "\n")
print()
print("wrote %s" % os.path.join(OUT, "validate.txt"))
if MISMATCH:
    raise SystemExit(1)
