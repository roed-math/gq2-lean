"""W64-PSI4: the stage-four shift's certificate row as an exact INTEGER linear form.

W63-FOUR reduced the forcing at wave 61's four gap markings to one `Z/8`-linear identity,
`psiOne (gaThreeShift h (gapOneMark h j) z) = 0` for every dressing whose slots lie in
`gapKOne` (and the `psiTwo` analogue).  A Lean proof of that identity has to close a
polynomial identity over `gr3R = ZMod 8`, and `ring` does NOT reduce numerals modulo `8`.
The standard fix is `linear_combination c_1 * h_1 + ... + W * h8` with `h8 : (8 : gr3R) = 0`
and `W` an EXPLICIT integer-coefficient linear form.  Computing `W` is what this module is
for: it reimplements the Lean forms

    gaThreePairL, gaThreePairR, gaThreePair, sqFoxX6, gaThreeCorr, gaThreeCore, gaThreeHandle

over the INTEGERS, symbolically in the thirty dressing coordinates
`(z_s).c` for `s` in `{sigma, x0, x1, U, V}` and `c` in `{j, k, l, m, n, o}`, so that

    psi(gaThreeShift) - (combination of the target's conditions) = 8 * W

holds as an identity of integer polynomials.  `derive.py` cross-checks the result mod `8`
against wave 61's `sharp4lib.slot_matrix`, which is read off the honest `6 x 6` matrices and
never touches the Lean formulas, so a transcription error here cannot survive.

⚠ The two BLOCK terms of `gaThreeShiftO` are deliberately absent.  They enter `psi` multiplied
by `4` and each carries a factor `-4 (z 1).x + 2 (z 2).x`, so `4 * block` is `8 * something`
and vanishes mod `8`; the Lean proof discharges them separately, by the same `h8`.  Everything
below is therefore the shift's certificate row MODULO 8, which is all the identity needs.
"""

import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
LEAN_FOUR = os.path.join(ROOT, "GQ2", "Dyadic", "SqCore", "GradedStageFour.lean")

FIELDS = "abcdefghijklmno"
COORD6 = "jklmno"
SLOT = ["sigma", "x0", "x1", "U", "V"]

# how the Lean file writes the dressing of each slot of a `fiveTuple` marking
LEAN_SLOT = ["z 0", "z 1", "z 2", "z (sqHandleIdxU j)", "z (sqHandleIdxV j)"]


# ---- linear forms in the thirty dressing coordinates ---------------------------------------

def V(s, c):
    """The variable `(z_s).c`, as a linear form."""
    return {(s, COORD6.index(c)): 1}


def add(*fs):
    out = {}
    for f in fs:
        for k, v in f.items():
            out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v}


def smul(a, f):
    return {k: a * v for k, v in f.items() if a * v}


def sub(f, g):
    return add(f, smul(-1, g))


def coeffs(f, s):
    """The six coefficients of `f` on slot `s`."""
    return tuple(f.get((s, t), 0) for t in range(6))


def show_form(f):
    parts = []
    for s in range(5):
        for t in range(6):
            c = f.get((s, t), 0)
            if c:
                parts.append("%+d*%s.%s" % (c, SLOT[s], COORD6[t]))
    return " ".join(parts) if parts else "0"


def show_vec(v, names=COORD6):
    """A coefficient vector on `(j, k, l, m, n, o)`, reduced mod `8`, as a linear form."""
    parts = ["%d%s" % (v[i] % 8, names[i]) for i in range(len(v)) if v[i] % 8]
    return " + ".join(parts) if parts else "0"


def show_char_psi(v):
    return show_vec(v, "jklmno").replace("1l", "l").replace("1m", "m")


def lean_form(f):
    """`f` as a Lean term in the dressing tuple `z` at a `fiveTuple` marking."""
    out = ""
    for s in range(5):
        for t in range(6):
            c = f.get((s, t), 0)
            if not c:
                continue
            atom = "(%s).%s" % (LEAN_SLOT[s], COORD6[t])
            body = atom if abs(c) == 1 else "%d * %s" % (abs(c), atom)
            if not out:
                out = body if c > 0 else "-" + body
            else:
                out += (" + " if c > 0 else " - ") + body
    return out or "0"


# ---- the letters, read out of the Lean file ------------------------------------------------

def lean_letters():
    """Every `def gap... : SqU6 gr3R := <...>` of `GradedStageFour.lean`, as a field dict.

    Reading the letters out of the Lean source rather than out of a Python transcription is
    what makes the emitted `linear_combination` a statement about the file that will consume
    it: if the Lean letters and the measured letters ever disagree, `derive.py`'s cross-check
    against `sharp4lib` fails.
    """
    src = open(LEAN_FOUR).read()
    out = {}
    for m in re.finditer(r"def (gap[A-Za-z]+'?) : SqU6 gr3R := ⟨([^⟩]*)⟩", src):
        vals = [int(x) for x in m.group(2).split(",")]
        assert len(vals) == 15, m.group(1)
        out[m.group(1)] = dict(zip(FIELDS, vals))
    return out


def lean_certificate(name):
    """`psiOne` / `psiTwo` as a coefficient vector on `(j, k, l, m, n, o)`."""
    src = open(LEAN_FOUR).read()
    m = re.search(r"def %s \(w : SqU6 gr3R\) : gr3R := (.*)" % name, src)
    assert m, name
    v = [0] * 6
    for term in m.group(1).split(" + "):
        mm = re.fullmatch(r"(?:(\d+) \* )?w\.([jklmno])", term.strip())
        assert mm, term
        v[COORD6.index(mm.group(2))] = int(mm.group(1) or 1)
    return tuple(v)


def lean_target(name):
    """`gapKOne` / `gapKTwo` as a list of coefficient vectors, one per defining condition."""
    src = open(LEAN_FOUR).read()
    m = re.search(r"def %s : Subgroup \(SqU6 gr3R\) where\n  carrier := \{z \| z\.IsGaThree ∧ (.*)\}"
                  % name, src)
    assert m, name
    rows = []
    for cond in m.group(1).split(" ∧ "):
        lhs = cond.split(" = ")[0]
        v = [0] * 6
        for term in lhs.split(" + "):
            mm = re.fullmatch(r"(?:(\d+) \* )?z\.([jklmno])", term.strip())
            assert mm, term
            v[COORD6.index(mm.group(2))] = int(mm.group(1) or 1)
        rows.append(tuple(v))
    return rows


# ---- the Lean forms, over the integers -----------------------------------------------------

def pairL(s, L):
    """`gaThreePairL (z s) L = (z s).j * L.d - (z s).k * L.a`."""
    return add(smul(L["d"], V(s, "j")), smul(-L["a"], V(s, "k")))


def pairR(s, L):
    """`gaThreePairR (z s) L = (z s).k * L.e - (z s).l * L.b`."""
    return add(smul(L["e"], V(s, "k")), smul(-L["b"], V(s, "l")))


def pair(s, L):
    """`gaThreePair (z s) L`."""
    return add(smul(L["e"], V(s, "m")), smul(-L["a"], V(s, "n")), smul(L["i"], V(s, "j")),
               smul(-L["f"], V(s, "l")), smul(L["a"] * L["b"], V(s, "l")),
               smul(-(L["a"] * L["e"]), V(s, "k")))


def fox(s, x, y):
    """`sqFoxX6 s x y = 10 * x - s - 8 * y`, columnwise."""
    return {c: 10 * x[c] - s[c] - 8 * y[c] for c in FIELDS}


def corr(s, x, y):
    """`gaThreeCorr s x y (z 0) (z 1) (z 2)`, all nine blocks."""
    c0j = (-(s["d"] * x["e"]) + s["e"] * x["d"] - 4 * (x["d"] * x["e"])
           + 2 * (x["d"] * y["e"]) + y["d"] * y["e"])
    c0k = (8 * (x["a"] * x["e"]) - 2 * (x["a"] * y["e"]) - 2 * (x["e"] * y["a"])
           - 2 * (y["a"] * y["e"]))
    c0l = (s["a"] * x["b"] - s["b"] * x["a"] - 4 * (x["a"] * x["b"])
           + 2 * (x["b"] * y["a"]) + y["a"] * y["b"])
    c1j = (3 * (s["d"] * x["e"]) - 2 * (s["d"] * y["e"]) + s["e"] * x["d"]
           - 20 * (x["d"] * x["e"]) + 20 * (x["d"] * y["e"]) - 4 * (y["d"] * y["e"]))
    c1k = (2 * (s["a"] * s["e"]) - 14 * (s["a"] * x["e"]) + 10 * (s["a"] * y["e"])
           - 14 * (s["e"] * x["a"]) + 10 * (s["e"] * y["a"]) + 130 * (x["a"] * x["e"])
           - 100 * (x["a"] * y["e"]) - 100 * (x["e"] * y["a"]) + 80 * (y["a"] * y["e"]))
    c1l = (-2 * (s["a"] * s["b"]) + 11 * (s["a"] * x["b"]) - 8 * (s["a"] * y["b"])
           + 13 * (s["b"] * x["a"]) - 10 * (s["b"] * y["a"]) - 110 * (x["a"] * x["b"])
           + 80 * (x["a"] * y["b"]) + 100 * (x["b"] * y["a"]) - 76 * (y["a"] * y["b"]))
    c2j = -2 * (s["d"] * y["e"]) + s["e"] * y["d"]
    c2k = s["a"] * y["e"] + s["e"] * y["a"]
    c2l = s["a"] * y["b"] - 2 * (s["b"] * y["a"])
    return add(smul(c0j, V(0, "j")), smul(c0k, V(0, "k")), smul(c0l, V(0, "l")),
               smul(c1j, V(1, "j")), smul(c1k, V(1, "k")), smul(c1l, V(1, "l")),
               smul(c2j, V(2, "j")), smul(c2k, V(2, "k")), smul(c2l, V(2, "l")))


def core_row(s, x, y, row):
    """The `m`-, `n`- or `o`-row of `gaThreeCore s x y (z 0) (z 1) (z 2)`."""
    fx = fox(s, x, y)
    frob = add(smul(-4, V(1, row)), smul(2, V(2, row)))
    if row == "m":
        return add(frob, pairL(0, x), pairL(1, fx), pairL(2, y))
    if row == "n":
        return add(frob, pairR(0, x), pairR(1, fx), pairR(2, y))
    return add(frob, pair(0, x), pair(1, fx), pair(2, y), corr(s, x, y))


def handle_row(p, q, row):
    """The `m`-, `n`- or `o`-row of `gaThreeHandle U V (z (idxU j)) (z (idxV j))`."""
    if row == "m":
        return sub(pairL(3, q), pairL(4, p))
    if row == "n":
        return sub(pairR(3, q), pairR(4, p))
    blockJ = p["d"] * q["e"] - p["e"] * q["d"]
    blockL = p["a"] * q["b"] - p["b"] * q["a"]
    return add(sub(pair(3, q), pair(4, p)),
               smul(-blockJ, add(V(3, "j"), V(4, "j"))),
               smul(blockL, add(V(3, "l"), V(4, "l"))))


def shift_row(s, x, y, u, v, row):
    """The `m`-, `n`- or `o`-row of `gaThreeShift h (fiveTuple ... ) z`, MODULO the two block
    terms of the `o`-row (which the certificate kills outright, being multiplied by `4`)."""
    if row == "l":
        return add(smul(-4, V(1, "l")), smul(2, V(2, "l")))
    return add(core_row(s, x, y, row), handle_row(u, v, row))


def psi_row(psi, s, x, y, u, v):
    """`psi (gaThreeShift h (fiveTuple gr3R h j s x y u v) z)`, modulo the block terms.

    `psi` is a coefficient vector on `(j, k, l, m, n, o)`.  Only the `l`-, `m`-, `n`- and
    `o`-entries of the certificates used here are non-zero; a `j`- or `k`-entry would need the
    two further shift rows and is rejected rather than silently ignored.
    """
    assert psi[0] == 0 and psi[1] == 0, "certificate reads a class-three row"
    out = {}
    for t, row in ((2, "l"), (3, "m"), (4, "n"), (5, "o")):
        if psi[t]:
            out = add(out, smul(psi[t], shift_row(s, x, y, u, v, row)))
    return out


# ---- the combination -----------------------------------------------------------------------

def slot_conditions(rows, s):
    """The target's defining conditions, as linear forms in slot `s`'s coordinates."""
    return [add(*[smul(r[t], V(s, COORD6[t])) for t in range(6) if r[t]]) for r in rows]


def solve_slot(f, rows, s, bound=8):
    """Integer coefficients `c` with `f|_s - sum c_t * cond_t` divisible by `8` coefficientwise.

    Exhaustive over `[0, 8)^len(rows)`; the smallest solution in lexicographic order is
    returned, or `None` if the slot's form is not in the mod-`8` span of the conditions.
    """
    conds = slot_conditions(rows, s)
    fs = coeffs(f, s)
    cc = [coeffs(c, s) for c in conds]
    n = len(rows)
    for code in range(bound ** n):
        c, t = [], code
        for _ in range(n):
            c.append(t % bound)
            t //= bound
        if all((fs[i] - sum(c[u] * cc[u][i] for u in range(n))) % 8 == 0 for i in range(6)):
            return tuple(c)
    return None


def witness(f, rows, cs):
    """`W = (f - sum_s sum_t cs[s][t] * cond_{s,t}) / 8`, exactly."""
    tot = dict(f)
    for s in range(5):
        for t, cond in enumerate(slot_conditions(rows, s)):
            tot = sub(tot, smul(cs[s][t], cond))
    assert all(v % 8 == 0 for v in tot.values()), "residue not divisible by 8"
    return {k: v // 8 for k, v in tot.items() if v // 8}
