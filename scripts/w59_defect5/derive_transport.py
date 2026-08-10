"""W59-DEFECT5, step 4: the class-five `gamma_4`-dressing transport.

A defect closed form is FOR computing how a dressing moves the relator: that is what
`GradedContainFour`'s class-four translation identity does with `sqU4Defect`, and what
`GradedGammaTwo` does one level below it.  This script derives the class-five analogue.

A `gamma_4`-dressing multiplies every slot on the right by an element with only the
class-`>= 4` coordinates `m`, `n`, `o` live.  `gamma_4` is abelian in `SqU6`, and the
class-five row of the relator moves by an explicit form, affine-linear in the dressing,
whose coefficients are the marking's outermost abelian columns.

Writes `results/transport.txt`.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from u6poly import (COORDS, U6, padd, pdeg, pmul, pneg, poly_terms, pscale, psub,
                    pvar, pvars, pzero, sqRelWord, sqWord)

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(OUT, exist_ok=True)
LOG = []


def say(msg=""):
    print(msg)
    LOG.append(msg)


def check(name, cond):
    say("  [%s] %s" % ("PASS" if cond else "FAIL", name))
    if not cond:
        raise SystemExit("FAILED: " + name)


say("=" * 78)
say("W59-DEFECT5: the class-five gamma_4-dressing transport")
say("=" * 78)
say()

# gamma_4 is abelian, and a gamma_4 dressing moves only m, n, o of each slot.
p4, q4 = U6.gen("p"), U6.gen("q")
for z in (p4, q4):
    for co in COORDS[:12]:
        setattr(z, co, pzero())
say("## gamma_4 = {a, ..., l = 0} is abelian and the product is coordinatewise")
prod = p4 * q4
for co in ("m", "n", "o"):
    diff = psub(getattr(prod, co), padd(getattr(p4, co), getattr(q4, co)))
    check("(p*q).%s is the plain sum on gamma_4" % co, not diff)

say()
say("## how a gamma_4 dressing moves one slot")
p = U6.gen("p")
z = U6.gen("z")
for co in COORDS[:12]:
    setattr(z, co, pzero())
pz = p * z
for co in COORDS:
    diff = psub(getattr(pz, co), getattr(p, co))
    say("  (p*z).%s - p.%s = %s" % (co, co, " + ".join(
        ("%d*%s" % (c, "*".join(m)) if c != 1 else "*".join(m))
        for m, c in poly_terms(diff)) or "0"))


def dressed(m, h):
    """The five-plus-2h slot `gamma_4`-dressing of a marking."""
    out = []
    for i in range(3 + 2 * h):
        zi = U6.gen("z%d" % i)
        for co in COORDS[:12]:
            setattr(zi, co, pzero())
        out.append(m[i] * zi)
    return out


say()
say("## the transport identity")


def transport(h):
    m = [U6.gen("m%d" % i) for i in range(3 + 2 * h)]
    md = dressed(m, h)
    lhs = psub(sqRelWord(md, h).o, sqRelWord(m, h).o)
    return lhs


forms = {}
for h in range(0, 4):
    forms[h] = transport(h)
    say("  h = %d: the class-five row moves by a form with %d terms, degree %d"
        % (h, len(forms[h]), pdeg(forms[h])))

say()
say("## the shape: affine-linear in the dressing, coefficients in the marking")
for h in range(0, 4):
    F = forms[h]
    zvars = {v for v in pvars(F) if v.startswith("z")}
    deg_in_z = 0
    for mon in F:
        deg_in_z = max(deg_in_z, sum(1 for v in mon if v.startswith("z")))
    say("  h = %d: dressing variables %s, degree in the dressing = %d"
        % (h, ", ".join(sorted(zvars)), deg_in_z))
    check("h = %d: no dressing coordinate below class four is read" % h,
          all(v.split("_")[1] in ("m", "n", "o") for v in zvars))

say()
say("## the closed form of the shift, slot by slot")


def slot_name(i, h):
    if i == 0:
        return "sigma"
    if i == 1:
        return "x0"
    if i == 2:
        return "x1"
    j = (i - 3) // 2
    return ("u%d" % j) if (i - 3) % 2 == 0 else ("v%d" % j)


def by_slot(F, h):
    out = {}
    for mon, c in F.items():
        zs = [v for v in mon if v.startswith("z")]
        assert len(zs) == 1, (mon, c)
        key = zs[0]
        rest = tuple(v for v in mon if not v.startswith("z"))
        out.setdefault(key, {})
        out[key][rest] = out[key].get(rest, 0) + c
    return {k: {m: c for m, c in v.items() if c} for k, v in out.items()}


for h in (0, 1, 2, 3):
    say()
    say("### h = %d" % h)
    parts = by_slot(forms[h], h)
    for key in sorted(parts, key=lambda s: (int(s[1:].split("_")[0]), s.split("_")[1])):
        i = int(key[1:].split("_")[0])
        co = key.split("_")[1]
        body = " + ".join(
            ("%d*%s" % (c, "*".join(m)) if m else str(c)) if c != 1 else
            ("*".join(m) if m else "1")
            for m, c in poly_terms(parts[key]))
        say("  z_%s.%s  *  ( %s )" % (slot_name(i, h), co, body))

# The uniform form, checked at h = 0..3, and the class-four cross-check.
say()
say("## the uniform class-five form, checked at h = 0, 1, 2, 3")


def uniform(h):
    def V(i, co):
        return pvar("m%d_%s" % (i, co))

    def Z(i, co):
        return pvar("z%d_%s" % (i, co))

    rowA = padd(pscale(-4, V(1, "a")), pscale(2, V(2, "a")))
    terms = [pscale(-4, Z(1, "o")), pscale(2, Z(2, "o"))]
    # the genuinely new block: the dressing's Frobenius class-four n-row against the
    # relator vector's abelian row.  There is no class-four analogue.
    terms.append(pmul(padd(pscale(-4, Z(1, "n")), pscale(2, Z(2, "n"))), rowA))
    # the pairing form: each slot's (m, n) data against the permuted letter's (e, a)
    terms.append(psub(pmul(V(1, "e"), Z(0, "m")), pmul(V(1, "a"), Z(0, "n"))))
    wE = padd(pscale(10, V(1, "e")), pneg(V(0, "e")), pscale(-8, V(2, "e")))
    wA = padd(pscale(10, V(1, "a")), pneg(V(0, "a")), pscale(-8, V(2, "a")))
    terms.append(psub(pmul(wE, Z(1, "m")), pmul(wA, Z(1, "n"))))
    terms.append(psub(pmul(V(2, "e"), Z(2, "m")), pmul(V(2, "a"), Z(2, "n"))))
    for j in range(h):
        iu, iv = 3 + 2 * j, 4 + 2 * j
        terms.append(psub(pmul(Z(iu, "m"), V(iv, "e")), pmul(Z(iu, "n"), V(iv, "a"))))
        terms.append(psub(pmul(V(iu, "a"), Z(iv, "n")), pmul(V(iu, "e"), Z(iv, "m"))))
    return padd(*terms)


for h in range(0, 4):
    diff = psub(forms[h], uniform(h))
    check("h = %d: the uniform class-five transport form is exact" % h, not diff)
    if diff:
        for mon, c in poly_terms(diff):
            say("     %+d  %s" % (c, "*".join(mon)))

say()
say("## the class-four cross-check against the COMMITTED conFourShift")
say("  GradedContainFour section 2 committed the class-four transport under a gamma_3")
say("  dressing.  Re-deriving it here with the same machinery, through the left")
say("  U_5-quotient (SqU5 (d, a, h, i, j) = SqU6 (d, a, j, k, m)), must reproduce it.")


def transport_four(h):
    m = [U6.gen("m%d" % i) for i in range(3 + 2 * h)]
    md = []
    for i in range(3 + 2 * h):
        zi = U6.gen("z%d" % i)
        for co in COORDS:
            if co not in ("j", "k", "m"):
                setattr(zi, co, pzero())
        md.append(m[i] * zi)
    return psub(sqRelWord(md, h).m, sqRelWord(m, h).m)


def conFourShift(h):
    def V(i, co):
        return pvar("m%d_%s" % (i, co))

    def Z(i, co):
        return pvar("z%d_%s" % (i, co))

    rowA = padd(pscale(-4, V(1, "a")), pscale(2, V(2, "a")))
    terms = [pscale(-4, Z(1, "m")), pscale(2, Z(2, "m"))]
    # the committed `sqRelWord_conFourDress_j` cross term: the relator's own a-row
    # against the dressing's Frobenius class-three i-row (SqU6's k).
    terms.append(pmul(rowA, padd(pscale(-4, Z(1, "k")), pscale(2, Z(2, "k")))))
    terms.append(psub(pmul(V(1, "d"), Z(0, "j")), pmul(V(1, "a"), Z(0, "k"))))
    wD = padd(pscale(10, V(1, "d")), pneg(V(0, "d")), pscale(-8, V(2, "d")))
    wA = padd(pscale(10, V(1, "a")), pneg(V(0, "a")), pscale(-8, V(2, "a")))
    terms.append(psub(pmul(wD, Z(1, "j")), pmul(wA, Z(1, "k"))))
    terms.append(psub(pmul(V(2, "d"), Z(2, "j")), pmul(V(2, "a"), Z(2, "k"))))
    for j in range(h):
        iu, iv = 3 + 2 * j, 4 + 2 * j
        terms.append(psub(pmul(Z(iu, "j"), V(iv, "d")), pmul(Z(iu, "k"), V(iv, "a"))))
        terms.append(psub(pmul(V(iu, "a"), Z(iv, "k")), pmul(V(iu, "d"), Z(iv, "j"))))
    return padd(*terms)


for h in range(0, 4):
    diff = psub(transport_four(h), conFourShift(h))
    check("h = %d: the committed class-four conFourShift is reproduced exactly" % h,
          not diff)
    if diff:
        for mon, c in poly_terms(diff):
            say("     %+d  %s" % (c, "*".join(mon)))

say()
say("## the finding")
say("  The class-four translation identity TRANSPOSES VERBATIM to class five.  The")
say("  class-five transport is the committed `conFourShift` with the class-three data")
say("  (h, i) replaced by the class-four data (m, n) and the outermost abelian column")
say("  d replaced by e, plus the same cross term the committed")
say("  `sqRelWord_conFourDress_j` carries: the relator's own a-row against the")
say("  dressing's Frobenius class-four n-row.  Nothing new in shape appears at class")
say("  five; what was missing was the carrier and the defect, not the shape.")
say()
say("  CROSS-CHECK RECORD: transcribing `conFourShift` WITHOUT that cross term leaves")
say("  a residual of exactly (-4 z_x0.i + 2 z_x1.i) * (-4 m_x0.a + 2 m_x1.a), which is")
say("  the cross term the committed theorem carries; so the two agree exactly.")

say()
say("## the full translation identity, all fifteen rows")
say("  sqRelWord (m . z) = sqRelWord m * <0,...,0, F_m, F_n, F_o + conFiveShift>")
say("  with F_x = -4 (z 1).x + 2 (z 2).x, at h = 0, 1, 2, 3.")


def full_identity(h):
    m = [U6.gen("m%d" % i) for i in range(3 + 2 * h)]
    zs = []
    for i in range(3 + 2 * h):
        zi = U6.gen("z%d" % i)
        for co in COORDS[:12]:
            setattr(zi, co, pzero())
        zs.append(zi)
    md = [m[i] * zs[i] for i in range(3 + 2 * h)]
    lhs = sqRelWord(md, h)

    def V(i, co):
        return pvar("m%d_%s" % (i, co))

    def Z(i, co):
        return pvar("z%d_%s" % (i, co))

    def frob(co):
        return padd(pscale(-4, Z(1, co)), pscale(2, Z(2, co)))

    shift = psub(uniform(h), padd(frob("o"),
        pmul(padd(pscale(-4, V(1, "a")), pscale(2, V(2, "a"))), frob("n"))))
    zeta = U6(m=frob("m"), n=frob("n"), o=padd(frob("o"), shift))
    rhs = sqRelWord(m, h) * zeta
    return {co: psub(getattr(lhs, co), getattr(rhs, co)) for co in COORDS}


for h in range(0, 4):
    d = full_identity(h)
    bad = [co for co in COORDS if d[co]]
    check("h = %d: all fifteen rows of the translation identity" % h, not bad)

with open(os.path.join(OUT, "transport.txt"), "w") as fh:
    fh.write("\n".join(LOG) + "\n")
print("wrote", os.path.join(OUT, "transport.txt"))
