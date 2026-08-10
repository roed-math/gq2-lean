#!/usr/bin/env python3
"""W60-HOM5 certificate: the class-five sigma forcing at the level of `sqArbFrame`.

An independent re-implementation of the class-five carrier `SqU6 (ZMod 8)` (fifteen
coordinates a..o), used to certify the facts the Lean file
`GQ2/Dyadic/SqCore/GradedFiveFrame.lean` states about the hom-level transport of
`GradedFiveForce.fiveWit_sigma_forced`:

  A  the group law reproduces the two committed verdicts at the binder point;
  B  the achievable gamma_4-lattice of the image is EXACTLY forceN4, so quantifying the
     hom-level forcing over forceN4 is the sharpest form and not a widening by fiat;
  C  the exclusion sweep over the whole of forceN4 (plus arbitrary central dressings);
  D  a NON-VACUITY witness: an explicit nontrivial triple commutator of the point's own
     letters, which is what the Lean non-vacuity theorem exhibits;
  E  the c-column (the "(3,4)-column") of every element of the image is even, which is what
     discharges the class-five legality hypothesis for EVERY dressing;
  F  the pivot anchor is flat: all ten obstructions of `SqU6.zpowZtwo_of_flat` vanish at the
     binder point's x0-slot, and the pivot image is displaced off the identity, which is why
     the reachable row type is forced to the one cleared at the selected handle.

No dependency beyond the standard library.
"""

from itertools import product
import random

M = 8


def mod(x):
    return x % M


IDX = "abcdefghijklmno"


def mk(**kw):
    v = [0] * 15
    for k, x in kw.items():
        v[IDX.index(k)] = mod(x)
    return tuple(v)


ONE = tuple([0] * 15)


def mul(p, q):
    (pa, pb, pc, pd, pe, pf, pg, ph, pi, pj, pk, pl, pm, pn, po) = p
    (qa, qb, qc, qd, qe, qf, qg, qh, qi, qj, qk, ql, qm, qn, qo) = q
    return (
        mod(pa + qa),
        mod(pb + qb),
        mod(pc + qc),
        mod(pd + qd),
        mod(pe + qe),
        mod(pf + qf + pa * qb),
        mod(pg + qg + pb * qc),
        mod(ph + qh + pc * qd),
        mod(pi + qi + pd * qe),
        mod(pj + qj + pa * qg + pf * qc),
        mod(pk + qk + pb * qh + pg * qd),
        mod(pl + ql + pc * qi + ph * qe),
        mod(pm + qm + pa * qk + pf * qh + pj * qd),
        mod(pn + qn + pb * ql + pg * qi + pk * qe),
        mod(po + qo + pa * qn + pf * ql + pj * qi + pm * qe),
    )


def inv(p):
    (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o) = p
    return (
        mod(-a),
        mod(-b),
        mod(-c),
        mod(-d),
        mod(-e),
        mod(a * b - f),
        mod(b * c - g),
        mod(c * d - h),
        mod(d * e - i),
        mod(-(a * b * c) + a * g + c * f - j),
        mod(-(b * c * d) + b * h + d * g - k),
        mod(-(c * d * e) + c * i + e * h - l),
        mod(a * b * c * d - a * b * h - a * d * g + a * k - c * d * f + d * j + f * h - m),
        mod(b * c * d * e - b * c * i - b * e * h + b * l - d * e * g + e * k + g * i - n),
        mod(
            -(a * b * c * d * e)
            + a * b * c * i
            + a * b * e * h
            - a * b * l
            + a * d * e * g
            - a * e * k
            - a * g * i
            + a * n
            + c * d * e * f
            - c * f * i
            - d * e * j
            - e * f * h
            + e * m
            + f * l
            + i * j
            - o
        ),
    )


def conjP(x, g):
    return mul(mul(inv(g), x), g)


def commP(x, y):
    return mul(mul(mul(inv(x), inv(y)), x), y)


def powp(x, k):
    r = ONE
    for _ in range(k):
        r = mul(r, x)
    return r


def liftC6(w):
    return mk(o=w)


def sqWord(s, x, y):
    return mul(
        mul(mul(inv(conjP(x, s)), inv(powp(x, 3))), powp(y, 2)),
        commP(y, conjP(y, s)),
    )


# ---------------------------------------------------------------- the binder point

fiveSigMark = mk(b=1)
forceX = mk(a=2, e=1)
forceY = mk(e=2, f=1, h=3, i=1, j=2, k=2, l=2, m=3, n=2, o=2)
forceU = mk(a=1, c=2, d=3, f=3, g=2, h=2, i=2)
forceV = mk(d=1, e=2, f=3, g=2, h=3, i=3)

LETTERS = {
    "sigMark": fiveSigMark,
    "X": forceX,
    "Y": forceY,
    "U": forceU,
    "V": forceV,
}


def relator_one_handle(S, X, Y, U, V):
    """sqRelWord of a one-handle-live tuple: the core word times the single commutator."""
    return mul(sqWord(S, X, Y), commP(U, V))


def fiveWit_relator(v):
    return relator_one_handle(mul(fiveSigMark, v), forceX, forceY, forceU, forceV)


results = []


def check(name, cond, detail=""):
    results.append((name, bool(cond), detail))


# ---------------------------------------------------------------- A the two verdicts

check("A1 undressed frame kills the relator", fiveWit_relator(ONE) == ONE,
      f"relator = {fiveWit_relator(ONE)}")
check("A2 a0 = a1 dressing leaves liftC6 7", fiveWit_relator(forceX) == liftC6(7),
      f"relator = {fiveWit_relator(forceX)}")
check("A3 the residue is odd", fiveWit_relator(forceX)[14] % 2 == 1)
check("A4 class-four rows of the dressed relator vanish",
      fiveWit_relator(forceX)[12] == 0 and fiveWit_relator(forceX)[13] == 0)

# ---------------------------------------------------------------- B the image and its lcs


def closure(gens):
    """Subgroup generated by `gens`, by incremental BFS on a reduced generating set.

    A finite group is the semigroup generated by any generating set, so right
    multiplication alone suffices; the reduced set keeps each BFS pass cheap."""
    elems = {ONE}
    reduced = []
    for g in gens:
        if g in elems:
            continue
        reduced.append(g)
        elems = {ONE}
        frontier = [ONE]
        while frontier:
            nxt = []
            for x in frontier:
                for s in reduced:
                    y = mul(x, s)
                    if y not in elems:
                        elems.add(y)
                        nxt.append(y)
            frontier = nxt
    return elems


# A random word in the letters and their inverses (the image is far too large to enumerate;
# every statement below that mentions the image is checked on random words in it).
def random_word(rng, length):
    z = ONE
    for _ in range(length):
        g = LETTERS[rng.choice(sorted(LETTERS))]
        z = mul(z, inv(g) if rng.randrange(2) else g)
    return z


# The sharpness claim is proved in one direction in Lean (`forceLcs_three_le_forceN4`:
# gamma_4 of the image is contained in forceN4).  The other direction is the computation
# here: the triple commutators of the letters alone already generate the whole of forceN4,
# and each of them is by construction an element of gamma_4 of the image.
triple_gens = [
    commP(commP(commP(LETTERS[a], LETTERS[b]), LETTERS[c]), LETTERS[d])
    for a, b, c, d in product(sorted(LETTERS), repeat=4)
]
g4_lower = closure(triple_gens)

forceN4 = set()
for m4 in range(0, M, 2):
    for n4 in range(0, M, 2):
        for o5 in range(M):
            forceN4.add(mk(m=m4, n=n4, o=o5))

check("B2 the letterwise triple commutators generate exactly forceN4 (128 elements)",
      g4_lower == forceN4,
      f"|<triples>| = {len(g4_lower)}, |forceN4| = {len(forceN4)}")
check("B3 hence gamma_4(image) = forceN4 EXACTLY: the forceN4 bound is SHARP",
      g4_lower == forceN4 and all(z[:12] == tuple([0] * 12) and z[12] % 2 == 0
                                  and z[13] % 2 == 0 for z in g4_lower))
check("B4 forceN4 is a subgroup of the carrier",
      all(mul(x, y) in forceN4 for x in list(forceN4)[:40] for y in list(forceN4)[:40]))
kill3_pre = commP(commP(fiveSigMark, forceU), forceY)
check("B5 gamma_3(image) contains an odd-m gamma_4-shaped element (the wider hole)",
      kill3_pre[:12] == tuple([0] * 12) and kill3_pre[12] % 2 == 1,
      f"[[sigMark,U],Y] = {kill3_pre}")

# ---------------------------------------------------------------- C the exclusion sweep

BAD = []
evens = [0, 2, 4, 6]
for z0m, z0n, z3m, z3n, z4m, z4n in product(evens, repeat=6):
    for w1o, w2o in product(range(M), repeat=2):
        inc = (
            (z0m * forceX[4] - z0n * forceX[0])
            + (-4 * w1o + 2 * w2o)
            + ((z3m * forceV[4] - z3n * forceV[0]) + (forceU[0] * z4n - forceU[4] * z4m))
        )
        if mod(7 + inc) == 0:
            BAD.append((z0m, z0n, z3m, z3n, z4m, z4n, w1o, w2o))
check("C1 no forceN4 refinement kills the dressed frame (262144 combinations)",
      not BAD, f"kills = {len(BAD)}")

# honest cross-check of the translation identity at 4000 random refinements
random.seed(60)


def five_lift_relator(v, z0, w1, w2, z3, z4):
    return relator_one_handle(
        mul(mul(fiveSigMark, v), z0),
        mul(forceX, w1),
        mul(forceY, w2),
        mul(forceU, z3),
        mul(forceV, z4),
    )


bad_id = 0
for _ in range(4000):
    z0 = random.choice(sorted(forceN4))
    z3 = random.choice(sorted(forceN4))
    z4 = random.choice(sorted(forceN4))
    w1 = liftC6(random.randrange(M))
    w2 = liftC6(random.randrange(M))
    inc = (
        (z0[12] * forceX[4] - z0[13] * forceX[0])
        + (-4 * w1[14] + 2 * w2[14])
        + ((z3[12] * forceV[4] - z3[13] * forceV[0]) + (forceU[0] * z4[13] - forceU[4] * z4[12]))
    )
    if five_lift_relator(forceX, z0, w1, w2, z3, z4) != mul(liftC6(7), liftC6(mod(inc))):
        bad_id += 1
check("C2 translation identity, 4000 honest refinements of the dressed point", bad_id == 0,
      f"mismatches = {bad_id}")

bad_kill = 0
for _ in range(4000):
    z0 = random.choice(sorted(forceN4))
    z3 = random.choice(sorted(forceN4))
    z4 = random.choice(sorted(forceN4))
    w1 = liftC6(random.randrange(M))
    w2 = liftC6(random.randrange(M))
    if five_lift_relator(forceX, z0, w1, w2, z3, z4) == ONE:
        bad_kill += 1
check("C3 honest sweep: no kill among 4000 random forceN4 refinements", bad_kill == 0,
      f"kills = {bad_kill}")

# the two negatives that bound the class from above
unrestricted = mk(m=1)
check("C4 the unrestricted gamma_4-move <m=1> DOES kill",
      five_lift_relator(forceX, unrestricted, ONE, ONE, ONE, ONE) == ONE)
check("C5 ... and is not in forceN4", unrestricted not in forceN4)
kill3 = commP(commP(fiveSigMark, forceU), forceY)
check("C6 the triple commutator [[sigma,U],x1] = <m=5,n=6> DOES kill",
      five_lift_relator(forceX, kill3, ONE, ONE, ONE, ONE) == ONE, f"kill3 = {kill3}")
check("C7 ... is gamma_4-shaped, lies in gamma_3(image) by construction, and is not in forceN4",
      kill3[:12] == tuple([0] * 12) and kill3 not in forceN4)

# ---------------------------------------------------------------- D non-vacuity witness

nontrivial = []
moving = []
for na, nb, nc, nd in product(sorted(LETTERS), repeat=4):
    z = commP(commP(commP(LETTERS[na], LETTERS[nb]), LETTERS[nc]), LETTERS[nd])
    if z != ONE:
        nontrivial.append(((na, nb, nc, nd), z))
        if (z[12], z[13]) != (0, 0):
            moving.append(((na, nb, nc, nd), z))
check("D1 nontrivial letterwise triple commutators exist", len(nontrivial) > 0,
      f"{len(nontrivial)} of {5 ** 4}")
check("D2 ... and some of them move the class-five residue", len(moving) > 0,
      f"{len(moving)} of {5 ** 4} have a non-zero class-four coordinate")

# the witness the Lean file exhibits: [[[V, U], x0], sigma] = <n = 2>
witness = commP(commP(commP(forceV, forceU), forceX), fiveSigMark)
check("D3 [[[V,U],x0],sigma] = <n=2>", witness == mk(n=2), f"witness = {witness}")
check("D4 the witness is an achievable dressing (lies in forceN4)", witness in forceN4)
wit_rel = five_lift_relator(forceX, witness, ONE, ONE, ONE, ONE)
check("D5 dressing the sigma slot by it MOVES the residue from 7 to 3 without killing it",
      wit_rel == liftC6(3), f"relator = {wit_rel}")

# ------------------------------------------------- G the SHARP class the forcing really needs
#
# The five-slot increment at this point is
#     z0.m * X.e - z0.n * X.a  +  (-4 w1.o + 2 w2.o)
#         + (z3.m * V.e - z3.n * V.a) + (U.a * z4.n - U.e * z4.m)
#   = z0.m - 2 z0.n - 4 w1.o + 2 w2.o + 2 z3.m + z4.n ,
# so only TWO of the six class-four coordinates of a five-slot refinement are load-bearing:
# z0.m and z4.n.  The Lean file states the forcing against that class, which is strictly
# larger than forceN4^3.

wrong_way, no_witness = 0, 0
for z0m, z0n, z3m, z4n, w1o, w2o in product(range(M), repeat=6):
    inc = z0m - 2 * z0n - 4 * w1o + 2 * w2o + 2 * z3m + z4n
    if mod(7 + inc) == 0 and (z0m + z4n) % 2 == 0:
        wrong_way += 1
for z0m, z0n, z3m, z4n in product(range(M), repeat=4):
    if (z0m + z4n) % 2 == 1:
        if not any(mod(7 + (z0m - 2 * z0n + 2 * w2o + 2 * z3m + z4n)) == 0 for w2o in range(M)):
            no_witness += 1
check("G1 no refinement with z0.m + z4.n EVEN kills (262144 combinations)", wrong_way == 0,
      f"kills = {wrong_way}")
check("G2 every refinement with z0.m + z4.n ODD is killed by some central w2, so the "
      "condition is a CHARACTERISATION", no_witness == 0, f"missing witnesses = {no_witness}")

sharp_rand = 0
rng_s = random.Random(6010)
for _ in range(4000):
    z0m = rng_s.randrange(M)
    z4n = (rng_s.randrange(M) * 2 - z0m) % M if (rng_s.randrange(2) or True) else 0
    if (z0m + z4n) % 2 == 1:
        z4n = mod(z4n + 1)
    z0 = mk(m=z0m, n=rng_s.randrange(M), o=rng_s.randrange(M))
    z3 = mk(m=rng_s.randrange(M), n=rng_s.randrange(M), o=rng_s.randrange(M))
    z4 = mk(m=rng_s.randrange(M), n=z4n, o=rng_s.randrange(M))
    w1 = liftC6(rng_s.randrange(M))
    w2 = liftC6(rng_s.randrange(M))
    if five_lift_relator(forceX, z0, w1, w2, z3, z4) == ONE:
        sharp_rand += 1
check("G3 honest sweep of the even-sum class, 4000 refinements, no kill", sharp_rand == 0,
      f"kills = {sharp_rand}")

check("G4 the condition is NECESSARY on the sigma side: <m=1> on the sigma slot kills",
      five_lift_relator(forceX, mk(m=1), ONE, ONE, ONE, ONE) == ONE)
check("G5 ... and on the handle-V side: <n=1> on the handle-V slot kills",
      five_lift_relator(forceX, ONE, ONE, ONE, ONE, mk(n=1)) == ONE)
check("G6 ⭐ but the two together do NOT kill: the sharp line is the SUM, residue 1",
      five_lift_relator(forceX, mk(m=1), ONE, ONE, ONE, mk(n=1)) == liftC6(1))
check("G7 the handle-U dressing z3 is UNCONSTRAINED: <m=1> there leaves residue 1",
      five_lift_relator(forceX, ONE, ONE, ONE, mk(m=1), ONE) == liftC6(1))
check("G8 z0.n is unconstrained: <n=1> on the sigma slot leaves residue 5",
      five_lift_relator(forceX, mk(n=1), ONE, ONE, ONE, ONE) == liftC6(5))
check("G9 z4.m is unconstrained: <m=1> on the handle-V slot leaves residue 7",
      five_lift_relator(forceX, ONE, ONE, ONE, ONE, mk(m=1)) == liftC6(7))
check("G10 z3.n never enters the relator at all (2000 random pairs)",
      all(five_lift_relator(forceX, ONE, ONE, ONE, mk(m=a, n=b), ONE)
          == five_lift_relator(forceX, ONE, ONE, ONE, mk(m=a, n=0), ONE)
          for a in range(M) for b in range(M)))

# --------------------------------- H the legal (lambda- and nu'-trivial) escape dressing
#
# The x0-generator is nu'-trivial but NOT lambda-trivial, so the wave-59 escape dressing is
# only half-legal.  A commutator is in the kernel of every character, and [x1, u_j] does the
# same job: purely central ODD residue, class-four blind.

legal = commP(forceY, forceU)
legal_rel = fiveWit_relator(legal)
check("H1 [x1, u_j] leaves the purely central residue liftC6 5", legal_rel == liftC6(5),
      f"relator = {legal_rel}")
check("H2 ... which is ODD, so it survives every even-sum refinement", legal_rel[14] % 2 == 1)
check("H3 ... and central, so both U_5-quotients of the relator are trivial",
      legal_rel[:14] == tuple([0] * 14))
legal_bad = 0
for z0m, z0n, z3m, z4n, w1o, w2o in product(range(M), repeat=6):
    if (z0m + z4n) % 2 == 0:
        inc = z0m - 2 * z0n - 4 * w1o + 2 * w2o + 2 * z3m + z4n
        if mod(5 + inc) == 0:
            legal_bad += 1
check("H4 no even-sum refinement kills the legal dressing (262144 combinations)",
      legal_bad == 0, f"kills = {legal_bad}")
half_legal = [(k, v) for k, v in
              [("[x0,u]", commP(forceX, forceU)), ("[x0,v]", commP(forceX, forceV)),
               ("[x0,x1]", commP(forceX, forceY)), ("[x1,u]", commP(forceY, forceU)),
               ("[x1,v]", commP(forceY, forceV)), ("[u,v]", commP(forceU, forceV)),
               ("[sig,u]", commP(fiveSigMark, forceU)), ("[sig,v]", commP(fiveSigMark, forceV)),
               ("[sig,x0]", commP(fiveSigMark, forceX)),
               ("[sig,x1]", commP(fiveSigMark, forceY))]]
central_odd = [k for k, v in half_legal
               if fiveWit_relator(v)[:14] == tuple([0] * 14) and fiveWit_relator(v)[14] % 2 == 1]
check("H5 [x1,u] is the unique letterwise commutator with a central ODD relator",
      central_odd == ["[x1,u]"], f"central odd commutator dressings: {central_odd}")

# ---------------------------------------------------------------- E the c-column

check("E1 every letter has an even c-column",
      all(v[2] % 2 == 0 for v in LETTERS.values()),
      ", ".join(f"{k}.c = {v[2]}" for k, v in sorted(LETTERS.items())))
rng_c = random.Random(605)
check("E2 every element of the image has an even c-column (20000 random words)",
      all(random_word(rng_c, 12)[2] % 2 == 0 for _ in range(20000)))
check("E3 forceU is the only letter with a non-zero c-column, and it is 2",
      [k for k, v in LETTERS.items() if v[2] != 0] == ["U"] and forceU[2] == 2)

# ---------------------------------------------------------------- F the pivot anchor


def flat_obstructions(g):
    (a, b, c, d, e, f, gg, h, i, j, k, l, m, n, o) = g
    return [
        ("a*b", mod(a * b)),
        ("b*c", mod(b * c)),
        ("c*d", mod(c * d)),
        ("d*e", mod(d * e)),
        ("a*g+f*c", mod(a * gg + f * c)),
        ("b*h+g*d", mod(b * h + gg * d)),
        ("c*i+h*e", mod(c * i + h * e)),
        ("a*k+f*h+j*d", mod(a * k + f * h + j * d)),
        ("b*l+g*i+k*e", mod(b * l + gg * i + k * e)),
        ("a*n+f*l+j*i+m*e", mod(a * n + f * l + j * i + m * e)),
    ]


obs = flat_obstructions(forceX)
check("F1 all ten flat obstructions vanish at forceX (the pivot lemma is FLAT here)",
      all(v == 0 for _, v in obs), ", ".join(f"{k} = {v}" for k, v in obs))

# the class-four x0-slot needs the even-obstruction lemma: recorded for contrast
sigFourX_like = "class four's sigFourX has a*i = 2, so its sixth obstruction is non-zero"

for cexp in [1, 3, 5, 7]:
    powX = mk(a=mod(2 * cexp), e=mod(cexp))
    pivot = mul(fiveSigMark, inv(powX))
    check(f"F2 pivot image at c = {cexp} is <a={mod(-2 * cexp)}, b=1, e={mod(-cexp)}>",
          pivot == mk(a=mod(-2 * cexp), b=1, e=mod(-cexp)), f"pivot = {pivot}")
    check(f"F3 pivot image at c = {cexp} is non-trivial (b = 1)", pivot != ONE)
    check(f"F4 displaced U-slot at c = {cexp} differs from forceU",
          mul(inv(pivot), forceU) != forceU)
    check(f"F5 displaced V-slot at c = {cexp} differs from forceV",
          mul(forceV, inv(pivot)) != forceV)

# ---------------------------------------------------------------- report

lines = []
lines.append("W60-HOM5 certificate: the class-five sigma forcing on `sqArbFrame`")
lines.append("=" * 78)
lines.append("")
lines.append("carrier: SqU6(Z/8), fifteen coordinates a..o, re-implemented from the group law")
lines.append("point:   fiveSigMark = <b=1>, forceX = <a=2,e=1>,")
lines.append("         forceY = <e=2,f=1,h=3,i=1,j=2,k=2,l=2,m=3,n=2,o=2>,")
lines.append("         forceU = <a=1,c=2,d=3,f=3,g=2,h=2,i=2>, forceV = <d=1,e=2,f=3,g=2,h=3,i=3>")
lines.append("")
nfail = 0
for name, ok, detail in results:
    tag = "PASS" if ok else "FAIL"
    if not ok:
        nfail += 1
    lines.append(f"[{tag}] {name}" + (f"   ({detail})" if detail else ""))
lines.append("")
lines.append(f"{len(results)} checks, {nfail} failures")
lines.append("")
lines.append("note: " + sigFourX_like)
lines.append(
    "non-vacuity witness: commP (commP (commP V U) x0) sigma = "
    + "<" + ", ".join(f"{IDX[t]}={witness[t]}" for t in range(15) if witness[t] != 0) + ">"
    + f", residue moves 7 -> {wit_rel[14]}"
)
lines.append(
    "wider-hole witness:  commP (commP sigma U) x1 = "
    + "<" + ", ".join(f"{IDX[t]}={kill3[t]}" for t in range(15) if kill3[t] != 0) + ">"
    + ", kills the dressed frame outright"
)
report = "\n".join(lines)
print(report)

import os

out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(out, exist_ok=True)
with open(os.path.join(out, "verify_frame5.txt"), "w") as fh:
    fh.write(report + "\n")
raise SystemExit(1 if nfail else 0)
