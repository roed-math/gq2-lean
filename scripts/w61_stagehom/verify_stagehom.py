"""W61-STAGEHOM verification: the class-five forcing, unconditional AND at the hom level.

Everything measured here is measured on the INDEPENDENT `6 x 6` matrix group of
`scripts/w59_force5/u6mat.py` (matrix multiplication, Gaussian back-substitution inverse),
cross-checked in section 0 against wave 58's independent coordinate library before any
measurement is taken.  Nothing is transcribed from a Lean file.

The Lean file this certifies is `GQ2/Dyadic/SqCore/GradedStageFrame.lean`.  The statements it
proves are about a continuous homomorphism on `D_sq h`; what a script can see is the tuple
arithmetic underneath, so the checks below are exactly the arithmetic facts the Lean proofs
consume plus the two censuses the docstring cites.

Sections:

  0  library cross-check
  A  the three verdicts at the new stage-four point, h = 1..4, every handle
  B  the pivot anchor: the ten flat obstructions at `stageX`, and the pivot image
  C  the wave-59 killing word at BOTH points, side by side
  D  the achievable stage-four lattice at the new point, and the exclusion re-run
  E  the legal-dressing census, EXHAUSTIVE over `gamma_2` of the image at both points
  F  the commutator repair, old point versus new point

BRACKET CONVENTION.  [PAPER-RAW]
This script builds RAW nested bracket sets, and its Lean target is written with commP,
so the paper convention is the right one to compute.  Raw bracket sets are the only
computations in this tree that can be wrong about the convention: check this line
before repointing the script at a [.,.]-written statement.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""
import os
import sys
import random

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w58_sigma5"))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w60_stage4"))

import u6mat as M                                                        # noqa: E402
import u6lib as L                                                        # noqa: E402
import modlib                                                            # noqa: E402

N = 8
ONE = M.ONE
CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append((name, bool(ok), detail))
    print(f"  [{'ok ' if ok else 'FAIL'}] {name}{('  ' + detail) if detail else ''}")


# ---------------------------------------------------------------- the two points

stageX = (2, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
stageY = (0, 0, 0, 0, 2, 1, 1, 1, 0, 0, 0, 0, 3, 3, 0)
stageU = (6, 7, 4, 1, 3, 0, 5, 5, 0, 0, 0, 0, 0, 0, 0)
stageV = (6, 7, 6, 1, 3, 5, 3, 3, 4, 0, 0, 0, 0, 0, 0)
forceX = (2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
forceY = (0, 0, 0, 0, 2, 1, 0, 3, 1, 2, 2, 2, 3, 2, 2)
forceU = (1, 0, 2, 3, 0, 3, 2, 2, 2, 0, 0, 0, 0, 0, 0)
forceV = (0, 0, 0, 1, 2, 3, 2, 3, 3, 0, 0, 0, 0, 0, 0)
SIG = (0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

STAGE = (stageX, stageY, stageU, stageV)
WAVE59 = (forceX, forceY, forceU, forceV)


def wit(pt, v, h=1, j=0):
    X, Y, U, V = pt
    return M.mirTuple(h, j, M.mul(SIG, v), X, Y, U, V)


def rel(pt, v, h=1, j=0):
    return M.sqRelWord(wit(pt, v, h, j))


def central(r):
    return all(x % N == 0 for x in r[:14])


# ---------------------------------------------------------------- 0 library cross-check

print("=== 0 library cross-check: u6mat (6x6 matrices) against u6lib (coordinates) ===")
random.seed(20260810)


def rnd():
    return tuple(random.randrange(N) for _ in range(15))


bad_mul = bad_inv = bad_rel = 0
for _ in range(3000):
    p, q = rnd(), rnd()
    if M.mul(p, q) != L.mul(p, q):
        bad_mul += 1
    if M.inv(p) != L.inv(p):
        bad_inv += 1
for _ in range(400):
    m = [rnd() for _ in range(5)]
    if M.sqRelWord(m) != L.sqRelWord(m):
        bad_rel += 1
check("0.1 the two libraries agree on 3000 random products", bad_mul == 0)
check("0.2 the two libraries agree on 3000 random inverses", bad_inv == 0)
check("0.3 the two libraries agree on 400 random relators", bad_rel == 0)

# ---------------------------------------------------------------- A the three verdicts

print()
print("=== A the three verdicts at the new stage-four point ===")
triv_ok = diag_ok = True
seen = 0
for h in range(1, 5):
    for j in range(h):
        seen += 1
        if rel(STAGE, ONE, h, j) != ONE:
            triv_ok = False
        if rel(STAGE, stageX, h, j) != tuple([0] * 14 + [1]):
            diag_ok = False
check(f"A.1 the undressed frame kills the relator at all {seen} (h, j) with h <= 4", triv_ok)
check(f"A.2 the x0-dressing leaves exactly <o = 1> at all {seen} (h, j)", diag_ok)
check("A.3 the residue is odd, so the selection bit separates",
      rel(STAGE, stageX)[14] % 2 == 1)
check("A.4 both U_5-quotients of the x0-dressed relator are trivial (class-four blind)",
      M.toU5L(rel(STAGE, stageX)) == (0,) * 10 and M.toU5R(rel(STAGE, stageX)) == (0,) * 10)

# ---------------------------------------------------------------- B the pivot anchor

print()
print("=== B the pivot anchor at the new point ===")
g = stageX
obs = [g[0] * g[1], g[1] * g[2], g[2] * g[3], g[3] * g[4],
       g[0] * g[6] + g[5] * g[2], g[1] * g[7] + g[6] * g[3], g[2] * g[8] + g[7] * g[4],
       g[0] * g[10] + g[5] * g[7] + g[9] * g[3],
       g[1] * g[11] + g[6] * g[8] + g[10] * g[4],
       g[0] * g[13] + g[5] * g[11] + g[9] * g[8] + g[12] * g[4]]
check("B.1 all ten flat obstructions vanish at stageX",
      all(x % N == 0 for x in obs), f"obstructions {[x % N for x in obs]}")
lin = True
for c in range(N):
    if M.power(stageX, c) != tuple((c * x) % N for x in stageX):
        lin = False
check("B.2 the x0-slot's powers are coordinatewise linear (flat)", lin)
piv = {c: M.mul(SIG, M.inv(M.power(stageX, c))) for c in range(N)}
check("B.3 the pivot image has b-coordinate 1 at every pivot residue",
      all(p[1] % N == 1 for p in piv.values()))
check("B.4 the pivot image is a = -2c, e = -5c",
      all(piv[c][0] % N == (-2 * c) % N and piv[c][4] % N == (-5 * c) % N for c in range(N)))
check("B.5 the pivot image is never trivial", all(p != ONE for p in piv.values()))

# ---------------------------------------------------------------- C the wave-59 kill word

print()
print("=== C the wave-59 killing word [[sigma, u_j], x1] at both points ===")
k59_old = M.commP(M.commP(SIG, forceU), forceY)
k59_new = M.commP(M.commP(SIG, stageU), stageY)
check("C.1 at wave 59's point its image is <m = 5, n = 6>",
      k59_old == tuple([0] * 12 + [5, 6, 0]), M.show(k59_old))
check("C.2 at the new point its image is <m = 2, n = 2, o = 4>",
      k59_new == tuple([0] * 12 + [2, 2, 4]), M.show(k59_new))
check("C.3 at wave 59's point it has an ODD class-four coordinate, so it is outside stageN3",
      k59_old[12] % 2 == 1)
check("C.4 at the new point j, l and m are all even, so it IS in stageN3",
      k59_new[9] % 2 == 0 and k59_new[11] % 2 == 0 and k59_new[12] % 2 == 0)


def dress_sigma(pt, v, z, h=1, j=0):
    m = list(wit(pt, v, h, j))
    m[0] = M.mul(m[0], z)
    return M.sqRelWord(m)


check("C.5 at wave 59's point it KILLS the x0-dressed frame",
      dress_sigma(WAVE59, forceX, k59_old) == ONE)
ok = all(dress_sigma(STAGE, stageX, k59_new, h, j) == tuple([0] * 14 + [7])
         for h in range(1, 5) for j in range(h))
check("C.6 at the new point it moves the residue 1 -> 7 and does NOT kill, at all h <= 4", ok)

# ---------------------------------------------------------------- the lattices


def gamma_module(letters, cap=6):
    """`gamma_3` of the image as a Z/8-module in the coordinates (j, k, l, m, n, o).

    `gamma_3` is abelian (`[gamma_3, gamma_3] <= gamma_6 = 1`) with coordinatewise addition, and
    `[-, c]` is a homomorphism on it, so the module is spanned by the triple commutators of the
    letters together with the iterated brackets of a basis against the letters.
    """
    rows = [list(M.commP(M.commP(a, b), c)[9:])
            for a in letters for b in letters for c in letters]
    B = modlib.howell(rows, 6)
    for _ in range(cap):
        extra = []
        for r in B:
            t = tuple([0] * 9 + list(r))
            for c in letters:
                extra.append(list(M.commP(t, c)[9:]))
        B2 = modlib.howell([list(r) for r in B] + extra, 6)
        if B2 == B:
            break
        B = B2
    return B


def module_members(B):
    return [tuple([0] * 9 + list(r)) for r in modlib.members(B, 6)]


def howell_reduce(B, v):
    """The canonical residue of `v` modulo the module with Howell basis `B`.

    Two vectors are congruent modulo the module exactly when their residues agree, which is
    what the Howell form exists for; that is what makes the coset enumeration below exact.
    """
    v = list(x % N for x in v)
    for r in B:
        c = next(i for i in range(6) if r[i] % N)
        p = r[c] % N
        q = v[c] // p
        if q:
            v = [(v[i] - q * r[i]) % N for i in range(6)]
    return tuple(v)


print()
print("=== D the achievable stage-four lattice at the new point, and the exclusion ===")
for name, pt in [("stage", STAGE), ("wave59", WAVE59)]:
    X, Y, U, V = pt
    letters = [SIG, X, Y, U, V]
    B3 = gamma_module(letters)
    mem3 = module_members(B3)
    print(f"  [{name}] |gamma_3(image)| = {len(mem3)}")
    if name == "stage":
        STAGE_G3 = mem3
        check("D.1 gamma_3 of the new point's image has order 8192, matching wave 60",
              len(mem3) == 8192, f"order {len(mem3)}")
        check("D.2 every achievable stage-four dressing has j, l, m even (the Lean chain)",
              all(z[9] % 2 == 0 and z[11] % 2 == 0 and z[12] % 2 == 0 for z in mem3))
        kills = [z for z in mem3 if dress_sigma(STAGE, stageX, z) == ONE]
        check("D.3 no achievable single-slot stage-four dressing kills the x0-dressed frame",
              len(kills) == 0, f"{len(kills)} of {len(mem3)} kill")
    else:
        WAVE_G3 = mem3
        kills = [z for z in mem3 if dress_sigma(WAVE59, forceX, z) == ONE]
        check("D.4 at wave 59's point achievable stage-four dressings DO kill",
              len(kills) > 0, f"{len(kills)} of {len(mem3)} kill")

random.seed(31415)
bad = 0
for _ in range(4000):
    z = [random.choice(STAGE_G3) for _ in range(5)]
    m = list(wit(STAGE, stageX))
    for i in range(5):
        m[i] = M.mul(m[i], z[i])
    if M.sqRelWord(m) == ONE:
        bad += 1
check("D.5 4000 random FIVE-slot achievable stage-four refinements kill nothing", bad == 0)

# ---------------------------------------------------------------- E the legal census

print()
print("=== E the legal-dressing census, exhaustive over gamma_2 of the image ===")
print("    A dressing that is legal for EVERY continuous nu' must lie in the commutator")
print("    subgroup, so its image lies in gamma_2 of the point's image.  The relator under a")
print("    gamma_2 sigma dressing has only j, l, m, n, o live, and gamma_2 = U coset reps x")
print("    gamma_3, so the census below is exhaustive rather than sampled.")

for name, pt in [("stage", STAGE), ("wave59", WAVE59)]:
    X, Y, U, V = pt
    letters = [SIG, X, Y, U, V]
    comms = [M.commP(a, b) for a in letters for b in letters if a != b]
    B3 = gamma_module(letters)
    mem3 = module_members(B3)

    # gamma_2(image) is the normal closure of the letter commutators, and conjugation acts
    # trivially modulo gamma_3(image), so gamma_2(image) = <letter commutators> * gamma_3(image).
    # Enumerating the products modulo gamma_3(image) is therefore an exact coset enumeration.
    def key_of(p):
        return (tuple(x % N for x in p[:9]), howell_reduce(B3, p[9:]))

    # the key is well defined on cosets: check it on random module elements
    random.seed(11)
    wd = True
    for _ in range(200):
        p = random.choice(comms)
        z = random.choice(mem3)
        if key_of(M.mul(p, z)) != key_of(p):
            wd = False
    check(f"E.0 [{name}] the coset key is constant on gamma_3(image)-cosets", wd)

    reps = {key_of(ONE): ONE}
    frontier = [ONE]
    acts = comms + [M.inv(c) for c in comms]
    while frontier:
        nxt = []
        for p in frontier:
            for c in acts:
                q = M.mul(p, c)
                k = key_of(q)
                if k not in reps:
                    reps[k] = q
                    nxt.append(q)
        frontier = nxt

    total = len(reps) * len(mem3)

    # `z |-> rel(c)^{-1} rel(c z)` is ADDITIVE on gamma_3(image), because the stage-four shift
    # is linear in the dressing there.  It is checked on random pairs and then used: the set of
    # residues reachable from the coset of `c` is `rel(c)` times the Z/8-span of the shift's
    # values on a basis, so the whole coset is settled by linear algebra rather than by
    # 8192 relator evaluations.
    def shift(c, r0inv, z):
        return M.mul(r0inv, rel(pt, M.mul(c, z)))

    add_ok = True
    random.seed(97)
    for _ in range(60):
        c = random.choice(list(reps.values()))
        r0inv = M.inv(rel(pt, c))
        z1, z2 = random.choice(mem3), random.choice(mem3)
        zs = tuple((z1[k] + z2[k]) % N for k in range(15))
        s1, s2 = shift(c, r0inv, z1), shift(c, r0inv, z2)
        if shift(c, r0inv, zs) != tuple((s1[k] + s2[k]) % N for k in range(15)):
            add_ok = False
    check(f"E.a [{name}] the coset shift is additive in the dressing (60 random pairs)", add_ok)

    hits = []
    live_cosets = 0
    for c in reps.values():
        r0 = rel(pt, c)
        # the class-three rows j, k, l of the relator do not move under a gamma_3 dressing of
        # the sigma slot beyond the dressing's own, so they must already vanish
        if r0[9] % N or r0[10] % N or r0[11] % N:
            continue
        live_cosets += 1
        r0inv = M.inv(r0)
        Bs = modlib.howell([list(shift(c, r0inv, tuple([0] * 9 + list(r)))[9:]) for r in B3], 6)
        # the Howell rows with vanishing (j, k, l) span exactly the shifts that keep the
        # relator's class-three rows dead; at most three of them, so the residues are enumerable
        tail = modlib.sub_zero_prefix(Bs, 3)
        for d in modlib.members(tail, 6) if tail else [(0,) * 6]:
            if (d[3] + r0[12]) % N == 0 and (d[4] + r0[13]) % N == 0 \
                    and (d[5] + r0[14]) % 2 == 1:
                hits.append((c, d))
    print(f"  [{name}] |gamma_2/gamma_3| = {len(reps)}, |gamma_3| = {len(mem3)}, "
          f"|gamma_2(image)| = {total}; cosets whose class-three rows vanish: {live_cosets}; "
          f"central-and-odd dressings: {len(hits)}")
    if name == "stage":
        check("E.1 gamma_2 of the new point's image has order 67108864 and is exhausted by the "
              "coset decomposition", total == 67108864, f"order {total}")
        check("E.2 universally legal dressings leaving a CENTRAL ODD residue DO exist at the "
              "new point", len(hits) == 1024, f"{len(hits)} of {total}")
        # the explicit two-commutator witness the Lean file carries
        wit_new = M.mul(M.commP(stageY, stageV), M.inv(M.commP(stageY, stageU)))
        r_new = rel(STAGE, wit_new)
        check("E.5 [x1, v_j] * [x1, u_j]^-1 is one of them, with residue <o = 5>",
              central(r_new) and r_new[14] % N == 5, M.show(r_new))
        ok = all(rel(STAGE, wit_new, h, j) == tuple([0] * 14 + [5])
                 for h in range(1, 5) for j in range(h))
        check("E.6 …at every handle count and handle up to h = 4", ok)
        check("E.7 …and the single commutator [x1, u_j] is NOT one of them",
              not central(rel(STAGE, M.commP(stageY, stageU))))
    else:
        check("E.3 at wave 59's point such dressings also exist", len(hits) > 0,
              f"{len(hits)} of {total}")
        rep59 = M.commP(forceY, forceU)
        r59 = rel(WAVE59, rep59)
        check("E.4 and there the SINGLE commutator [x1, u_j] is one of them",
              central(r59) and r59[14] % 2 == 1, M.show(r59))

# ---------------------------------------------------------------- F the commutator repair

print()
print("=== F wave 60's commutator repair [x1, u_j], old point versus new point ===")
rep_old = M.commP(forceY, forceU)
rep_new = M.commP(stageY, stageU)
r_old = rel(WAVE59, rep_old)
r_new = rel(STAGE, rep_new)
check("F.1 at wave 59's point the repair leaves the purely central odd residue <o = 5>",
      central(r_old) and r_old[14] % N == 5, M.show(r_old))
check("F.2 at the new point the SAME group element leaves <m = 4, n = 2, o = 5>",
      r_new == tuple([0] * 12 + [4, 2, 5]), M.show(r_new))
check("F.3 the new residue is still ODD at class five, so the exclusion applies to it",
      r_new[14] % 2 == 1)
check("F.4 but it is NOT central, so the left U_5-quotient is non-trivial and class four "
      "sees it", M.toU5L(r_new) != (0,) * 10)
ok = all(rel(STAGE, rep_new, h, j) == tuple([0] * 12 + [4, 2, 5])
         for h in range(1, 5) for j in range(h))
check("F.5 the new residue is the same at every handle count and handle up to h = 4", ok)
check("F.6 the two-commutator replacement restores BOTH halves at the new point: central and "
      "odd", central(rel(STAGE, M.mul(M.commP(stageY, stageV),
                                      M.inv(M.commP(stageY, stageU)))))
      and rel(STAGE, M.mul(M.commP(stageY, stageV),
                           M.inv(M.commP(stageY, stageU))))[14] % 2 == 1)

# ---------------------------------------------------------------- summary

print()
fails = [n for n, ok, _ in CHECKS if not ok]
print(f"=== {len(CHECKS)} named checks, {len(fails)} failures ===")
for n in fails:
    print(f"  FAILED: {n}")
