"""W59-FORCE5 step 2: how far the exclusion reaches, and where it stops.

The Lean forcing dresses the sigma and handle slots by achievable `gamma_4`-elements and the
two exponent slots by achievable `gamma_5`-elements: the exact transposition of the committed
`GradedSigmaFour.sigFourWit_sigma_forced`, whose dressings are `gamma_3` and `gamma_4` one
class down.  `verify_force5.py` found that WIDER moves - achievable `gamma_3`-dressings, which
are stage-FOUR moves and do disturb the class-four rows - can kill the dressed frame.  This
script pins that down:

  A. which slots those killing `gamma_3`-moves act on, and what they look like;
  B. whether the committed class-FOUR point has the same property one class down, i.e. whether
     an achievable `gamma_2`-dressing rescues the odd dressing `sigFourU` that
     `GradedSigmaFour.sqRelWord_sigFourWit_U_ne_one` excludes.

If B behaves like A the finding is a property of the campaign's stage convention, not of this
wave's point.
"""
import sys
import os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w58_sigma5"))

import u6mat as M                                             # noqa: E402
import u6lib as W58                                           # noqa: E402


def note(s):
    print("   " + s)


def subgroup(seeds, conj_gens, mul, conjP, inv, one):
    seen = {one}
    gens = []
    for s in sorted({t for t in seeds if t != one}):
        if s in seen:
            continue
        gens.append(s)
        gens.append(inv(s))
        changed = True
        while changed:
            changed = False
            for p in list(seen):
                for g in gens:
                    q = mul(p, g)
                    if q not in seen:
                        seen.add(q)
                        changed = True
                for c in conj_gens:
                    q = conjP(p, c)
                    if q not in seen:
                        seen.add(q)
                        changed = True
    return seen


# =========================================================================================
print("== A. the class-five point: which gamma_3-moves kill the dressed frame ==")
sigma, X, Y, U, V = M.sigFiveMark, M.sepX, M.sepY, M.sepU, M.sepV
letters = [sigma, X, Y, U, V]
base = [W58.mul(sigma, X), X, Y, U, V]

g3 = subgroup([W58.commP(W58.commP(a, b), c)
               for a in letters for b in letters for c in letters], letters,
              W58.mul, W58.conjP, W58.inv, M.ONE)
note("|gamma_3 of the image| = %d" % len(g3))
SLOT = ["sigma", "x0", "x1", "U", "V"]
for i in range(5):
    kills = []
    for z in sorted(g3):
        m = list(base)
        m[i] = W58.mul(m[i], z)
        if W58.sqRelWord(m) == M.ONE:
            kills.append(z)
    note("slot %-5s : %5d of %5d achievable gamma_3-dressings kill the frame"
         % (SLOT[i], len(kills), len(g3)))
    if kills:
        note("            e.g. %s" % ", ".join(M.show(z) for z in kills[:3]))
        note("            (all of them move the class-four rows: %s)"
             % ("yes" if all(z[12] % 2 or z[13] % 2 or z[9] or z[10] or z[11]
                             for z in kills) else "not all"))
print()
note("A gamma_3-dressing is a stage-FOUR move: it changes the class-four rows of the relator,")
note("which the stage-four verdict has already fixed.  The class-five forcing quantifies over")
note("stage-FIVE moves, exactly as the committed class-four forcing quantifies over stage-four")
note("ones.  The question B settles is whether the committed class-four statement has the same")
note("shape of caveat one class down.")

# =========================================================================================
print()
print("== B. the committed class-four point, one class down ==")

# --- an independent U_5 library, same construction as u6mat ------------------------------
POS5 = [(1, 2), (2, 3), (3, 4), (4, 5), (1, 3), (2, 4), (3, 5), (1, 4), (2, 5), (1, 5)]
ONE5 = (0,) * 10
N = 8


def mat5(p):
    A = [[0] * 5 for _ in range(5)]
    for r in range(5):
        A[r][r] = 1
    for k, (i, j) in enumerate(POS5):
        A[i - 1][j - 1] = p[k] % N
    return A


def tup5(A):
    return tuple(A[i - 1][j - 1] % N for (i, j) in POS5)


def mmul5(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(5)) % N for j in range(5)] for i in range(5)]


def minv5(A):
    Xm = [[0] * 5 for _ in range(5)]
    for j in range(5):
        for i in range(j, -1, -1):
            rhs = (1 if i == j else 0) - sum(A[i][k] * Xm[k][j] for k in range(i + 1, 5))
            Xm[i][j] = rhs % N
    return Xm


def mul5(p, q):
    return tup5(mmul5(mat5(p), mat5(q)))


def inv5(p):
    return tup5(minv5(mat5(p)))


def pow5(p, k):
    r = ONE5
    for _ in range(k):
        r = mul5(r, p)
    return r


def conjP5(p, g):
    return mul5(mul5(inv5(g), p), g)


def commP5(p, q):
    return mul5(mul5(inv5(p), inv5(q)), mul5(p, q))


def sqWord5(s, x, y):
    return mul5(mul5(mul5(inv5(conjP5(x, s)), inv5(pow5(x, 3))), pow5(y, 2)),
                commP5(y, conjP5(y, s)))


def sqRelWord5(m):
    h = (len(m) - 3) // 2
    r = sqWord5(m[0], m[1], m[2])
    for k in range(h):
        r = mul5(r, commP5(m[3 + 2 * k], m[4 + 2 * k]))
    return r


def show5(p):
    nm = "abcdefghij"
    parts = ["%s=%d" % (nm[k], p[k]) for k in range(10) if p[k]]
    return "<" + ", ".join(parts) + ">" if parts else "<1>"


# GradedSigmaFour's committed binder point (SqU5 coordinates a,b,c,d,e,f,g,h,i,j)
sigFourMark = (0, 1, 0, 0, 0, 0, 0, 0, 0, 0)
sigFourU = (1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
sigFourV = (2, 0, 0, 0, 0, 0, 0, 0, 0, 0)
sigFourX = (2, 0, 0, 0, 0, 0, 0, 0, 1, 0)
sigFourY = (0, 0, 0, 0, 1, 0, 4, 0, 2, 0)
letters4 = [sigFourMark, sigFourX, sigFourY, sigFourU, sigFourV]
base4triv = [sigFourMark, sigFourX, sigFourY, sigFourU, sigFourV]
base4odd = [mul5(sigFourMark, sigFourU), sigFourX, sigFourY, sigFourU, sigFourV]
note("committed verdicts, re-derived: undressed relator = %s, sigFourU-dressed = %s"
     % (show5(sqRelWord5(base4triv)), show5(sqRelWord5(base4odd))))

g2four = subgroup([commP5(a, b) for a in letters4 for b in letters4], letters4,
                  mul5, conjP5, inv5, ONE5)
note("|gamma_2 of the class-four image| = %d" % len(g2four))
tot = 0
for i in range(5):
    kills = []
    for z in sorted(g2four):
        m = list(base4odd)
        m[i] = mul5(m[i], z)
        if sqRelWord5(m) == ONE5:
            kills.append(z)
    tot += len(kills)
    note("slot %-5s : %4d of %4d achievable gamma_2-dressings kill the ODD class-four frame"
         % (SLOT[i], len(kills), len(g2four)))
    if kills:
        note("            e.g. %s" % ", ".join(show5(z) for z in kills[:3]))
print()
if tot:
    note("=> The committed class-four exclusion `sqRelWord_sigFourWit_U_ne_one` has EXACTLY the")
    note("   same caveat: a stage-THREE move (a gamma_2-dressing) rescues the odd dressing it")
    note("   excludes.  The class-five statement of this wave is therefore no weaker than the")
    note("   class-four one it transposes; the scope is the campaign's stage convention, not a")
    note("   defect of this point.")
else:
    note("=> The committed class-four exclusion survives gamma_2-dressings, so the class-five")
    note("   statement IS weaker than its class-four model, and that must be said out loud.")
