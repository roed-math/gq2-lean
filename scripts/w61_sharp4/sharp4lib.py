"""W61-SHARP4: the STAGE-FOUR sharp-line engine.

Everything runs on `scripts/w59_force5/u6mat.py`, the independent `U_6(Z/8)` library built
from honest 6 x 6 matrices, and on `scripts/w60_stage4/modlib.py`, the Howell-form module
engine wave 60 validated against honest element-by-element closure.  No group law and no
translation identity is re-implemented here: every stage-four shift is read off as

    shift(m, z) = sqRelWord(m)^{-1} * sqRelWord(m dressed by z)

through the honest matrices, so nothing derived in Lean is trusted by the measurement.

What is added:

* `gamma3_basis(letters)`: a Howell basis of `gamma_3(im)` inside `(Z/8)^6` on the coordinates
  `(j, k, l, m, n, o)`, that is, the achievable STAGE-FOUR dressings;
* `slot_matrix(m, i)`: the `6 x 6` matrix over `Z/8` of the slot-`i` shift map, obtained by
  dressing that slot with each of the six unit `gamma_3`-elements;
* `image_basis(m, L)`: a Howell basis of the module of ALL achievable five-slot shifts, i.e.
  the exact image of the achievable tuple lattice;
* `kill_exists`, `orth_all` (the parity line on the whole lattice) and `orth_central` (the
  parity line on the CENTRALLY ACTING tuples only), the three verdicts the census compares;
* `covector(m, i)`: the five mod-2 entries `(j, k, l, m, n)` of a slot's covector, read off the
  honest shift map, plus `covector_formula(...)`, the same thing transcribed from
  `GradedFiveStageFour` so that the two can be compared.

Coordinates: index 0..14 = a b c d e | f g h i | j k l | m n | o.
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w60_stage4"))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w60_sharp5"))

import u6mat as M                                                      # noqa: E402
import modlib as MD                                                    # noqa: E402
import pointlib as PL                                                  # noqa: E402
import sharp5lib as S5                                                 # noqa: E402

N = 8
ONE = M.ONE

IA, IB, IC, ID, IE = 0, 1, 2, 3, 4
IF, IG, IH, II = 5, 6, 7, 8
IJ, IK, IL = 9, 10, 11
IM, IN, IO = 12, 13, 14

G3IDX = [IJ, IK, IL, IM, IN, IO]                       # the six live coordinates of gamma_3
SLOT = ["sigma", "x0", "x1", "U", "V"]


# ---- the committed point ----------------------------------------------------------------

stageX = M.named(a=2, e=5)
stageY = M.named(e=2, f=1, g=1, h=1, m=3, n=3)
stageU = M.named(a=6, b=7, c=4, d=1, e=3, g=5, h=5)
stageV = M.named(a=6, b=7, c=6, d=1, e=3, f=5, g=3, h=3, i=4)
sigMark = M.named(b=1)


def stage_point():
    """The wave-60 stage-four witness, `a0 = a1`-dressed: the marking the forcing is about."""
    return [M.mul(sigMark, stageX), stageX, stageY, stageU, stageV]


def wave59_point():
    """Wave 59's binder point, `a0 = a1`-dressed (`u6mat`'s `sep*` letters)."""
    return [M.mul(sigMark, M.sepX), M.sepX, M.sepY, M.sepU, M.sepV]


# ---- gamma_3 of the image, as a Z/8-module ----------------------------------------------

def vec(z):
    """The (j,k,l,m,n,o)-vector of a gamma_3-shaped carrier element."""
    return tuple(z[k] % N for k in G3IDX)


def elt(v):
    """...and back."""
    t = [0] * 15
    for i, k in enumerate(G3IDX):
        t[k] = v[i] % N
    return tuple(t)


def gamma3_gens(letters):
    """Generators of `gamma_3(im)`: `[[a,b],c]` and its two further brackets.

    Legitimate because `[-, c]` is a homomorphism on `gamma_3` of a class-five carrier
    (`[gamma_3, gamma_3] <= gamma_6 = 1`), which is `SqU6.gaThree_comm`.  `validate_sharp4.py`
    section 0 checks the resulting cardinality against `pointlib`'s honest closure.
    """
    t3 = {M.commP(M.commP(a, b), c) for a in letters for b in letters for c in letters}
    t4 = {M.commP(z, c) for z in t3 for c in letters}
    t5 = {M.commP(z, c) for z in t4 for c in letters}
    gens = t3 | t4 | t5
    assert all(all(z[k] == 0 for k in range(9)) for z in gens), "not gamma_3-shaped"
    return [vec(z) for z in gens]


def gamma3_basis(letters):
    return MD.howell(gamma3_gens(letters), 6)


def members(basis, ncols=6):
    return MD.members(basis, ncols)


# ---- the honest stage-four shift ---------------------------------------------------------

def relator(m):
    return M.sqRelWord(list(m))


def dress(m, i, w):
    mm = list(m)
    mm[i] = M.mul(mm[i], elt(w) if isinstance(w, tuple) and len(w) == 6 else w)
    return mm


def shift(m, zs):
    """The honest stage-four shift of a five-slot dressing `zs` (a list of 6-vectors)."""
    mm = list(m)
    for i, w in enumerate(zs):
        mm[i] = M.mul(mm[i], elt(w))
    r = M.sqRelWord(list(m))
    return vec(M.mul(M.inv(r), M.sqRelWord(mm)))


def slot_shift(m, i, w):
    """The honest shift when slot `i` alone is dressed by the gamma_3-element `w`."""
    zs = [(0,) * 6] * len(m)
    zs[i] = w
    return shift(m, zs)


UNIT = [tuple(1 if t == s else 0 for t in range(6)) for s in range(6)]


def slot_matrix(m, i):
    """Rows = the images of the six unit gamma_3-elements under the slot-`i` shift map."""
    return [slot_shift(m, i, u) for u in UNIT]


def apply_matrix(mat, w):
    return tuple(sum(w[s] * mat[s][t] for s in range(6)) % N for t in range(6))


# ---- the three verdicts -------------------------------------------------------------------

def image_basis(m, L):
    """A Howell basis of the module of ALL achievable five-slot stage-four shifts.

    The shift map is `Z/8`-linear in the dressing tuple and additive across slots (both
    checked in `validate_sharp4.py`), so the image of the achievable tuple lattice `L^5` is
    spanned by the slot images of a basis of `L`.
    """
    gens = []
    for i in range(len(m)):
        mat = slot_matrix(m, i)
        for g in L:
            gens.append(apply_matrix(mat, g))
    return MD.howell(gens, 6)


def central_basis(basis):
    """The achievable shifts that are CENTRAL: the five lower rows vanish."""
    return MD.sub_zero_prefix(basis, 5)


def reachable_o(basis):
    """The subgroup of `Z/8` of class-five residues reachable by a CENTRAL achievable shift."""
    rows = [r[5] for r in central_basis(basis)]
    g = 0
    for r in rows:
        g = _gcd8(g, r)
    return {(g * t) % N for t in range(N)} if g else {0}


def _gcd8(a, b):
    while b:
        a, b = b, a % b
    return a % N


def kill_exists(m, L=None, basis=None):
    """Does SOME achievable five-slot stage-four dressing kill the relator?

    Exact, not sampled: the relator must be gamma_3-shaped, and then the kill condition is
    membership of `-relator` in the image module.
    """
    r = relator(m)
    if any(r[k] for k in range(9)):
        return False                                    # not gamma_3-shaped: no shift can match
    if basis is None:
        basis = image_basis(m, L)
    return in_module(basis, tuple((-r[k]) % N for k in G3IDX))


def in_module(basis, v):
    """Membership in the Z/8-module with the given Howell basis."""
    v = list(x % N for x in v)
    for r in basis:
        c = next((i for i in range(len(v)) if r[i] % N), None)
        if c is None or v[c] % N == 0:
            continue
        piv = r[c] % N
        # solve q * piv = v[c] in Z/8; piv = 2^t * unit
        t = MD.val2(piv)
        if MD.val2(v[c]) < t:
            return False
        u = piv >> t
        q = ((v[c] >> t) * MD.INV[u]) % (N >> t)
        v = [(v[i] - q * r[i]) % N for i in range(len(v))]
    return not any(v)


def orth_all(m, L):
    """THE PARITY LINE ON THE WHOLE LATTICE: every achievable stage-four dressing moves the
    class-five row by an EVEN amount.  Equivalently all five slot covectors annihilate the
    parity image of the achievable lattice."""
    for i in range(len(m)):
        mat = slot_matrix(m, i)
        for g in L:
            if apply_matrix(mat, g)[5] % 2:
                return False
    return True


def orth_central(m, L=None, basis=None):
    """THE PARITY LINE ON THE CENTRALLY ACTING TUPLES: every achievable dressing whose shift
    is CENTRAL moves the class-five row by an even amount."""
    if basis is None:
        basis = image_basis(m, L)
    return all(r[5] % 2 == 0 for r in central_basis(basis))


def orth_gafour(m, L):
    """The parity line restricted to the gamma_4-SHAPED achievable dressings, i.e. wave 60's
    class-five covector condition applied to the gamma_4-shaped part of gamma_3(im).

    A gamma_4-shaped dressing acts CENTRALLY (its two class-four pairings vanish), so this is
    NECESSARY for the forcing; the census measures whether it is sufficient."""
    sub = MD.sub_zero_prefix(L, 3)
    for i in range(len(m)):
        mat = slot_matrix(m, i)
        for g in sub:
            if apply_matrix(mat, g)[5] % 2:
                return False
    return True


def row_covectors(m, i):
    """The slot-`i` mod-2 covectors of the shift's class-four rows `m`, `n` and its class-five
    row `o`, each a functional on the dressing's `(j, k, l, m, n)`."""
    mat = slot_matrix(m, i)
    return (tuple(mat[s][3] % 2 for s in range(5)),
            tuple(mat[s][4] % 2 for s in range(5)),
            tuple(mat[s][5] % 2 for s in range(5)))


def total_matrix(m):
    """The `(6 * slots) x 6` matrix over `Z/8` of the whole five-slot stage-four shift map:
    row `(i, s)` is the shift produced by dressing slot `i` by the unit `gamma_3`-element on
    coordinate `s`."""
    return [row for i in range(len(m)) for row in slot_matrix(m, i)]


def central_kernel(m):
    """A generating set of the module of `gamma_3`-dressing TUPLES whose shift is CENTRAL,
    with no achievability assumed.

    Computed as the kernel of the five lower rows by the standard augmented-Howell route:
    the row span of `[Psi | I]` intersected with `{prefix = 0}` is `{(0, v) : v Psi = 0}`, and
    the Howell property is exactly that the zero-prefix rows generate that intersection.
    """
    rows = total_matrix(m)
    d = len(rows)
    aug = [tuple(list(rows[t][:5]) + [1 if s == t else 0 for s in range(d)])
           for t in range(d)]
    basis = MD.howell(aug, 5 + d)
    return [r[5:] for r in MD.sub_zero_prefix(basis, 5)]


def orth_central_unrestricted(m):
    """THE ACHIEVABILITY-FREE FORM OF THE SHARP LINE: EVERY `gamma_3`-dressing tuple whose
    shift is central - achievable or not - moves the class-five row by an even amount.

    This is the stage-four analogue of wave 60's orthogonal point: where it holds, the forcing
    holds with no lower-central-series hypothesis at all.  It is weaker than `modlow`, which
    asks the class-five row to be a mod-2 combination of the class-four rows: an EVEN
    class-four row forces its coordinate even over `Z/8` while saying nothing mod 2.
    """
    rows = total_matrix(m)
    for v in central_kernel(m):
        if sum(v[t] * rows[t][5] for t in range(len(rows))) % 2:
            return False
    return True


def modlow(m):
    """THE SECOND, ACHIEVABILITY-FREE SUFFICIENT CONDITION: the class-five row is congruent
    mod 2 to a FIXED combination of the two class-four rows, uniformly over the slots.

    Then any dressing whatsoever - achievable or not - that kills the class-four rows leaves
    the class-five row even, and a kill has to kill them because the relator is central.  The
    class-three rows carry the Frobenius weights `(-4, 2)` and are even for free, so they never
    enter.  Returns the set of `(lam_m, lam_n)` that work, empty if none does.
    """
    out = []
    covs = [row_covectors(m, i) for i in range(len(m))]
    for lm in (0, 1):
        for ln in (0, 1):
            if all(all((cm[s] * lm + cn[s] * ln - co[s]) % 2 == 0 for s in range(5))
                   for (cm, cn, co) in covs):
                out.append((lm, ln))
    return out


# ---- what wave 60 carries -----------------------------------------------------------------

def stageN1_all(letters):
    """W60-HYP: every letter has an even `(1,2)`-column and an even `(3,4)`-column."""
    return all(g[IA] % 2 == 0 and g[IC] % 2 == 0 for g in letters)


def stageN3_all(L):
    """W60-CONS: every achievable stage-four dressing has `j`, `l` and `m` even."""
    return all(r[0] % 2 == 0 and r[2] % 2 == 0 and r[3] % 2 == 0 for r in L)


# ---- the covectors ------------------------------------------------------------------------

def covector(m, i):
    """The slot-`i` mod-2 covector, read off the HONEST shift map: the parities of the
    class-five row produced by the five unit dressings `j`, `k`, `l`, `m`, `n`."""
    return tuple(slot_shift(m, i, UNIT[s])[5] % 2 for s in range(5))


def covector_formula(m, i, h=1, jj=0):
    """The same covector, transcribed from `GradedFiveStageFour`'s `gaThreeCore`,
    `gaThreeCorr` and `gaThreeHandle`, reduced mod 2.  Compared with `covector` in
    `validate_sharp4.py`; the two are computed by completely different routes."""
    s, x, y = m[0], m[1], m[2]
    U, V = m[3 + 2 * jj], m[4 + 2 * jj]

    def pair(L):
        """gaThreePair's mod-2 covector on (j, k, l, m, n) against the letter L."""
        return [L[II] % 2, (L[IA] * L[IE]) % 2, (L[IF] + L[IA] * L[IB]) % 2,
                L[IE] % 2, L[IA] % 2]

    if i == 0:                                          # sigma slot, against the x0-letter
        c = pair(x)
        c[0] += s[ID] * x[IE] + s[IE] * x[ID] + y[ID] * y[IE]
        c[2] += s[IA] * x[IB] + s[IB] * x[IA] + y[IA] * y[IB]
    elif i == 1:                                        # x0-slot, against the Fox letter
        F = tuple((10 * x[k] - s[k] - 8 * y[k]) % N for k in range(15))
        c = pair(F)
        c[0] += s[ID] * x[IE] + s[IE] * x[ID]
        c[2] += s[IA] * x[IB] + s[IB] * x[IA]
    elif i == 2:                                        # x1-slot, against the x1-letter
        c = pair(y)
        c[0] += s[IE] * y[ID]
        c[1] += s[IA] * y[IE] + s[IE] * y[IA]
        c[2] += s[IA] * y[IB]
    elif i == 3 + 2 * jj:                               # handle-U dressing, against V
        c = pair(V)
        c[0] += U[ID] * V[IE] + U[IE] * V[ID]
        c[2] += U[IA] * V[IB] + U[IB] * V[IA]
    elif i == 4 + 2 * jj:                               # handle-V dressing, against U
        c = pair(U)
        c[0] += U[ID] * V[IE] + U[IE] * V[ID]
        c[2] += U[IA] * V[IB] + U[IB] * V[IA]
    else:
        c = [0] * 5
    return tuple(v % 2 for v in c)


# ---- admissible markings ------------------------------------------------------------------

def admissible(m):
    """The census condition, wave 60's verbatim (`sharp5lib.admissible`): the relator is a
    CENTRAL translation with an ODD class-five residue, which is the situation the stage-four
    forcing is about."""
    return S5.admissible(*m)


def solve_y(sigma, X, U, V, want=1, budget=1200):
    """Every `x1`-slot value making the marking admissible: wave 60's layered solve
    (`sharp5lib.solve_Y`), imported rather than re-implemented."""
    return S5.solve_Y(sigma, X, U, V, want=want, odd_only=True, budget=budget)


def show(p):
    return M.show(p)
