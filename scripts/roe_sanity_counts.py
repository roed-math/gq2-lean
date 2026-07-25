#!/usr/bin/env python3
"""roe_sanity_counts.py  --  R5 numerical cross-check harness for GQ2/Roe/Sanity.lean.

Independent brute-force recount of the Roe-candidate admissible-marking count
`admissibleCountR G = |Sur(Γ_R, G)|` for small finite groups, using **exactly the Lean
conventions** of `GQ2/Roe/Words.lean`:

    conjP x g   = g⁻¹ * x * g                 (Lean `conjP`,  g^h = h⁻¹gh)
    commP x y   = x⁻¹ * y⁻¹ * x * y           (Lean `commP`,  [x,y])
    powOmega2 x = x ^ omega2Exp(orderOf x)    (2-primary part; = id on a 2-group)
    aR          = powOmega2 ((x₀^3)⁻¹ * τ)
    y1R         = conjP x₁ (powOmega2 σ)
    cR          = commP x₁ y1R
    wildValueR  = (conjP x₀ σ)⁻¹ * aR * x₁^2 * cR
    AdmissibleR = Generates ∧ TameRel ∧ WildRelR ∧ Pro2Core
      TameRel   : conjP τ σ = τ^2
      WildRelR  : wildValueR = 1
      Generates : ⟨σ,τ,x₀,x₁⟩ = G
      Pro2Core  : normal closure of {x₀,x₁} is a 2-group  (⇔ x₀,x₁ ∈ O₂(G))

The June archive `~/claude/q2_galois_presentation` counts the *opposite-handed* problem
(g^h = hgh⁻¹, tame s t s⁻¹ = t², wild via `H.conj(a,s)=sas⁻¹`).  The relabelling
σ ↦ σ⁻¹ is a bijection archive-admissible ↔ Lean-admissible fixing τ,x₀,x₁,Generates,
Pro2Core, so the two counts are EQUAL.  To make that concrete this script computes the
count in BOTH conventions and asserts they agree, then prints the comparison against the
hard-coded June `|Sur(Γ_R, ·)|` values (final_validation.log / lmfdb_counts.json).

No Sage / GAP needed: explicit multiplication tables, exponent-`e` (= 1 on 2-groups)
form of ω₂.  Run:  python3 scripts/roe_sanity_counts.py
"""

from itertools import product


# ----------------------------------------------------------------------------- ω₂ exponent
def omega2_exp(n: int) -> int:
    """GQ2.omega2Exp: representative e of ω₂ mod n (e≡1 mod 2^{v₂n}, e≡0 mod oddpart)."""
    if n <= 0:
        return 0
    a = 0
    m = n
    while m % 2 == 0:
        m //= 2
        a += 1
    if a == 0:
        return 0
    odd = n // (2 ** a)
    return pow(odd, 2 ** (a - 1), n)


# ----------------------------------------------------------------------------- group model
class Grp:
    """Finite group by explicit element list + multiplication (indices)."""

    def __init__(self, name, elems, mul, inv, one):
        self.name = name
        self.elems = elems                    # list of hashable labels
        self.n = len(elems)
        self.idx = {g: i for i, g in enumerate(elems)}
        self.mul = mul                        # mul[i][j] -> index
        self.inv = inv                        # inv[i] -> index
        self.one = one                        # identity index
        self.order = [self._order(i) for i in range(self.n)]

    def _order(self, i):
        k, x = 1, i
        while x != self.one:
            x = self.mul[x][i]
            k += 1
        return k

    def m(self, *xs):
        acc = self.one
        for x in xs:
            acc = self.mul[acc][x]
        return acc

    def powr(self, i, k):
        k %= self.order[i]
        r, base = self.one, i
        while k:
            if k & 1:
                r = self.mul[r][base]
            base = self.mul[base][base]
            k >>= 1
        return r

    def pow_omega2(self, i):
        return self.powr(i, omega2_exp(self.order[i]))

    # two handedness conventions for conjugation --------------------------------------
    def conjP(self, x, g):        # Lean:  g⁻¹ x g
        return self.m(self.inv[g], x, g)

    def conjA(self, x, g):        # archive: g x g⁻¹
        return self.m(g, x, self.inv[g])

    def commP(self, x, y):        # x⁻¹ y⁻¹ x y   (both conventions agree)
        return self.m(self.inv[x], self.inv[y], x, y)

    # generation / normal closure ------------------------------------------------------
    def closure(self, gens):
        seen = {self.one} | set(gens)
        frontier = list(seen)
        while frontier:
            nf = []
            for x in frontier:
                for g in list(seen):
                    for y in (self.mul[x][g], self.mul[g][x]):
                        if y not in seen:
                            seen.add(y)
                            nf.append(y)
            frontier = nf
        return seen

    def generates(self, gens):
        return len(self.closure(gens)) == self.n

    def normal_closure(self, gens):
        cur = set(gens) | {self.one}
        while True:
            sub = self.closure(sorted(cur))
            new = set()
            for x in sorted(sub):
                for c in range(self.n):
                    y = self.conjP(x, c)          # normal closure is convention-free
                    if y not in sub:
                        new.add(y)
            if not new:
                return sub
            cur = sub | new

    def is_two_group_subset(self, elem_set):
        k = len(elem_set)
        return k > 0 and (k & (k - 1)) == 0     # |subgroup| is a power of 2


# --------------------------------------------------------------------------- constructors
def cyclic(n):
    elems = list(range(n))
    mul = [[(i + j) % n for j in range(n)] for i in range(n)]
    inv = [(-i) % n for i in range(n)]
    return Grp(f"C{n}", elems, mul, inv, 0)


def direct_product(G, H, name):
    elems = list(product(G.elems, H.elems))
    idx = {g: i for i, g in enumerate(elems)}
    mul = [[idx[(G.elems[G.mul[G.idx[a[0]]][G.idx[b[0]]]],
                 H.elems[H.mul[H.idx[a[1]]][H.idx[b[1]]]])]
            for b in elems] for a in elems]
    inv = [idx[(G.elems[G.inv[G.idx[a[0]]]], H.elems[H.inv[H.idx[a[1]]]])] for a in elems]
    one = idx[(G.elems[G.one], H.elems[H.one])]
    return Grp(name, elems, mul, inv, one)


def dihedral(n):
    """Mathlib DihedralGroup n (order 2n):  r i * r j = r(i+j), r i * sr j = sr(j-i),
    sr i * r j = sr(i+j), sr i * sr j = r(j-i);  (r i)⁻¹ = r(-i), (sr i)⁻¹ = sr i."""
    elems = [('r', i) for i in range(n)] + [('sr', i) for i in range(n)]
    idx = {g: k for k, g in enumerate(elems)}

    def prod(x, y):
        (tx, i), (ty, j) = x, y
        if tx == 'r' and ty == 'r':
            return ('r', (i + j) % n)
        if tx == 'r' and ty == 'sr':
            return ('sr', (j - i) % n)
        if tx == 'sr' and ty == 'r':
            return ('sr', (i + j) % n)
        return ('r', (j - i) % n)

    mul = [[idx[prod(a, b)] for b in elems] for a in elems]
    inv = [idx[('r', (-i) % n)] if t == 'r' else idx[('sr', i)] for (t, i) in elems]
    return Grp(f"D{n}(|.|={2*n})", elems, mul, inv, idx[('r', 0)])


def quaternion(n):
    """Mathlib QuaternionGroup n (order 4n): a i * a j = a(i+j), a i * xa j = xa(j-i),
    xa i * a j = xa(i+j), xa i * xa j = a(j-i+n);  ZMod (2n);  (a i)⁻¹=a(-i),
    (xa i)⁻¹ = xa(n+i).  QuaternionGroup 2 = Q8."""
    M = 2 * n
    elems = [('a', i) for i in range(M)] + [('xa', i) for i in range(M)]
    idx = {g: k for k, g in enumerate(elems)}

    def prod(x, y):
        (tx, i), (ty, j) = x, y
        if tx == 'a' and ty == 'a':
            return ('a', (i + j) % M)
        if tx == 'a' and ty == 'xa':
            return ('xa', (j - i) % M)
        if tx == 'xa' and ty == 'a':
            return ('xa', (i + j) % M)
        return ('a', (j - i + n) % M)

    mul = [[idx[prod(a, b)] for b in elems] for a in elems]
    inv = [idx[('a', (-i) % M)] if t == 'a' else idx[('xa', (n + i) % M)] for (t, i) in elems]
    return Grp(f"Q{4*n}", elems, mul, inv, idx[('a', 0)])


# ---------------------------------------------------------------------------- the relator
def wild_value(G, s, t, a, b, conj):
    """(x₀^σ)⁻¹ · (x₀⁻³τ)^ω₂ · x₁² · [x₁, x₁^{σ₂}]  in the given conjugation convention."""
    aR = G.pow_omega2(G.m(G.inv[G.powr(a, 3)], t))           # (a^3)⁻¹ t, then ω₂
    sigma2 = G.pow_omega2(s)
    y1 = conj(b, sigma2)
    cR = G.commP(b, y1)
    x0sig_inv = G.inv[conj(a, s)]
    return G.m(x0sig_inv, aR, G.powr(b, 2), cR)


def admissible_count(G, handed):
    """Count admissible markings.  handed='P' = Lean (g^h=h⁻¹gh); 'A' = archive (g^h=hgh⁻¹)."""
    conj = G.conjP if handed == 'P' else G.conjA
    O2 = G.normal_closure([])              # placeholder; recomputed per marking below
    cnt = 0
    witness = None
    for s, t in product(range(G.n), repeat=2):
        if conj(t, s) != G.powr(t, 2):     # TameRel: conjP τ σ = τ²  (resp. archive)
            continue
        for a, b in product(range(G.n), repeat=2):
            if wild_value(G, s, t, a, b, conj) != G.one:      # WildRelR
                continue
            if not G.is_two_group_subset(G.normal_closure([a, b])):   # Pro2Core
                continue
            if not G.generates([s, t, a, b]):                 # Generates
                continue
            cnt += 1
            if witness is None:
                witness = (s, t, a, b)
    return cnt, witness


# ------------------------------------------------------------------------------- driver
JUNE = {          # archive |Sur(Γ_R, G)|  (final_validation.log; C2/C4/V4 via Aut·#fields)
    'C2': 7,
    'C4': 24,
    'C2xC2 (V4)': 42,
    'D4(|.|=8)': 144,
    'Q8': 144,
}

def main():
    C2 = cyclic(2)
    C4 = cyclic(4)
    V4 = direct_product(cyclic(2), cyclic(2), 'C2xC2 (V4)')
    D4 = dihedral(4)
    Q8 = quaternion(2)
    groups = [('C2', C2), ('C4', C4), ('C2xC2 (V4)', V4), ('D4(|.|=8)', D4), ('Q8', Q8)]

    print(f"{'group':14} {'Lean N_R':>9} {'archive-conv':>12} {'June |Sur|':>10}  verdict")
    print('-' * 60)
    all_ok = True
    for key, G in groups:
        nP, _ = admissible_count(G, 'P')
        nA, _ = admissible_count(G, 'A')
        june = JUNE[key]
        ok = (nP == nA == june)
        all_ok = all_ok and ok
        print(f"{key:14} {nP:9d} {nA:12d} {june:10d}  {'MATCH' if ok else '** MISMATCH **'}")
    print('-' * 60)
    print('ALL MATCH' if all_ok else 'FAILURES PRESENT')

    # emit the explicit markings + wildValueExpR(e=1) values pinned by GQ2/Roe/Sanity.lean.
    # e=1 form = powOmega2 replaced by (·)^1, valid because every group here is a 2-group
    # (ω₂ = identity); we assert it against the genuine ω₂ form as a self-check.
    D8 = dihedral(8)

    def exp1(G, s, t, a, b):
        aR = G.m(G.inv[G.powr(a, 3)], t)                       # (x₀^3)⁻¹ τ  (ω₂ = id here)
        y1 = G.conjP(b, s)                                     # σ₂ = σ^1
        cR = G.commP(b, y1)
        val = G.m(G.inv[G.conjP(a, s)], aR, G.powr(b, 2), cR)
        aR2 = G.pow_omega2(G.m(G.inv[G.powr(a, 3)], t))        # genuine ω₂ form
        val2 = G.m(G.inv[G.conjP(a, s)], aR2, G.powr(b, 2),
                   G.commP(b, G.conjP(b, G.pow_omega2(s))))
        assert val == val2, (G.name, val, val2)
        return val, cR

    print("\n# explicit markings pinned by GQ2/Roe/Sanity.lean (wildValueExpR t 1, Lean conjP):")
    pins = [
        ("C2 c2MarkingR (WildRel FAILS)", C2, 1, 1, 1, 1),
        ("C2 c2WitR    (WildRel HOLDS)", C2, 1, 0, 1, 1),
        ("C4 c4MarkingR", C4, C4.idx[1], C4.idx[0], C4.idx[1], C4.idx[1]),
    ]
    for label, G, s, t, a, b in pins:
        val, cR = exp1(G, s, t, a, b)
        print(f"  {label:32}: wildValueExpR t 1 = {G.elems[val]}   (cR={G.elems[cR]})")
    # V4, D4, D8 (need index lookup for tuple/labelled elements)
    s, t, a, b = V4.idx[(1, 0)], V4.idx[(1, 1)], V4.idx[(0, 1)], V4.idx[(1, 0)]
    val, cR = exp1(V4, s, t, a, b)
    print(f"  {'V4 v4MarkingR':32}: wildValueExpR t 1 = {V4.elems[val]}   (cR={V4.elems[cR]})")
    for label, G, sl, tl, al, bl in [
        ("D4 d4MarkingR (nonab, x₀^σ≠x₀)", D4, ('r', 1), ('r', 0), ('sr', 0), ('sr', 1)),
        ("D8 d8MarkingR (nonab, cR≠1)", D8, ('r', 1), ('r', 0), ('sr', 0), ('sr', 0))]:
        s, t, a, b = G.idx[sl], G.idx[tl], G.idx[al], G.idx[bl]
        val, cR = exp1(G, s, t, a, b)
        print(f"  {label:32}: wildValueExpR t 1 = {G.elems[val]}   (cR={G.elems[cR]}, "
              f"x₀^σ={G.elems[G.conjP(a, s)]})")


if __name__ == '__main__':
    main()
