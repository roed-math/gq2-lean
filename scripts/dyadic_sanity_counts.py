#!/usr/bin/env python3
"""dyadic_sanity_counts.py  --  F5 finite-target regression harness for the frozen
general-dyadic presentation family (ramified-i, degree n = 1 quadratic instances).

**Regressions only — this script must never be cited by a proof.**  It enumerates
epimorphisms onto three small finite groups and compares the counts against a hard-coded
table.  Finite-target agreement is evidence that a word was transcribed correctly, never
evidence that a presentation is correct; the presentation content lives in the Lean
development and in the sage-side certificates (merge gate 5: "no theorem proved by
finite-target testing").

Port of `docs/dyadic/refs/check_dyadic_current.py` (ticket F5), re-pointed at the words
frozen at gate G-1 by `general_2adic/artifacts/reports/selection-freeze.md` (2026-07-31) and
extended with the retired-word regression and the mutant tripwire rows.

Conventions (freeze §"The five frozen rows", packet Rem. 2.3) — identical to the Lean side:

    x^g          = g⁻¹ x g                       (`conjP`; `x^{-g}` is sugar for `(x⁻¹)^g`)
    [x,y]        = x⁻¹ y⁻¹ x y
    x^{ω₂}       = the 2-primary component of x  (packet Lem. 2.2)
    σ₂           = σ^{ω₂}
    u_i          = (x_i τ)^{ω₂},  δ_i = u_i x_i⁻¹
    𝓔(g,h;δ₀,δ₁) = (δ₁^h δ₁ δ₀)^g δ₀
    𝒩_{U,m}(z)   = ∏_{j=1}^m z^{U^j}
    tame         : τ^σ = τ^q     (q = q_K)
    admissible   : tame ∧ relator = 1 ∧ ⟨σ,τ,x₀,x₁,x₂⟩ = G,  with every x_i in O₂(G)

Targets: S₃, D₈, A₄.  Handles are absent (h = 0) throughout.

What these targets can and cannot see (measured, see section C):

  * they DO see a wrong conjugator (σ₂ where the frozen word has σ) — that is the classic
    transcription catch, and it moves the A₄ count 120 → 504;
  * they DO see the archived sign-row word, but only pointwise: it kills an admissible
    generating marking of the word of record while leaving every total count unchanged;
  * they are STRUCTURALLY BLIND to the compact-M 𝓔-block ordering.  On all three targets
    every δ-letter is trivial (the tame relation forces τ = 1 on D₈ and on A₄ at q = 2,
    O₂(S₃) = 1 kills the wild slots, and at q = 4 the tame relation forces σ into an
    odd-order centralizer so σ₂ = 1 and the block collapses to δ₁²δ₀² = 1 in the
    elementary-abelian wild layer).  That is the freeze's own coverage criterion — "a
    separating orbit needs dim ≥ 2^α" (freeze §4, proof-grade) — and these wild layers have
    𝔽₂-dimension ≤ 2 against 2^α = 8 (√2, α = 3) and 4 (√5, α = 2).  The forward-order
    rejection lives in the §9.4 difference formula, not here.  Section C pins the blindness
    so that it fails loudly if it ever stops being true.

No sage, no magma, no GAP: explicit permutations and dependency-free 2-primary exponents.
Deterministic (fixed enumeration order, no randomness).  Exits nonzero on any deviation.

Run:  python3 scripts/dyadic_sanity_counts.py
"""

from __future__ import annotations

import itertools
import sys
from collections import deque
from typing import Callable, Iterable, Sequence

Perm = tuple[int, ...]
Relator = Callable[[Perm, Perm, Perm, Perm, Perm], Perm]


# ----------------------------------------------------------------- permutation arithmetic
def mul(a: Perm, b: Perm) -> Perm:
    """Composition a after b."""
    return tuple(a[b[i]] for i in range(len(a)))


def inv(a: Perm) -> Perm:
    ans = [0] * len(a)
    for i, j in enumerate(a):
        ans[j] = i
    return tuple(ans)


def power(a: Perm, n: int) -> Perm:
    if n < 0:
        return power(inv(a), -n)
    ans = tuple(range(len(a)))
    base = a
    while n:
        if n & 1:
            ans = mul(ans, base)
        base = mul(base, base)
        n >>= 1
    return ans


def order(a: Perm) -> int:
    identity = tuple(range(len(a)))
    cur = identity
    for n in range(1, 10_000):
        cur = mul(cur, a)
        if cur == identity:
            return n
    raise RuntimeError("order search failed")


def conj(x: Perm, g: Perm) -> Perm:
    """x^g = g⁻¹ x g — the house convention (Lean `conjP`)."""
    return mul(mul(inv(g), x), g)


def conj_wrong_side(x: Perm, g: Perm) -> Perm:
    """MUTANT ONLY: g x g⁻¹, the opposite-handed conjugation (section C, row C1)."""
    return mul(mul(g, x), inv(g))


def comm(x: Perm, y: Perm) -> Perm:
    """[x,y] = x⁻¹ y⁻¹ x y — the same in both handedness conventions."""
    return mul(mul(mul(inv(x), inv(y)), x), y)


def product(*xs: Perm) -> Perm:
    ans = tuple(range(len(xs[0])))
    for x in xs:
        ans = mul(ans, x)
    return ans


def omega2_power(x: Perm) -> Perm:
    """x^{ω₂}: the 2-primary component of x (packet Lem. 2.2)."""
    n = order(x)
    two_part = 1
    while n % 2 == 0:
        two_part *= 2
        n //= 2
    odd_part = n
    if odd_part == 1:
        exponent = 1 % two_part
    elif two_part == 1:
        exponent = 0
    else:
        exponent = next(
            e
            for e in range(two_part * odd_part)
            if e % two_part == 1 and e % odd_part == 0
        )
    return power(x, exponent)


def delta(x: Perm, tau: Perm) -> Perm:
    """δ = (x τ)^{ω₂} x⁻¹."""
    return mul(omega2_power(mul(x, tau)), inv(x))


def subgroup_generated(generators: Sequence[Perm]) -> set[Perm]:
    identity = tuple(range(len(generators[0])))
    generators = list(generators) + [inv(g) for g in generators]
    seen = {identity}
    queue = deque([identity])
    while queue:
        x = queue.popleft()
        for g in generators:
            y = mul(x, g)
            if y not in seen:
                seen.add(y)
                queue.append(y)
    return seen


def parity(p: Perm) -> int:
    return sum(p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p))) % 2


def symmetric_group(n: int) -> list[Perm]:
    return list(itertools.permutations(range(n)))


# --------------------------------------------------------------------------- the targets
S3 = symmetric_group(3)
A4 = [p for p in symmetric_group(4) if parity(p) == 0]
D8 = list(subgroup_generated([(1, 2, 3, 0), (0, 3, 2, 1)]))

GROUPS = {"S3": S3, "D8": D8, "A4": A4}
GROUP_NAMES = ("S3", "D8", "A4")

# O₂(G): the wild generators x₀,x₁,x₂ range over the maximal normal 2-subgroup.
O2 = {
    "S3": [tuple(range(3))],
    "D8": D8,
    "A4": [g for g in A4 if order(g) in (1, 2)],
}


# ------------------------------------------------------------------- the five frozen rows
# Every word below is transcribed from selection-freeze.md (2026-07-31, gate R5 = G-1).
# `cj` is threaded so that section C can re-run a word with one convention flipped: a mutant
# is literally the same code with one flag changed, never a second transcription.

def rel_N_compact(sigma, tau, x0, x1, x2, *, alpha=2, cj=conj, conjugator_sigma2=False):
    """Freeze §2, compact N (r = 0), h = 0:

        R(N,α,0) = x₀^{2+2^α} [x₀,x₁] · x₂^{-σ} (x₂τ)^{ω₂}

    `conjugator_sigma2=True` is the wrong-σ₂ mutant (section C, row C4)."""
    conjugator = omega2_power(sigma) if conjugator_sigma2 else sigma
    return product(
        power(x0, 2 + 2 ** alpha),
        comm(x0, x1),
        cj(inv(x2), conjugator),
        omega2_power(mul(x2, tau)),
    )


def rel_M_compact(sigma, tau, x0, x1, x2, *, m, cj=conj, conjugator_sigma2=False,
                  forward_E=False):
    """Freeze §4, compact M (r = 0), h = 0, m = 2^{α−1}:

        A₀ = x₀⁻¹σ₂⁻ᵐ,  J₂ = x₂^{-σ}(x₂τ)^{ω₂},  E_m^rev = 𝓔(σ₂^m, σ₂^m; δ₀, δ₁)
        R(M,0) = A₀² [A₀,x₁] σ₂^{2m} · J₂ · E_m^rev

    with 𝓔(σ₂^m, σ₂^m; δ₀,δ₁) = δ₁^{σ₂^{2m}} δ₁^{σ₂^m} δ₀^{σ₂^m} δ₀.  `forward_E=True`
    reverses that product into the draft's rejected forward order (section C, row C2);
    `conjugator_sigma2=True` is the wrong-σ₂ mutant."""
    sigma2 = omega2_power(sigma)
    d0, d1 = delta(x0, tau), delta(x1, tau)
    A0 = product(inv(x0), power(sigma2, -m))
    conjugator = sigma2 if conjugator_sigma2 else sigma
    J2 = product(cj(inv(x2), conjugator), omega2_power(mul(x2, tau)))
    factors = [
        cj(d1, power(sigma2, 2 * m)),
        cj(d1, power(sigma2, m)),
        cj(d0, power(sigma2, m)),
        d0,
    ]
    if forward_E:
        factors.reverse()
    return product(power(A0, 2), comm(A0, x1), power(sigma2, 2 * m), J2, product(*factors))


def rel_M_procyclic(sigma, tau, x0, x1, x2, *, alpha=2, r=1, eps=1, cj=conj):
    """Freeze §5, procyclic M (r ≥ 1, η odd), η = 1 so σ^{η̂} = σ; h = 0.  With
    m = 2^{α−1}, s = 2^r, p = ε2^{r−1}, U = σ₂^s, V = σ₂^p, z = δ₂δ₂^V:

        C₀ = x₂σ₂^s,  A = x₀⁻¹C₀⁻ᵐ,  B = x₁σ₂^p,  D = σ^{η̂}
        E₀₁^pc = 𝓔(σ₂^{p+sm}, σ₂^{sm}; δ₀, δ₁),   E₂^pc = δ₂^U · (𝒩_{U,m}(z))^{U^m}
        R_lin^pc = A²[A,B] C₀^{2^α} [C₀,D] E₀₁^pc E₂^pc
        R̂^pc     = Sh_M(R_lin^pc)   (x₀↦δ₀, x₁↦δ₁, x₂↦1, δ₂↦1, τ↦1, σ↦σ, δ-letters atomic)
        R(M,pc)  = R_lin^pc · R̂^pc · D₀²[D₀,D₁]

    (r,ε) = (1,1) is ℚ₂(√−10) — packet Cor. 8.2, merge gate 9 — and (1,0) is ℚ₂(√10)."""
    sigma2 = omega2_power(sigma)
    D0, D1, D2 = delta(x0, tau), delta(x1, tau), delta(x2, tau)
    m = 2 ** (alpha - 1)
    s, p = 2 ** r, eps * 2 ** (r - 1)

    C0 = product(x2, power(sigma2, s))
    A = product(inv(x0), power(C0, -m))
    B = product(x1, power(sigma2, p))
    D = sigma                                        # σ^{η̂} at η = 1

    E01 = product(
        cj(D1, power(sigma2, p + 2 * s * m)),
        cj(D1, power(sigma2, p + s * m)),
        cj(D0, power(sigma2, p + s * m)),
        D0,
    )
    e2 = [cj(D2, power(sigma2, s))]                  # δ₂^U
    for j in range(1, m + 1):                        # (𝒩_{U,m}(δ₂δ₂^V))^{U^m}, increasing j
        e2.append(cj(D2, power(sigma2, s * (m + j))))
        e2.append(cj(D2, power(sigma2, p + s * (m + j))))
    Rlin = product(power(A, 2), comm(A, B), power(C0, 2 ** alpha), comm(C0, D),
                   E01, product(*e2))

    Chat = power(sigma2, s)                          # Sh_M: x₂ ↦ 1
    Ahat = product(inv(D0), power(Chat, -m))
    Bhat = product(D1, power(sigma2, p))
    Rhat = product(power(Ahat, 2), comm(Ahat, Bhat), power(Chat, 2 ** alpha),
                   comm(Chat, sigma), E01)           # E₂^pc ↦ 1 (δ₂ ↦ 1)

    return product(Rlin, Rhat, power(D0, 2), comm(D0, D1))


# ------------------------------------------- superseded spellings, kept as regressions only
def rel_minus10_relative_norm(sigma, tau, x0, x1, x2, *, cj=conj):
    """RETIRED (freeze §5): the ℚ₂(√−10) field-specific relative-norm word, draft §7.4.

    The freeze demoted this word to regression-only status — the shadow route is the only
    one reaching Q₊ (radical 0; plus-only and relative-norm both give radical 2, errata
    item 7).  The word of record for √−10 is `rel_M_procyclic(..., r=1, eps=1)`."""
    sigma2 = omega2_power(sigma)
    D0, D1 = delta(x0, tau), delta(x1, tau)
    Aminus = product(inv(x0), power(x1, -2))
    Rraw = product(
        power(Aminus, 2),
        comm(Aminus, sigma),
        power(x1, 4),
        comm(x1, product(sigma, x2)),
        inv(comm(sigma, x2)),
        cj(inv(x2), sigma2),
        omega2_power(product(x2, tau)),
    )
    W = product(D0, cj(D0, sigma), D1, cj(D1, sigma))
    Ab = product(inv(D0), power(D1, -2))
    norm = product(omega2_power(product(W, tau)), inv(omega2_power(tau)))
    Rb = product(
        power(Ab, 2),
        comm(Ab, sigma),
        power(D1, 4),
        comm(D1, product(sigma, W)),
        inv(comm(sigma, W)),
        cj(inv(W), sigma),
        norm,
    )
    return product(Rraw, product(Rb, power(D0, 2), comm(D0, D1)))


def rel_plus10_draft73(sigma, tau, x0, x1, x2, *, cj=conj):
    """SUPERSEDED: the ℚ₂(√10) field-specific word of draft §7.3,

        R₁₀ = A²[A,x₁] C₀⁴ [C₀,σ] E₁₀,   C₀ = x₂σ₂², A = x₀⁻¹C₀⁻²,
        E₁₀ = δ₁^{σ₂^8} δ₁^{σ₂^4} δ₀^{σ₂^4} δ₀ · δ₂^{σ₂^2}

    This is the word `refs/check_dyadic_current.py` used for d = 10.  It is NOT the frozen
    spelling: against `rel_M_procyclic(..., r=1, eps=0)` it is missing the orbit-norm tail of
    E₂^pc, the whole shadow copy R̂^pc, and the D₀²[D₀,D₁] correction (its E₁₀ is exactly
    E₀₁^pc followed by the δ₂^U prefix of E₂^pc).  Row B2 pins that the two agree on every
    marking of every target here, so the harness's d = 10 column is unaffected by the
    re-point — but the frozen spelling is what row A4 tests."""
    sigma2 = omega2_power(sigma)
    d0, d1, d2 = delta(x0, tau), delta(x1, tau), delta(x2, tau)
    C0 = product(x2, power(sigma2, 2))
    A = product(inv(x0), power(C0, -2))
    E10 = product(
        cj(d1, power(sigma2, 8)),
        cj(d1, power(sigma2, 4)),
        cj(d0, power(sigma2, 4)),
        d0,
        cj(d2, power(sigma2, 2)),
    )
    return product(power(A, 2), comm(A, x1), power(C0, 4), comm(C0, sigma), E10)


def rel_M_sign(sigma, tau, x0, x1, x2, *, alpha=2, eta=2, cj=conj):
    """ARCHIVED MUTANT — the sign-Frobenius row does NOT exist in ramified-i.

    Packet Prop. 8.1: η = λ(u) is odd, so the M_α families are exactly compact (r = 0) and
    procyclic (r ≥ 1, η ∈ ℤ₂ˣ); freeze ruling 5 keeps the formulas only under
    `artifacts/rejected/sign-row/` discipline, and `check_dyadic.sh`'s D3 guard forbids a
    sign-row datum anywhere under `GQ2/Dyadic/`.  Transcribed from draft eq:Msign-word
    (η even ⇒ r = 1, ε = 1; left-adapted basis), m = 2^{α−1}:

        C₀ = x₁σ₂²,  A = x₀⁻¹C₀⁻ᵐ,  D = σ₂^η x₂,  F₂ = [σ,x₂]⁻¹x₂^{-σ}(x₂τ)^{ω₂}
        E₀^sgn = δ₀^{σσ₂^{2m}} δ₀
        E₁^sgn = δ₁^{σ₂^{2+η}} δ₁^{σ₂^2} ∏_{j=m}^{1} (δ₁^{σσ₂^{2(m+j)}} δ₁^{σ₂^{2(m+j)}})
        R_lin^sgn = A²[A,σ] C₀^{2^α} [C₀,D] F₂ E₁^sgn E₀^sgn
        R̂^sgn     = Â²[Â,σ] Ĉ^{2^α} [Ĉ,D̂] E₁^sgn E₀^sgn,  Ĉ = δ₁σ₂², Â = δ₀⁻¹Ĉ⁻ᵐ, D̂ = σ₂^η
        R(M,sgn)  = R_lin^sgn · R̂^sgn · δ₀²[δ₀,δ₁]

    It exists in this file only so that re-entering it fails loudly (section C, row C3)."""
    sigma2 = omega2_power(sigma)
    d0, d1 = delta(x0, tau), delta(x1, tau)
    m = 2 ** (alpha - 1)

    C0 = product(x1, power(sigma2, 2))
    A = product(inv(x0), power(C0, -m))
    D = product(power(sigma2, eta), x2)
    F2 = product(inv(comm(sigma, x2)), cj(inv(x2), sigma), omega2_power(product(x2, tau)))

    E0 = product(cj(d0, product(sigma, power(sigma2, 2 * m))), d0)
    factors = [cj(d1, power(sigma2, 2 + eta)), cj(d1, power(sigma2, 2))]
    for j in range(m, 0, -1):                        # decreasing j, per eq:E1sign
        factors.append(cj(d1, product(sigma, power(sigma2, 2 * (m + j)))))
        factors.append(cj(d1, power(sigma2, 2 * (m + j))))
    E01 = product(product(*factors), E0)

    Rlin = product(power(A, 2), comm(A, sigma), power(C0, 2 ** alpha), comm(C0, D), F2, E01)
    Chat = product(d1, power(sigma2, 2))
    Ahat = product(inv(d0), power(Chat, -m))
    Rhat = product(power(Ahat, 2), comm(Ahat, sigma), power(Chat, 2 ** alpha),
                   comm(Chat, power(sigma2, eta)), E01)
    return product(Rlin, Rhat, power(d0, 2), comm(d0, d1))


# ------------------------------------------------------------------------------ enumeration
def markings(group_name: str, q: int) -> Iterable[tuple[Perm, Perm, Perm, Perm, Perm]]:
    """Every (σ,τ,x₀,x₁,x₂) with τ^σ = τ^q and x_i ∈ O₂(G), in a fixed order."""
    group = GROUPS[group_name]
    for sigma, tau in itertools.product(group, repeat=2):
        if conj(tau, sigma) != power(tau, q):
            continue
        for x0, x1, x2 in itertools.product(O2[group_name], repeat=3):
            yield sigma, tau, x0, x1, x2


def count_epimorphisms(group_name: str, q: int, relator: Relator) -> int:
    group = GROUPS[group_name]
    identity = tuple(range(len(group[0])))
    count = 0
    for marking in markings(group_name, q):
        if relator(*marking) != identity:
            continue
        if len(subgroup_generated(list(marking))) == len(group):
            count += 1
    return count


def count_vector(q: int, relator: Relator) -> list[int]:
    return [count_epimorphisms(name, q, relator) for name in GROUP_NAMES]


def pointwise_differences(q: int, left: Relator, right: Relator) -> list[int]:
    """Per target, the number of markings on which the two words take different values."""
    out = []
    for name in GROUP_NAMES:
        out.append(sum(1 for mk in markings(name, q) if left(*mk) != right(*mk)))
    return out


# ----------------------------------------------------------------------------- the row set
FIELDS = ("-2", "2", "5", "10", "-10")

# S₃: 6,6,0,6,6 · D₈: 1568×5 · A₄: 120,120,480,120,120   (ticket F5)
EXPECTED = {
    "S3": [6, 6, 0, 6, 6],
    "D8": [1568, 1568, 1568, 1568, 1568],
    "A4": [120, 120, 480, 120, 120],
}

# (label, q_K, relator) for d = -2, 2, 5, 10, -10 — all five in their frozen spelling.
FROZEN_ROWS = [
    ("d=-2   N(alpha=2, r=0)", 2, lambda *a: rel_N_compact(*a, alpha=2)),
    ("d=2    M(alpha=3, r=0)", 2, lambda *a: rel_M_compact(*a, m=4)),
    ("d=5    M(alpha=2, r=0)", 4, lambda *a: rel_M_compact(*a, m=2)),
    ("d=10   M(alpha=2, r=1, eps=0)", 2, lambda *a: rel_M_procyclic(*a, r=1, eps=0)),
    ("d=-10  M(alpha=2, r=1, eps=1)", 2, lambda *a: rel_M_procyclic(*a, r=1, eps=1)),
]

# The pinned sign-row witnesses (row C3): markings that are admissible AND generating for the
# √−10 word of record, on which the archived sign-row word is not trivial.  Found by the
# deterministic sweep of `markings(...)`; hard-coded so the row costs nothing.
SIGN_ROW_WITNESSES = [
    ("A4", (0, 2, 3, 1), (0, 1, 2, 3), (1, 0, 3, 2), (0, 1, 2, 3), (0, 1, 2, 3)),
    ("D8", (3, 2, 1, 0), (0, 1, 2, 3), (3, 2, 1, 0), (3, 0, 1, 2), (2, 1, 0, 3)),
]

FAILURES: list[str] = []


def check(ok: bool, row: str, detail: str) -> str:
    if ok:
        return "OK"
    FAILURES.append(f"{row}: {detail}")
    return "** FAIL **"


def fmt(vec: Sequence[int]) -> str:
    return "/".join(str(v) for v in vec)


# ---------------------------------------------------------------------------------- driver
def section_a() -> dict[str, list[int]]:
    print("== A. corrected quadratic-field words vs the expected table "
          "(frozen spellings, h=0) ==")
    print(f"  {'row':32} {'q':>2} {'S3':>6} {'D8':>6} {'A4':>6}  "
          f"{'expected':>14}  verdict")
    observed: dict[str, list[int]] = {}
    for i, (label, q, relator) in enumerate(FROZEN_ROWS):
        vec = count_vector(q, relator)
        want = [EXPECTED[g][i] for g in GROUP_NAMES]
        observed[FIELDS[i]] = vec
        status = check(vec == want, f"A/{label.split()[0]}",
                       f"counts {fmt(vec)} != expected {fmt(want)}")
        print(f"  {label:32} {q:2d} {vec[0]:6d} {vec[1]:6d} {vec[2]:6d}  "
              f"{fmt(want):>14}  {'MATCH' if status == 'OK' else status}")
    return observed


def section_b(observed: dict[str, list[int]]) -> None:
    print("\n== B. superseded spellings, regression-only (never the word of record) ==")
    print(f"  {'row':32} {'q':>2} {'S3':>6} {'D8':>6} {'A4':>6}  "
          f"{'expected':>14}  verdict")

    # B1 — the freeze RETIRED the √−10 field-specific relative-norm word to regression-only
    # status (freeze §5, R4 riding decision); THIS ROW IS EXACTLY THAT REGRESSION.  The word
    # of record for ℚ₂(√−10) is the procyclic row at (r,ε,η) = (1,1,1) — packet Cor. 8.2,
    # merge gate 9 — which row A5 above tests; here the retired word must still reproduce
    # that same d = −10 column.
    vec = count_vector(2, rel_minus10_relative_norm)
    want = observed["-10"]
    status = check(vec == want, "B1/relative-norm",
                   f"counts {fmt(vec)} != procyclic word of record {fmt(want)}")
    print(f"  {'B1 sqrt(-10) relative-norm':32} {2:2d} {vec[0]:6d} {vec[1]:6d} {vec[2]:6d}  "
          f"{fmt(want):>14}  {'MATCH' if status == 'OK' else status}")

    # B2 — the d = 10 word of `refs/check_dyadic_current.py` is the draft §7.3 field-specific
    # word, not the frozen procyclic row (see `rel_plus10_draft73`).  Both counts and every
    # pointwise value agree here, so the port's re-point of the d = 10 row is count-neutral.
    vec = count_vector(2, rel_plus10_draft73)
    want = observed["10"]
    status = check(vec == want, "B2/draft-7.3",
                   f"counts {fmt(vec)} != frozen procyclic row {fmt(want)}")
    print(f"  {'B2 sqrt(10) draft 7.3':32} {2:2d} {vec[0]:6d} {vec[1]:6d} {vec[2]:6d}  "
          f"{fmt(want):>14}  {'MATCH' if status == 'OK' else status}")
    diffs = pointwise_differences(2, rel_plus10_draft73,
                                  lambda *a: rel_M_procyclic(*a, r=1, eps=0))
    status = check(diffs == [0, 0, 0], "B2/draft-7.3-pointwise",
                   f"pointwise differences {fmt(diffs)} != 0/0/0")
    print(f"  {'   ... pointwise vs frozen row':32} {'':2} {'':6} {'':6} {'':6}  "
          f"{'diffs ' + fmt(diffs):>14}  {'MATCH' if status == 'OK' else status}")


def section_c() -> None:
    print("\n== C. mutant rows (transcription tripwires; a mutant must never look frozen) ==")
    print(f"  {'mutant':38} {'statistic':22} {'observed':>12}  verdict")

    # C1 — wrong conjugation side: x^g spelled g x g⁻¹ inside the relator.  The counts AND the
    # admissible sets are blind to it (measured: whenever either word is trivial, so is the
    # other), so this row uses the pointwise word value, which is not blind.
    frozen_n = lambda *a: rel_N_compact(*a, alpha=2)
    mutant_n = lambda *a: rel_N_compact(*a, alpha=2, cj=conj_wrong_side)
    diffs = pointwise_differences(2, frozen_n, mutant_n)
    counts = count_vector(2, mutant_n)
    status = check(diffs == [0, 0, 384] and counts == [6, 1568, 120], "C1/conj-side",
                   f"pointwise {fmt(diffs)} (want 0/0/384), counts {fmt(counts)}")
    print(f"  {'C1 wrong conjugation side (N, d=-2)':38} {'pointwise value':22} "
          f"{fmt(diffs):>12}  {'REJECTED (A4)' if status == 'OK' else status}")
    print(f"  {'   ... its epimorphism counts':38} {'epi-count vector':22} "
          f"{fmt(counts):>12}  {'BLIND (by design)' if status == 'OK' else status}")

    # C2 — un-reversed 𝓔-block (the compact-M forward order).  STRUCTURALLY INVISIBLE at these
    # targets: every δ-letter is trivial on S₃/D₈/A₄ (module docstring), so both orders
    # evaluate to 1 on every marking.  The freeze's coverage criterion says so in advance —
    # a separating orbit needs dim ≥ 2^α (8 for √2, 4 for √5) and these wild layers give
    # dim ≤ 2.  The rejection of the forward order is the §9.4 difference formula, NOT this
    # harness.  The row pins the blindness: if a future target ever separates the two orders,
    # this row fails and the verdict must be upgraded to REJECTED.
    for label, m, q in (("C2 un-reversed E_m (M, d=2, m=4)", 4, 2),
                        ("C2 un-reversed E_m (M, d=5, m=2)", 2, 4)):
        frozen_m = lambda *a, _m=m: rel_M_compact(*a, m=_m)
        mutant_m = lambda *a, _m=m: rel_M_compact(*a, m=_m, forward_E=True)
        diffs = pointwise_differences(q, frozen_m, mutant_m)
        status = check(diffs == [0, 0, 0], f"C2/forward-E/m={m}",
                       f"pointwise differences {fmt(diffs)} != 0/0/0 — the targets now "
                       f"SEE the 𝓔-order; upgrade this row to REJECTED")
        print(f"  {label:38} {'pointwise value':22} {fmt(diffs):>12}  "
              f"{'NOT-SEPARATED (pinned)' if status == 'OK' else status}")

    # C3 — the sign-row word (packet Prop. 8.1: the branch does not exist).  Counts are blind
    # to it as well; the rejection is an explicit admissible generating marking of the √−10
    # word of record that the sign-row word kills.
    for gname, sigma, tau, x0, x1, x2 in SIGN_ROW_WITNESSES:
        mk = (sigma, tau, x0, x1, x2)
        identity = tuple(range(len(GROUPS[gname][0])))
        of_record = rel_M_procyclic(*mk, r=1, eps=1)
        sign_value = rel_M_sign(*mk)
        tame = conj(tau, sigma) == power(tau, 2)
        generates = len(subgroup_generated(list(mk))) == len(GROUPS[gname])
        ok = tame and generates and of_record == identity and sign_value != identity
        status = check(ok, f"C3/sign-row/{gname}",
                       f"witness broke: tame={tame} generates={generates} "
                       f"word_of_record_trivial={of_record == identity} "
                       f"sign_row_trivial={sign_value == identity}")
        print(f"  {'C3 sign-row word (Prop 8.1) vs ' + gname:38} {'pinned witness':22} "
              f"{'kills marking':>12}  {'REJECTED' if status == 'OK' else status}")

    # C4 — the classic transcription catch: σ₂ where the frozen word has σ in x₂^{-σ}.
    # This one the counts do see, loudly: A₄ moves 120 → 504.
    for label, q, relator, want in (
        ("C4 wrong-sigma2 conjugator (N, d=-2)", 2,
         lambda *a: rel_N_compact(*a, alpha=2, conjugator_sigma2=True), [6, 1568, 504]),
        ("C4 wrong-sigma2 conjugator (M, d=2)", 2,
         lambda *a: rel_M_compact(*a, m=4, conjugator_sigma2=True), [6, 1568, 504]),
    ):
        vec = count_vector(q, relator)
        frozen = EXPECTED["A4"][0]
        status = check(vec == want and vec[2] != frozen, f"C4/wrong-sigma2/{label[-8:]}",
                       f"counts {fmt(vec)} != {fmt(want)} — the wrong-σ₂ mutant must not "
                       f"reproduce the frozen A4 count {frozen}")
        print(f"  {label:38} {'epi-count vector':22} {fmt(vec):>12}  "
              f"{'REJECTED (A4 504!=120)' if status == 'OK' else status}")


def main() -> int:
    print("dyadic_sanity_counts: finite-target regressions for the frozen dyadic family "
          "(gate G-1, 2026-07-31)")
    print("regressions only — never cited by a proof; targets S3, D8, A4; "
          "x^g = g^-1 x g, [x,y] = x^-1 y^-1 x y\n")
    observed = section_a()
    section_b(observed)
    section_c()
    if FAILURES:
        print(f"\ndyadic_sanity_counts: FAILED ({len(FAILURES)} row(s))")
        for f in FAILURES:
            print(f"  {f}")
        return 1
    print("\ndyadic_sanity_counts: all rows as expected")
    return 0


if __name__ == "__main__":
    sys.exit(main())
