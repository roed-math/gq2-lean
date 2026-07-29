#!/usr/bin/env python3
"""Finite-target regression for the corrected dyadic presentation draft.

This dependency-free script enumerates epimorphisms from the corrected
quadratic-field words to S3, D8, and A4.  It also checks that the general
procyclic M_2 word with (r, epsilon, eta) = (1, 1, 1), the correct branch for
Q_2(sqrt(-10)), has the same three small-target counts as the field-specific
relative-norm alternative.

The enumeration is a regression test, not a proof of the presentations.
"""

from __future__ import annotations

import itertools
from collections import deque
from typing import Callable, Iterable, Sequence

Perm = tuple[int, ...]
Relator = Callable[[Perm, Perm, Perm, Perm, Perm], Perm]


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
    """x^g = g^{-1} x g, as in the paper."""
    return mul(mul(inv(g), x), g)


def comm(x: Perm, y: Perm) -> Perm:
    """[x,y] = x^{-1} y^{-1} x y, as in the paper."""
    return mul(mul(mul(inv(x), inv(y)), x), y)


def product(*xs: Perm) -> Perm:
    ans = tuple(range(len(xs[0])))
    for x in xs:
        ans = mul(ans, x)
    return ans


def omega2_power(x: Perm) -> Perm:
    """Evaluate x^{omega_2}: the 2-primary component of x."""
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


S3 = symmetric_group(3)
A4 = [p for p in symmetric_group(4) if parity(p) == 0]
r = (1, 2, 3, 0)
s = (0, 3, 2, 1)
D8 = list(subgroup_generated([r, s]))

O2 = {
    "S3": [tuple(range(3))],
    "D8": D8,
    "A4": [g for g in A4 if order(g) in (1, 2)],
}
GROUPS = {"S3": S3, "D8": D8, "A4": A4}


def tame_ok(sigma: Perm, tau: Perm, q: int) -> bool:
    return conj(tau, sigma) == power(tau, q)


def rel_N_compact(
    sigma: Perm,
    tau: Perm,
    x0: Perm,
    x1: Perm,
    x2: Perm,
    *,
    corrected: bool,
) -> Perm:
    sigma2 = omega2_power(sigma)
    conjugator = sigma if corrected else sigma2
    return product(
        power(x0, 6),
        comm(x0, x1),
        conj(inv(x2), conjugator),
        omega2_power(mul(x2, tau)),
    )


def rel_M_compact(
    sigma: Perm,
    tau: Perm,
    x0: Perm,
    x1: Perm,
    x2: Perm,
    *,
    m: int,
    corrected: bool,
) -> Perm:
    sigma2 = omega2_power(sigma)
    d0, d1 = delta(x0, tau), delta(x1, tau)
    A0 = product(inv(x0), power(sigma2, -m))
    conjugator = sigma if corrected else sigma2
    J2 = product(conj(inv(x2), conjugator), omega2_power(mul(x2, tau)))
    E = product(
        conj(d1, power(sigma2, 2 * m)),
        conj(d1, power(sigma2, m)),
        conj(d0, power(sigma2, m)),
        d0,
    )
    return product(power(A0, 2), comm(A0, x1), power(sigma2, 2 * m), J2, E)


def rel_plus10(sigma: Perm, tau: Perm, x0: Perm, x1: Perm, x2: Perm) -> Perm:
    sigma2 = omega2_power(sigma)
    d0, d1, d2 = delta(x0, tau), delta(x1, tau), delta(x2, tau)
    C0 = product(x2, power(sigma2, 2))
    A = product(inv(x0), power(C0, -2))
    E10 = product(
        conj(d1, power(sigma2, 8)),
        conj(d1, power(sigma2, 4)),
        conj(d0, power(sigma2, 4)),
        d0,
        conj(d2, power(sigma2, 2)),
    )
    return product(power(A, 2), comm(A, x1), power(C0, 4), comm(C0, sigma), E10)


def rel_minus10(sigma: Perm, tau: Perm, x0: Perm, x1: Perm, x2: Perm) -> Perm:
    sigma2 = omega2_power(sigma)
    D0, D1 = delta(x0, tau), delta(x1, tau)
    Aminus = product(inv(x0), power(x1, -2))
    Rraw = product(
        power(Aminus, 2),
        comm(Aminus, sigma),
        power(x1, 4),
        comm(x1, product(sigma, x2)),
        inv(comm(sigma, x2)),
        conj(inv(x2), sigma2),
        omega2_power(product(x2, tau)),
    )
    W = product(D0, conj(D0, sigma), D1, conj(D1, sigma))
    Ab = product(inv(D0), power(D1, -2))
    norm = product(omega2_power(product(W, tau)), inv(omega2_power(tau)))
    Rb = product(
        power(Ab, 2),
        comm(Ab, sigma),
        power(D1, 4),
        comm(D1, product(sigma, W)),
        inv(comm(sigma, W)),
        conj(inv(W), sigma),
        norm,
    )
    theta = product(Rb, power(D0, 2), comm(D0, D1))
    return product(Rraw, theta)



def rel_M_procyclic_minus10(
    sigma: Perm, tau: Perm, x0: Perm, x1: Perm, x2: Perm
) -> Perm:
    """General M_2 procyclic word at r=1, epsilon=1, eta=1, m=2.

    This is equation (5.8) of the revised draft specialized to the marked
    parameters for Q_2(sqrt(-10)).  Since eta=1, sigma^hat(eta)=sigma.
    """
    sigma2 = omega2_power(sigma)
    D0, D1, D2 = delta(x0, tau), delta(x1, tau), delta(x2, tau)

    alpha = 2
    m = 2
    s_exp = 2
    p_exp = 1

    C0 = product(x2, power(sigma2, s_exp))
    A = product(inv(x0), power(C0, -m))
    B = product(x1, power(sigma2, p_exp))
    D = sigma

    E01 = product(
        conj(D1, power(sigma2, p_exp + 2 * s_exp * m)),
        conj(D1, power(sigma2, p_exp + s_exp * m)),
        conj(D0, power(sigma2, s_exp * m + p_exp)),
        D0,
    )

    e2_factors: list[Perm] = [conj(D2, power(sigma2, s_exp))]
    for j in range(1, m + 1):
        e2_factors.extend(
            [
                conj(D2, power(sigma2, s_exp * (m + j))),
                conj(D2, power(sigma2, p_exp + s_exp * (m + j))),
            ]
        )
    E2 = product(*e2_factors)

    Rlin = product(
        power(A, 2),
        comm(A, B),
        power(C0, 2**alpha),
        comm(C0, D),
        E01,
        E2,
    )

    Chat = power(sigma2, s_exp)
    Ahat = product(inv(D0), power(Chat, -m))
    Bhat = product(D1, power(sigma2, p_exp))
    Dhat = sigma
    Rhat = product(
        power(Ahat, 2),
        comm(Ahat, Bhat),
        power(Chat, 2**alpha),
        comm(Chat, Dhat),
        E01,
    )

    return product(Rlin, Rhat, power(D0, 2), comm(D0, D1))


def relators(corrected: bool) -> dict[str, tuple[int, Relator]]:
    return {
        "-2": (2, lambda *args: rel_N_compact(*args, corrected=corrected)),
        "2": (2, lambda *args: rel_M_compact(*args, m=4, corrected=corrected)),
        "5": (4, lambda *args: rel_M_compact(*args, m=2, corrected=corrected)),
        "10": (2, rel_plus10),
        "-10": (2, rel_minus10),
    }


def count_epimorphisms(group_name: str, q: int, relator: Relator) -> int:
    group = GROUPS[group_name]
    identity = tuple(range(len(group[0])))
    count = 0
    for sigma, tau in itertools.product(group, repeat=2):
        if not tame_ok(sigma, tau, q):
            continue
        for x0, x1, x2 in itertools.product(O2[group_name], repeat=3):
            if relator(sigma, tau, x0, x1, x2) != identity:
                continue
            if len(subgroup_generated([sigma, tau, x0, x1, x2])) == len(group):
                count += 1
    return count


def run(corrected: bool) -> dict[str, list[int]]:
    ans: dict[str, list[int]] = {}
    rels = relators(corrected)
    for group_name in ("S3", "D8", "A4"):
        ans[group_name] = [
            count_epimorphisms(group_name, q, relator)
            for q, relator in rels.values()
        ]
    return ans


def main() -> None:
    fields = ["-2", "2", "5", "10", "-10"]
    expected = {
        "S3": [6, 6, 0, 6, 6],
        "D8": [1568, 1568, 1568, 1568, 1568],
        "A4": [120, 120, 480, 120, 120],
    }

    current = run(corrected=True)
    print("Corrected quadratic-field words")
    print("fields: ", fields)
    for name in ("S3", "D8", "A4"):
        print(f"{name:>3}:    {current[name]}")
        assert current[name] == expected[name], (name, current[name], expected[name])

    print("\nQ_2(sqrt(-10)): procyclic M_2 word versus relative-norm alternative")
    comparison: dict[str, tuple[int, int]] = {}
    for name in ("S3", "D8", "A4"):
        pc = count_epimorphisms(name, 2, rel_M_procyclic_minus10)
        alt = count_epimorphisms(name, 2, rel_minus10)
        comparison[name] = (pc, alt)
        print(f"{name:>3}: procyclic={pc}, alternative={alt}")
        assert pc == alt == expected[name][-1], (name, pc, alt)

    print("\nAll finite-target regressions passed.")


if __name__ == "__main__":
    main()
