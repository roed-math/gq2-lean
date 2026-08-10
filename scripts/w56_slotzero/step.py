#!/usr/bin/env python3
"""W56-SLOTZERO: exhaustive check of the two-adic step and of the slot-zero arithmetic.

Three checks, all exhaustive over the relevant residues.

(1) `evenSlotZero_step`.  For `j >= 2`, if `t = 1 (mod 2^j)` and `t^2 = 1 (mod 2^(j+2))`
    then `t = 1 (mod 2^(j+1))`.  Also: the hypothesis `j >= 2` is sharp -- at `j = 1` the
    conclusion fails.

(2) The slot-zero collision.  For `k >= 3` and `alpha >= 2`, the two facts

      `t = 1 (mod 2^(k+alpha-2))`      (the depth boundary on `lambda_{k-1}`)
      `t^2 = 1 (mod 2^(k+alpha))`      (the trapped square, via `lambda_{k+1}`)

    force `t = 1 (mod 2^(k+alpha-1))`, i.e. the negation of the flip's sharpness demand
    `not 2^(k+(alpha-1)) | t - 1`.  Checked for every residue.

(3) The margin at the nonzero coordinates.  Without the square constraint the demand IS
    met: the level of `u^(2^(k-2)) - 1` for `u` of exact level `alpha` is exactly
    `k+alpha-2`, one digit inside the demand.  So the refutation at coordinate `0` is
    exactly the cost of the square, not a slackness in the bookkeeping.
"""

import sys


def v2(x):
    if x == 0:
        return None
    j = 0
    while x % 2 == 0:
        x //= 2
        j += 1
    return j


out = []
W = out.append

W("### W56-SLOTZERO: exhaustive two-adic certificates")
W("")

# ------------------------------------------------------------------ check 1
W("## (1) the step  [t = 1 mod 2^j  and  t^2 = 1 mod 2^(j+2)]  =>  t = 1 mod 2^(j+1)")
bad = 0
tested = 0
for j in range(2, 12):
    N = j + 6
    for u in range(2 ** (N - j)):
        t = 1 + (2 ** j) * u
        tested += 1
        if (t * t - 1) % 2 ** (j + 2) == 0 and (t - 1) % 2 ** (j + 1) != 0:
            bad += 1
W(f"    j = 2..11, all residues mod 2^(j+6): {tested} cases, {bad} failures")
assert bad == 0

# sharpness of j >= 2
witnesses = []
for u in range(2 ** 6):
    t = 1 + 2 * u
    if (t * t - 1) % 2 ** 3 == 0 and (t - 1) % 2 ** 2 != 0:
        witnesses.append(t % 2 ** 7)
W(f"    at j = 1 the step FAILS; smallest witnesses t = {sorted(set(witnesses))[:4]}")
assert witnesses
W("")

# ------------------------------------------------------------------ check 2
W("## (2) the slot-zero collision: depth boundary + trapped square kill the demand")
W("       k      alpha   admissible levels of chi(g)-1   demand (<= k+alpha-2)   verdict")
allbad = 0
for k in range(3, 8):
    for alpha in range(2, 8):
        N = k + alpha + 4
        levels = set()
        for u in range(2 ** (N - (k + alpha - 2))):
            t = 1 + (2 ** (k + alpha - 2)) * u          # depth boundary
            if (t * t - 1) % 2 ** (k + alpha) != 0:     # trapped square
                continue
            lv = v2((t - 1) % 2 ** N)
            levels.add(lv if lv is not None else "inf")
        finite = sorted(x for x in levels if x != "inf")
        ok = all(x >= k + alpha - 1 for x in finite)
        if not ok:
            allbad += 1
        W(f"       {k}      {alpha}       >= {min(finite) if finite else 'inf'}"
          f"                        <= {k + alpha - 2}"
          f"                 {'REFUTED' if ok else '!! SUPPLIED'}")
assert allbad == 0
W("")

# ------------------------------------------------------------------ check 3
W("## (3) the margin at a nonzero coordinate: level of u^(2^(k-2)) - 1 for exact level alpha")
W("       k      alpha   level of mUnit(alpha)^(2^(k-2)) - 1   demand   verdict")
for k in range(3, 7):
    for alpha in range(2, 7):
        N = k + alpha + 6
        # mUnit alpha = (1 - 2^alpha)^{-1} mod 2^N, exact level alpha
        u = pow((1 - 2 ** alpha) % 2 ** N, -1, 2 ** N)
        w = pow(u, 2 ** (k - 2), 2 ** N)
        lv = v2((w - 1) % 2 ** N)
        W(f"       {k}      {alpha}       {lv}"
          f"                                  <= {k + alpha - 2}"
          f"      {'meets it exactly' if lv == k + alpha - 2 else '!! off'}")
        assert lv == k + alpha - 2
        # and the N-branch unit, one squaring later
        n = (-pow((1 + 2 ** alpha) % 2 ** N, -1, 2 ** N)) % 2 ** N
        wn = pow(n, 2 ** (k - 2), 2 ** N)
        assert v2((wn - 1) % 2 ** N) == k + alpha - 2

W("")
W("## conclusion")
W("    every level admissible at coordinate 0 is >= k+alpha-1;")
W("    the flip demands <= k+alpha-2;  the two never meet, at any alpha >= 2.")
W("    at the nonzero coordinates the tower's own boundary k+alpha-2 meets the demand")
W("    exactly, so the whole margin is the one digit the slot-0 square costs.")

text = "\n".join(out) + "\n"
sys.stdout.write(text)
with open("results/w56_slotzero_step.txt", "w") as f:
    f.write(text)
