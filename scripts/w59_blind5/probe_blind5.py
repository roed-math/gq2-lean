"""W59-BLIND5: is the class-five block parity really sigma-slot-free?

`docs/dyadic/w58-sigma5-note.md` section 4.2 argues that the relator pins `H = W^{-1}` and
that `W_46 = y_45 * y_56 (mod 2)`, so the block's `(4,6)` coordinate "is even at every
relator-killing marking, at every handle count, on every row".  `derive_blind5.py` section 2
shows the printed closed form is the `sigma = E_23` instance: at a general sigma slot the row
also carries `s_45 * x_56 - s_56 * x_45`, which the abelian rows do not touch.

This script decides whether that is a real gap or only a bookkeeping one, by building an
honest relator-killing marking at `h = 1` whose handle block has ODD `(4,6)` coordinate, at a
sigma slot that is the committed `E_23` dressed by a single `nu'`-trivial letter.

Run:  python3 scripts/w59_blind5/probe_blind5.py > scripts/w59_blind5/results/probe_blind5.txt

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""

import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])

from u6lib import NAMES, SIG_FIVE, U6, commP, inv, mul, sqWord  # noqa: E402

M = 8
CLASSES = [["a", "b", "c", "d", "e"], ["f", "g", "h", "i"], ["j", "k", "l"], ["m", "n"], ["o"]]

CHECKS = []


def check(name, ok):
    CHECKS.append((name, bool(ok)))
    print(f"  [{'ok ' if ok else 'FAIL'}] {name}")


def red(p):
    return U6({k: int(p.co[k]) % M for k in NAMES})


def solve_core(s, target, seed):
    """Layered solve for `x, y` with `sqWord s x y = target` over Z/8.

    Each row `r` of the core word is `-4 * x.r + 2 * y.r + junk(strictly lower coordinates)`,
    so the rows can be met class by class.  `seed` pins the coordinates that must carry odd
    values; everything else is solved for.  Returns `(x, y)` or `None`.
    """
    x = U6({k: seed.get("x" + k, 0) for k in NAMES})
    y = U6({k: seed.get("y" + k, 0) for k in NAMES})
    pinned = set(seed)
    for layer in CLASSES:
        for r in layer:
            cur = red(sqWord(s, x, y))
            need = (int(target.co[r]) - int(cur.co[r])) % M
            frozen = ("y" + r) in pinned
            if frozen:
                if need != 0:
                    return None, f"row {r}: pinned, but off target by {need}"
                continue
            if need % 2 != 0:
                return None, f"row {r}: residue {need} is odd and cannot be met by -4x+2y"
            y.co[r] = (y.co[r] + need // 2) % M
            cur = red(sqWord(s, x, y))
            if int(cur.co[r]) % M != int(target.co[r]) % M:
                return None, f"row {r}: correction failed"
    return (x, y), None


print("=" * 78)
print("W59-BLIND5  probe_blind5.py   is the class-five block parity sigma-slot-free?")
print("=" * 78)

# --- the block ------------------------------------------------------------
U = U6({"d": 1})
V = U6({"e": 1})
H = red(commP(U, V))
print("\n## 1  A handle block with odd (4,6) coordinate\n")
print(f"      U = <d=1>,  V = <e=1>,  H = [U,V] = {H}")
check("the block is exactly the (4,6) generator, so H.i = 1 is ODD", H.co["i"] % 2 == 1)

target = red(inv(H))
print(f"      the relator pins the core word to H^-1 = {target}")

# --- the sigma slot -------------------------------------------------------
print("\n## 2  Two sigma slots, one committed and one nu'-trivially dressed\n")

s_committed = SIG_FIVE                      # E_23
s_dressed = red(mul(SIG_FIVE, U6({"e": 1})))  # E_23 * <e = 1>, and <e = 1> has b = 0
print(f"      committed : s = {s_committed}")
print(f"      dressed   : s = {s_dressed}   (E_23 times a nu'-trivial letter)")
check("the dressing letter is nu'-trivial (b-column zero)", U6({"e": 1}).co["b"] == 0)

# --- the solve ------------------------------------------------------------
print("\n## 3  A relator-killing marking at the dressed sigma slot\n")

seed = {"xd": 1, "yd": 2, "xe": 0, "ye": 0, "xi": 0, "yi": 0}
res, err = solve_core(s_dressed, target, seed)
check("layered solve succeeds at the dressed sigma slot", res is not None)
if res is None:
    print("      ", err)
else:
    x, y = res
    print(f"      x0 slot = {x}")
    print(f"      x1 slot = {y}")
    W = red(sqWord(s_dressed, x, y))
    print(f"      core word W = {W}")
    rel = red(mul(W, H))
    check("the full fifteen-row relator dies: sqWord * [U,V] = 1",
          all(int(rel.co[k]) % M == 0 for k in NAMES))
    check("...and the block's (4,6) coordinate is ODD there", H.co["i"] % 2 == 1)
    print(f"      x as a fifteen-tuple: {[int(x.co[k]) for k in NAMES]}")
    print(f"      y as a fifteen-tuple: {[int(y.co[k]) for k in NAMES]}")
    print(f"      s as a fifteen-tuple: {[int(s_dressed.co[k]) for k in NAMES]}")

# --- the committed slot, for contrast -------------------------------------
print("\n## 4  The same block is unreachable at the committed sigma slot\n")

res2, err2 = solve_core(s_committed, target, seed)
check("the layered solve FAILS at the committed sigma slot E_23", res2 is None)
print("      ", err2 if err2 else "(unexpected success)")
print("      that is theorem (a): at s = E_23 the row i residue the relator demands is even,")
print("      so no relator-killing marking there can carry an odd block coordinate.")

# --- exhaustive corroboration of the parity claim at the committed slot ----
print("\n## 5  Exhaustive corroboration at the committed slot\n")

bad = 0
tot = 0
for xd in range(M):
    for yd in range(M):
        if (-4 * xd + 2 * yd) % M:
            continue
        for xe in range(M):
            for ye in range(M):
                if (-4 * xe + 2 * ye) % M:
                    continue
                for xi in range(M):
                    for yi in range(M):
                        tot += 1
                        w = (-4 * xi + 2 * yi + 10 * xd * xe - 8 * xd * ye + yd * ye) % M
                        if w % 2:
                            bad += 1
check(f"at s = E_23 the (4,6) row is even at all {tot} abelian-row solutions, {bad} odd",
      bad == 0)

# --- does the block actually become VISIBLE off the committed slot? --------
print("\n## 6  Is the refuted lemma load-bearing, or does the theorem survive anyway?\n")

print("      The coupling term is  coefficient * H.i  with")
print("        coefficient = v.a*x.g - v.g*x.a + v.f*x.c - v.c*x.f - s.b*(v.a*x.c + v.c*x.a).")
print("      At the section-3 point the coefficient is 0 for every dressing, so the block is")
print("      still invisible there.  A genuine failure of theorem (a) needs BOTH factors odd.")

seed6 = {"xd": 1, "yd": 2, "xe": 0, "ye": 0, "yi": 0, "xg": 1, "xc": 0,
         "xj": 0, "xk": 0, "xl": 1, "xm": 0, "xn": 0}
res6, err6 = solve_core(s_dressed, target, seed6)
check("layered solve succeeds with the class-three response also switched on", res6 is not None)
if res6 is None:
    print("      ", err6)
if res6 is not None:
    x6, y6 = res6
    rel6 = red(mul(red(sqWord(s_dressed, x6, y6)), H))
    check("the fifteen-row relator dies at that point too",
          all(int(rel6.co[k]) % M == 0 for k in NAMES))
    v6 = U6({"a": 1})
    check("the dressing is nu'-trivial", v6.co["b"] == 0)
    coeff = (v6.co["a"] * x6.co["g"] - v6.co["g"] * x6.co["a"] + v6.co["f"] * x6.co["c"]
             - v6.co["c"] * x6.co["f"]
             - s_dressed.co["b"] * (v6.co["a"] * x6.co["c"] + v6.co["c"] * x6.co["a"])) % M
    coupling = (coeff * H.co["i"]) % M
    print(f"      x0 slot = {x6}")
    print(f"      x1 slot = {y6}")
    print(f"      coefficient = {coeff},  H.i = {H.co['i']},  coupling term = {coupling}")
    check("the coupling term is ODD: the class-five bit DOES see the block here",
          coupling % 2 == 1)
    rel_resp = (int(red(sqWord(s_dressed, x6, y6)).co["o"]) * 0 +
                (int(red(mul(red(sqWord(red(mul(s_dressed, v6)), x6, y6)), H)).co["o"])
                 - int(rel6.co["o"]))) % M
    core_resp = (int(red(sqWord(red(mul(s_dressed, v6)), x6, y6)).co["o"])
                 - int(red(sqWord(s_dressed, x6, y6)).co["o"])) % M
    print(f"      relator response = {rel_resp},  core-word reading = {core_resp},"
          f"  difference = {(rel_resp - core_resp) % M}")
    check("relator response and core reading differ by an ODD amount",
          (rel_resp - core_resp) % 2 == 1)
    print(f"      x as a fifteen-tuple: {[int(x6.co[k]) for k in NAMES]}")
    print(f"      y as a fifteen-tuple: {[int(y6.co[k]) for k in NAMES]}")

print("\n" + "=" * 78)
ok = sum(1 for _, v in CHECKS if v)
print(f"{ok} of {len(CHECKS)} named checks passed, {len(CHECKS) - ok} failures")
print("=" * 78)
