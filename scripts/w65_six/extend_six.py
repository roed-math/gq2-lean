"""W65-SIX: the class-six bit, by EXTENDING a class-five relator-killing marking up column 7.

`U_7` is block triangular in the index `7`: the `(r,c)` entry of any product with `c <= 6`
never involves index `7`.  So if `(s,x,y)` kill the core word in `U_6`, then any extension of
`s, x, y` to `U_7` still kills the first fifteen rows, and only the six cells of column `7`
remain -- one per class, `(6,7)` at class one up to `(1,7)` at class six.

That makes the class-six question directly reachable: fix a class-five solution, choose the
column-`7` entries of `s` and `x` freely, solve the six remaining cells for `y`, and read the
parity of the dressed word at `(1,7)`.
"""

import random
import sys

sys.path.insert(0, "/Users/roed/claude/cla/worktrees/w65-six/scripts/w65_six")

from u7lib import ModRing, cells, eye, is_one, label, mmul, rand_mat, sqWord

M = 8
R8 = ModRing(M)


def find_u6_solution(seed, tries=4000):
    """A `(s,x,y)` in `U_6(Z/8)` with `sqWord s x y = 1`, by the layered solve."""
    from u7lib import solve_x1
    rng = random.Random(seed)
    for _ in range(tries):
        s = rand_mat(6, rng, M)
        x = rand_mat(6, rng, M)
        y, blk = solve_x1(s, x, 6, rng, M)
        if y is not None:
            return s, x, y
    return None


def embed(a6, col7=None):
    """Embed a `6 x 6` unitriangular matrix into `U_7`, with an optional column-`7`."""
    a = eye(7, R8)
    for r in range(6):
        for c in range(r + 1, 6):
            a[r][c] = a6[r][c]
    if col7 is not None:
        for r in range(6):
            a[r][6] = col7[r]
    return a


COL7 = [(r, 6) for r in range(6)]  # (1,7) class 6 ... (6,7) class 1
COL7_BY_CLASS = sorted(COL7, key=lambda rc: rc[1] - rc[0])  # (6,7) first


def solve_col7(s, x, y0, branch=None, rng=None):
    """Solve the six column-`7` cells for `y`, given the `6 x 6` block already solved."""
    y = [row[:] for row in y0]
    picks = iter(branch) if branch is not None else None
    for (r, c) in COL7_BY_CLASS:
        w = sqWord(s, x, y, R8)
        resid = (-w[r][c]) % M
        if resid % 2 != 0:
            return None, (r, c)
        half = (resid // 2) % (M // 2)
        bit = next(picks) if picks is not None else (rng.randrange(2) if rng else 0)
        y[r][c] = (y[r][c] + half + (M // 2) * bit) % M
    if not is_one(sqWord(s, x, y, R8), R8):
        return None, "VERIFY"
    return y, None


def main():
    base = find_u6_solution(seed=20260811)
    if base is None:
        print("no class-five solution found")
        return 1
    s6, x6, y6 = base
    print("class-five base marking found in U_6 (sqWord s x y = 1):")
    for nm, a in (("s", s6), ("x", x6), ("y", y6)):
        print(f"  {nm} = " + " ".join(f"{label(r,c)}={a[r][c]}" for (r, c) in cells(6)))
    print()

    rng = random.Random(4242)
    tested = 0
    odd = []
    blocked = {}
    parities = {0: 0, 1: 0}
    values = {}
    for _ in range(4000):
        scol = [rng.randrange(M) for _ in range(6)]
        xcol = [rng.randrange(M) for _ in range(6)]
        s = embed(s6, scol)
        x = embed(x6, xcol)
        y0 = embed(y6, [0] * 6)
        for branch in range(64):
            bits = [(branch >> i) & 1 for i in range(6)]
            y, blk = solve_col7(s, x, y0, branch=bits)
            if y is None:
                blocked[blk] = blocked.get(blk, 0) + 1
                continue
            tested += 1
            dressed = sqWord(mmul(s, x, R8), x, y, R8)
            val = dressed[0][6]
            values[val] = values.get(val, 0) + 1
            parities[val % 2] += 1
            if val % 2:
                odd.append((s, x, y, val))
            break  # one marking per (s,x) is enough for the parity census
        if tested >= 400:
            break

    print(f"class-six markings tested : {tested}")
    print(f"  dressed (1,7) EVEN : {parities[0]}")
    print(f"  dressed (1,7) ODD  : {parities[1]}")
    print(f"  value census: {dict(sorted(values.items()))}")
    tot = sum(blocked.values())
    print(f"  branch deaths: {tot}; cells: "
          + ", ".join(f"{(label(*c) if isinstance(c, tuple) else c)}:{k}"
                      for c, k in sorted(blocked.items(), key=lambda kv: -kv[1])[:6]))
    if odd:
        s, x, y, val = odd[0]
        print()
        print("=" * 88)
        print(f"  ==> NOT FORCED.  A handle-free relator-killing marking with ODD class-six bit.")
        print("=" * 88)
        for nm, a in (("s", s), ("x", x), ("y", y)):
            print(f"  {nm} = " + " ".join(f"{label(r,c)}={a[r][c]}" for (r, c) in cells(7)))
        print(f"  sqWord s x y = 1 : {is_one(sqWord(s, x, y, R8), R8)}")
        print(f"  dressed (1,7)    : {val}  (odd)")
    else:
        print("  ==> forced in every sample")
    return 0


if __name__ == "__main__":
    sys.exit(main())
