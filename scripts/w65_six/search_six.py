"""W65-SIX: backtracking search for handle-free relator-killing markings, and the class-six bit.

`solve_x1` picks the free top bit at each cell at random, so it fails whenever ANY later layer
turns up an odd residue.  The bit choices at earlier cells change the later residues, so the
right instrument is a backtracking search over the free bits, not rejection sampling.

At each cell of `U_n` in class order: the residual `-sqWord(s,x,y)[r][c]` must be even (else the
branch dies); if it is, `y[r][c]` gains `resid/2`, and the top bit `+ m/2` is a free binary
choice which leaves this cell's residual alone but moves later ones.
"""

import random
import sys

sys.path.insert(0, "/Users/roed/claude/cla/worktrees/w65-six/scripts/w65_six")

from u7lib import (ModRing, cells, eye, is_one, label, mmul, rand_mat, sqWord)

M = 8


def search(s, x, n, m=M, want=1, cap=200000):
    """All (or `want`) solutions `y` of `sqWord s x y = 1`, by backtracking over free bits.

    Returns `(solutions, blocked_cell_histogram, nodes)`.
    """
    R = ModRing(m)
    cs = cells(n)
    sols = []
    blocked = {}
    nodes = [0]

    def rec(idx, y):
        if len(sols) >= want or nodes[0] > cap:
            return
        nodes[0] += 1
        if idx == len(cs):
            if is_one(sqWord(s, x, y, R), R):
                sols.append([row[:] for row in y])
            return
        (r, c) = cs[idx]
        w = sqWord(s, x, y, R)
        resid = (-w[r][c]) % m
        if resid % 2 != 0:
            blocked[(r, c)] = blocked.get((r, c), 0) + 1
            return
        half = (resid // 2) % (m // 2)
        base = y[r][c]
        for bit in (0, 1):
            y[r][c] = (base + half + (m // 2) * bit) % m
            rec(idx + 1, y)
            if len(sols) >= want or nodes[0] > cap:
                break
        y[r][c] = base

    rec(0, eye(n, R))
    return sols, blocked, nodes[0]


def run(n, trials, seed, want=1, verbose_first=0):
    """Sample `(s,x)`, search for relator-killing `y`, read the dressed top-row parity."""
    rng = random.Random(seed)
    R = ModRing(M)
    tr, cr = 0, n - 1
    found_sx = 0
    markings = 0
    odd = []
    blocked_hist = {}
    shown = 0
    for _ in range(trials):
        s = rand_mat(n, rng, M)
        x = rand_mat(n, rng, M)
        sols, blk, _ = search(s, x, n, want=want)
        for cell, k in blk.items():
            blocked_hist[cell] = blocked_hist.get(cell, 0) + k
        if not sols:
            continue
        found_sx += 1
        for y in sols:
            markings += 1
            dressed = sqWord(mmul(s, x, R), x, y, R)
            val = dressed[tr][cr]
            if shown < verbose_first:
                shown += 1
                print(f"    dressed top {label(tr, cr)} = {val}   parity {val % 2}")
            if val % 2:
                odd.append((s, x, y, val))
    return found_sx, markings, odd, blocked_hist


def main():
    for n in (6, 7):
        print("=" * 90)
        print(f"W65-SIX backtracking search in U_{n}  (class {n - 1});"
              f" top cell {label(0, n - 1)}")
        print("=" * 90)
        trials = 400 if n == 6 else 400
        found, markings, odd, blk = run(n, trials, seed=31337 + n, want=4, verbose_first=5)
        print(f"  (s,x) sampled          : {trials}")
        print(f"  (s,x) admitting some y : {found}")
        print(f"  relator-killing markings tested: {markings}")
        print(f"  ODD class-{n - 1} responses: {len(odd)}")
        if odd:
            s, x, y, val = odd[0]
            print(f"  ==> NOT FORCED.  witness dressed top = {val}")
        else:
            print(f"  ==> every marking even at class {n - 1}")
        tot = sum(blk.values())
        top = sorted(blk.items(), key=lambda kv: -kv[1])[:8]
        print(f"  branch deaths: {tot}; worst cells: "
              + ", ".join(f"{label(*c)}:{k}" for c, k in top))
        print()


if __name__ == "__main__":
    main()
