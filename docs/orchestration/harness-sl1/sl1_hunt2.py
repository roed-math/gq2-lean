#!/usr/bin/env python3
"""SL1 hunt v2: tower-layer membership with delta-descent + coker functionals."""
import sys
from itertools import product
from span_model import inv, comm, pw2, lyndon_upto, bracketing, magnus, rank2
from sl1_hunt import conj, d0, dr, chi_values, chi_of, minv, fox_row, v2

class Solver:
    """GF(2) span with combination tracking (vectors as ints)."""
    def __init__(self):
        self.rows = []          # (echelon_vec, combo_mask over inserted gens)
        self.n = 0
    def insert(self, v):
        idx = self.n; self.n += 1
        combo = 1 << idx
        for b, c in self.rows:
            if (v ^ b) < v: v ^= b; combo ^= c
        if v: self.rows.append((v, combo)); self.rows.sort(key=lambda t: -t[0])
        return v != 0
    def reduce(self, v):
        combo = 0
        for b, c in self.rows:
            if (v ^ b) < v: v ^= b; combo ^= c
        return v, combo          # v==0 => in span, combo = generator mask
    @property
    def rank(self): return len(self.rows)

def coords_at(word, j, K, wl):
    """Free-Z_j coordinates; asserts word in lambda_j(free)."""
    mod = 1 << K
    mu = magnus(word, max(len(w) for w in wl), mod)
    bits = 0
    for idx, w in enumerate(wl):
        c = mu.get(w, 0) % mod
        e = j - len(w)
        if e > 0:
            assert c % (1 << e) == 0, f"not in free lambda_{j}: {w} coeff {c}"
        if e >= 0 and (c >> e) & 1: bits |= (1 << idx)
    return bits

def relator_atoms(rword, j):
    out, frontier = [], [(rword, 2)]
    while frontier:
        w, lvl = frontier.pop()
        if lvl == j: out.append(w); continue
        frontier.append((w + w, lvl + 1))
        for g in (1, 2, 3): frontier.append((comm(w, [g]), lvl + 1))
    return out

def descend(word, rword, k, K):
    """Multiply word by relator atoms to bring it into lambda_k(free).
    Returns corrected word or None if stuck (not relator-deep enough)."""
    for j in range(2, k):
        wl = [t for L in range(1, j + 1) for t in product(range(3), repeat=L)]
        try:
            v = coords_at(word, j, K, wl)
        except AssertionError:
            return None
        if v == 0: continue
        atoms = relator_atoms(rword, j)
        sol = Solver()
        avs = []
        for a in atoms:
            av = coords_at(a, j, K, wl)
            avs.append(av); sol.insert(av)
        rem, combo = sol.reduce(v)
        if rem != 0: return None
        for i, a in enumerate(atoms):
            if (combo >> i) & 1: word = word + inv(a)
    return word

TOWER_DIMS = {3: 10, 4: 20, 5: 44}

def run(direction, k, seed, tag):
    K = k + 5
    M = 1 << K
    gen, tgt = chi_values(direction, K)
    wl = [t for L in range(1, k + 1) for t in product(range(3), repeat=L)]
    rword = dr([[1],[2],[3]]) if direction == 1 else d0([[1],[2],[3]])
    tested = d0 if direction == 1 else dr
    shape = "r0" if direction == 1 else "r2"
    chis8 = [(chi_of(seed[i], gen, M) - tgt[i]) % 8 for i in range(3)]
    P = all(c == 0 for c in chis8)
    # base span: relator layer at k + dbar atoms at seed slots
    sol = Solver()
    for a in relator_atoms(rword, k):
        sol.insert(coords_at(a, k, K, wl))
    rR = sol.rank
    lyn = [l for l in lyndon_upto(k - 1) if len(l) <= k - 1]
    mods = [pw2(bracketing(l), k - 1 - len(l)) for l in lyn]
    for w in mods:
        if shape == "r0":
            group = [w + w + comm(w, seed[0]), comm(w, seed[2]), comm(w, seed[1])]
        else:
            group = [w + w + comm(w, seed[2]), comm(w, seed[1]), comm(w, seed[0])]
        for a in group: sol.insert(coords_at(a, k, K, wl))
    rBase = sol.rank
    Nk = len(lyndon_upto(k))
    dimT = Nk - rR
    coker = dimT - (rBase - rR)
    dword = descend(tested(list(seed)), rword, k, K)
    if dword is None:
        print(f"dir{direction} k={k} {tag}: P={'Y' if P else 'N'} delta NOT relator-deep (triple dead at this level)")
        return
    dv = coords_at(dword, k, K, wl)
    rem, _ = sol.reduce(dv)
    member = (rem == 0)
    t_idx = (1, 2) if shape == "r0" else (0, 1)
    tailv = [coords_at(pw2(list(seed[i]), k - 1), k, K, wl) for i in t_idx]
    tadd = 0
    for tv in tailv:
        r, _ = sol.reduce(tv)
        if r: tadd += 1; sol.insert(tv)
    print(f"dir{direction} k={k} {tag}: P={'Y' if P else 'N'} towerdim={dimT}"
          f"{'(OK)' if TOWER_DIMS.get(k)==dimT else '(?)'} coker={coker} "
          f"delta_{'IN' if member else 'OUT'} tails_add={tadd}")
    return member

if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    # seeds: good + P-violating controls that still kill the relator deeply enough
    seeds = {
        1: {"good": ([3], [1, 2], [2]), "good2": ([3], [1, 2], [1]),
            "ctrl": ([3], [1], [2]), "ctrl2": ([3, 3, 3], [1, 2], [2])},
        2: {"good": ([1, 3], [3], [-1]), "good2": ([1, 3], [3], [1, 1, -1]),
            "ctrl": ([1, 3], [3], [3]), "ctrl2": ([3, 1], [3], [-1])},
    }
    for direction in (1, 2):
        for k in range(3, kmax + 1):
            for tag, s in seeds[direction].items():
                run(direction, k, list(s), tag)
