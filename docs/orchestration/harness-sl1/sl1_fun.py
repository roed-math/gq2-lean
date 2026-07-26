#!/usr/bin/env python3
"""Extract coker functionals in PBW coordinates + crossed-D depth test."""
import sys
from itertools import product
from span_model import inv, comm, pw2, lyndon_upto, bracketing, rank2
from sl1_hunt import conj, d0, dr, chi_values, chi_of, minv, fox_row, v2
from sl1_hunt2 import Solver, coords_at, relator_atoms, descend

def pbw_basis(k, K, wl):
    lyn = lyndon_upto(k)
    return lyn, [coords_at(pw2(bracketing(l), k - len(l)), k, K, wl, ) if False else
                 coords_at(pw2(bracketing(l), k - len(l)), k, K, wl) for l in lyn]

def in_pbw(v, pbw_sol):
    rem, combo = pbw_sol.reduce(v)
    assert rem == 0, "vector outside PBW span?!"
    return combo

def analyze(direction, k, seed):
    K = k + 5; M = 1 << K
    gen, tgt = chi_values(direction, K)
    wl = [t for L in range(1, k + 1) for t in product(range(3), repeat=L)]
    rword = dr([[1],[2],[3]]) if direction == 1 else d0([[1],[2],[3]])
    tested = d0 if direction == 1 else dr
    shape = "r0" if direction == 1 else "r2"
    lyn = lyndon_upto(k)
    pbw_sol = Solver()
    for l in lyn:
        pbw_sol.insert(coords_at(pw2(bracketing(l), k - len(l)), k, K, wl))
    N = len(lyn)
    # base-span words (R-layer + dbar atoms), reduced into PBW-coordinates
    base_words = relator_atoms(rword, k)
    lynm = [l for l in lyndon_upto(k - 1) if len(l) <= k - 1]
    mods = [pw2(bracketing(l), k - 1 - len(l)) for l in lynm]
    for w in mods:
        if shape == "r0":
            base_words += [w + w + comm(w, seed[0]), comm(w, seed[2]), comm(w, seed[1])]
        else:
            base_words += [w + w + comm(w, seed[2]), comm(w, seed[1]), comm(w, seed[0])]
    base_pbw = [in_pbw(coords_at(w, k, K, wl), pbw_sol) for w in base_words]
    t_idx = (1, 2) if shape == "r0" else (0, 1)
    tails_w = [pw2(list(seed[i]), k - 1) for i in t_idx]
    tails_pbw = [in_pbw(coords_at(w, k, K, wl), pbw_sol) for w in tails_w]
    dword = descend(tested(list(seed)), rword, k, K)
    delta_pbw = in_pbw(coords_at(dword, k, K, wl), pbw_sol) if dword else None
    # nullspace: phi in F2^N with phi . base = 0 for all base vectors
    # solve: build matrix, find kernel by echelon on columns
    phis = []
    for cand in range(1 << N):
        pass  # too big; do proper linear algebra instead
    # proper: kernel of the base matrix (rows = base vectors)
    # represent as columns: unknown phi bits; conditions: parity(phi & b)=0
    # gaussian elimination over conditions
    conds = []
    solb = Solver()
    for b in base_pbw:
        if solb.insert(b): conds.append(b)
    # free solve: iterate basis of the orthogonal complement
    # complement of span(conds) in F2^N: standard: echelonize conds, find pivots
    piv, ech = [], []
    for b in conds:
        for p, e in zip(piv, ech):
            if (b >> p) & 1: b ^= e
        if b:
            p = b.bit_length() - 1
            piv.append(p); ech.append(b)
    # back-substitute to reduced echelon
    for i in range(len(ech)):
        for jj in range(len(ech)):
            if i != jj and (ech[jj] >> piv[i]) & 1: ech[jj] ^= ech[i]
    free = [i for i in range(N) if i not in piv]
    kernel = []
    for f in free:
        phi = 1 << f
        for p, e in zip(piv, ech):
            # condition e: parity(phi_bits at e's support)=0 -> set pivot bit
            if bin(e & phi).count("1") % 2: phi |= (1 << p)
        kernel.append(phi)
    print(f"dir{direction} k={k}: N={N} rank(base)={len(conds)} kernel-dim={len(kernel)}")
    for j, phi in enumerate(kernel):
        supp = [lyn[i] for i in range(N) if (phi >> i) & 1]
        tvals = [bin(phi & t).count('1') % 2 for t in tails_pbw]
        dval = bin(phi & delta_pbw).count('1') % 2 if delta_pbw is not None else "-"
        print(f"  phi{j}: tails->{tvals} delta->{dval} support={supp}")
    # crossed-D depth table
    row_r, _ = fox_row(rword, gen, M)
    unit_i = next(i for i in range(3) if row_r[i] % 2 == 1)
    for free_i in [i for i in range(3) if i != unit_i]:
        al = [0, 0, 0]; al[free_i] = 1
        al[unit_i] = (-row_r[free_i] * minv(row_r[unit_i], M)) % M
        def Dv(word):
            row, _ = fox_row(word, gen, M)
            return v2(sum(al[i] * row[i] for i in range(3)) % M, K)
        dbase = min(Dv(w) for w in base_words)
        dt = [Dv(w) for w in tails_w]
        dd = Dv(dword) if dword else "-"
        print(f"  crossedD(free={free_i}): min-depth base={dbase} tails={dt} delta={dd}")

if __name__ == "__main__":
    analyze(1, 3, [[3], [1, 2], [2]])
    analyze(1, 4, [[3], [1, 2], [2]])
    # direction 2 seed search (level-2 kill + P mod 8)
    K = 12; M = 1 << K
    gen, tgt = chi_values(2, K)
    rword2 = d0([[1],[2],[3]])
    wl2 = [t for L in range(1, 3) for t in product(range(3), repeat=L)]
    R2sol = Solver()
    for a in relator_atoms(rword2, 2): R2sol.insert(coords_at(a, 2, 5, wl2))
    base_words = [[1],[2],[3],[1,2],[1,3],[2,3],[2,1],[3,1],[3,2],[1,2,3]]
    found = []
    for T in product(base_words + [inv(w) for w in base_words], repeat=3):
        ok = all((chi_of(T[i], gen, M) - tgt[i]) % 8 == 0 for i in range(3))
        if not ok: continue
        rem, _ = R2sol.reduce(coords_at(dr(list(T)), 2, 5, wl2))
        if rem == 0: found.append(T)
    print("dir2 P-good level-2-killing seeds:", found[:4])
    if found: analyze(2, 3, [list(w) for w in found[0]])
