#!/usr/bin/env python3
"""SL1 mechanism hunt.  Model the tower layers Z_k(D) = Z_k(F)/R_k in Magnus
coordinates; test SL1 (delta in Im dbar + relator layer) at chi-good seeds vs
chi-violating controls; tabulate crossed-derivation (Fox/chi) depths.

Direction 1: tower D_R = F(s,x,y)/N(drWord), chi-gen-values (S,X,Y);
  tested relator d0Word(T) = T0^2 T1^4 [T1,T2]; T-targets (-1, 1, eta).
Direction 2: tower D0 = F(a,s,y)/N(d0Word), chi-gen-values (-1,1,eta);
  tested relator drWord(T) = (T1^T0)^-1 T1^-3 T2^2 [T2, T2^T0]; targets (S,X,Y).
"""
import sys
from itertools import product
from span_model import inv, comm, pw2, lyndon_upto, bracketing, coords, rank2

def conj(x, g):  return inv(g) + x + g                     # conjP x g = g^-1 x g
def d0(T):       return T[0]+T[0] + T[1]*4 + comm(T[1], T[2])
def dr(T):       return inv(conj(T[1], T[0])) + inv(T[1]*3) + T[2]+T[2] \
                        + comm(T[2], conj(T[2], T[0]))

# ---------- 2-adic scalar arithmetic mod 2^K
def minv(a, M):  return pow(a, -1, M)
def hensel_X(K):
    M, Z = 1 << K, 437                                     # root of Z^3+2Z^2+1, =437 mod 2^9
    for _ in range(8):
        f  = (Z*Z*Z + 2*Z*Z + 1) % M
        fp = (3*Z*Z + 4*Z) % M
        Z  = (Z - f * minv(fp, M)) % M
    assert (Z*Z*Z + 2*Z*Z + 1) % M == 0
    return Z

def chi_values(direction, K):
    M = 1 << K
    if direction == 1:
        X = hensel_X(K); S = (-X**3 * minv((X*X + X + 1) % M, M)) % M; Y = (-X*X) % M
        gen = (S, X, Y); tgt = (M - 1, 1, (-minv(3, M)) % M)
    else:
        eta = (-minv(3, M)) % M
        X = hensel_X(K); S = (-X**3 * minv((X*X + X + 1) % M, M)) % M; Y = (-X*X) % M
        gen = (M - 1, 1, eta); tgt = (S, X, Y)
    return gen, tgt

def chi_of(word, gen, M):
    v = 1
    for a in word:
        g = gen[abs(a) - 1]
        v = (v * (g if a > 0 else minv(g, M))) % M
    return v

def fox_row(word, gen, M):
    """Crossed derivation: D(w) = sum over letters of chi(prefix)*D(letter);
    returns the 3-vector of coefficients of D(g_i)."""
    row, chi = [0, 0, 0], 1
    for a in word:
        i = abs(a) - 1
        g = gen[i]
        if a > 0:
            row[i] = (row[i] + chi) % M
            chi = (chi * g) % M
        else:
            gi = minv(g, M)
            row[i] = (row[i] - chi * gi) % M
            chi = (chi * gi) % M
    return row, chi

def v2(n, K):
    n %= (1 << K)
    if n == 0: return K
    v = 0
    while n % 2 == 0: n //= 2; v += 1
    return v

# ---------- families
def relator_layer(rword, k, K, wordlist):
    """R_k: coords of all pi/ad-compositions taking r (level 2) to level k."""
    out, frontier = [], [(rword, 2)]
    while frontier:
        w, lvl = frontier.pop()
        if lvl == k:
            out.append(coords(w, k, K, wordlist, "R"))
            continue
        frontier.append((w + w, lvl + 1))
        for g in (1, 2, 3):
            frontier.append((comm(w, [g]), lvl + 1))
    return out

def dbar_atoms(seed, k, K, wordlist, shape):
    """Single-slot dbar atoms at the seed slots, modifications = Lyndon family."""
    lyn = [l for l in lyndon_upto(k - 1) if len(l) <= k - 1]
    mods = [pw2(bracketing(l), k - 1 - len(l)) for l in lyn]
    A = []
    for w in mods:
        if shape == "r0":   # dbarWordR0 a s y w = w0^2 [w0,a] [w1,y] [w2,s] at (a,s,y)=seed
            A.append(coords(w + w + comm(w, seed[0]), k, K, wordlist, "A0"))
            A.append(coords(comm(w, seed[2]), k, K, wordlist, "A1"))
            A.append(coords(comm(w, seed[1]), k, K, wordlist, "A2"))
        else:               # dbarWordR2 s x y w = w2^2 [w2,y] [w0,x] [w1,s]
            A.append(coords(w + w + comm(w, seed[2]), k, K, wordlist, "B2"))
            A.append(coords(comm(w, seed[1]), k, K, wordlist, "B0"))
            A.append(coords(comm(w, seed[0]), k, K, wordlist, "B1"))
    return A

TOWER_DIMS = {3: 10, 4: 20, 5: 44, 6: 94}                  # spike, f-blind

def run(direction, k, seeds):
    K = k + 5
    M = 1 << K
    gen, tgt = chi_values(direction, K)
    wordlist = [t for L in range(1, k + 1) for t in product(range(3), repeat=L)]
    Nk = len(lyndon_upto(k))
    rword = dr([[1], [2], [3]]) if direction == 1 else d0([[1], [2], [3]])
    tested = d0 if direction == 1 else dr
    shape = "r0" if direction == 1 else "r2"
    R = relator_layer(rword, k, K, wordlist)
    rR = rank2(R[:])
    dim_tower = Nk - rR
    cal = "OK " if dim_tower == TOWER_DIMS.get(k) else f"BAD(dim={dim_tower})"
    print(f"dir{direction} k={k}: N_k={Nk} rank(R_k)={rR} tower-dim={dim_tower} [{cal}]")
    for name, seed in seeds.items():
        # chi mod 8 check of the seed
        chis = [chi_of(s, gen, M) % 8 for s in seed]
        good = all((chi_of(seed[i], gen, M) - tgt[i]) % 8 == 0 for i in range(3))
        A = dbar_atoms(seed, k, K, wordlist, shape)
        base = R + A
        rBase = rank2(base[:])
        delta = coords(tested(seed), k, K, wordlist, "delta")
        rWith = rank2(base + [delta])
        member = (rWith == rBase)
        # tails at the seed
        t_idx = (1, 2) if shape == "r0" else (0, 1)
        tails = [coords(pw2(seed[i], k - 1), k, K, wordlist, "tail") for i in t_idx]
        rTails = rank2(base + tails)
        print(f"  seed {name} chi%8={chis} P={'YES' if good else 'NO '} "
              f"rank(R+A)={rBase} (coker {dim_tower - (rBase - rR)}) "
              f"delta{'IN' if member else 'OUT'} tails+{rTails - rBase}")
    return gen, tgt, M

def depth_tables(direction, k):
    """Crossed-derivation depth scan: v2 of kernel-D on atoms/tails/delta."""
    K = k + 6
    M = 1 << K
    gen, tgt = chi_values(direction, K)
    rword = dr([[1], [2], [3]]) if direction == 1 else d0([[1], [2], [3]])
    tested = d0 if direction == 1 else dr
    shape = "r0" if direction == 1 else "r2"
    row_r, _ = fox_row(rword, gen, M)
    # kernel of D(r)=0: solve a0*row0+a1*row1+a2*row2 = 0 mod 2^K; row entries:
    # find a unit entry, express its alpha in terms of the others
    unit_i = next(i for i in range(3) if row_r[i] % 2 == 1)
    others = [i for i in range(3) if i != unit_i]
    kernels = []
    for free in others:
        alpha = [0, 0, 0]
        alpha[free] = 1
        alpha[unit_i] = (-row_r[free] * minv(row_r[unit_i], M)) % M
        kernels.append(alpha)
    seed = SEEDS[(direction, "good")]
    lyn = [l for l in lyndon_upto(k - 1) if len(l) <= k - 1]
    mods = [pw2(bracketing(l), k - 1 - len(l)) for l in lyn]
    atoms = []
    for w in mods:
        if shape == "r0":
            atoms += [w + w + comm(w, seed[0]), comm(w, seed[2]), comm(w, seed[1])]
        else:
            atoms += [w + w + comm(w, seed[2]), comm(w, seed[1]), comm(w, seed[0])]
    # relator-layer words too
    rl, frontier = [], [(rword, 2)]
    while frontier:
        w, lvl = frontier.pop()
        if lvl == k: rl.append(w); continue
        frontier.append((w + w, lvl + 1))
        for g in (1, 2, 3): frontier.append((comm(w, [g]), lvl + 1))
    t_idx = (1, 2) if shape == "r0" else (0, 1)
    tails = [pw2(seed[i], k - 1) for i in t_idx]
    delta = tested(seed)
    for j, al in enumerate(kernels):
        def Dv(word):
            row, _ = fox_row(word, gen, M)
            return v2(sum(al[i] * row[i] for i in range(3)), K)
        da = sorted(set(Dv(w) for w in atoms))
        drl = sorted(set(Dv(w) for w in rl))
        print(f"dir{direction} k={k} D{j}: atoms v2 in {da[:6]}..  R-layer {drl[:6]}..  "
              f"tails {[Dv(t) for t in tails]}  delta {Dv(delta)}")

SEEDS = {
    (1, "good"): ([3], [1, 2], [2]),          # (y, s*x, x) in letters s=1,x=2,y=3
    (2, "good"): ([1, 3], [3], [-1]),         # (s*y, y, a^-1)? will test variants
}

if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    # find good + control seeds by mod-8 chi and level-3 relator kill
    for direction in (1, 2):
        K = 12; M = 1 << K
        gen, tgt = chi_values(direction, K)
        rword = dr([[1], [2], [3]]) if direction == 1 else d0([[1], [2], [3]])
        tested = d0 if direction == 1 else dr
        wordlist3 = [t for L in range(1, 3) for t in product(range(3), repeat=L)]
        # level-2 test: relator-killed mod lambda_3 <=> coords at k=2 lie in R_2-span
        R2 = relator_layer(rword, 2, 5, wordlist3)
        cands = []
        base_words = [[1], [2], [3], [1, 2], [1, 3], [2, 3], [1, 2, 3]]
        for T in product(base_words + [inv(w) for w in base_words], repeat=3):
            chis = tuple((chi_of(T[i], gen, M) - tgt[i]) % 8 for i in range(3))
            try:
                dcoords = coords(tested(list(T)), 2, 5, wordlist3, "s")
            except AssertionError:
                continue
            killed = rank2(R2 + [dcoords]) == rank2(R2[:])
            if killed:
                cands.append((T, chis == (0, 0, 0)))
        goods = [T for T, g in cands if g]
        bads = [T for T, g in cands if not g]
        print(f"dir{direction}: {len(goods)} good / {len(bads)} control seeds "
              f"(showing good {goods[:2]} control {bads[:1]})")
        seeds = {"good": list(goods[0])}
        if bads: seeds["ctrl"] = list(bads[0])
        SEEDS[(direction, "good")] = list(goods[0])
        for k in range(3, kmax + 1):
            run(direction, k, seeds)
        depth_tables(direction, 3)
        depth_tables(direction, 4)
