#!/usr/bin/env python3
"""Validate the Magnus-functional architecture for span_free_r0/r2 (GL-campaign).

Everything is computed against the HONEST free group via truncated Magnus expansion
mu: F(3) -> Z_2<<xi_0,xi_1,xi_2>>, x_i |-> 1+xi_i, coefficients mod 2^K, words of
length <= k.  Coordinates of z in lambda_k: bit_{(w, j)}(z) := (coeff_w(mu z) / 2^j) mod 2
with j = k - |w|  (well-defined iff 2^{k-|w|} | coeff_w -- asserted = filtration lemma).

Checks per level k and role tau (twisted generator; tails = the other two letters):
  (F)  filtration: every family/column word lands in 1+m^k coefficientwise (assert).
  (U)  the PBW family B_k = { bracketing(c)^{2^{k-|c|}} : c Lyndon, |c| <= k } has
       coordinate rank exactly N_k = #Lyndon words of length <= k.
  (S)  full column set (twisted D-columns + both bracket-column families over the whole
       modification family + 2 tails) spans the same space: rank = N_k, joint rank = N_k.
  (S') SELECTED subset (all twisted + brackets at weight-(k-1) modifications + tails).
  (D)  rank WITHOUT tails = N_k - 2 (spike: coker of pure d-bar = 2, free group).
"""
import sys
from itertools import product

# ---------- free-group words: list of nonzero ints, +(i+1) = x_i, -(i+1) = inverse
def inv(w): return [-a for a in reversed(w)]
def comm(a, b): return inv(a) + inv(b) + a + b     # repo commP x y = x^-1 y^-1 x y
def pw2(w, m):                                      # w^(2^m)
    for _ in range(m): w = w + w
    return w

# ---------- truncated Magnus series: dict {tuple(word over 0..2): int mod 2^K}
def series_mul(a, b, maxlen, mod):
    out = {}
    for wa, ca in a.items():
        if ca == 0: continue
        la = len(wa)
        for wb, cb in b.items():
            if la + len(wb) > maxlen or cb == 0: continue
            w = wa + wb
            v = (out.get(w, 0) + ca * cb) % mod
            out[w] = v
    return out

def series_inv(a, maxlen, mod):
    n = {w: (-c) % mod for w, c in a.items() if len(w) >= 1}
    out = {(): 1}
    term = {(): 1}
    for _ in range(maxlen):
        term = series_mul(term, n, maxlen, mod)
        if not term: break
        for w, c in term.items():
            out[w] = (out.get(w, 0) + c) % mod
    return out

def magnus(word, maxlen, mod):
    gens, invs = {}, {}
    out = {(): 1}
    for a in word:
        i = abs(a) - 1
        if a > 0:
            if i not in gens: gens[i] = {(): 1, (i,): 1}
            out = series_mul(out, gens[i], maxlen, mod)
        else:
            if i not in invs:
                invs[i] = series_inv({(): 1, (i,): 1}, maxlen, mod)
            out = series_mul(out, invs[i], maxlen, mod)
    return out

# ---------- Lyndon words over 0<1<2 (Duval), standard factorization, bracketing
def lyndon_upto(n, alph=3):
    res = []
    w = [0]
    res.append(tuple(w))
    while True:
        w = (w * (n // len(w) + 1))[:n]
        while w and w[-1] == alph - 1:
            w.pop()
        if not w:
            break
        w[-1] += 1
        res.append(tuple(w))
    return sorted(res, key=lambda t: (len(t), t))

def is_lyndon(w):
    return all(w < w[i:] + w[:i] for i in range(1, len(w)))

def std_fact(w):
    for i in range(1, len(w)):          # smallest i => longest proper Lyndon suffix
        v = w[i:]
        if is_lyndon(v):
            return w[:i], v
    raise ValueError(w)

def bracketing(w):
    if len(w) == 1: return [w[0] + 1]
    u, v = std_fact(w)
    return comm(bracketing(u), bracketing(v))

# ---------- GF(2) rank via python ints as bitvectors
def rank2(rows):
    basis = []
    for r in rows:
        for b in basis:
            if (r ^ b) < r: r ^= b
        if r: basis.append(r)
        basis.sort(reverse=True)
    return len(basis)

def coords(word, k, K, wordlist, tag):
    mod = 1 << K
    mu = magnus(word, k, mod)
    assert mu.get((), 0) % mod == 1 % mod, f"const term != 1 for {tag}"
    bits = 0
    for idx, w in enumerate(wordlist):
        c = mu.get(w, 0) % mod
        j = k - len(w)
        assert c % (1 << j) == 0, \
            f"filtration FAIL ({tag}): coeff at {w} = {c}, need 2^{j}"
        if (c >> j) & 1: bits |= (1 << idx)
    return bits

def run(k, tau):
    K = k + 3
    lyn = lyndon_upto(k)
    Nk = len(lyn)
    wordlist = [t for L in range(1, k + 1) for t in product(range(3), repeat=L)]
    betas = [i for i in range(3) if i != tau]

    B = [coords(pw2(bracketing(l), k - len(l)), k, K, wordlist, f"B{l}") for l in lyn]
    rB = rank2(B[:])

    twisted, brackets, brackets_top = [], [], []
    for c in lyn:
        if len(c) > k - 1: continue
        m = k - 1 - len(c)
        u = pw2(bracketing(c), m)
        twisted.append(coords(u + u + comm(u, [tau + 1]), k, K, wordlist, f"D{c}"))
        for b in betas:
            col = coords(comm(u, [b + 1]), k, K, wordlist, f"[{c},{b}]")
            brackets.append(col)
            if len(c) == k - 1: brackets_top.append(col)
    tails = [coords(pw2([b + 1], k - 1), k, K, wordlist, f"tail{b}") for b in betas]

    full = twisted + brackets + tails
    sel = twisted + brackets_top + tails
    rFull, rSel = rank2(full[:]), rank2(sel[:])
    rNoTails = rank2((twisted + brackets)[:])
    rJoint = rank2((full + B)[:])
    ok = (rB == Nk) and (rFull == Nk) and (rJoint == Nk) and (rNoTails == Nk - 2)
    okSel = (rSel == Nk)
    print(f"k={k} tau={tau}: N_k={Nk}  rank(B)={rB}  rank(cols+tails)={rFull}  "
          f"rank(joint)={rJoint}  rank(no-tails)={rNoTails}  rank(SELECTED)={rSel}  "
          f"=> {'OK' if ok else 'FAIL'}{'  SEL-OK' if okSel else '  SEL-FAIL'}")
    return ok, okSel

if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    allok, allsel = True, True
    for k in range(3, kmax + 1):
        for tau in (0, 2):
            ok, okSel = run(k, tau)
            allok, allsel = allok and ok, allsel and okSel
    print("ALL CORE CHECKS PASS" if allok else "CORE FAILURE",
          "| SELECTED certificate:", "uniform-OK" if allsel else "NOT sufficient")
