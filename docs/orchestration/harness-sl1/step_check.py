#!/usr/bin/env python3
"""Validate the induction-step transport identities for the span proof.

Claim 1 (THE step identity, k >= 4):  pi(dbar_{k-1}(w)) = dbar_k(w^2)  in Z_k,
  i.e. the word  [dbar-word(W0,W1,W2)]^2 * [dbar-word(W0^2,W1^2,W2^2)]^{-1}
  lies in lambda_{k+1}, for modifications W_i in lambda_{k-2}.
Claim 2 (bracket absorption): [v, x_tau] * v^2 = dbar-word(v,1,1) -- definitional
  for r0-shape; check the r2 slot-shape analogue too.
Claim 3 (tail transport): trivially word-equal, skipped.

Equality test in Z_k: both words lie in lambda_k (filtration-asserted); their
Magnus coordinates at level k separate Z_k (rank(B)=N_k validated separately),
so coordinate-vanishing of the quotient certifies equality in Z_k.
"""
import sys, random
from itertools import product
from span_model import (inv, comm, pw2, magnus, lyndon_upto, bracketing, coords, rank2)

def dbar_r0(W, tau, b1, b2):
    # dbarWordR0 a s y w = w0^2 * commP(w0,a) * commP(w1,y) * commP(w2,s)
    # role: a = x_tau twisted; brackets with y = x_b2, s = x_b1 (slot1->y, slot2->s)
    return W[0] + W[0] + comm(W[0], [tau + 1]) + comm(W[1], [b2 + 1]) + comm(W[2], [b1 + 1])

def dbar_r2(W, tau, b1, b2):
    # dbarWordR2 s x y w = w2^2 * commP(w2,y) * commP(w0,x) * commP(w1,s)
    # role: y = x_tau twisted (slot 2); brackets with x = x_b2 (slot0), s = x_b1 (slot1)
    return W[2] + W[2] + comm(W[2], [tau + 1]) + comm(W[0], [b2 + 1]) + comm(W[1], [b1 + 1])

def zero_coords(word, k, K, wordlist, tag):
    bits = coords(word, k, K, wordlist, tag)
    return bits == 0

def mods_at(depth, rng, count):
    """Random modification words in lambda_depth: products of <=3 family elements
    bracketing(c)^{2^m} with |c| + m = depth."""
    lyn = [l for l in lyndon_upto(depth) if len(l) <= depth]
    fam = [pw2(bracketing(l), depth - len(l)) for l in lyn]
    out = []
    for _ in range(count):
        n = rng.randint(1, 3)
        w = []
        for _ in range(n):
            f = rng.choice(fam)
            w = w + (inv(f) if rng.random() < 0.3 else f)
        out.append(w)
    return out

def run(k, shape, tau, trials, rng):
    K = k + 4
    wordlist = [t for L in range(1, k + 1) for t in product(range(3), repeat=L)]
    betas = [i for i in range(3) if i != tau]
    b1, b2 = betas
    dbar = dbar_r0 if shape == "r0" else dbar_r2
    pool = mods_at(k - 2, rng, trials * 3)
    ok = True
    for t in range(trials):
        W = [pool[3 * t], pool[3 * t + 1], pool[3 * t + 2]]
        low = dbar(W, tau, b1, b2)                       # dbar_{k-1}-atom word
        W2 = [w + w for w in W]                          # squared modifications
        high = dbar(W2, tau, b1, b2)                     # dbar_k-atom word
        test = low + low + inv(high)                     # pi(atom) * atom'^{-1}
        if not zero_coords(test, k, K, wordlist, f"step {shape} t{t}"):
            print(f"  STEP FAIL k={k} {shape} tau={tau} trial {t}")
            ok = False
    # bracket absorption (single-slot): [v,tau]*v^2 vs dbar(v,1,1)-shape
    v = pool[0]
    if shape == "r0":
        lhs = v + v + comm(v, [tau + 1])
        rhs = dbar_r0([v, [], []], tau, b1, b2)
    else:
        lhs = v + v + comm(v, [tau + 1])
        rhs = dbar_r2([[], [], v], tau, b1, b2)
    if lhs != rhs:  # word-level identity (empty commutators vanish as words? they are [] lists)
        # commP with empty word: comm(w,[]) = inv(w)+[]+w+[] reduces to nothing in the
        # group but is not the empty LIST; check via coordinates instead
        test = lhs + inv(rhs)
        if not zero_coords(test, k, K, wordlist, f"absorb {shape}"):
            print(f"  ABSORB FAIL k={k} {shape} tau={tau}")
            ok = False
    print(f"k={k} {shape} tau={tau}: {'OK' if ok else 'FAIL'} ({trials} step trials)")
    return ok

if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    rng = random.Random(20260726)
    allok = True
    for k in range(4, kmax + 1):
        for shape, tau in (("r0", 0), ("r2", 2)):
            allok &= run(k, shape, tau, trials=6, rng=rng)
    print("STEP IDENTITY VALIDATED" if allok else "STEP IDENTITY FAILS")
