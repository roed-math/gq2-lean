#!/usr/bin/env python3
"""Exact GF(2) diagnostic for the sheared, tame-corrected hyperbolic source.

This is a finite-action falsification/regression tool, not a general proof. It
implements the actual right-commutator MCompact spelling and HeisLift law from
the Lean sources. Normalized cochains have sigma=tau offsets zero; the tame
correction therefore has zero jets/charge and does not alter these calculations.
We nevertheless check the uncorrected base defect lies in <tau>, and compute
its exact correcting tau exponent. No third-party dependencies are required.

Scope: the strict-row conditions allow these shear profiles algebraically, but
realizability of a particular profile by an actual selected field's transported
unramified character has NOT been established. Neither a finite obstruction nor
a successful shadow regression is a proof of the full field-facing theorem.

Examples:
  python3 scripts/w361_hyperbolic_action_diagnostic.py --self-test
  python3 scripts/w361_hyperbolic_action_diagnostic.py --coefficients 0,0,0,0,1 --full-cohomology
  python3 scripts/w361_hyperbolic_action_diagnostic.py --coefficients 0,1,0,0,0 --shadow --full-cohomology

GF4 uses the basis (1,a), a^2=a+1, S(1)=1,S(a)=1+a, T(1)=a,T(a)=1+a.
For k=(0,0,0,0,1), pure x2=1 and pure V=1 are independent noncoboundary
radical vectors. Both pair against arbitrary normal dual y as y(U)(1), which
the dual cocycle row forces to zero. The full calculation uses correction
exponent16 (1 mod3 and0 mod8), not an odd correction exponent.

With --shadow, test P(R_normalized)*H_raw*P(H_raw)^-1, where P fixes sigma,
kills tau, and replaces Xi by (Xi*tau)^omega2*(tau^omega2)^-1. The same
finite examples then recover the good raw Fox matrix and pairing exactly.
"""

import argparse
import itertools
import json
from functools import lru_cache


def parity(x):
    return x.bit_count() & 1


@lru_cache(None)
def apply_mat(g, v):
    out = 0
    while v:
        bit = v & -v
        out ^= g[bit.bit_length() - 1]
        v ^= bit
    return out


@lru_cache(None)
def compose(g, h):
    return tuple(apply_mat(g, v) for v in h)


@lru_cache(None)
def inverse(g):
    n = len(g)
    rows = [sum(((g[j] >> i) & 1) << j for j in range(n)) | (1 << (n+i))
            for i in range(n)]
    for j in range(n):
        i = next(i for i in range(j, n) if (rows[i] >> j) & 1)
        rows[j], rows[i] = rows[i], rows[j]
        for i in range(n):
            if i != j and ((rows[i] >> j) & 1):
                rows[i] ^= rows[j]
    return tuple(sum(((rows[i] >> (n+j)) & 1) << i for i in range(n)) for j in range(n))


@lru_cache(None)
def dual_apply(g, lam):
    return sum(parity(lam & col) << i for i, col in enumerate(inverse(g)))


def gf_mul(a, b, modulus):
    high = 1 << (modulus.bit_length() - 1)
    out = 0
    while b:
        if b & 1:
            out ^= a
        b >>= 1
        a <<= 1
        if a & high:
            a ^= modulus
    return out


def gf_pow(a, n, modulus):
    out = 1
    while n:
        if n & 1:
            out = gf_mul(out, a, modulus)
        a = gf_mul(a, a, modulus)
        n >>= 1
    return out


def rank(vectors):
    pivots = {}
    for v in vectors:
        while v:
            p = v.bit_length() - 1
            if p in pivots:
                v ^= pivots[p]
            else:
                pivots[p] = v
                break
    return len(pivots)


def kernel(columns):
    pivots = {}
    out = []
    for i, v in enumerate(columns):
        mask = 1 << i
        while v:
            p = v.bit_length() - 1
            if p in pivots:
                w, bits = pivots[p]
                v ^= w
                mask ^= bits
            else:
                pivots[p] = (v, mask)
                break
        if not v:
            out.append(mask)
    return out


class ActionDiagnostic:
    MODULI = {2: 0b111, 3: 0b1011, 4: 0b10011, 6: 0b1000011, 8: 0b100011101}

    def __init__(self, degree, qpower=1, shadow=False):
        self.degree = degree
        self.modulus = self.MODULI[degree]
        self.identity = tuple(1 << i for i in range(degree))
        self.one = (0, 0, 0, self.identity)
        self.tau = tuple(gf_mul(2, 1 << i, self.modulus) for i in range(degree))
        frob = tuple(gf_pow(1 << i, 2, self.modulus) for i in range(degree))
        self.sigma = self.power((0, 0, 0, inverse(frob)), qpower)[3]
        self.q = 2 ** qpower
        self.shadow = shadow
        order_bound = degree * (2**degree - 1)
        two = order_bound & -order_bound
        odd = order_bound // two
        self.omega_exp = odd * pow(odd, -1, 4*two)
        assert self.omega_exp % (4*two) == 1
        assert self.omega_exp % odd == 0
        self.sigma2 = self.power((0, 0, 0, self.sigma), self.omega_exp)[3]
        assert self.conj((0, 0, 0, self.tau), (0, 0, 0, self.sigma))[3] == self.power((0, 0, 0, self.tau), self.q)[3]
        tau_powers = {}
        current = self.identity
        for i in range(2**degree - 1):
            tau_powers[current] = i
            current = compose(current, self.tau)
        assert len(tau_powers) == 2**degree - 1, "Chosen field generator is not primitive"
        self.tau_powers = tau_powers

    def mul(self, p, q):
        a, l, z, g = p
        b, m, w, h = q
        gb = apply_mat(g, b)
        return (a ^ gb, l ^ dual_apply(g, m), z ^ w ^ parity(l & gb), compose(g, h))

    def inv(self, p):
        a, l, z, g = p
        gi = inverse(g)
        return (apply_mat(gi, a), dual_apply(gi, l), z ^ parity(l & a), gi)

    def power(self, p, n):
        if n < 0:
            return self.power(self.inv(p), -n)
        out = self.one
        while n:
            if n & 1:
                out = self.mul(out, p)
            p = self.mul(p, p)
            n >>= 1
        return out

    def product(self, ps):
        out = self.one
        for p in ps:
            out = self.mul(out, p)
        return out

    def conj(self, p, q):
        return self.product([self.inv(q), p, q])

    def comm(self, p, q):
        return self.product([self.inv(p), self.inv(q), p, q])

    def compact(self, generators, alpha):
        sigma, tau, x0, x1, x2, *handles = generators
        m = 2**(alpha-1)
        sig2 = self.power(sigma, self.omega_exp)
        sigm = self.power(sig2, m)
        sig2m = self.power(sig2, 2*m)
        a0 = self.mul(self.inv(x0), self.inv(sigm))
        delta = [self.mul(self.power(self.mul(x, tau), self.omega_exp), self.inv(x))
                 for x in (x0, x1)]
        j2 = self.mul(self.inv(self.conj(x2, sigma)), self.power(self.mul(x2, tau), self.omega_exp))
        erev = self.product([self.conj(delta[1], sig2m), self.conj(delta[1], sigm),
                             self.conj(delta[0], sigm), delta[0]])
        return self.product([self.power(a0, 2), self.comm(a0, x1), sig2m, j2, erev] +
                            [self.comm(handles[i], handles[i+1]) for i in range(0, len(handles), 2)])

    def evaluate(self, coefficients, primal, dual, alpha=2):
        """Coordinates list: x0,x1,x2,U0,V0,U1,V1,...; selected handle is 0."""
        d = self.degree
        mask = (1 << d)-1
        return self.evaluate_full(coefficients, primal << (2*d), dual << (2*d), alpha)[1]

    def evaluate_full(self, coefficients, primal, dual, alpha=2, correction_exp=0):
        d = self.degree
        mask = (1 << d)-1
        final = [((primal >> (i*d)) & mask, (dual >> (i*d)) & mask, 0, g)
                 for i, g in enumerate([self.sigma, self.tau] + [self.identity]*len(coefficients))]
        sigma, tau = final[:2]
        if self.shadow:
            tau2 = self.power(tau, self.omega_exp)
            shadow = [sigma, self.one] + [self.mul(self.power(self.mul(x,tau),self.omega_exp),self.inv(tau2)) for x in final[2:]]
            zero = [0]*len(coefficients)
            wild = self.product([self.normalized_word(shadow,coefficients,alpha),
                                 self.normalized_word(final,zero,alpha),
                                 self.inv(self.normalized_word(shadow,zero,alpha))])
        else:
            wild = self.mul(self.normalized_word(final,coefficients,alpha), self.power(tau, -correction_exp))
        tame = self.mul(self.conj(tau, sigma), self.power(tau, -self.q))
        return tame, wild

    def normalized_word(self, final, coefficients, alpha):
        sigma, tau = final[:2]
        raw = [sigma, tau]
        for i, k in enumerate(coefficients):
            gen = final[i+2]
            raw.append(self.mul(gen, self.power(sigma, k*self.omega_exp)))
        # Hyperbolic backward: compact sigma=raw U; compact x2=raw V;
        # compact U=raw sigma*raw U; compact V=raw x2; others unchanged.
        compact_gens = [raw[5], raw[1], raw[2], raw[3], raw[6], self.mul(raw[0], raw[5]), raw[4]] + raw[7:]
        return self.compact(compact_gens, alpha)

    def full_test(self, coefficients, alpha=2):
        normal = self.test(coefficients, alpha, full_matrix=True)
        tau_exp = normal['correction_tau_exp']
        assert tau_exp is not None
        # A prime-to-two lift of the correcting exponent, divisible by all
        # possible 2-parts in the Heisenberg lift and equal to the defect mod |T|.
        two = 4*(self.degree & -self.degree)
        correction = two * ((tau_exp * pow(two, -1, 2**self.degree-1)) % (2**self.degree-1))
        n = (len(coefficients)+2)*self.degree
        ev = lambda p,y: self.evaluate_full(coefficients,p,y,alpha,correction)
        assert all(w[3] == self.identity for w in ev(0,0))
        pcols = [sum(w[0] << (i*self.degree) for i,w in enumerate(ev(1<<j,0))) for j in range(n)]
        dcols = [sum(w[1] << (i*self.degree) for i,w in enumerate(ev(0,1<<j))) for j in range(n)]
        pk, dk = kernel(pcols), kernel(dcols)
        eta = lambda p,y: ev(p,y)[0][2] ^ ev(p,y)[1][2]
        gram = [sum(eta(p,y) << j for j,y in enumerate(dk)) for p in pk]
        coboundaries = [sum((apply_mat(g,1<<i) ^ (1<<i)) << (j*self.degree)
                           for j,g in enumerate([self.sigma,self.tau]+[self.identity]*len(coefficients)))
                       for i in range(self.degree)]
        assert all(all(w[0] == 0 for w in ev(p,0)) for p in coboundaries)
        assert all(eta(p,y) == 0 for p in coboundaries for y in dk)
        radicals = kernel(gram)
        witnesses = []
        for r in radicals:
            p = 0
            for i,v in enumerate(pk):
                if (r >> i) & 1:
                    p ^= v
            if rank(coboundaries+[p]) > rank(coboundaries):
                witnesses.append(p)
        return dict(normal=normal, correction_prime_to_two_exp=correction,
                    full_primal_d1_rank=rank(pcols), full_dual_d1_rank=rank(dcols),
                    full_primal_kernel_dim=len(pk), full_dual_kernel_dim=len(dk),
                    coboundary_rank=rank(coboundaries), full_pairing_rank=rank(gram),
                    full_radical_dim=len(radicals), noncoboundary_radical_witnesses=witnesses)

    def test(self, coefficients, alpha=2, full_matrix=False):
        n = len(coefficients)*self.degree
        base = self.evaluate(coefficients, 0, 0, alpha)[3]
        correction = self.tau_powers.get(base)
        pcols = [self.evaluate(coefficients, 1 << i, 0, alpha)[0] for i in range(n)]
        dcols = [self.evaluate(coefficients, 0, 1 << i, alpha)[1] for i in range(n)]
        pk = kernel(pcols)
        dk = kernel(dcols)
        gram = [sum(self.evaluate(coefficients, p, mu, alpha)[2] << j for j, mu in enumerate(dk))
                for p in pk]
        result = dict(degree=self.degree, q=self.q, alpha=alpha, coefficients=coefficients, shadow=self.shadow,
                      omega=self.omega_exp, correction_tau_exp=correction,
                      primal_row_rank=rank(pcols), dual_row_rank=rank(dcols),
                      primal_normal_dim=len(pk), dual_normal_dim=len(dk),
                      pairing_rank=rank(gram), left_radical_dim=len(pk)-rank(gram),
                      right_radical_dim=len(dk)-rank(gram))
        if full_matrix:
            result.update(primal_columns=pcols, dual_columns=dcols,
                          primal_kernel=pk, dual_kernel=dk, gram=gram)
        return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--degree', type=int, default=2)
    parser.add_argument('--alpha', type=int, default=2)
    parser.add_argument('--qpower', type=int, default=1)
    parser.add_argument('--coefficients', type=str, default='0,0,0,0,0')
    parser.add_argument('--sweep', action='store_true')
    parser.add_argument('--full-matrix', action='store_true')
    parser.add_argument('--full-cohomology', action='store_true')
    parser.add_argument('--shadow', action='store_true', help='Test projection-shadow repair instead of corrected original source')
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    if args.self_test:
        baseline = ActionDiagnostic(2).full_test([0,0,0,0,0])
        assert baseline['full_pairing_rank'] == 8
        for coefficients in ([0,0,0,0,1],[0,1,0,0,0],[0,1,0,0,1]):
            bad = ActionDiagnostic(2).full_test(coefficients)
            assert bad['full_primal_d1_rank'] == bad['full_dual_d1_rank'] == 4
            assert bad['coboundary_rank'] == 2
            assert bad['full_pairing_rank'] == 6
            fixed = ActionDiagnostic(2,shadow=True).full_test(coefficients)
            assert fixed['full_pairing_rank'] == 8
            assert not fixed['noncoboundary_radical_witnesses']
            assert fixed['normal']['primal_columns'] == baseline['normal']['primal_columns']
            assert fixed['normal']['dual_columns'] == baseline['normal']['dual_columns']
            assert fixed['normal']['gram'] == baseline['normal']['gram']
        print('PASS: raw baseline, three strict-row radical diagnostics, and shadow repairs')
        return
    test = ActionDiagnostic(args.degree, args.qpower, args.shadow)
    if args.sweep:
        profiles = ([0, b, 0, c, d] for b, c, d in itertools.product(range(args.degree), repeat=3) if c % 2 == 0)
    else:
        profiles = [list(map(int, args.coefficients.split(',')))]
    for coefficients in profiles:
        result = test.full_test(coefficients, args.alpha) if args.full_cohomology else test.test(coefficients, args.alpha, args.full_matrix)
        print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()

