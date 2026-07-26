#!/usr/bin/env python3
"""SL1-N core: level-climb refinement, coker functionals, phi(delta) regression.

Model (inherited from `span_model.py` / `sl1_hunt*.py`, calibrated in the spike):
  * free group F3 on the TOWER letters (dir 1: (s,x,y) = 1,2,3; dir 2: (a,s,y) = 1,2,3);
  * Magnus expansion mod 2^K truncated at word length k;
  * Z_j(F) coordinates: bit_(w) = (coeff_w(mu z) / 2^{j-|w|}) mod 2 for |w| <= j;
  * Z_k(D) = Z_k(F) / R_k, R_k = span of the level-k layer of the PRESENTING relator;
  * delta(T) = class of the descent-corrected TESTED relator word at the triple T.
"""
import sys
from itertools import product

from span_model import (inv, comm, pw2, lyndon_upto, bracketing, magnus,
                        series_mul, rank2, std_fact)
from sl1_hunt import conj, d0, dr, chi_values, chi_of, minv, v2
from sl1_hunt2 import Solver

# --------------------------------------------------------------------------- words
def freered(w):
    out = []
    for a in w:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return out

def abel2(w):
    """exponent-sum vector mod 2 (bitmask over letters 0,1,2)."""
    v = 0
    for a in w:
        v ^= 1 << (abs(a) - 1)
    return v

def gen_matrix_ok(T):
    """Frattini/generation test: the mod-2 abelianized triple must be a GL_3(F_2) basis."""
    return rank2([abel2(t) for t in T]) == 3

def frattini(T):
    return tuple(abel2(t) for t in T)

# --------------------------------------------------------------------------- Magnus
class Mag:
    """Memoized truncated Magnus expansion (divide & conquer on the word)."""
    def __init__(self, maxlen, K):
        self.maxlen, self.mod, self.memo = maxlen, 1 << K, {}

    def of(self, w):
        t = tuple(w)
        r = self.memo.get(t)
        if r is not None:
            return r
        if len(t) <= 6:
            r = magnus(list(t), self.maxlen, self.mod)
        else:
            h = len(t) // 2
            r = series_mul(self.of(t[:h]), self.of(t[h:]), self.maxlen, self.mod)
        self.memo[t] = r
        return r

# --------------------------------------------------------------------------- context
class Ctx:
    """Everything tied to (direction, level k)."""
    def __init__(self, direction, k, Kextra=6):
        self.direction, self.k = direction, k
        self.K = k + Kextra
        self.M = self.mod = 1 << self.K
        self.gen, self.tgt = chi_values(direction, self.K)
        # presenting relator of the tower / tested relator word shape
        self.rword = dr([[1], [2], [3]]) if direction == 1 else d0([[1], [2], [3]])
        self.tested = d0 if direction == 1 else dr
        self.shape = "r0" if direction == 1 else "r2"
        self.tail_slots = (1, 2) if direction == 1 else (0, 1)
        self.auto_slot = 0 if direction == 1 else 2
        self.mag = Mag(k, self.K)
        self.wl = {j: [t for L in range(1, j + 1) for t in product(range(3), repeat=L)]
                   for j in range(2, k + 1)}
        self.lyn = lyndon_upto(k)
        self._rat, self._ratc, self._cc = {}, {}, {}
        self._pbw = None

    # ---- coordinates
    def coords(self, w, j=None, tag=""):
        j = self.k if j is None else j
        key = (tuple(w), j)
        c = self._cc.get(key)
        if c is not None:
            return c
        mu = self.mag.of(w)
        bits = 0
        for idx, ww in enumerate(self.wl[j]):
            c = mu.get(ww, 0) % self.mod
            e = j - len(ww)
            if e > 0:
                assert c % (1 << e) == 0, f"not in lambda_{j} [{tag}]: {ww} coeff {c}"
            if (c >> e) & 1:
                bits |= 1 << idx
        self._cc[key] = bits
        return bits

    # ---- relator layer
    def ratoms(self, j):
        if j in self._rat:
            return self._rat[j]
        out, frontier = [], [(self.rword, 2)]
        while frontier:
            w, lvl = frontier.pop()
            if lvl == j:
                out.append(freered(w))
                continue
            frontier.append((w + w, lvl + 1))
            for g in (1, 2, 3):
                frontier.append((comm(w, [g]), lvl + 1))
        self._rat[j] = out
        return out

    def ratom_coords(self, j):
        if j not in self._ratc:
            self._ratc[j] = [self.coords(a, j, "R") for a in self.ratoms(j)]
        return self._ratc[j]

    # ---- PBW basis of Z_k(F)
    def pbw(self):
        if self._pbw is None:
            sol = Solver()
            for l in self.lyn:
                sol.insert(self.coords(pw2(bracketing(l), self.k - len(l)), self.k, "pbw"))
            self._pbw = sol
        return self._pbw

    def in_pbw(self, v):
        rem, combo = self.pbw().reduce(v)
        assert rem == 0, "vector outside the PBW span"
        return combo

    @property
    def letters(self):
        return "sxy" if self.direction == 1 else "asy"

    def _bracket_name(self, l):
        """Name of the Lyndon bracketing, following the standard factorization."""
        if len(l) == 1:
            return self.letters[l[0]]
        u, v = std_fact(l)
        return f"[{self._bracket_name(u)},{self._bracket_name(v)}]"

    def pbw_name(self, i):
        """Readable name of PBW basis element i: pi^{k-|l|} bracketing(l)."""
        l = self.lyn[i]
        m = self.k - len(l)
        return (f"pi^{m}." if m > 1 else "pi." if m == 1 else "") + self._bracket_name(l)

    def supp_names(self, phi):
        return [self.pbw_name(i) for i in range(len(self.lyn)) if (phi >> i) & 1]

    def column(self, root, addir):
        """PBW-dual mask of the column {pi^{k-1-m} (ad addir)^m (root) : m = 0..k-1}.
        The Lyndon representative of (ad c)^m(z) is c^m z if c < z, else z c^m."""
        idx = {l: i for i, l in enumerate(self.lyn)}
        phi = 0
        for m in range(self.k):
            w = ((addir,) * m + (root,)) if addir < root else ((root,) + (addir,) * m)
            if w not in idx:
                return None
            phi |= 1 << idx[w]
        return phi

    def column_name(self, root, addir):
        return f"col({self.letters[root]}; ad {self.letters[addir]})"

    # ---- dbar
    def dbar_atom(self, u, slot, T):
        if self.shape == "r0":            # dbar a s y w = w0^2 [w0,a][w1,y][w2,s]
            if slot == 0:
                return freered(u + u + comm(u, T[0]))
            if slot == 1:
                return freered(comm(u, T[2]))
            return freered(comm(u, T[1]))
        else:                             # dbar s x y w = w2^2 [w2,y][w0,x][w1,s]
            if slot == 2:
                return freered(u + u + comm(u, T[2]))
            if slot == 0:
                return freered(comm(u, T[1]))
            return freered(comm(u, T[0]))

    def mods(self, j=None):
        """Generators of lambda_j mod lambda_{j+1} (default j = k-1)."""
        j = self.k - 1 if j is None else j
        return [pw2(bracketing(l), j - len(l)) for l in lyndon_upto(j) if len(l) <= j]

    def dbar_coords(self, T, w):
        """coords of dbar_T(w) for a slotwise modification w = (w0,w1,w2) (word lists)."""
        v = 0
        for slot in range(3):
            if w[slot]:
                v ^= self.coords(self.dbar_atom(w[slot], slot, T), self.k, "dbar")
        return v

    # ---- chi
    def chi(self, w):
        return chi_of(w, self.gen, self.M)

    def dev(self, T):
        """chi(T_i)/target_i in (Z/2^K)^x."""
        return [(self.chi(T[i]) * minv(self.tgt[i], self.M)) % self.M for i in range(3)]

    def chidepth(self, T):
        return [v2(d - 1, self.K) for d in self.dev(T)]

    def digits(self, T, level):
        """deviation digit at 2^level (requires dev = 1 mod 2^level)."""
        out = []
        for d in self.dev(T):
            r = (d - 1) % self.M
            assert r % (1 << level) == 0, f"chi-depth < {level}: dev-1 = {r}"
            out.append((r >> level) & 1)
        return out

    # ---- descent of the tested relator
    def descend(self, word, upto=None):
        """Push `word` into lambda_upto(F) by relator atoms; None if it is not
        relator-deep enough (i.e. the triple fails the relator clause)."""
        upto = self.k if upto is None else upto
        cur = freered(word)
        for j in range(2, upto):
            try:
                v = self.coords(cur, j, "descend")
            except AssertionError:
                return None
            if v == 0:
                continue
            atoms, avs = self.ratoms(j), self.ratom_coords(j)
            sol = Solver()
            for av in avs:
                sol.insert(av)
            rem, combo = sol.reduce(v)
            if rem != 0:
                return None
            for i, a in enumerate(atoms):
                if (combo >> i) & 1:
                    cur = freered(cur + inv(a))
        return cur

    def delta(self, T, upto=None):
        """Descent-corrected delta(T) as a word in lambda_k(F), or None."""
        return self.descend(self.tested(list(T)), upto)

    def delta_coords(self, T):
        d = self.delta(T)
        return None if d is None else self.coords(d, self.k, "delta")

    # ---- clause checks
    def relator_ok(self, T, upto=None):
        return self.delta(T, upto) is not None

    def is_sP(self, T, level=None):
        """T in S^P_level (relator kill in Q_level, generation, chi mod 2^level)."""
        level = self.k if level is None else level
        if not gen_matrix_ok(T):
            return False, "gen"
        if self.delta(T, level) is None:
            return False, "rel"
        if any((d - 1) % (1 << level) for d in self.dev(T)):
            return False, "chi"
        return True, "ok"

    # ---- the span / coker machinery
    def base_span(self, T, with_combo=False):
        """Solver over R_k + Im dbar_T; the generator order is
        [R-atoms] ++ [(mod u, slot) in mods x (0,1,2)]."""
        sol = Solver()
        for av in self.ratom_coords(self.k):
            sol.insert(av)
        nR = sol.n
        gens = []
        for u in self.mods():
            for slot in (0, 1, 2):
                sol.insert(self.coords(self.dbar_atom(u, slot, T), self.k, "atom"))
                gens.append((u, slot))
        return (sol, nR, gens) if with_combo else sol

    def tails(self, T):
        return [pw2(list(T[i]), self.k - 1) for i in self.tail_slots]

    def tail_coords(self, T):
        return [self.coords(t, self.k, "tail") for t in self.tails(T)]

    def solve_delta(self, T):
        """Find a lambda_{k-1}-modification w with dbar_T(w) = delta(T) in Z_k(D).
        Returns (w0,w1,w2) as word lists, or None if delta is not in the span."""
        dv = self.delta_coords(T)
        if dv is None:
            return None
        sol, nR, gens = self.base_span(T, with_combo=True)
        rem, combo = sol.reduce(dv)
        if rem != 0:
            return None
        w = [[], [], []]
        for i, (u, slot) in enumerate(gens):
            if (combo >> (nR + i)) & 1:
                w[slot] = w[slot] + u
        return w

    def coker_functionals(self, T):
        """The dual basis (phi_a, phi_b) of the 2-dim coker of R_k + Im dbar_T,
        normalized against the two tails: phi_i(tail_j) = delta_ij.
        Returns (phi_a, phi_b) as bitmasks in the PBW-dual basis."""
        sol, nR, gens = self.base_span(T, with_combo=True)
        base = [self.in_pbw(v) for v, _ in sol.rows]
        N = len(self.lyn)
        # reduced echelon of the base rows, then the orthogonal complement
        piv, ech = [], []
        for b in base:
            for p, e in zip(piv, ech):
                if (b >> p) & 1:
                    b ^= e
            if b:
                p = b.bit_length() - 1
                piv.append(p)
                ech.append(b)
        for i in range(len(ech)):
            for jj in range(len(ech)):
                if i != jj and (ech[jj] >> piv[i]) & 1:
                    ech[jj] ^= ech[i]
        free = [i for i in range(N) if i not in piv]
        ker = []
        for f in free:
            phi = 1 << f
            for p, e in zip(piv, ech):
                if bin(e & phi).count("1") % 2:
                    phi |= 1 << p
            ker.append(phi)
        assert len(ker) == 2, f"coker dim = {len(ker)}, expected 2"
        tp = [self.in_pbw(v) for v in self.tail_coords(T)]
        # 2x2 matrix ker_i(tail_j); invert over F2 to get the dual basis
        m = [[bin(ker[i] & tp[j]).count("1") % 2 for j in (0, 1)] for i in (0, 1)]
        det = (m[0][0] * m[1][1] ^ m[0][1] * m[1][0]) & 1
        assert det == 1, f"tails do not span the coker: {m}"
        # inverse of [[a,b],[c,d]] over F2 (det=1) is [[d,b],[c,a]]
        a, b, c, dd = m[0][0], m[0][1], m[1][0], m[1][1]
        phi_a = (ker[0] if dd else 0) ^ (ker[1] if b else 0)
        phi_b = (ker[0] if c else 0) ^ (ker[1] if a else 0)
        # check
        assert bin(phi_a & tp[0]).count("1") % 2 == 1
        assert bin(phi_a & tp[1]).count("1") % 2 == 0
        assert bin(phi_b & tp[0]).count("1") % 2 == 0
        assert bin(phi_b & tp[1]).count("1") % 2 == 1
        return phi_a, phi_b

    def tail_coeffs(self, T, phis=None):
        """(c_a, c_b): coordinates of delta(T) in the coker w.r.t. the tail basis.
        (0,0) iff delta in R_k + Im dbar_T."""
        dv = self.delta_coords(T)
        if dv is None:
            return None
        phi_a, phi_b = self.coker_functionals(T) if phis is None else phis
        dp = self.in_pbw(dv)
        return (bin(phi_a & dp).count("1") % 2, bin(phi_b & dp).count("1") % 2)

    # ---- SL2 digit-fix witnesses (memo section 1.2)
    def digit_moves(self, T):
        """The two explicit kernel witnesses; each is a slotwise modification."""
        m = self.k - 2
        if self.direction == 1:
            v = pw2(list(T[1]) + list(T[2]), m)
            return [[[], pw2(list(T[2]), m), []],          # slot1 <- t2^{2^{k-2}}
                    [[], v, v]]                            # slots1,2 <- (t1t2)^{2^{k-2}}
        else:
            return [[pw2(list(T[1]), m), [], []],          # slot0 <- t1^{2^{k-2}}
                    [[], pw2(list(T[0]), m), []]]          # slot1 <- t0^{2^{k-2}}


def mul_triple(T, w):
    return [freered(list(T[i]) + list(w[i])) for i in range(3)]


# --------------------------------------------------------------------------- seeds
def word_of_mask(m):
    return [j + 1 for j in range(3) if (m >> j) & 1]

def all_frattini_classes():
    """The 168 GL_3(F_2) mod-2 seed classes, with canonical short-word representatives."""
    out = []
    for m in product(range(1, 8), repeat=3):
        T = [word_of_mask(x) for x in m]
        if gen_matrix_ok(T):
            out.append((m, T))
    return out

def seed_census(direction, verbose=False):
    """The k=3 census: which mod-2 classes kill the relator in Q_3, and which satisfy P.
    (Both clauses depend only on the mod-2 class: chi(lambda_2) is in 1+8Z_2 and the
    lambda_2-shift of the relator dies in Z_2.)"""
    c = Ctx(direction, 3)
    rows = []
    for m, T in all_frattini_classes():
        if not c.relator_ok(T, 3):
            continue
        okchi = all((d - 1) % 8 == 0 for d in c.dev(T))
        rows.append((m, T, okchi, [d % 8 for d in c.dev(T)]))
    if verbose:
        print(f"dir{direction}: 168 mod-2 classes, {len(rows)} kill the relator in Q_3, "
              f"{sum(r[2] for r in rows)} also satisfy P")
        for m, T, okchi, dv in rows:
            print(f"   class {m} T={T} chi/target %8={dv} P={'YES' if okchi else 'no'}")
    return rows

def good_seeds(direction, verbose=False):
    return [T for _, T, ok, _ in seed_census(direction, verbose) if ok]


# --------------------------------------------------------------------------- climb
def climb(ctx, T, want=(0, 0), verbose=False, tag="", extra_kernel=None):
    """The greedy level-climb.  ctx = Ctx(direction, k), T in S^P_k (as words).

    step 1 (SL1): solve dbar_T(w) = delta(T) in Z_k(D)  ->  T.w kills the relator in Q_{k+1}
    step 2 (SL2): fix the two fresh chi digits with the memo-1.2 witness moves
    step 3:       verify the three S^P_{k+1} clauses.

    `want` = the fresh chi-digit pattern to install at the two tail slots; (0,0) is the
    honest refinement, anything else builds a P-violating but relator-deep CONTROL.
    `extra_kernel` = an element of ker dbar added to the SL1 solution (a different, equally
    valid solution of the same solve)."""
    k = ctx.k
    info = {"k": k, "tag": tag, "want": want}
    ok, why = ctx.is_sP(T)
    assert ok, f"input not in S^P_{k}: {why}"

    w = ctx.solve_delta(T)
    if w is None:
        info["fail"] = "delta NOT in span(R_k + Im dbar) -- SL1 STALL"
        return None, info
    if extra_kernel is not None:
        w = [w[i] + extra_kernel[i] for i in range(3)]
    T1 = mul_triple(T, w)
    info["solve_slots"] = [len(x) for x in w]
    if not ctx.relator_ok(T1, k + 1):
        info["fail"] = "shift formula failed: relator not killed at k+1"
        return None, info

    d0v = ctx.digits(T1, k)
    info["digits_after_solve"] = d0v
    info["auto_slot_digit"] = d0v[ctx.auto_slot]
    moves = ctx.digit_moves(T1)
    info["move_effects"] = [tuple(a ^ b for a, b in
                                  zip(ctx.digits(mul_triple(T1, mv), k), d0v))
                            for mv in moves]
    chosen, T2 = None, None
    for c0 in (0, 1):
        for c1 in (0, 1):
            mv = [[], [], []]
            for j, cj in enumerate((c0, c1)):
                if cj:
                    mv = [mv[i] + moves[j][i] for i in range(3)]
            cand = mul_triple(T1, mv)
            dd = ctx.digits(cand, k)
            if all(dd[i] == 0 for i in range(3) if i not in ctx.tail_slots) and \
               tuple(dd[i] for i in ctx.tail_slots) == tuple(want):
                chosen, T2 = (c0, c1), cand
                break
        if chosen:
            break
    if T2 is None:
        info["fail"] = f"no digit-move combination reaches {want}"
        return None, info
    info["digit_move_combo"] = chosen
    info["final_digits"] = ctx.digits(T2, k)
    info["wordlens"] = [len(t) for t in T2]

    nxt = Ctx(ctx.direction, k + 1)
    info["verify"] = {"gen": gen_matrix_ok(T2), "relator_k+1": nxt.relator_ok(T2, k + 1),
                      "chi_mod_2^(k+1)": all((d - 1) % (1 << (k + 1)) == 0
                                             for d in nxt.dev(T2)),
                      "frattini_preserved": all(abel2(T2[i]) == abel2(T[i])
                                                for i in range(3))}
    if verbose:
        print(f"  climb {tag} k={k}->{k+1} want={want}: digits_after_solve={d0v} "
              f"moves={chosen} final={info['final_digits']} lens={info['wordlens']} "
              f"verify={info['verify']}")
    if not (info["verify"]["gen"] and info["verify"]["relator_k+1"]):
        info["fail"] = "verification failed"
    return T2, info


# ------------------------------------------------------------------- move kernels
def kernel_combos(vectors):
    """basis of {c : XOR_{i in c} v_i = 0}, as index bitmasks."""
    rows, ker = [], []
    for i, v in enumerate(vectors):
        cb = 1 << i
        for b, c in rows:
            if (v ^ b) < v:
                v ^= b
                cb ^= c
        if v:
            rows.append((v, cb))
            rows.sort(key=lambda t: -t[0])
        else:
            ker.append(cb)
    return ker

def move_kernel(direction, T, j, level):
    """lambda_j-modifications whose dbar-shift vanishes in Z_level(D) (needs level = j+1).
    Returns (gens, kernel combos over [R-atoms] ++ [dbar-atoms], nR)."""
    assert level == j + 1, "the shift of a lambda_j-move lives in Z_{j+1}"
    c = Ctx(direction, level)
    vecs = list(c.ratom_coords(level))
    nR = len(vecs)
    gens = []
    for u in c.mods(j):
        for slot in (0, 1, 2):
            vecs.append(c.coords(c.dbar_atom(u, slot, T), level, "atom"))
            gens.append((u, slot))
    return gens, kernel_combos(vecs), nR

def combo_to_move(gens, nR, combo):
    w = [[], [], []]
    for i, (u, slot) in enumerate(gens):
        if (combo >> (nR + i)) & 1:
            w[slot] = w[slot] + u
    return w

def rand_lambda_move(c, j, rng, p=0.35):
    w = [[], [], []]
    for slot in (0, 1, 2):
        for u in c.mods(j):
            if rng.random() < p:
                w[slot] = w[slot] + u
    return w


# ------------------------------------------------------------- canonical functionals
def roots_and_addir(direction):
    """The ad-direction is the TOWER's presenting-relator squared letter; the two roots
    are the other two letters.  dir 1: tower D_R = F(s,x,y)/N(r_2), r_2 has y^2  ->
    ad y, roots {s,x}.  dir 2: tower D_0 = F(a,s,y)/N(r_0), r_0 has a^2  ->  ad a,
    roots {s,y}."""
    return ((0, 1), 2) if direction == 1 else ((1, 2), 0)

def column_pair(c):
    (r1, r2), ad = roots_and_addir(c.direction)
    return [(r1, c.column(r1, ad)), (r2, c.column(r2, ad))], ad

def coker_coords(c, T):
    """(c_a, c_b) with delta(T) = c_a * tail(T_p) + c_b * tail(T_q) in the coker,
    computed through the canonical (T-independent) column functionals.
    Also returns the raw column values and the columns-vs-tails pairing matrix."""
    cols, _ = column_pair(c)
    dp = c.in_pbw(c.delta_coords(T))
    phi = [bin(col & dp).count("1") % 2 for _, col in cols]
    tp = [c.in_pbw(v) for v in c.tail_coords(T)]
    m = [[bin(col & t).count("1") % 2 for t in tp] for _, col in cols]
    det = (m[0][0] * m[1][1] ^ m[0][1] * m[1][0]) & 1
    assert det == 1, f"columns/tails pairing singular: {m}"
    ca = (m[1][1] * phi[0] ^ m[0][1] * phi[1]) & 1
    cb = (m[1][0] * phi[0] ^ m[0][0] * phi[1]) & 1
    return (ca, cb), tuple(phi), m

def chi_digits_top(c, T):
    """e_i = the chi-deviation digit at 2^{k-1} (asserts chi-depth >= k-1)."""
    out = []
    for d in c.dev(T):
        r = (d - 1) % c.M
        assert r % (1 << (c.k - 1)) == 0, f"chi-depth < k-1: dev-1 = {r}"
        out.append((r >> (c.k - 1)) & 1)
    return out


# ------------------------------------------------ the column functional, closed form
def theta_D(word, root, addir, M, tval=-1):
    """The theta-crossed derivation (right theta-twisted Fox derivative).

    theta sends the ad-direction letter to `tval` and the other two letters to 1;
    D(z) = 1 for the root letter z, D = 0 on the others, and
        D(uv) = D(u) * theta(v) + D(v).
    Returns (theta(word), D(word)) mod M.  Any tval with v_2(tval-1) = 1 gives the same
    digit functional; tval = -1 additionally makes theta kill both presenting relators."""
    th, D = 1, 0
    for g in word:
        i = abs(g) - 1
        gt, gd = (1, 1) if i == root else ((tval % M, 0) if i == addir else (1, 0))
        if g < 0:
            gti = pow(gt, -1, M)
            gd, gt = (-gd * gti) % M, gti
        D, th = (D * gt + gd) % M, (th * gt) % M
    return th, D

def crossed_digit(c, word, root, tval=-1):
    """phi^root(word) for a word representing a class in Z_k: the (k-1)-st 2-adic digit
    of the crossed derivation.  Equals the PBW-dual column functional (verified)."""
    _, ad = roots_and_addir(c.direction)
    _, D = theta_D(word, root, ad, c.M, tval)
    assert D % (1 << (c.k - 1)) == 0, f"crossed derivation not deep enough: {D}"
    return (D >> (c.k - 1)) & 1
