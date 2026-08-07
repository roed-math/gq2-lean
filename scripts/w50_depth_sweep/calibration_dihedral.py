"""W50 calibration: reproduce the committed small-group kill patterns, as a harness control.

Controls (EichRefutation.lean / UVFrames.lean / ArbFrames.lean docstrings):

  * D4 = DihedralGroup 4 (order 8).  refMark: sigma |-> sr 0, x0 |-> 1, x1 |-> r 1,
    u |-> a, v |-> b with [a,b] = r 2 kills the relator; at nuSel h j 0 1 it kills the
    whole V-family at EVERY weight tuple, because V |-> 1 and the surviving core word is
    sqWord (sr 0) 1 (r 1) = r 2 =/= 1.
  * The two-letter family sqEichFrameUV is refuted at nuSel h j 1 1 at every weight tuple
    (not_sqRelWord_sqEichFrameUV_nuSel), d and d' included.
  * The ARBITRARY-dressing family survives every such probe (sqArbRelWord_iff_clearingStep):
    no homomorphism-based refutation can reach it.  A harness that does not see the
    restricted family die and the arbitrary one live has no discriminating power.

DihedralGroup n follows mathlib: r i * r j = r (i+j), r i * sr j = sr (j-i),
sr i * r j = sr (i+j), sr i * sr j = r (j-i).
"""

from itertools import product
from padic_c0 import c0


class Dih:
    def __init__(self, n):
        self.n = n
        self.N = N = 2 * n
        t = [[0] * N for _ in range(N)]
        for x in range(N):
            kx, ix = ('r', x) if x < n else ('sr', x - n)
            for y in range(N):
                ky, iy = ('r', y) if y < n else ('sr', y - n)
                if kx == 'r' and ky == 'r':
                    t[x][y] = (ix + iy) % n
                elif kx == 'r' and ky == 'sr':
                    t[x][y] = n + (iy - ix) % n
                elif kx == 'sr' and ky == 'r':
                    t[x][y] = n + (ix + iy) % n
                else:
                    t[x][y] = (iy - ix) % n
        self.t = t
        self.iv = [next(y for y in range(N) if t[x][y] == 0) for x in range(N)]
        self.expo = 1
        while any(self.pw(x, self.expo) != 0 for x in range(N)):
            self.expo *= 2

    def r(self, i):
        return i % self.n

    def sr(self, i):
        return self.n + i % self.n

    def mul(self, *xs):
        z = 0
        for x in xs:
            z = self.t[z][x]
        return z

    def pw(self, x, k):
        k = int(k)
        y = x if k >= 0 else self.iv[x]
        z = 0
        for _ in range(abs(k)):
            z = self.t[z][y]
        return z

    def conj(self, x, g):
        return self.t[self.t[self.iv[g]][x]][g]

    def comm(self, x, y):
        return self.t[self.t[self.iv[x]][self.iv[y]]][self.t[x][y]]

    def closure(self, gens):
        S, fr = {0}, [0]
        while fr:
            x = fr.pop()
            for g in gens:
                for y in (self.t[x][g], self.t[x][self.iv[g]]):
                    if y not in S:
                        S.add(y)
                        fr.append(y)
        return sorted(S)

    def core(self, s, x, y):
        """sqWord s x y = (x^s)^-1 (x^3)^-1 y^2 [y, y^s]"""
        return self.mul(self.iv[self.conj(x, s)], self.iv[self.pw(x, 3)],
                        self.pw(y, 2), self.comm(y, self.conj(y, s)))

    def relw(self, m):
        return self.t[self.core(m[0], m[1], m[2])][self.comm(m[3], m[4])]


def run(n, label, only_surjective, ts_list):
    D = Dih(n)
    E = D.expo
    c0e = c0 % E
    print(f"--- {label}: order {D.N}, exponent {E}, c0 mod {E} = {c0e} ---")

    if n == 4:
        assert D.comm(D.sr(1), D.sr(0)) == D.r(2), "commP (sr 1) (sr 0) != r 2"
        assert D.core(D.sr(0), 0, D.r(1)) == D.r(2), "sqWord (sr 0) 1 (r 1) != r 2"
        assert D.relw([D.sr(0), 0, D.r(1), D.sr(1), D.sr(0)]) == 0
        print("   anchors: commP(sr1,sr0)=r2, sqWord(sr0,1,r1)=r2, sqRelWord(refMark)=1 .. OK")

    homs = [m for m in product(range(D.N), repeat=5) if D.relw(m) == 0]
    if only_surjective:
        homs = [m for m in homs if len(D.closure(m)) == D.N]
    print(f"   homs D_sq 1 -> D{' (surjective)' if only_surjective else ''}: {len(homs)}")

    for (t, s) in ts_list:
        kill = {"V": 0, "T": 0, "UV": 0, "ARB": 0}
        for m in homs:
            S, X0, X1, U0, V0 = m
            w = D.mul(S, D.iv[D.pw(X0, c0e)])
            U = D.mul(D.iv[D.pw(w, t)], U0)
            V = D.mul(V0, D.iv[D.pw(w, s)])
            Up = [D.pw(U, k) for k in range(E)]
            Vp = [D.pw(V, k) for k in range(E)]

            def survives(dressA, dressBC, hset):
                """some (A-slot, (B,C)-slots, handle) choice kills the relator?"""
                return any(D.core(D.t[S][a], D.t[X0][b], D.t[X1][c]) in hset
                           for a in dressA for (b, c) in dressBC)

            # sqEichFrame (V-family):   (sigma V^e, x0 V^e', x1 V^2e', U V^d, V)
            hV = {D.iv[D.comm(D.t[U][Vp[d]], V)] for d in range(E)}
            dA = {Vp[e] for e in range(E)}
            dBC = {(Vp[e], Vp[(2 * e) % E]) for e in range(E)}
            if not survives(dA, dBC, hV):
                kill["V"] += 1

            # sqEichFrameT (U-family):  (sigma U^f, x0 U^f', x1 U^2f', U, V U^d')
            hT = {D.iv[D.comm(U, D.t[V][Up[d]])] for d in range(E)}
            dA = {Up[f] for f in range(E)}
            dBC = {(Up[f], Up[(2 * f) % E]) for f in range(E)}
            if not survives(dA, dBC, hT):
                kill["T"] += 1

            # sqEichFrameUV (two-letter): all six weights
            hUV = {D.iv[D.comm(D.t[U][Vp[d]], D.t[V][Up[dd]])]
                   for d in range(E) for dd in range(E)}
            dA = {D.t[Up[f]][Vp[e]] for f in range(E) for e in range(E)}
            dBC = {(D.t[Up[f]][Vp[e]], D.t[Up[(2 * f) % E]][Vp[(2 * e) % E]])
                   for f in range(E) for e in range(E)}
            if not survives(dA, dBC, hUV):
                kill["UV"] += 1

            # ARBITRARY family: a_i in phi(K) = <U, V, x0^-2 x1> . [im phi, im phi]
            tb = D.mul(D.iv[D.pw(X0, 2)], X1)
            im = D.closure(m)
            der = D.closure([D.comm(a, b) for a in im for b in im])
            KG = D.closure([U, V, tb] + der)
            hA = {D.iv[D.comm(D.t[U][a3], D.t[V][a4])] for a3 in KG for a4 in KG}
            if not survives(set(KG), {(b, c) for b in KG for c in KG}, hA):
                kill["ARB"] += 1
        print(f"   (t,s)=({t},{s}) : killing configs -- V-family {kill['V']}, "
              f"T-family {kill['T']}, two-letter UV {kill['UV']}, ARBITRARY {kill['ARB']}")


if __name__ == "__main__":
    run(4, "D4 = DihedralGroup 4 (order 8)", False,
        [(0, 1), (1, 0), (1, 1), (1, 2), (2, 1), (0, 0)])
    run(8, "D8 = DihedralGroup 8 (order 16)", True, [(1, 1), (0, 1), (1, 0)])
