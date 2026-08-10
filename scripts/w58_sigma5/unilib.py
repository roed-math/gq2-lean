"""Generic unitriangular U_k arithmetic, exact, over Z/n and over the symbolic ring `poly6.P`.

`u6lib` is the class-five (k = 6) special case, written out in the campaign's coordinate
naming; this module is the same group law at arbitrary k, used to (a) certify `u6lib` and
(b) run the class-four / class-six comparisons that decide whether a class-five phenomenon is
a one-off or a pattern.

An element of U_k is a dict {(i, j): value} with 1 <= i < j <= k, or equivalently the k x k
unitriangular matrix.  Everything is done on matrices; no coordinate names are needed.
"""

from poly6 import P


def one(k, ring_one=1, ring_zero=0):
    return [[ring_one if i == j else ring_zero for j in range(k)] for i in range(k)]


class Uni:
    """U_k over Z/n (n = None means over the symbolic ring `P`)."""

    def __init__(self, k, n=8):
        self.k = k
        self.n = n
        self.sym = (n is None)
        self.zero = P() if self.sym else 0
        self.unit = P.const(1) if self.sym else 1
        self.ONE = one(k, self.unit, self.zero)

    # ---- basic matrix ops ----------------------------------------------------------
    def _r(self, v):
        return v if self.sym else v % self.n

    def mul(self, A, B):
        k = self.k
        out = []
        for i in range(k):
            row = []
            for j in range(k):
                s = self.zero
                for t in range(i, j + 1):
                    s = s + A[i][t] * B[t][j]
                row.append(self._r(s))
            out.append(row)
        return out

    def inv(self, A):
        """I - N + N^2 - ... , N = A - I nilpotent of order k."""
        k = self.k
        Nm = [[self._r(A[i][j] - (self.unit if i == j else self.zero)) for j in range(k)]
              for i in range(k)]
        R = one(k, self.unit, self.zero)
        Q = one(k, self.unit, self.zero)
        sign = 1
        for _ in range(k - 1):
            Q = self.mul(Q, Nm)
            sign = -sign
            R = [[self._r(R[i][j] + (Q[i][j] if sign > 0 else -Q[i][j])) for j in range(k)]
                 for i in range(k)]
        return R

    def power(self, A, e):
        R = self.ONE
        for _ in range(e):
            R = self.mul(R, A)
        return R

    def conjP(self, p, g):
        return self.mul(self.mul(self.inv(g), p), g)

    def commP(self, p, q):
        return self.mul(self.mul(self.inv(p), self.inv(q)), self.mul(p, q))

    def sqWord(self, s, x, y):
        return self.mul(self.mul(self.mul(self.inv(self.conjP(x, s)), self.inv(self.power(x, 3))),
                                 self.power(y, 2)),
                        self.commP(y, self.conjP(y, s)))

    def handleWord(self, us, vs):
        R = self.ONE
        for u, v in zip(us, vs):
            R = self.mul(R, self.commP(u, v))
        return R

    def sqRelWord(self, m):
        h = (len(m) - 3) // 2
        us = [m[3 + 2 * t] for t in range(h)]
        vs = [m[4 + 2 * t] for t in range(h)]
        return self.mul(self.sqWord(m[0], m[1], m[2]), self.handleWord(us, vs))

    # ---- constructors --------------------------------------------------------------
    def elem(self, i, j, val=None):
        """The elementary matrix I + val * E_{ij} (1-based i < j)."""
        val = self.unit if val is None else val
        A = one(self.k, self.unit, self.zero)
        A[i - 1][j - 1] = val
        return A

    def symbolic(self, tag):
        """A symbolic element with entry (i, j) the variable tag_i_j."""
        A = one(self.k, self.unit, self.zero)
        for i in range(self.k):
            for j in range(i + 1, self.k):
                A[i][j] = P.var("%s%d%d" % (tag, i + 1, j + 1))
        return A

    def from_dict(self, d):
        A = one(self.k, self.unit, self.zero)
        for (i, j), v in d.items():
            A[i - 1][j - 1] = v
        return A

    def entries(self, A):
        return {(i + 1, j + 1): A[i][j] for i in range(self.k) for j in range(i + 1, self.k)}

    def is_one(self, A):
        return all(A[i][j] == self.zero for i in range(self.k) for j in range(i + 1, self.k))

    def corner(self, A, lo, hi):
        """The (lo..hi) principal corner, an element of U_{hi-lo+1} (1-based, inclusive)."""
        return [row[lo - 1:hi] for row in A[lo - 1:hi]]
