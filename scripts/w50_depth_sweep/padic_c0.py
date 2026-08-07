"""W50: the 2-adic constants of the L_sq core, to whatever precision we need.

X  = the unique root of Z^3 + 2Z^2 + 1 in Z_2      (GQ2/Roe/ChiR.lean, rootXUnit)
S  = -X^3 / (X^2 + X + 1)                          (SvalUnit)
Y  = -X^2                                          (YvalUnit)
c0 = sqPivotExp: the unique c in Z_2 with X^c = S  (SqCore/Certificate.lean)

Committed cross-checks (Cores.lean docstring):   X = 5, S = 13, Y = 7   (mod 16).
Extra check: Y^2 = X^4 (YvalUnit_sq_eq), which is the abelian collapse of the relator.

Everything is plain integer arithmetic modulo 2^N; no dependencies.
"""

N = 160                       # working precision, bits
MOD = 1 << N


def inv(a, mod=MOD):
    return pow(a % mod, -1, mod)


def root_X(N=N):
    """Hensel-lift the root of f(Z)=Z^3+2Z^2+1 with Z = 1 (mod 2)."""
    mod = 1 << N
    x = 1
    prec = 1
    while prec < N:
        prec = min(2 * prec, N)
        m = 1 << (prec + 4)
        f = (x * x * x + 2 * x * x + 1) % m
        fp = (3 * x * x + 4 * x) % m          # odd, so invertible
        x = (x - f * pow(fp, -1, m)) % m
    return x % mod


X = root_X()
S = (-(X ** 3) * inv(X * X + X + 1)) % MOD
Y = (-(X * X)) % MOD


def log2adic(u, N=N):
    """2-adic log on 1 + 4Z_2 : log(u) = sum_{k>=1} (-1)^(k+1) (u-1)^k / k."""
    mod = 1 << (N + 40)
    z = (u - 1) % mod
    assert z % 4 == 0, "log2adic needs u = 1 mod 4"
    total, term = 0, z
    k = 1
    while True:
        v2k = (k & -k).bit_length() - 1           # v_2(k)
        # v_2(term/k) >= 2k - v2k ; stop once that exceeds our target
        if 2 * k - v2k > N + 20:
            break
        odd = k >> v2k
        contrib = (term >> v2k) * pow(odd, -1, mod) % mod
        total = (total + contrib) if k % 2 == 1 else (total - contrib)
        total %= mod
        term = term * z % mod
        k += 1
    return total % (1 << N)


def c0_value(N=N):
    lS, lX = log2adic(S, N), log2adic(X, N)
    # both have valuation exactly 2 (X, S = 5, 13 mod 16, so u-1 = 4 mod 8)
    assert lS % 4 == 0 and lX % 4 == 0
    assert (lS // 4) % 2 == 1 and (lX // 4) % 2 == 1, "log valuations not both 2"
    mod = 1 << (N - 2)
    return (lS // 4) * pow(lX // 4, -1, mod) % mod


c0 = c0_value()

if __name__ == "__main__":
    import sys
    if "--magma" in sys.argv:                # python3 padic_c0.py --magma > c0.m
        print("C0 :=", c0 % (1 << 64), ";")
        raise SystemExit
    print("X mod 2^8 =", X % 256, " X mod 16 =", X % 16, "(want 5)")
    print("S mod 2^8 =", S % 256, " S mod 16 =", S % 16, "(want 13)")
    print("Y mod 2^8 =", Y % 256, " Y mod 16 =", Y % 16, "(want 7)")
    print("check f(X) = 0 mod 2^%d :" % (N - 8), (X**3 + 2*X*X + 1) % (1 << (N - 8)) == 0)
    print("check S*(X^2+X+1) + X^3 = 0 :", (S * (X*X + X + 1) + X**3) % (1 << (N - 8)) == 0)
    print("check Y^2 = X^4 (YvalUnit_sq_eq) :", (Y * Y - X**4) % (1 << (N - 8)) == 0)
    print()
    for k in (1, 2, 3, 4, 5, 6, 8, 16, 32):
        print("c0 mod 2^%-2d = %d" % (k, c0 % (1 << k)))
    # the defining relation X^c0 = S, verified as a power in 1+4Z_2
    m = 1 << 64
    assert pow(X % m, c0 % (1 << 62), m) == S % m, "X^c0 != S"
    print("\nverified X^c0 = S mod 2^64")
