"""W60-STAGE4: why a candidate (x0, U, V) has no class-five sigma witness.

The two-sided cascade needs, at every coordinate `k` of class `<= 4`, that the undressed and
the `a0 = a1`-dressed relator rows AGREE and are EVEN.  This script reports the first
coordinate at which that fails, so the structured search can be aimed rather than widened
blindly.
"""
import sys
import os
import random

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))

import u6mat as M                                             # noqa: E402
import pointlib as P                                          # noqa: E402

SIG = M.sigFiveMark
CLS = P.CLS


def first_fail(X, U, V, h=1, jj=0):
    """Walk the cascade greedily (sparsest lift) and report where it dies."""
    Y = M.ONE
    for c in range(1, 6):
        for k in CLS[c]:
            r0 = M.sqRelWord(P.mirTuple(h, jj, SIG, X, Y, U, V))
            r1 = M.sqRelWord(P.mirTuple(h, jj, M.mul(SIG, X), X, Y, U, V))
            if c == 5:
                if r0[k] % 2:
                    return ("class 5: undressed row odd", k, r0[k], r1[k])
                if (r1[k] - r0[k]) % 2 == 0:
                    return ("class 5: residue EVEN", k, r0[k], r1[k])
                return ("OK", k, r0[k], r1[k])
            if r0[k] != r1[k]:
                return ("rows differ at %s (class %d)" % (M.COORDS[k], c), k, r0[k], r1[k])
            if r0[k] % 2:
                return ("row odd at %s (class %d)" % (M.COORDS[k], c), k, r0[k], r1[k])
            Y = P.setc(Y, k, (-(r0[k] // 2)) % 4)
    return ("OK", None, None, None)


if __name__ == "__main__":
    print("== the wave-59 point ==")
    print("   %s" % (first_fail(M.sepX, M.sepU, M.sepV),))
    print()

    print("== the wave-59 point with U.a even ==")
    for a in (0, 2):
        U = M.named(a=a, c=2, d=3, f=3, g=2, h=2, i=2)
        print("   U.a=%d : %s" % (a, first_fail(M.sepX, U, M.sepV)))
    print()

    print("== a random sweep: where do candidates die? ==")
    random.seed(60021)
    tally = {}
    for _ in range(4000):
        X = M.named(a=random.randrange(0, 8, 2), e=random.choice((1, 3, 5, 7)))

        def letter():
            return M.named(a=random.randrange(0, 8, 2), b=random.randrange(8),
                           c=random.randrange(0, 8, 2), d=random.randrange(8),
                           e=random.randrange(8), f=random.randrange(8), g=random.randrange(8),
                           h=random.randrange(8), i=random.randrange(8))
        U, V = letter(), letter()
        tag = first_fail(X, U, V)[0]
        tally[tag] = tally.get(tag, 0) + 1
    for tag, n in sorted(tally.items(), key=lambda kv: -kv[1]):
        print("   %6d   %s" % (n, tag))
