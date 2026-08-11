"""W62-CHANNELS step 2: the EXHAUSTIVE parity sweep.  Is an even-channel point possible at all?

`derive_channels.py` reduces the question to a finite one.  Whether the three-channel functional
is even at a binder point depends only on five bits per letter - `(d, e, f, h, j)` mod two - of
the four letters `x0`, `x1`, `U`, `V` (the sigma slot's dressed letter `sigma * x0` agrees with
`x0` in all five, because the committed sigma marking is `<b=1>`).  That is `2^20` patterns, and
this file enumerates every one of them.

For each pattern it evaluates

  * `ODD`      the residue condition `x0.e = x1.f = x1.h = 1` (wave 58's form, with `stageN1`
               making `x0.a` even);
  * `EVEN`     the channel condition: for every letter pair `(p, q)` and every permuted letter
               `L`, the pairing of `parity3([p,q])` against `covector(L)` vanishes;
  * `GAUGE`    the committed class-two-forced gauge, which asks `x0.d`, `x0.f` and `x1.d` even.

and reports the four-way census.  The headline number is `|ODD and EVEN and GAUGE|`.
"""
import sys
import os
import itertools

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

BITS = "defhj"                       # the five parities that decide everything
NAMES = ["x0", "x1", "U", "V"]


def parity3(p, q):
    """(m, i, l) mod two of `[p, q]` for `stageN1` letters, from `derive_channels.py` 2."""
    m = (p["j"] * q["d"] + p["d"] * q["j"] + p["f"] * q["h"] + p["h"] * q["f"]) % 2
    i = (p["d"] * q["e"] + p["e"] * q["d"]) % 2
    l = (p["h"] * q["e"] + p["e"] * q["h"]) % 2
    return (m, i, l)


def covector(L):
    return (L["e"], L["j"], L["f"])


def chan(z, L):
    c = covector(L)
    return (z[0] * c[0] + z[1] * c[1] + z[2] * c[2]) % 2


def unpack(bits):
    """20 bits -> four letter dictionaries."""
    out = []
    for t in range(4):
        out.append({BITS[k]: (bits >> (5 * t + k)) & 1 for k in range(5)})
    return out


def channels_even(letters):
    """The channel condition, and the first offender."""
    for a in range(4):
        for b in range(a + 1, 4):
            z = parity3(letters[a], letters[b])
            if z == (0, 0, 0):
                continue
            for c in range(4):
                if chan(z, letters[c]):
                    return False, (NAMES[a], NAMES[b], NAMES[c])
    return True, None


def main():
    X, Y, U, V = 0, 1, 2, 3
    nodd = neven = ngauge = nforced = 0
    good_gauge = []
    good_free = []
    good_forced = []
    offenders = {}
    for bits in range(1 << 20):
        L = unpack(bits)
        odd = (L[X]["e"] == 1 and L[Y]["f"] == 1 and L[Y]["h"] == 1)
        gauge = (L[X]["d"] == 0 and L[X]["f"] == 0 and L[Y]["d"] == 0)
        # what the RELATOR forces at any marking killing the four abelian rows
        forced = (L[Y]["d"] == 0 and L[Y]["e"] == 0)
        ev, off = channels_even(L)
        nodd += odd
        neven += ev
        ngauge += gauge
        nforced += forced
        if odd and ev:
            (good_gauge if gauge else good_free).append(bits)
            if forced:
                good_forced.append(bits)
        if odd and gauge and not ev:
            offenders[off] = offenders.get(off, 0) + 1

    print("=" * 96)
    print("== W62-CHANNELS: the exhaustive parity sweep, all 2^20 letter patterns ==")
    print("=" * 96)
    print()
    print("   patterns swept                                         %8d" % (1 << 20))
    print("   with an ODD class-five residue                         %8d" % nodd)
    print("   with all three channels EVEN                           %8d" % neven)
    print("   on the committed class-two-forced gauge                %8d" % ngauge)
    print()
    print("   with x1.d, x1.e even (what the RELATOR forces)         %8d" % nforced)
    print()
    print("   ODD and EVEN, ON the gauge                             %8d" % len(good_gauge))
    print("   ODD and EVEN, with only the relator's own two columns  %8d" % len(good_forced))
    print("   ODD and EVEN, OFF the gauge                            %8d" % len(good_free))
    print()
    if not good_forced:
        print("   *** THE TWO CONDITIONS ARE ALREADY INCOMPATIBLE UNDER WHAT THE RELATOR")
        print("       FORCES: no gauge hypothesis on the x0 slot is needed.  This is")
        print("       `SqU6.gaTwoChannel_even_bit_even`, from the other side. ***")
        print()
    if not good_gauge:
        print("   *** ON THE GAUGE THE TWO CONDITIONS ARE INCOMPATIBLE. ***")
        print()
        print("   Which pair and which slot refutes each odd gauge pattern:")
        for k, n in sorted(offenders.items(), key=lambda t: -t[1]):
            print("      [%s, %s] against the %s slot : %6d patterns" % (k[0], k[1], k[2], n))
        print()
    if good_free:
        print("   the OFF-gauge survivors, as (d, e, f, h, j) parities:")
        shown = 0
        pats = {}
        for bits in good_free:
            L = unpack(bits)
            key = tuple(tuple(L[t][b] for b in BITS) for t in range(4))
            pats[key] = pats.get(key, 0) + 1
        for key in sorted(pats):
            if shown < 40:
                print("      x0=%s x1=%s U=%s V=%s"
                      % tuple("".join(str(x) for x in k) for k in key))
            shown += 1
        print("      ... %d distinct patterns in all" % len(pats))
        print()
        # which gauge columns do they need?
        needs_xf = sum(1 for bits in good_free if unpack(bits)[X]["f"])
        needs_yd = sum(1 for bits in good_free if unpack(bits)[Y]["d"])
        needs_xd = sum(1 for bits in good_free if unpack(bits)[X]["d"])
        print("   of the %d off-gauge survivors: %d have x0.f odd, %d have x1.d odd,"
              % (len(good_free), needs_xf, needs_yd))
        print("   %d have x0.d odd (the gauge forbids all three)." % needs_xd)
        print()
        with open(os.path.join(HERE, "results", "survivors.txt"), "w") as f:
            for bits in good_free:
                L = unpack(bits)
                f.write("%s\n" % " ".join(
                    "%s=%s" % (NAMES[t], "".join(str(L[t][b]) for b in BITS))
                    for t in range(4)))
    print("=" * 96)
    return good_free


if __name__ == "__main__":
    main()
