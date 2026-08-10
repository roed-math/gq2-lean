"""W61-WIDER step 7: block-by-block evenness on the achievable lattice, with Lean witnesses.

The hypotheses, exactly wave 60's:

    frame  2 | L.a  and  2 | L.c        (`GradedFiveStageFour.stageN1`)
    dress  2 | z.f,  2 | z.h,  2 | z.j   (`GradedFiveStageFour.stageN2`)

For each block of the class-five row this file (i) certifies that the block is even under those
hypotheses by exact substitution and coefficient division, and (ii) emits the HALF as Lean
source, so the Lean proof is a `refine <witness>, by rw [...]; ring` with nothing guessed.
"""
import sys
import os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_defect5"))
sys.path.insert(0, HERE)

import u6poly as P                                            # noqa: E402
from u6poly import U6, padd, psub, pmul, pneg, pscale, pzero, pvar, poly_str  # noqa: E402
import wlib as W                                              # noqa: E402
SUB = {"z0": "z\u2080", "z1": "z\u2081", "z2": "z\u2082"}


def render(p, namer, width=92, indent=6):
    """Render a polynomial as Lean source with explicit + / - joins and line wrapping."""
    if not p:
        return "0"
    pieces = []
    for mon, c in sorted(p.items(), key=lambda kv: (len(kv[0]), kv[0])):
        sign = "-" if c < 0 else "+"
        k = abs(c)
        body = " * ".join(namer(v) for v in mon) if mon else "1"
        pieces.append((sign, body if k == 1 else "%d * %s" % (k, body)))
    lines, cur = [], ""
    for i, (sign, txt) in enumerate(pieces):
        chunk = txt if i == 0 and sign == "+" else ("-" + txt if i == 0 else sign + " " + txt)
        add = chunk if not cur else cur + " " + chunk
        if len(add) + indent > width and cur:
            lines.append(cur)
            cur = chunk
        else:
            cur = add
    lines.append(cur)
    return ("\n" + " " * indent).join(lines)

COORDS = P.COORDS

FRAME_EVEN = ["a", "c"]
DRESS_EVEN = ["f", "h", "j"]

HALF = {}


def rules(frames, dresses):
    r = {}
    for nm in frames:
        for co in FRAME_EVEN:
            r["%s_%s" % (nm, co)] = pscale(2, pvar("%s%s" % (nm, co)))
    for nm in dresses:
        for co in DRESS_EVEN:
            r["%s_%s" % (nm, co)] = pscale(2, pvar("%s%s%s" % (nm[0], co, nm[1:])))
    return r


def subst(p, r):
    out = {}
    for mon, c in p.items():
        term = {(): c}
        for v in mon:
            term = pmul(term, r.get(v, pvar(v)))
        out = padd(out, term)
    return out


def half(p, r, label):
    q = subst(p, r)
    odd = {mon: c for mon, c in q.items() if c % 2}
    if not odd:
        # re-multiply: the emitted witness really is a half, checked as an exact identity
        assert not psub(q, pscale(2, {m: c // 2 for m, c in q.items()})), label
    ok = not odd
    print("   %-28s : %s" % (label, "EVEN (%d terms, half has %d)" % (len(q), len(q))
                             if ok else "NOT EVEN, %d odd terms: %s"
                             % (len(odd), poly_str(odd))))
    if not ok:
        return None
    return {mon: c // 2 for mon, c in q.items()}


def leanname(v):
    """`sa` -> `sa`, `s_a` -> `s.a`, `d0f` -> `f0` style is fixed here."""
    if "_" in v:
        head, _, tail = v.partition("_")
        return "%s.%s" % (SUB.get(head, head), tail)
    return v


print("=" * 92)
print("== block-by-block evenness of the class-five row ==")
s, x, y = U6.gen("s"), U6.gen("x"), U6.gen("y")
z0, z1, z2 = W.ga2("z0"), W.ga2("z1"), W.ga2("z2")
blocks = W.coreBlocks(s, x, y, z0, z1, z2)
R3 = rules(["s", "x", "y"], ["z0", "z1", "z2"])

HALF["quadO"] = half(blocks["o"][1], R3, "gaTwoQuadO")
HALF["corrO"] = half(blocks["o"][0], R3, "gaTwoCorrO")

# the class-five pairing form against its three surviving channels
z, L = W.ga2("z"), U6.gen("L")
chan = padd(pmul(z.m, L.e), pmul(z.i, L.j), pmul(z.l, L.f))
RL = rules(["L"], ["z"])
HALF["pairO"] = half(psub(W.pairO(z, L), chan), RL, "gaTwoPairO - channel")
HALF["pairJ"] = half(W.pairJ(z, L), RL, "gaTwoPairJ")

# the handle shift's class-five row against its two channels
p, q = U6.gen("p"), U6.gen("q")
zz, ww = W.ga2("z"), W.ga2("w")
hs = W.handleShift(p, q, zz, ww)
hchan = psub(padd(pmul(zz.m, q.e), pmul(zz.i, q.j), pmul(zz.l, q.f)),
             padd(pmul(ww.m, p.e), pmul(ww.i, p.j), pmul(ww.l, p.f)))
RH = rules(["p", "q"], ["z", "w"])
HALF["handleO"] = half(psub(hs.o, hchan), RH, "gaTwoHandle.o - channels")
HALF["handleJ"] = half(hs.j, RH, "gaTwoHandle.j")
HALF["handleX"] = half(W.handleX(p, q, zz, ww), RH, "gaTwoHandleX")
print()

print("=" * 92)
print("== the class-four rows, for the record ==")
HALF["quadM"] = half(blocks["m"][1], R3, "gaTwoQuadM")
HALF["quadN"] = half(blocks["n"][1], R3, "gaTwoQuadN")
print()

# ------------------------------------------------------------------ emit Lean witnesses
NAMES = {}
for nm in ("s", "x", "y", "L", "p", "q"):
    for co in FRAME_EVEN:
        NAMES["%s%s" % (nm, co)] = "%s%s" % (nm, co)
for nm in ("z0", "z1", "z2", "z", "w"):
    for co in DRESS_EVEN:
        NAMES["%s%s%s" % (nm[0], co, nm[1:])] = "%s%s%s" % (nm[0], co, nm[1:])


def namer(v):
    if v in NAMES:
        return NAMES[v]
    return leanname(v)


out = []
for key in ("quadO", "corrO", "pairO", "pairJ", "handleO", "handleJ", "handleX",
            "quadM", "quadN"):
    if HALF.get(key) is None:
        out.append("-- %s : NOT EVEN\n" % key)
        continue
    out.append("-- witness for %s (%d terms)\n%s\n"
               % (key, len(HALF[key]), render(HALF[key], namer, width=92, indent=6)))
with open(os.path.join(HERE, "results", "witnesses.txt"), "w") as fh:
    fh.write("\n".join(out))
print("witnesses written to results/witnesses.txt")
