"""W59-DEFECT5, step 2: emit the Lean source of the two new core polynomials.

Writes `results/sqU6Core.lean.txt` and `results/sqU6Core4.lean.txt`, the bodies of
the `def sqU6Core` and `def sqU6Core4` declarations transcribed into
`GQ2/Dyadic/SqCore/GradedFiveDefect.lean`.  The polynomials themselves come from
`derive_defect5.py`; nothing is typed by hand.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from u6poly import COORDS, U6, padd, poly_terms, pscale, psub, pvar, sqWord

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(OUT, exist_ok=True)

WIDTH = 96
INDENT = "    "


def lean_factor(v):
    slot, co = v.split("_")
    return "%s.%s" % (slot, co)


def lean_term(mon, c):
    body = " * ".join(lean_factor(v) for v in mon) if mon else "1"
    mag = abs(c)
    if mag == 1:
        return ("-" if c < 0 else "+"), body
    if len(mon) <= 1:
        return ("-" if c < 0 else "+"), "%d * %s" % (mag, body)
    return ("-" if c < 0 else "+"), "%d * (%s)" % (mag, body)


def lean_body(p):
    """The right-hand side of a `def`, wrapped, in the campaign's layout."""
    terms = [lean_term(mon, c) for mon, c in poly_terms(p)]
    pieces = []
    sign0, body0 = terms[0]
    pieces.append(("-(%s)" % body0) if sign0 == "-" else body0)
    for sign, body in terms[1:]:
        pieces.append("%s %s" % (sign, body))
    lines, cur = [], INDENT + pieces[0]
    for piece in pieces[1:]:
        if len(cur) + 1 + len(piece) <= WIDTH:
            cur += " " + piece
        else:
            lines.append(cur)
            cur = INDENT + "  " + piece
    lines.append(cur)
    return "\n".join(lines)


s, x, y = U6.gen("s"), U6.gen("x"), U6.gen("y")
W = sqWord(s, x, y)

for name, co in (("sqU6Core4", "m"), ("sqU6Core", "o")):
    head = padd(pscale(-4, pvar("x_" + co)), pscale(2, pvar("y_" + co)))
    body = psub(getattr(W, co), head)
    text = lean_body(body)
    path = os.path.join(OUT, name + ".lean.txt")
    with open(path, "w") as fh:
        fh.write(text + "\n")
    print("%s: %d terms, %d lines -> %s"
          % (name, len(body), text.count("\n") + 1, path))
