"""W61-WIDER step 6: emit the Lean definitions and a matching plain-Python evaluator.

The two outputs come from the SAME certified polynomial data in `wlib.py`, so the Lean file and
the validator cannot drift apart by a transcription slip; the validator then checks that data
against honest 6 x 6 matrix collection, which is a genuinely independent group law.

  results/lean_defs.txt   the Lean `def` bodies, ready to paste
  forms.py                the same forms as Python expressions, for `validate_wider.py`
"""
import sys
import os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_defect5"))

import u6poly as P                                            # noqa: E402
from u6poly import U6, padd, psub, pmul, pneg, pscale, pzero, pvar  # noqa: E402
import wlib as W                                              # noqa: E402

SUB = {"z0": "z₀", "z1": "z₁", "z2": "z₂"}


def lean_var(v, sub=True):
    head, _, tail = v.partition("_")
    if sub:
        head = SUB.get(head, head)
    return "%s.%s" % (head, tail)


def py_var(v):
    head, _, tail = v.partition("_")
    return "%s.%s" % (head, tail)


def terms_sorted(p):
    return sorted(p.items(), key=lambda kv: (len(kv[0]), kv[0]))


def render(p, namer, width=94, indent=6):
    """Render a polynomial as source text with explicit + / - joins and line wrapping."""
    if not p:
        return "0"
    pieces = []
    for mon, c in terms_sorted(p):
        sign = "-" if c < 0 else "+"
        k = abs(c)
        body = " * ".join(namer(v) for v in mon) if mon else "1"
        txt = body if k == 1 else "%d * %s" % (k, body)
        pieces.append((sign, txt))
    out_lines = []
    cur = ""
    for i, (sign, txt) in enumerate(pieces):
        chunk = txt if i == 0 and sign == "+" else ("-" + txt if i == 0 else sign + " " + txt)
        add = chunk if not cur else cur + " " + chunk
        if len(add) + indent > width and cur:
            out_lines.append(cur)
            cur = chunk
        else:
            cur = add
    out_lines.append(cur)
    pad = "\n" + " " * indent
    return pad.join(out_lines)


# ------------------------------------------------------------------ the blocks
s, x, y = U6.gen("s"), U6.gen("x"), U6.gen("y")
z0, z1, z2 = W.ga2("z0"), W.ga2("z1"), W.ga2("z2")
blocks = W.coreBlocks(s, x, y, z0, z1, z2)

DRESS_ORDER = ["z0_f", "z0_g", "z0_h", "z0_i", "z0_j", "z0_k", "z0_l",
               "z1_f", "z1_g", "z1_h", "z1_i", "z1_j", "z1_k", "z1_l",
               "z2_f", "z2_g", "z2_h", "z2_i", "z2_j", "z2_k", "z2_l"]
FRAME_ORDER = ["", "s_a", "s_c", "s_e", "x_a", "x_c", "x_e", "y_a", "y_c", "y_e"]


def group_by_dress(corr):
    by = {}
    for mon, c in corr.items():
        zs = [v for v in mon if v.startswith("z")]
        assert len(zs) == 1, (mon, c)
        rest = tuple(v for v in mon if not v.startswith("z"))
        by.setdefault(zs[0], {})[rest] = c
    return by


def group_by_frame(quad):
    by = {}
    for mon, c in quad.items():
        rest = tuple(v for v in mon if not v.startswith("z"))
        assert len(rest) <= 1, (mon, c)
        by.setdefault(rest[0] if rest else "", {})[tuple(v for v in mon
                                                         if v.startswith("z"))] = c
    return by


def emit_corr(name, corr, namer, indent=4):
    by = group_by_dress(corr)
    lines = []
    for i, v in enumerate(DRESS_ORDER):
        if v not in by:
            continue
        head = ("  " if i == 0 or not lines else "    + ") + namer(v) + " * ("
        body = render(by[v], namer, width=92, indent=8)
        lines.append(head + body + ")")
    if lines:
        lines[0] = "  " + namer([v for v in DRESS_ORDER if v in by][0]) + " * (" \
            + render(by[[v for v in DRESS_ORDER if v in by][0]], namer, 92, 8) + ")"
    return "\n".join(lines)


def emit_quad(quad, namer):
    by = group_by_frame(quad)
    out = []
    for key in FRAME_ORDER:
        if key not in by:
            continue
        body = render(by[key], namer, width=92, indent=8)
        if key == "":
            out.append("  (" + body + ")")
        else:
            out.append("    + " + namer(key) + " * (" + body + ")")
    return "\n".join(out)


LEAN = []
PY = []


def both(lean_text, py_text):
    LEAN.append(lean_text)
    PY.append(py_text)


# --- the three correction blocks
for co, sig in (("m", "m"), ("n", "n"), ("o", "o")):
    corr, quad = blocks[co]
    LEAN.append("def SqU6.gaTwoCorr%s (s x y z₀ z₁ z₂ : SqU6 R) : R :=\n%s"
                % (co.upper(), emit_corr("", corr, lambda v: lean_var(v))))
    PY.append("def gaTwoCorr%s(s, x, y, z0, z1, z2):\n    return (%s)"
              % (co.upper(),
                 emit_corr("", corr, py_var).replace("\n", "\n    ").strip().lstrip()))

for co in ("m", "n", "o"):
    corr, quad = blocks[co]
    if co == "o":
        LEAN.append("def SqU6.gaTwoQuadO (s x y z₀ z₁ z₂ : SqU6 R) : R :=\n%s"
                    % emit_quad(quad, lambda v: lean_var(v)))
        PY.append("def gaTwoQuadO(s, x, y, z0, z1, z2):\n    return (%s)"
                  % emit_quad(quad, py_var).replace("\n", "\n    ").strip())
    else:
        LEAN.append("def SqU6.gaTwoQuad%s (z₀ z₁ z₂ : SqU6 R) : R :=\n  %s"
                    % (co.upper(), render(quad, lambda v: lean_var(v), 92, 4)))
        PY.append("def gaTwoQuad%s(z0, z1, z2):\n    return (%s)"
                  % (co.upper(), render(quad, py_var, 92, 8)))

with open(os.path.join(HERE, "results", "lean_defs.txt"), "w") as fh:
    fh.write("\n\n".join(LEAN) + "\n")

with open(os.path.join(HERE, "forms.py"), "w") as fh:
    fh.write('"""Emitted by emit_lean.py from wlib.py: the correction and quadratic blocks '
             'as plain\nPython, for validation against honest 6 x 6 collection.  Do not edit '
             'by hand."""\n\n\n')
    fh.write("\n\n\n".join(PY) + "\n")

print("emitted %d Lean blocks -> results/lean_defs.txt" % len(LEAN))
print("emitted %d Python blocks -> forms.py" % len(PY))
for co in ("m", "n", "o"):
    corr, quad = blocks[co]
    print("   %s: correction %d terms, quadratic %d terms" % (co, len(corr), len(quad)))
