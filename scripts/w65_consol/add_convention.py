"""W65-CONSOL: add a BRACKET CONVENTION line to every certification script.

W64-VERIFY's closing recommendation, item 6: "a certification script should state which bracket
its Lean target uses and compute that one".  This script does it, across `scripts/w5*/` and
`scripts/w6*/`, using the classification of `convention_lib.py`, and is IDEMPOTENT: a second run
rewrites an existing block in place rather than stacking a second one.

Run `python3 scripts/w65_consol/add_convention.py --check` to classify without editing, and
`python3 scripts/w65_consol/add_convention.py` to write.  The certified table lands in
`scripts/w65_consol/results/convention.txt`.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import convention_lib as C  # noqa: E402

MARK = "BRACKET CONVENTION."

RULE = (
    "Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP\n"
    "in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,\n"
    "[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a\n"
    "paper-convention computation certifies a commP-written Lean statement and MIS-certifies a\n"
    "[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE."
)

BODY = {
    "MATHLIB": (
        "WARNING: the Lean target of this script is written with MATHLIB's bracket, not with\n"
        "commP.  Any raw bracket set computed here must be computed in mathlib's convention.\n"
        "{ev}"
    ),
    "PAPER-RAW": (
        "This script builds RAW nested bracket sets, and its Lean target is written with commP,\n"
        "so the paper convention is the right one to compute.  Raw bracket sets are the only\n"
        "computations in this tree that can be wrong about the convention: check this line\n"
        "before repointing the script at a [.,.]-written statement."
    ),
    "IMMUNE": (
        "This script only ever sifts brackets into a closure, which is convention-IMMUNE (the\n"
        "generated subgroup is the same in either convention), so nothing here depends on the\n"
        "choice.  Its Lean target is written with commP."
    ),
    "PAPER": (
        "This script computes brackets in the paper convention, and its Lean target is written\n"
        "with commP, the same convention."
    ),
    "NONE": "This script computes no commutators, so the convention does not arise.",
}


def block(verdict, evidence):
    ev = ""
    if evidence and evidence != ["(directory target)"]:
        ev = "Lean declarations named here that use it: " + ", ".join(evidence) + ".\n"
    elif evidence:
        ev = ("The target is GQ2/Dyadic/SqCore/GradedStageFour.lean, whose gapOneABr .. gapTwoBBr\n"
              "are [[L a, L b], L c] in mathlib's bracket.\n")
    return "%s  [%s]\n%s%s\n%s" % (MARK, verdict, BODY[verdict].format(ev=ev), "", RULE)


def strip_old(text):
    """Remove a previously inserted block, so the script is idempotent."""
    i = text.find(MARK)
    if i == -1:
        return text, False
    j = text.find("convention-IMMUNE.", i)
    if j == -1:
        return text, False
    j = text.find("\n", j)
    k = j + 1
    while k < len(text) and text[k] == "\n":
        k += 1
    start = i
    while start > 0 and text[start - 1] == "\n":
        start -= 1
    return text[:start] + "\n" + text[k:], True


def insert(path, verdict, evidence, write=True):
    text = open(path, encoding="utf-8").read()
    text, had = strip_old(text)
    blk = block(verdict, evidence)
    if text.startswith('"""'):
        end = text.find('"""', 3)
        head, tail = text[: end], text[end:]
        if not head.endswith("\n"):
            head += "\n"
        new = head + "\n" + blk + "\n" + tail
    else:
        lead = ""
        rest = text
        if text.startswith("#!"):
            nl = text.find("\n") + 1
            lead, rest = text[:nl], text[nl:]
        new = lead + '"""' + os.path.basename(path) + ".\n\n" + blk + '\n"""\n\n' + rest.lstrip("\n")
    if write:
        open(path, "w", encoding="utf-8").write(new)
    return had


def main():
    write = "--check" not in sys.argv
    risky = C.risky_lean_names()
    dirs = C.mathlib_directories(risky)
    rows = []
    for f in C.script_files():
        if os.sep + "w65_consol" + os.sep in f:
            continue
        v, e = C.classify(f, risky, dirs)
        had = insert(f, v, e, write=write)
        rows.append((f, v, "rewrote" if had else "added"))
    counts = {}
    for _, v, _ in rows:
        counts[v] = counts.get(v, 0) + 1
    out = []
    out.append("W65-CONSOL: BRACKET CONVENTION lines, one per certification script")
    out.append("=" * 78)
    out.append("")
    out.append("Element-level mathlib-bracket declarations in GQ2/ (the whole risk surface):")
    base = C.element_level_names()
    for n in sorted(base):
        out.append("    %-12s  %s" % (n, base[n][0]))
    out.append("")
    out.append("Names stated in terms of them (also risky to certify in the wrong convention):")
    out.append("    " + ", ".join(sorted(set(risky) - set(base))))
    out.append("")
    out.append("Wave directories whose Lean target is mathlib-bracketed: " + ", ".join(sorted(dirs)))
    out.append("")
    for f, v, act in rows:
        out.append("  %-9s %-8s %s" % (v, act, f))
    out.append("")
    out.append("totals: " + ", ".join("%s=%d" % kv for kv in sorted(counts.items())))
    out.append("scripts touched: %d" % len(rows))
    txt = "\n".join(out) + "\n"
    res = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results", "convention.txt")
    os.makedirs(os.path.dirname(res), exist_ok=True)
    if write:
        open(res, "w", encoding="utf-8").write(txt)
    print(txt)


if __name__ == "__main__":
    main()
