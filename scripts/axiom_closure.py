#!/usr/bin/env python3
"""Render docs/axiom-closure.md from the JSON emitted by scripts/AxiomClosureProbe.lean.

Usage: python3 scripts/axiom_closure.py <probe-output.json> > docs/axiom-closure.md
Driver: scripts/axiom_closure.sh (runs the probe, then this renderer).

Line numbers are resolved by scanning each module's source for the declaration; a
declaration that cannot be located textually (e.g. produced by `alias` or notation
machinery) is linked to its file without a line anchor.
"""
import json
import re
import sys
from collections import defaultdict
from datetime import date
from pathlib import Path

BTAG = {
    "GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated": "B1",
    "GQ2.Foundations.absGalQ2_localEulerCharacteristic": "B7",
    "GQ2.dyadicOrientation": "B3c",
    "GQ2.localReciprocity": "B5",
    "GQ2.markedRecipAt": "B5-K",
    "GQ2.tateDualityAt": "B6",
    "GQ2.peripheralCyclotomicAction": "B8",
    "GQ2.relativeStiefelWhitney_dyadic": "B9",
    "GQ2.tameQuotient": "B10",
    "GQ2.hilbertSymbol_normCriterion_finiteDyadic": "B11a",
}

DECL_KEYWORDS = (
    "def|abbrev|theorem|lemma|structure|class|inductive|instance|opaque|axiom|alias"
)
MODIFIERS = r"(?:@\[[^\]]*\]\s*)*(?:public\s+|private\s+|protected\s+|noncomputable\s+|scoped\s+|partial\s+|unsafe\s+)*"


def module_file(module: str) -> Path:
    return Path(module.replace(".", "/") + ".lean")


def find_line(module: str, name: str, cache: dict) -> int | None:
    """First line declaring `name` (matched by its last component) in `module`'s source."""
    path = module_file(module)
    if path not in cache:
        try:
            cache[path] = path.read_text().splitlines()
        except OSError:
            cache[path] = []
    last = re.escape(name.rsplit(".", 1)[-1])
    pat = re.compile(
        rf"^\s*{MODIFIERS}(?:{DECL_KEYWORDS})\s+(?:[\w'.]+\.)?{last}(?![\w'])"
    )
    for i, line in enumerate(cache[path], 1):
        if pat.match(line):
            return i
    return None


def link(module: str, line: int | None) -> str:
    path = module_file(module)
    if line is None:
        return f"[{path}](../{path})"
    return f"[{path}:{line}](../{path}#L{line})"


def main() -> None:
    text = Path(sys.argv[1]).read_text()
    data = json.loads(text[text.index("{"):])
    axioms = data["axioms"]
    cache: dict = {}

    # union vocabulary: name -> (module, kind, doc, set of B-tags)
    vocab: dict[str, dict] = {}
    for ax in axioms:
        tag = BTAG[ax["axiom"]]
        for e in ax["closure"]:
            v = vocab.setdefault(
                e["name"],
                {"module": e["module"], "kind": e["kind"], "doc": e["doc"], "tags": set()},
            )
            v["tags"].add(tag)

    tag_order = ["B1", "B3c", "B5", "B5-K", "B6", "B7", "B8", "B9", "B10", "B11a"]

    def tags_str(tags):
        return ", ".join(t for t in tag_order if t in tags)

    out = []
    p = out.append
    p("# Axiom statement closures")
    p("")
    p(f"*Generated {date.today().isoformat()} by `scripts/axiom_closure.sh`; regenerate after")
    p("any change to `GQ2/Foundations/Axioms.lean` or to a definition listed below.*")
    p("")
    p("For each of the nine literature axioms this lists every **project** constant a reader")
    p("must understand to know *what the axiom asserts*: the transitive closure of the axiom's")
    p("statement through definition bodies and structure fields.  Mathlib constants are not")
    p("listed (they are the shared trusted vocabulary), and **proofs are pruned**: a theorem")
    p("reached by a definition contributes only its statement, since its proof is")
    p("machine-checked — the Lean-Compass review model (`docs/atlas.md`).  Definitions and")
    p("structures are what a human auditor reads; the referenced theorems are listed")
    p("separately since only their (checked) statements participate in meaning.")
    p("")

    p("## Summary")
    p("")
    p("| axiom | leaf | defs/structures to read | proved theorems referenced |")
    p("|---|---|---:|---:|")
    for ax in axioms:
        tag = BTAG[ax["axiom"]]
        ndefs = sum(1 for e in ax["closure"] if e["kind"] != "theorem")
        nthms = sum(1 for e in ax["closure"] if e["kind"] == "theorem")
        p(f"| **{tag}** | `{ax['axiom']}` | {ndefs} | {nthms} |")
    ndefs_u = sum(1 for v in vocab.values() if v["kind"] != "theorem")
    nthms_u = sum(1 for v in vocab.values() if v["kind"] == "theorem")
    p(f"| **union** | all nine | {ndefs_u} | {nthms_u} |")
    p("")
    mods = sorted({v["module"] for v in vocab.values()})
    p(f"The union spans {len(mods)} modules: " + ", ".join(f"`{m}`" for m in mods) + ".")
    p("")

    p("## Vocabulary (union across the nine axioms)")
    p("")
    p("Grouped by module; *(kind, source)* — *used by* — first docstring line.")
    by_mod: dict[str, list] = defaultdict(list)
    for name, v in vocab.items():
        by_mod[v["module"]].append((name, v))
    for mod in mods:
        entries = by_mod[mod]
        resolved = [(find_line(mod, n, cache), n, v) for n, v in entries]
        resolved.sort(key=lambda t: (t[0] is None, t[0] or 0, t[1]))
        p(f"### `{module_file(mod)}`")
        p("")
        for line, name, v in resolved:
            doc = f" — {v['doc']}" if v["doc"] else ""
            p(f"- `{name}` ({v['kind']}, {link(mod, line)}) — *{tags_str(v['tags'])}*{doc}")
        p("")

    p("## Per-axiom closures")
    p("")
    for ax in axioms:
        tag = BTAG[ax["axiom"]]
        line = find_line(ax["module"], ax["axiom"], cache)
        p(f"### {tag} — `{ax['axiom']}` ({link(ax['module'], line)})")
        p("")
        defs = [e["name"] for e in ax["closure"] if e["kind"] != "theorem"]
        thms = [e["name"] for e in ax["closure"] if e["kind"] == "theorem"]
        if defs:
            p(f"*Read ({len(defs)}):* " + ", ".join(f"`{n}`" for n in defs))
        else:
            p("*Read:* nothing beyond Mathlib — the statement is Mathlib-pure.")
        if thms:
            p("")
            p(f"*Checked statements referenced ({len(thms)}):* "
              + ", ".join(f"`{n}`" for n in thms))
        p("")

    print("\n".join(out))


if __name__ == "__main__":
    main()
