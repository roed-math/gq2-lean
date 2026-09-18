#!/usr/bin/env python3
"""STAGED exact symbolic word-template tooling, separate from frozen S1.1.

Lean constructs THE tree and proves its denotation; this script validates that
tree and renders it. It never reconstructs a pair/mobile word from a formula,
approximates a two-adic value, or touches the old hash manifest.

Hash = SHA256(b"GQ2-W361-GENERAL-TEMPLATE\\0" + canonical_json(payload)).
Unlike S1.1, this staged hash binds schema, structural parameters, exact binding
and bridge declaration names, alphabet, and tree. It is NOT an approved gate-7
migration. An instance fixes discrete structural parameters; its continuous
parameters remain symbolic and are bound by the uniform Lean bridge.

Examples:
  python3 scripts/w361_general_word_tex.py generate --lean-runner /path/runner.sh pair 2 1 0
  python3 scripts/w361_general_word_tex.py generate --lean-runner /path/runner.sh mobile 2 1 1 0
  python3 scripts/w361_general_word_tex.py check generated/general-template-staged --lean-runner /path/runner.sh
  python3 scripts/w361_general_word_tex.py self-test
"""

from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Any

SCHEMA = "gq2.w361.general-template.v1.staged"
HASH_DOMAIN = b"GQ2-W361-GENERAL-TEMPLATE\x00"
LEAN_FILE = "GQ2/Dyadic/Word/GeneralTemplateExport.lean"
LEAN_PREFIX = "W361_GENERAL_TEMPLATE_JSON="
DEFAULT_OUT = Path("generated/general-template-staged")
PARAMETER_NAME = re.compile(r"[A-Za-z][A-Za-z0-9_]*\Z")
HEX_HASH = re.compile(r"[0-9a-f]{64}\Z")
PROVENANCE_SCHEMA = "gq2.w361.general-template-provenance.v1.staged"
PROVENANCE_FILES = (
    "GQ2/Dyadic/Word/GeneralTemplate.lean",
    "GQ2/Dyadic/Word/GeneralTemplateM.lean",
    "GQ2/Dyadic/Word/GeneralTemplateSplice.lean",
    "GQ2/Dyadic/Word/GeneralTemplateEval.lean",
    "GQ2/Dyadic/Word/GeneralTemplateExport.lean",
    "scripts/w361_general_word_tex.py",
)
DISPLAY_INLINE_LIMIT = 11
DISPLAY_ROWS_PER_BLOCK = 10


class TemplateError(ValueError):
    """An artifact is malformed, inconsistent, or outside the staged contract."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def template_hash(payload: dict[str, Any]) -> str:
    return hashlib.sha256(HASH_DOMAIN + canonical_json(payload).encode("utf-8")).hexdigest()


def fields(obj: Any, expected: set[str], where: str) -> None:
    if not isinstance(obj, dict) or set(obj) != expected:
        actual = set(obj) if isinstance(obj, dict) else type(obj).__name__
        raise TemplateError(f"{where}: expected fields {sorted(expected)}, got {actual}")


def integer(value: Any, where: str, *, natural: bool = False) -> int:
    if type(value) is not int or (natural and value < 0):
        raise TemplateError(f"{where}: expected {'natural number' if natural else 'integer'}")
    return value


def parameter_name(value: Any, where: str) -> str:
    if not isinstance(value, str) or not PARAMETER_NAME.fullmatch(value):
        raise TemplateError(f"{where}: expected an ASCII identifier")
    return value


def validate_padic(term: Any) -> None:
    if not isinstance(term, dict):
        raise TemplateError("two-adic exponent must be a typed symbolic expression")
    if term.get("type") == "integer":
        fields(term, {"type", "value"}, "two-adic integer")
        integer(term["value"], "two-adic integer")
    elif term.get("type") == "parameter":
        fields(term, {"type", "name", "index"}, "two-adic parameter")
        parameter_name(term["name"], "two-adic parameter")
        integer(term["index"], "two-adic parameter index", natural=True)
    else:
        raise TemplateError("unknown two-adic term; rational and truncated displays are not supported")


def validate_profinite(term: Any) -> None:
    if not isinstance(term, dict):
        raise TemplateError("profinite exponent must be a typed symbolic expression")
    kind = term.get("type")
    if not isinstance(kind, str):
        raise TemplateError("profinite term type must be a string")
    if kind == "integer":
        fields(term, {"type", "value"}, "profinite integer")
        integer(term["value"], "profinite integer")
    elif kind == "omega2":
        fields(term, {"type"}, "omega2")
    elif kind in {"padic_omega", "eta_hat"}:
        fields(term, {"type", "value"}, kind)
        validate_padic(term["value"])
    elif kind == "parameter":
        fields(term, {"type", "name"}, "profinite parameter")
        parameter_name(term["name"], "profinite parameter")
    else:
        raise TemplateError("unknown profinite term")


def child_fields(tree: dict[str, Any]) -> tuple[str, ...]:
    op = tree["op"]
    if op in {"mul", "comm"}:
        return ("left", "right")
    if op == "conj":
        return ("word", "by")
    if op in {"inv", "zpow", "z2pow", "prof_pow"}:
        return ("word",)
    return ()


def children(tree: dict[str, Any]) -> list[dict[str, Any]]:
    return [tree[field] for field in child_fields(tree)]


def validate_tree(tree: Any, degree: int) -> None:
    if not isinstance(tree, dict):
        raise TemplateError("word node must be an object")
    op = tree.get("op")
    if not isinstance(op, str):
        raise TemplateError("word operation must be a string")
    if op == "one":
        fields(tree, {"op"}, "identity")
    elif op == "gen":
        fields(tree, {"op", "name"}, "generator")
        name = tree["name"]
        if not isinstance(name, str):
            raise TemplateError("generator name must be a string")
        if name not in {"sigma", "tau"}:
            if not isinstance(name, str) or not re.fullmatch(r"x(?:0|[1-9][0-9]*)", name):
                raise TemplateError("generator must be sigma, tau, or a canonical x-index")
            if int(name[1:]) > degree:
                raise TemplateError("wild generator is outside the declared alphabet")
    elif op in {"mul", "comm"}:
        fields(tree, {"op", "left", "right"}, op)
    elif op == "inv":
        fields(tree, {"op", "word"}, op)
    elif op == "conj":
        fields(tree, {"op", "word", "by"}, op)
    elif op in {"zpow", "z2pow", "prof_pow"}:
        fields(tree, {"op", "word", "power"}, op)
        if op == "zpow":
            integer(tree["power"], "integer exponent")
        elif op == "z2pow":
            validate_padic(tree["power"])
        else:
            validate_profinite(tree["power"])
    else:
        raise TemplateError(f"unsupported staged node {op!r}; frozen Shadow is not accepted")
    for child in children(tree):
        validate_tree(child, degree)


def validate_envelope(envelope: Any) -> dict[str, Any]:
    fields(envelope, {"payload", "status", "template_hash"}, "envelope")
    if envelope["status"] != "STAGED":
        raise TemplateError("only STAGED artifacts are accepted")
    payload = envelope["payload"]
    fields(payload, {"alphabet_degree", "binding", "bridge", "family", "schema", "structural", "tree"},
           "payload")
    if payload["schema"] != SCHEMA:
        raise TemplateError("wrong staged schema")
    degree = integer(payload["alphabet_degree"], "alphabet degree", natural=True)
    family = payload["family"]
    if not isinstance(family, str) or family not in {"pair", "mobile"}:
        raise TemplateError("unknown source family")
    structure = payload["structural"]
    fields(structure, {"alpha", "h", "j"} if family == "pair" else {"alpha", "r", "p", "h"},
           "structural parameters")
    for key, value in structure.items():
        integer(value, key, natural=True)
    if degree != 2 + 2 * structure["h"]:
        raise TemplateError("alphabet degree does not match handle rank")
    if family == "pair" and not structure["j"] < structure["h"]:
        raise TemplateError("pair requires j < h")
    if payload["binding"] != f"GQ2.Dyadic.GeneralTemplate.{family}Environment":
        raise TemplateError("wrong exact parameter-binding declaration")
    bridge = "denote_pairSplice" if family == "pair" else "denote_mobileSplice"
    if payload["bridge"] != f"GQ2.Dyadic.GeneralTemplate.{bridge}":
        raise TemplateError("wrong exact source bridge")
    validate_tree(payload["tree"], degree)
    digest = envelope["template_hash"]
    if not isinstance(digest, str) or not HEX_HASH.fullmatch(digest) or digest != template_hash(payload):
        raise TemplateError("staged template hash mismatch")
    return payload


def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise TemplateError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def loads(text: str) -> dict[str, Any]:
    obj = json.loads(text, object_pairs_hook=reject_duplicates,
                     parse_constant=lambda value: (_ for _ in ()).throw(TemplateError(f"nonfinite {value}")))
    validate_envelope(obj)
    return obj


def latex_name(name: str) -> str:
    return r"\mathrm{" + name.replace("_", r"\_") + "}"


def padic_latex(term: dict[str, Any]) -> str:
    if term["type"] == "integer":
        return str(term["value"])
    if term["name"] == "eta" and term["index"] == 0:
        return r"\eta"
    return latex_name(term["name"]) + "_{" + str(term["index"]) + "}"


def profinite_latex(term: dict[str, Any]) -> str:
    kind = term["type"]
    if kind == "integer":
        return str(term["value"])
    if kind == "omega2":
        return r"\omega_2"
    if kind == "padic_omega":
        return "(" + padic_latex(term["value"]) + r")\omega_2"
    if kind == "eta_hat":
        return r"\widehat{" + padic_latex(term["value"]) + "}"
    return r"\gamma_{" + latex_name(term["name"]) + "}"


@dataclass(frozen=True)
class AbbreviationPlan:
    """Display-only exact DAG. refs are one-based, strictly backward references.

    This is NOT a new hashed word constructor or a modification of its schema.
    Each definition is a literal subtree, possibly with earlier subtrees named.
    """
    definitions: tuple[dict[str, Any], ...]
    root: dict[str, Any]


def inline_complexity(node: dict[str, Any]) -> int:
    """Count visible word constructors/leaves/refs; exponent atoms remain exact.

    This bounds structural complexity, not the typography of an arbitrarily
    long integer or identifier. Physical page widths still require PDF review.
    """
    return 1 + sum(inline_complexity(child) for child in children(node))


def abbreviation_plan(tree: dict[str, Any], inline_limit: int = DISPLAY_INLINE_LIMIT) -> AbbreviationPlan:
    """Deterministic postorder interning plus size-triggered literal aliases.

    With threshold floor((limit+1)/2), every child left inline has fewer than
    threshold nodes. Binary arity therefore bounds every definition by limit.
    Unlike repetition-only sharing, this also bounds a large unique root.
    """
    if type(inline_limit) is not int or inline_limit < 3:
        raise TemplateError("display inline limit must be an integer at least three")
    counts: Counter[str] = Counter()
    order: list[tuple[str, dict[str, Any], int]] = []
    visited: set[str] = set()

    def collect(node: dict[str, Any]) -> int:
        key = canonical_json(node)
        counts[key] += 1
        size = 1 + sum(collect(child) for child in children(node))
        if key not in visited:
            visited.add(key)
            order.append((key, node, size))
        return size

    collect(tree)
    threshold = (inline_limit + 1) // 2
    displayed: dict[str, dict[str, Any]] = {}
    definitions: list[dict[str, Any]] = []
    for key, node, size in order:
        body = deepcopy(node)
        for field in child_fields(node):
            body[field] = displayed[canonical_json(node[field])]
        if inline_complexity(body) >= threshold or (counts[key] > 1 and size >= 4):
            definitions.append(body)
            displayed[key] = {"op": "ref", "index": len(definitions)}
        else:
            displayed[key] = body
    return AbbreviationPlan(tuple(definitions), displayed[canonical_json(tree)])


def expand_abbreviation_plan(plan: AbbreviationPlan) -> dict[str, Any]:
    """Replay the display-only lets, rejecting forward/self/malformed refs."""
    expanded: list[dict[str, Any]] = []

    def expand(node: dict[str, Any]) -> dict[str, Any]:
        if node["op"] == "ref":
            fields(node, {"op", "index"}, "display reference")
            index = integer(node["index"], "display reference", natural=True)
            if not 1 <= index <= len(expanded):
                raise TemplateError("display reference is not strictly backward")
            return deepcopy(expanded[index - 1])
        result = deepcopy(node)
        for field in child_fields(node):
            result[field] = expand(node[field])
        return result

    for body in plan.definitions:
        expanded.append(expand(body))
    return expand(plan.root)


def check_abbreviation_plan(plan: AbbreviationPlan, tree: dict[str, Any],
                            inline_limit: int = DISPLAY_INLINE_LIMIT) -> None:
    if any(inline_complexity(node) > inline_limit for node in (*plan.definitions, plan.root)):
        raise TemplateError("display abbreviation exceeds its inline-complexity bound")
    if canonical_json(expand_abbreviation_plan(plan)) != canonical_json(tree):
        raise TemplateError("display abbreviation expansion differs from the exact word tree")


def display_node_tex(node: dict[str, Any]) -> str:
    op = node["op"]
    if op == "ref":
        return "W_{" + str(node["index"]) + "}"
    if op == "one":
        return "1"
    if op == "gen":
        name = node["name"]
        return chr(92) + name if name in {"sigma", "tau"} else "x_{" + name[1:] + "}"
    if op == "mul":
        return r"\bigl(" + display_node_tex(node["left"]) + r"\," + display_node_tex(node["right"]) + r"\bigr)"
    if op == "comm":
        return r"\bigl[" + display_node_tex(node["left"]) + "," + display_node_tex(node["right"]) + r"\bigr]"
    if op == "conj":
        return r"\bigl(" + display_node_tex(node["word"]) + r"\bigr)^{" + display_node_tex(node["by"]) + "}"
    if op == "inv":
        power = "-1"
    elif op == "zpow":
        power = str(node["power"])
    elif op == "z2pow":
        power = r"[" + padic_latex(node["power"]) + "]_2"
    else:
        power = profinite_latex(node["power"])
    return r"\bigl(" + display_node_tex(node["word"]) + r"\bigr)^{" + power + "}"


def render_tex(envelope: dict[str, Any]) -> str:
    """Render a checked, structurally bounded exact let plan, never a new word."""
    payload = validate_envelope(envelope)
    tree = payload["tree"]
    plan = abbreviation_plan(tree)
    check_abbreviation_plan(plan, tree)
    structure = ", ".join(f"{key}={value}" for key, value in sorted(payload["structural"].items()))
    lines = ["% STAGED: not an approved S1.1 migration or acceptance appendix.",
             "% Generated only from the Lean-denoting staged expression tree.",
             "% This hash identifies a SYMBOLIC TEMPLATE, not an instantiated profinite word.",
             "% It does NOT hash q, nuP, or the actual eta/k/correction parameter values.",
             "% Declaration names are references, not content addresses; see the provenance sidecar.",
             "% staged-template-hash: " + envelope["template_hash"],
             "% schema: " + SCHEMA,
             "% source bridge: " + payload["bridge"],
             "% exact binding: " + payload["binding"],
             "% structural instance: " + structure,
             "% k_i and eta are exact Z_2 values; gamma_correction is the chosen Zhat exponent.",
             "% The Lean bridge binds them exactly; arbitrary assignments need not satisfy source certificates.",
             "% W_i denote exact subtrees, shared or named to bound display complexity; no simplification.",
             "% Expanding the strictly backward references reproduces the hashed tree exactly.",
             "% Every definition/final expression has at most " + str(DISPLAY_INLINE_LIMIT) + " visible AST/ref nodes.",
             "% Literal integer/parameter widths are not truncated; font/page layout is checked separately."]
    rows = ["W_{" + str(i) + "} &:= " + display_node_tex(body)
            for i, body in enumerate(plan.definitions, 1)]
    rows.append("R_{\\mathrm{" + payload["family"] + "}} &:= " + display_node_tex(plan.root))
    # Short separate blocks avoid relying on a caller's global allowdisplaybreaks.
    for start in range(0, len(rows), DISPLAY_ROWS_PER_BLOCK):
        lines += [r"\begin{align*}",
                  (" " + chr(92)*2 + "\n").join(rows[start:start+DISPLAY_ROWS_PER_BLOCK]),
                  r"\end{align*}"]
    lines.append("")
    return "\n".join(lines)


def stem(payload: dict[str, Any]) -> str:
    s = payload["structural"]
    if payload["family"] == "pair":
        return f"pair-alpha{s['alpha']}-h{s['h']}-j{s['j']}"
    return f"mobile-alpha{s['alpha']}-r{s['r']}-p{s['p']}-h{s['h']}"


def lean_args(payload: dict[str, Any]) -> list[str]:
    s = payload["structural"]
    keys = ("alpha", "h", "j") if payload["family"] == "pair" else ("alpha", "r", "p", "h")
    return [payload["family"], *(str(s[key]) for key in keys)]


def from_lean(runner: Path, arguments: list[str]) -> dict[str, Any]:
    result = subprocess.run(["bash", str(runner.resolve()), "--run", LEAN_FILE, *arguments],
                            text=True, capture_output=True, check=False)
    if result.returncode:
        raise TemplateError("Lean exporter failed:\n" + result.stdout + result.stderr)
    records = [line[len(LEAN_PREFIX):] for line in result.stdout.splitlines() if line.startswith(LEAN_PREFIX)]
    if len(records) != 1:
        raise TemplateError("Lean exporter did not emit exactly one marked JSON artifact")
    obj = loads(records[0])
    if canonical_json(obj) != records[0]:
        raise TemplateError("Lean/Python canonical JSON mismatch")
    return obj


def provenance(envelope: dict[str, Any]) -> dict[str, Any]:
    """A separate byte snapshot: not a hash of transitive Lean dependencies."""
    root = Path(__file__).resolve().parent.parent
    return {
        "schema": PROVENANCE_SCHEMA,
        "scope": "staged-direct-sources-only-not-transitive-build-provenance",
        "source_sha256": {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
                          for name in PROVENANCE_FILES},
        "template_hash": envelope["template_hash"],
    }


def emit(envelope: dict[str, Any], output: Path) -> tuple[Path, Path, Path]:
    payload = validate_envelope(envelope)
    if "general-template-staged" not in output.resolve().parts:
        raise TemplateError("output must be inside a separate general-template-staged directory")
    output.mkdir(parents=True, exist_ok=True)
    base = output / stem(payload)
    json_path = base.with_suffix(".template.json")
    tex_path = base.with_suffix(".tex")
    provenance_path = base.with_suffix(".provenance.json")
    json_path.write_text(canonical_json(envelope) + "\n", encoding="utf-8")
    tex_path.write_text(render_tex(envelope), encoding="utf-8")
    provenance_path.write_text(canonical_json(provenance(envelope)) + "\n", encoding="utf-8")
    return json_path, tex_path, provenance_path


def check(directory: Path, runner: Path | None = None) -> int:
    paths = sorted(directory.glob("*.template.json"))
    if not paths:
        raise TemplateError("no staged template artifacts found")
    for path in paths:
        obj = loads(path.read_text(encoding="utf-8"))
        expected_path = directory / (stem(obj["payload"]) + ".template.json")
        if path != expected_path:
            raise TemplateError(f"noncanonical artifact filename: {path}")
        tex_path = directory / (stem(obj["payload"]) + ".tex")
        if tex_path.read_text(encoding="utf-8") != render_tex(obj):
            raise TemplateError(f"generated TeX drift: {tex_path}")
        provenance_path = directory / (stem(obj["payload"]) + ".provenance.json")
        recorded = json.loads(provenance_path.read_text(encoding="utf-8"), object_pairs_hook=reject_duplicates)
        if recorded != provenance(obj):
            raise TemplateError(f"direct source provenance drift: {provenance_path}")
        if runner is not None and from_lean(runner, lean_args(obj["payload"])) != obj:
            raise TemplateError(f"artifact differs from its actual Lean tree: {path}")
        mode = "Lean-replayed" if runner is not None else "artifact-only; NOT Lean-synchronized"
        print(f"STAGED {mode}: {path.name} {obj['template_hash']}")
    return len(paths)


def abbreviation_self_test() -> int:
    """Durable exact-expansion/layout tests, including all four actual exports."""
    count = 0

    def check_tree(tree: dict[str, Any], label: str) -> None:
        nonlocal count
        before = canonical_json(tree)
        plan = abbreviation_plan(tree)
        check_abbreviation_plan(plan, tree)
        assert expand_abbreviation_plan(plan) == tree
        count += 2
        assert all(inline_complexity(body) <= DISPLAY_INLINE_LIMIT for body in plan.definitions)
        assert inline_complexity(plan.root) < (DISPLAY_INLINE_LIMIT + 1)//2
        count += 2
        assert plan == abbreviation_plan(deepcopy(tree))
        assert plan == abbreviation_plan(json.loads(before))
        assert before == canonical_json(tree)  # planning has not mutated the input
        count += 3
        for limit in (3, 4, 7, 12):
            alternative = abbreviation_plan(tree, limit)
            check_abbreviation_plan(alternative, tree, limit)
            count += 1
        max_size = max(inline_complexity(body) for body in (*plan.definitions, plan.root))
        print(f"DISPLAY_DAG_CASE|{label}|definitions={len(plan.definitions)}|max_inline={max_size}")

    sigma = {"op": "gen", "name": "sigma"}
    unique = sigma
    for i in range(1, 65):
        unique = {"op": "mul", "left": unique,
                  "right": {"op": "zpow", "word": sigma, "power": i}}
    check_tree(unique, "unique-long-chain")
    assert abbreviation_plan(unique).definitions  # repetition-only sharing cannot suffice
    count += 1
    repeated = {"op": "comm", "left": sigma, "right": {"op": "gen", "name": "tau"}}
    for _ in range(7):
        repeated = {"op": "mul", "left": repeated, "right": repeated}
    check_tree(repeated, "deep-shared-tree")
    every_constructor = {"op": "mul", "left": {"op": "one"}, "right": {
        "op": "conj", "word": {"op": "inv", "word": {"op": "comm", "left": sigma,
        "right": {"op": "gen", "name": "x2"}}}, "by": {"op": "z2pow", "word": {
        "op": "prof_pow", "word": sigma, "power": {"type": "eta_hat", "value": {
        "type": "parameter", "name": "eta", "index": 0}}},
        "power": {"type": "parameter", "name": "k", "index": 1}}}}
    check_tree(every_constructor, "all-word-constructors")
    names = ("mobile-alpha2-r1-p0-h0", "mobile-alpha3-r2-p2-h1",
             "pair-alpha2-h1-j0", "pair-alpha3-h2-j1")
    directory = Path(__file__).resolve().parent.parent / DEFAULT_OUT
    for name in names:
        obj = loads((directory/(name+".template.json")).read_text())
        before = canonical_json(obj)
        check_tree(obj["payload"]["tree"], name)
        rendered = render_tex(obj)
        assert rendered == render_tex(deepcopy(obj))
        assert canonical_json(obj) == before
        count += 2
        for block in rendered.split(r"\begin{align*}")[1:]:
            body = block.split(r"\end{align*}")[0]
            assert body.count(" &:= ") <= DISPLAY_ROWS_PER_BLOCK
            assert body.count(" &:= ") >= 1
        count += 1

    bad_plans = [
        AbbreviationPlan(({"op": "ref", "index": 1},), {"op": "ref", "index": 1}),
        AbbreviationPlan(({"op": "ref", "index": 2}, sigma), {"op": "ref", "index": 1}),
        *(AbbreviationPlan((), {"op": "ref", "index": i}) for i in (True, 0, -1, "1", 1)),
        AbbreviationPlan((sigma,), {"op": "ref", "index": 1, "extra": 0}),
        AbbreviationPlan((), unique),
        AbbreviationPlan((), {"op": "gen", "name": "tau"}),
    ]
    for plan in bad_plans:
        try:
            check_abbreviation_plan(plan, sigma)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid display plan accepted")
    for bad_limit in (True, 0, 1, 2, 3.0):
        try:
            abbreviation_plan(sigma, bad_limit)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid inline limit accepted")
    print(f"DISPLAY_DAG_SELF_TEST_PASS|{count}")
    return count


def self_test() -> int:
    base = {"alphabet_degree": 2, "binding": "GQ2.Dyadic.GeneralTemplate.mobileEnvironment",
            "bridge": "GQ2.Dyadic.GeneralTemplate.denote_mobileSplice", "family": "mobile",
            "schema": SCHEMA, "structural": {"alpha": 2, "r": 1, "p": 0, "h": 0},
            "tree": {"op": "prof_pow", "word": {"op": "gen", "name": "sigma"},
                     "power": {"type": "eta_hat", "value": {"type": "parameter", "name": "eta", "index": 0}}}}
    def wrap(payload: dict[str, Any]) -> dict[str, Any]:
        return {"payload": payload, "status": "STAGED", "template_hash": template_hash(payload)}
    obj = wrap(base)
    assert loads(canonical_json(obj)) == obj
    assert r"\widehat{\eta}" in render_tex(obj)
    count = 2
    generator = {"op": "gen", "name": "sigma"}
    other = {"op": "gen", "name": "x2"}
    examples = [
        {"op": "one"}, generator, other,
        {"op": "mul", "left": generator, "right": other},
        {"op": "comm", "left": generator, "right": other},
        {"op": "conj", "word": generator, "by": other},
        {"op": "inv", "word": generator},
        {"op": "zpow", "word": generator, "power": -3},
        {"op": "z2pow", "word": generator,
         "power": {"type": "parameter", "name": "k", "index": 2}},
        {"op": "z2pow", "word": generator, "power": {"type": "integer", "value": -3}},
        *({"op": "prof_pow", "word": generator, "power": term} for term in [
            {"type": "omega2"}, {"type": "integer", "value": 4},
            {"type": "parameter", "name": "correction"},
            {"type": "padic_omega", "value": {"type": "parameter", "name": "k", "index": 1}},
        ]),
    ]
    for tree in examples:
        sample = deepcopy(base)
        sample["tree"] = tree
        assert loads(canonical_json(wrap(sample))) == wrap(sample)
        assert render_tex(wrap(sample)).endswith("\\end{align*}\n")
        count += 1
    mutations = [
        lambda p: p.update(schema="S1.1"),
        lambda p: p.update(alphabet_degree=4),
        lambda p: p.update(bridge="other"),
        lambda p: p["structural"].update(h=True),
        lambda p: p["tree"].update(extra=1),
        lambda p: p["tree"].update(op="Shadow"),
        lambda p: p["tree"].update(op=[]),
        lambda p: p["tree"]["word"].update(name="x3"),
        lambda p: p["tree"]["word"].update(name={}),
        lambda p: p["tree"]["word"].update(name="x01"),
        lambda p: p["tree"]["power"].update(value={"type": "rational", "num": 1, "den": 3}),
        lambda p: p["tree"]["power"].update(value={"type": "truncated", "precision": 8, "value": 3}),
        lambda p: p["tree"]["power"]["value"].update(index=-1),
        lambda p: p["tree"]["power"]["value"].update(name=r"bad\input"),
        lambda p: p["tree"]["power"]["value"].update(index=1.0),
        lambda p: p["tree"]["power"].update(type=[]),
    ]
    for mutate in mutations:
        p = deepcopy(base)
        mutate(p)
        try:
            validate_envelope(wrap(p))
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid mutation accepted")
    for malformed in [canonical_json(obj).replace('"STAGED"', '"APPROVED"'),
                      canonical_json(obj).replace('"eta"', '"different"'),
                      '{"payload":{},"payload":{}}']:
        try:
            loads(malformed)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid envelope accepted")
    changed = deepcopy(base)
    changed["structural"]["alpha"] = 3
    assert template_hash(changed) != template_hash(base)
    assert template_hash(base) != hashlib.sha256(canonical_json(base).encode()).hexdigest()
    count += 2 + abbreviation_self_test()
    print(f"STAGED self-test: {count} checks passed")
    return count


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    gen = sub.add_parser("generate")
    gen.add_argument("--lean-runner", type=Path, required=True)
    gen.add_argument("--output", type=Path, default=DEFAULT_OUT)
    gen.add_argument("family", choices=["pair", "mobile"])
    gen.add_argument("parameters", nargs="+")
    check_parser = sub.add_parser("check")
    check_parser.add_argument("directory", type=Path, nargs="?", default=DEFAULT_OUT)
    check_parser.add_argument("--lean-runner", type=Path,
                              help="required for strong acceptance: replay and compare the actual Lean tree")
    render_parser = sub.add_parser("render")
    render_parser.add_argument("artifact", type=Path)
    sub.add_parser("self-test")
    args = parser.parse_args()
    try:
        if args.command == "generate":
            obj = from_lean(args.lean_runner, [args.family, *args.parameters])
            for path in emit(obj, args.output):
                print(path)
            print("STAGED template hash: " + obj["template_hash"])
        elif args.command == "check":
            check(args.directory, args.lean_runner)
        elif args.command == "render":
            print(render_tex(loads(args.artifact.read_text(encoding="utf-8"))), end="")
        else:
            self_test()
    except (TemplateError, OSError, json.JSONDecodeError) as error:
        print(f"staged template error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
