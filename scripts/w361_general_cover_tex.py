#!/usr/bin/env python3
"""STAGED rendering of typed compact phase-cover fields exported by Lean.

The coefficient quadratic form is printed q_0 (not the residue-cardinality q).
The natural variable d remains symbolic, with #V=2^d. Artifact-only validation
checks syntax, hashes and rendering; only strong replay binds the Lean factory.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re
import subprocess

from w361_general_word_tex import TemplateError, canonical_json, fields, integer, reject_duplicates
from w361_general_phase_tex import coordinates, tree_tex, validate_coordinate, validate_tree

SCHEMA = "gq2.w361.phase-cover.v1.staged"
DOMAIN = b"GQ2-W361-PHASE-COVER\0"
LEAN_FILE = "GQ2/Dyadic/Word/GeneralPhaseCoverTemplateExport.lean"
PREFIX = "W361_PHASE_COVER_TEMPLATE_JSON="


def digest(payload):
    return hashlib.sha256(DOMAIN + canonical_json(payload).encode()).hexdigest()


def validate_input(term):
    fields(term, {"op"}, "cover input term")
    if term["op"] not in ("zero", "input"):
        raise TemplateError("unknown cover input term")


def validate_dimension(term):
    if not isinstance(term, dict):
        raise TemplateError("cover dimension term must be an object")
    op = term.get("op")
    if op == "literal":
        fields(term, {"op", "value"}, "cover dimension literal")
        integer(term["value"], "cover dimension literal", natural=True)
    elif op == "dimension":
        fields(term, {"op", "variable"}, "cover dimension variable")
        if term["variable"] != "d":
            raise TemplateError("cover dimension variable must be d")
    elif op in ("add", "mul"):
        fields(term, {"op", "left", "right"}, "cover dimension operation")
        validate_dimension(term["left"])
        validate_dimension(term["right"])
    else:
        raise TemplateError("unknown cover dimension operation")


def validate_embedding(table, h):
    # Check length before constructing a table for a potentially huge declared h.
    if not isinstance(table, list) or len(table) != 2 + 2*h:
        raise TemplateError("cover embedding has the wrong coordinate count")
    for entry in table:
        fields(entry, {"at", "value"}, "cover embedding entry")
        validate_coordinate(entry["at"], h)
        validate_input(entry["value"])
    if [entry["at"] for entry in table] != coordinates(h):
        raise TemplateError("cover embedding coordinate order mismatch")


def validate(envelope):
    fields(envelope, {"payload", "status", "template_hash"}, "cover envelope")
    if envelope["status"] != "STAGED":
        raise TemplateError("cover artifacts must remain STAGED")
    p = envelope["payload"]
    fields(p, {"base_dim", "base_sign", "bridge", "diagonal", "factory", "j0", "j1",
               "kind", "phase_template_hash", "phase_tree", "schema", "structural"}, "cover payload")
    if (p["schema"] != SCHEMA or p["kind"] != "compact-wall-handle"
            or p["factory"] != "GQ2.Dyadic.GeneralPhaseCoverTemplate.compactTemplate"
            or p["bridge"] != "GQ2.Dyadic.GeneralPhaseCoverTemplate.compactTemplate_agrees"):
        raise TemplateError("cover semantic identity mismatch")
    fields(p["structural"], {"h"}, "cover structural parameters")
    h = integer(p["structural"]["h"], "cover handle rank", natural=True)
    validate_embedding(p["j0"], h)
    validate_embedding(p["j1"], h)
    validate_dimension(p["base_dim"])
    if integer(p["base_sign"], "cover base sign") != 1:
        raise TemplateError("compact cover base sign must be positive one")
    fields(p["diagonal"], {"op", "at"}, "cover diagonal")
    if p["diagonal"]["op"] != "baseQuad":
        raise TemplateError("cover diagonal must retain the base quadratic form")
    validate_input(p["diagonal"]["at"])
    validate_tree(p["phase_tree"], h)
    if (not isinstance(p["phase_template_hash"], str)
            or re.fullmatch(r"[0-9a-f]{64}", p["phase_template_hash"]) is None):
        raise TemplateError("cover phase-template hash must be a lowercase SHA-256 digest")
    if envelope["template_hash"] != digest(p):
        raise TemplateError("cover template hash mismatch")
    return p


def loads(text):
    value = json.loads(text, object_pairs_hook=reject_duplicates,
                       parse_constant=lambda x: (_ for _ in ()).throw(TemplateError(x)))
    validate(value)
    return value


def from_lean(runner, h):
    integer(h, "cover handle rank", natural=True)
    result = subprocess.run(["bash", str(Path(runner).resolve()), "--run", LEAN_FILE, str(h)],
                            text=True, capture_output=True)
    if result.returncode:
        raise TemplateError("Lean cover exporter failed:\n" + result.stdout + result.stderr)
    records = [line[len(PREFIX):] for line in result.stdout.splitlines() if line.startswith(PREFIX)]
    if len(records) != 1:
        raise TemplateError("Lean cover exporter must emit exactly one marked artifact")
    obj = loads(records[0])
    if canonical_json(obj) != records[0]:
        raise TemplateError("Lean/Python cover canonical JSON mismatch")
    if obj["payload"]["structural"]["h"] != h:
        raise TemplateError("Lean cover exporter returned a different rank")
    return obj


def input_tex(term):
    return "v" if term["op"] == "input" else "0"


def dimension_tex(term):
    op = term["op"]
    if op == "literal":
        return str(term["value"])
    if op == "dimension":
        return "d"
    operation = "+" if op == "add" else r"\cdot "
    return r"\bigl(" + dimension_tex(term["left"]) + operation + dimension_tex(term["right"]) + r"\bigr)"


def embedding_tex(table):
    return r"\bigl(" + ",".join(input_tex(entry["value"]) for entry in table) + r"\bigr)"


def render_tex(envelope):
    p = validate(envelope)
    return "\n".join([
        "% STAGED symbolic phase-cover data; not a source-word or coefficient-space hash.",
        "% cover-template-hash: " + envelope["template_hash"],
        "% phase-template-hash: " + p["phase_template_hash"],
        "% exact bridge: " + p["bridge"],
        "% q_0 is the coefficient quadratic form, not residue cardinality q; #V=2^d.",
        "% Embedding vectors are in the listed flattened head/handle coordinate order.",
        r"\[j_0(v)=" + embedding_tex(p["j0"]) + r",\qquad j_1(v)=" + embedding_tex(p["j1"]) + r".\]",
        r"\[\operatorname{diag}(v)=q_0(" + input_tex(p["diagonal"]["at"]) + r"),\qquad m=" +
        dimension_tex(p["base_dim"]) + r",\qquad \varepsilon=" + str(p["base_sign"]) + r".\]",
        r"\[Q=" + tree_tex(p["phase_tree"]) + r".\]",
        "% Under compactTemplate_agrees hypotheses, diag(v)=dat.f(v,v);",
        "% the original cover certifies #W=2^(2m), Gauss(Q)=epsilon*2^m and the polar/kappa identities.",
        "% coordinate order: " + canonical_json([entry["at"] for entry in p["j0"]]), ""])


def self_test():
    head0, head1 = coordinates(0)
    payload = {
        "base_dim": {"op": "mul", "left": {"op": "add", "left": {"op": "literal", "value": 0},
                     "right": {"op": "literal", "value": 1}}, "right": {"op": "dimension", "variable": "d"}},
        "base_sign": 1, "bridge": "GQ2.Dyadic.GeneralPhaseCoverTemplate.compactTemplate_agrees",
        "diagonal": {"op": "baseQuad", "at": {"op": "input"}},
        "factory": "GQ2.Dyadic.GeneralPhaseCoverTemplate.compactTemplate",
        "j0": [{"at": head0, "value": {"op": "input"}}, {"at": head1, "value": {"op": "zero"}}],
        "j1": [{"at": head0, "value": {"op": "zero"}}, {"at": head1, "value": {"op": "input"}}],
        "kind": "compact-wall-handle", "phase_template_hash": "0"*64, "phase_tree": {"op": "zero"},
        "schema": SCHEMA, "structural": {"h": 0}}
    def wrap(p):
        return {"payload": p, "status": "STAGED", "template_hash": digest(p)}
    obj = wrap(payload)
    assert loads(canonical_json(obj)) == obj
    assert r"j_0(v)=\bigl(v,0\bigr)" in render_tex(obj)
    assert r"j_1(v)=\bigl(0,v\bigr)" in render_tex(obj)
    assert r"\operatorname{diag}(v)=q_0(v)" in render_tex(obj)
    count = 4
    mutations = [
        lambda p: p.update(schema="wrong"), lambda p: p.update(kind="wrong"),
        lambda p: p.update(factory="wrong"), lambda p: p.update(bridge="wrong"),
        lambda p: p.update(extra=0), lambda p: p["structural"].update(h=True),
        lambda p: p["structural"].update(h=-1), lambda p: p["structural"].update(h=0.0),
        lambda p: p["structural"].update(h=10**100), lambda p: p["structural"].update(extra=1),
        lambda p: p.update(j0={}), lambda p: p["j0"].reverse(), lambda p: p["j1"].pop(),
        lambda p: p["j0"][0].update(extra=1), lambda p: p["j0"][0]["at"].update(index=0),
        lambda p: p["j0"][0].update(value={"op": "input", "extra": 0}),
        lambda p: p["j1"][0].update(value={"op": "other"}),
        lambda p: p["base_dim"]["left"]["left"].update(value=True),
        lambda p: p["base_dim"]["left"]["left"].update(value=-1),
        lambda p: p["base_dim"]["left"]["left"].update(value=1.0),
        lambda p: p["base_dim"]["right"].update(variable="other"),
        lambda p: p.update(base_dim={"op": "mul", "left": 0, "right": 0}),
        lambda p: p.update(base_dim={"op": "dimension", "variable": "d", "extra": 0}),
        lambda p: p.update(base_dim={"op": "divide"}),
        lambda p: p.update(base_sign=True), lambda p: p.update(base_sign=1.0),
        lambda p: p.update(base_sign=-1), lambda p: p.update(diagonal={"op": "polar"}),
        lambda p: p["diagonal"].update(at={"op": "head0"}),
        lambda p: p.update(phase_tree={"op": "unknown"}),
        lambda p: p.update(phase_template_hash="0"*63),
        lambda p: p.update(phase_template_hash="A"*64),
        lambda p: p.update(phase_template_hash=0)]
    for mutate in mutations:
        p = deepcopy(payload)
        mutate(p)
        try:
            validate(wrap(p))
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid cover artifact accepted")
    one = deepcopy(payload)
    one["structural"]["h"] = 1
    for key in ("j0", "j1"):
        one[key].extend({"at": c, "value": {"op": "zero"}} for c in coordinates(1)[2:])
    validate(wrap(one))
    count += 1
    for bad in (False, 0.0, "0", -1, 1):
        p = deepcopy(one)
        p["j0"][2]["at"]["index"] = bad
        try:
            validate(wrap(p))
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid cover handle index accepted")
    for bad in ('[]', 'NaN', 'Infinity', '-Infinity', '{"payload":0,"payload":0}',
                canonical_json(obj).replace('"h":0', '"h":0,"h":0'),
                canonical_json(obj).replace('"STAGED"', '"APPROVED"'),
                canonical_json(obj).replace(obj["template_hash"], 'f'*64)):
        try:
            loads(bad)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid cover JSON/envelope accepted")
    print(f"COVER_TOOL_SELF_TEST_PASS|{count}")
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("self-test")
    generate = sub.add_parser("generate")
    generate.add_argument("h", type=int)
    generate.add_argument("--lean-runner", type=Path, required=True)
    generate.add_argument("--out", type=Path, default=Path("generated/general-certificate-staged"))
    check = sub.add_parser("check")
    check.add_argument("directory", type=Path)
    check.add_argument("--lean-runner", type=Path)
    args = parser.parse_args()
    if args.command == "self-test":
        self_test()
    elif args.command == "generate":
        integer(args.h, "cover handle rank", natural=True)
        if "general-certificate-staged" not in args.out.resolve().parts:
            raise TemplateError("cover output must be inside general-certificate-staged")
        obj = from_lean(args.lean_runner, args.h)
        args.out.mkdir(parents=True, exist_ok=True)
        base = args.out / f"compact-cover-h{args.h}"
        base.with_suffix(".cover.json").write_text(canonical_json(obj)+"\n")
        base.with_suffix(".cover.tex").write_text(render_tex(obj))
        print(f"STAGED_COVER_GENERATED|{args.h}|{obj['template_hash']}")
    else:
        paths = sorted(args.directory.glob("*.cover.json"))
        if not paths:
            raise TemplateError("no staged cover artifacts found")
        for path in paths:
            obj = loads(path.read_text())
            h = obj["payload"]["structural"]["h"]
            if path.name != f"compact-cover-h{h}.cover.json":
                raise TemplateError("noncanonical cover filename")
            if path.with_suffix(".tex").read_text() != render_tex(obj):
                raise TemplateError("generated cover TeX drift")
            if args.lean_runner and from_lean(args.lean_runner, h) != obj:
                raise TemplateError("cover artifact differs from the actual Lean template")
            mode = "Lean-replayed" if args.lean_runner else "artifact-only; NOT Lean-synchronized"
            print(f"STAGED_COVER_CHECK|{mode}|{path.name}|{obj['template_hash']}")


if __name__ == "__main__":
    try:
        main()
    except (TemplateError, OSError, ValueError, RecursionError) as exc:
        raise SystemExit(f"cover artifact error: {exc}") from exc
