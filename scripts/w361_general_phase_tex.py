#!/usr/bin/env python3
"""STAGED exact quadratic-phase/matrix rendering from the proved Lean tree.

The hash binds the symbolic q-template, not a concrete coefficient space or a
source word. Strong checks replay Lean; artifact-only checks are labelled as such.
No frozen generated appendix or hash manifest is read or changed.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess

from w361_general_word_tex import (TemplateError, canonical_json, fields, integer,
                                   reject_duplicates)

SCHEMA = "gq2.w361.quadratic-phase.v1.staged"
DOMAIN = b"GQ2-W361-QUADRATIC-PHASE\0"
LEAN_FILE = "GQ2/Dyadic/Word/GeneralPhaseTemplateExport.lean"
PREFIX = "W361_PHASE_TEMPLATE_JSON="


def digest(payload):
    return hashlib.sha256(DOMAIN + canonical_json(payload).encode()).hexdigest()


def coordinates(h):
    return [{"coordinate": "head0"}, {"coordinate": "head1"}] + [
        {"coordinate": kind, "index": j}
        for j in range(h) for kind in ("handleU", "handleV")]


def validate_coordinate(value, h):
    if not isinstance(value, dict):
        raise TemplateError("phase coordinate must be an object")
    kind = value.get("coordinate")
    if kind in ("head0", "head1"):
        fields(value, {"coordinate"}, "head coordinate")
    elif kind in ("handleU", "handleV"):
        fields(value, {"coordinate", "index"}, "handle coordinate")
        if not integer(value["index"], "handle index", natural=True) < h:
            raise TemplateError("phase handle is outside the actual rank")
    else:
        raise TemplateError("unknown phase coordinate")


def validate_tree(tree, h):
    if not isinstance(tree, dict):
        raise TemplateError("phase node must be an object")
    op = tree.get("op")
    if op == "zero":
        fields(tree, {"op"}, "zero phase")
    elif op == "baseQuad":
        fields(tree, {"op", "at"}, "base quadratic value")
        validate_coordinate(tree["at"], h)
    elif op == "polar":
        fields(tree, {"op", "left", "right"}, "polar value")
        validate_coordinate(tree["left"], h)
        validate_coordinate(tree["right"], h)
    elif op == "add":
        fields(tree, {"op", "left", "right"}, "phase sum")
        validate_tree(tree["left"], h)
        validate_tree(tree["right"], h)
    else:
        raise TemplateError("unknown phase operation")


def validate_matrix(matrix, n):
    if not isinstance(matrix, list) or len(matrix) != n:
        raise TemplateError("phase matrix has the wrong number of rows")
    for row in matrix:
        if not isinstance(row, list) or len(row) != n:
            raise TemplateError("phase matrix has the wrong number of columns")
        if any(type(value) is not int or value not in (0, 1) for value in row):
            raise TemplateError("phase matrix entries must be literal F2 bits")


def validate(envelope):
    fields(envelope, {"payload", "status", "template_hash"}, "phase envelope")
    if envelope["status"] != "STAGED":
        raise TemplateError("phase artifacts must remain STAGED")
    p = envelope["payload"]
    fields(p, {"bridge", "coordinates", "factory", "inverse_matrix", "kind", "matrix",
               "pairing", "schema", "structural", "tree"}, "phase payload")
    if (p["schema"] != SCHEMA or p["kind"] != "compact-wall-handle"
            or p["pairing"] != "polar(q)"
            or p["factory"] != "GQ2.Dyadic.GeneralPhaseTemplate.compactPhase"
            or p["bridge"] != "GQ2.Dyadic.GeneralPhaseTemplate.denote_compactPhase"):
        raise TemplateError("phase semantic identity mismatch")
    fields(p["structural"], {"h"}, "phase structural parameters")
    h = integer(p["structural"]["h"], "phase handle rank", natural=True)
    n = 2 + 2*h
    # Check the supplied length before constructing the expected coordinates:
    # an enormous declared rank must not allocate an enormous temporary list.
    if not isinstance(p["coordinates"], list) or len(p["coordinates"]) != n:
        raise TemplateError("phase coordinate count mismatch")
    # Python equality identifies False/0 and 0.0/0.  Validate the literal types
    # before comparing the ordered coordinate table to its canonical form.
    for coordinate in p["coordinates"]:
        validate_coordinate(coordinate, h)
    if p["coordinates"] != coordinates(h):
        raise TemplateError("phase coordinate order mismatch")
    validate_tree(p["tree"], h)
    validate_matrix(p["matrix"], n)
    validate_matrix(p["inverse_matrix"], n)
    for left, right in ((p["matrix"], p["inverse_matrix"]),
                        (p["inverse_matrix"], p["matrix"])):
        for i in range(n):
            for j in range(n):
                if sum(left[i][k]*right[k][j] for k in range(n)) % 2 != int(i == j):
                    raise TemplateError("exported matrix inverse does not replay over F2")
    if envelope["template_hash"] != digest(p):
        raise TemplateError("phase template hash mismatch")
    return p


def loads(text):
    value = json.loads(text, object_pairs_hook=reject_duplicates,
                       parse_constant=lambda x: (_ for _ in ()).throw(TemplateError(x)))
    validate(value)
    return value


def from_lean(runner, h):
    result = subprocess.run(["bash", str(Path(runner).resolve()), "--run", LEAN_FILE, str(h)],
                            text=True, capture_output=True)
    if result.returncode:
        raise TemplateError("Lean phase exporter failed:\n" + result.stdout + result.stderr)
    records = [line[len(PREFIX):] for line in result.stdout.splitlines() if line.startswith(PREFIX)]
    if len(records) != 1:
        raise TemplateError("Lean phase exporter must emit exactly one marked artifact")
    obj = loads(records[0])
    if canonical_json(obj) != records[0]:
        raise TemplateError("Lean/Python phase canonical JSON mismatch")
    if obj["payload"]["structural"]["h"] != h:
        raise TemplateError("Lean phase exporter returned a different rank")
    return obj


def coordinate_tex(c):
    kind = c["coordinate"]
    if kind == "head0":
        return "c_0"
    if kind == "head1":
        return "c_1"
    return ("u" if kind == "handleU" else "v") + "_{" + str(c["index"]) + "}"


def tree_tex(tree):
    op = tree["op"]
    if op == "zero":
        return "0"
    if op == "baseQuad":
        return "q_0(" + coordinate_tex(tree["at"]) + ")"
    if op == "polar":
        return "B(" + coordinate_tex(tree["left"]) + "," + coordinate_tex(tree["right"]) + ")"
    return r"\bigl(" + tree_tex(tree["left"]) + "+" + tree_tex(tree["right"]) + r"\bigr)"


def matrix_tex(matrix):
    return r"\begin{pmatrix}" + r"\\".join("&".join(map(str, row)) for row in matrix) + r"\end{pmatrix}"


def render_tex(envelope):
    p = validate(envelope)
    return "\n".join([
        "% STAGED symbolic phase; not a source-word or coefficient-space hash.",
        "% phase-template-hash: " + envelope["template_hash"],
        "% exact bridge: " + p["bridge"],
        "% q_0 is the coefficient quadratic form, not the residue size q in a Fox template.",
        "% Matrices are coefficients relative to B=polar(q_0), not a Gram matrix for q_0 itself.",
        r"\[Q=" + tree_tex(p["tree"]) + r".\]",
        r"\[J=" + matrix_tex(p["matrix"]) + r",\qquad J^{-1}=" + matrix_tex(p["inverse_matrix"]) + r".\]",
        "% coordinate order: " + canonical_json(p["coordinates"]), ""])


def self_test():
    c0, c1 = coordinates(0)
    payload = {"bridge": "GQ2.Dyadic.GeneralPhaseTemplate.denote_compactPhase",
               "coordinates": coordinates(0), "factory": "GQ2.Dyadic.GeneralPhaseTemplate.compactPhase",
               "inverse_matrix": [[0, 1], [1, 1]], "kind": "compact-wall-handle",
               "matrix": [[1, 1], [1, 0]], "pairing": "polar(q)", "schema": SCHEMA,
               "structural": {"h": 0},
               "tree": {"op": "add", "left": {
                   "op": "add", "left": {"op": "baseQuad", "at": c0},
                   "right": {"op": "polar", "left": c0, "right": c1}},
                   "right": {"op": "zero"}}}
    def wrap(p):
        return {"payload": p, "status": "STAGED", "template_hash": digest(p)}
    obj = wrap(payload)
    assert loads(canonical_json(obj)) == obj
    assert "q_0(c_0)" in render_tex(obj)
    assert "B(c_0,c_1)" in render_tex(obj)
    count = 3
    mutations = [
        lambda p: p.update(schema="wrong"), lambda p: p.update(kind="different"),
        lambda p: p.update(pairing="identity"), lambda p: p.update(factory="other"),
        lambda p: p.update(bridge="other"), lambda p: p.update(extra=True),
        lambda p: p["structural"].update(h=True), lambda p: p["structural"].update(h=-1),
        lambda p: p["structural"].update(h=0.0),
        lambda p: p["structural"].update(h=10**100),
        lambda p: p["structural"].update(h=1), lambda p: p["coordinates"].reverse(),
        lambda p: p.update(coordinates={}),
        lambda p: p["coordinates"][0].update(extra=0),
        lambda p: p.update(matrix=[[1, 0], [0, 1]]),
        lambda p: p.update(matrix=[[True, 1], [1, 0]]),
        lambda p: p.update(matrix=[[1.0, 1], [1, 0]]),
        lambda p: p.update(matrix=[[2, 1], [1, 0]]),
        lambda p: p.update(matrix=[[1, 1]]),
        lambda p: p.update(inverse_matrix=[[0, 1, 0], [1, 1]]),
        lambda p: p.update(tree={"op": "unknown"}),
        lambda p: p.update(tree={"op": "zero", "extra": 0}),
        lambda p: p.update(tree={"op": "baseQuad", "at": {"coordinate": "handleU", "index": 0}}),
        lambda p: p.update(tree={"op": "baseQuad", "at": {"coordinate": "head2"}}),
        lambda p: p.update(tree={"op": "baseQuad", "at": {"coordinate": "head0", "index": 0}}),
        lambda p: p.update(tree={"op": "add", "left": {"op": "zero"}, "right": 0}),
    ]
    for mutate in mutations:
        p = deepcopy(payload)
        mutate(p)
        try:
            validate(wrap(p))
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid phase artifact accepted")
    # A valid one-handle envelope exercises coordinate types that do not occur
    # at rank zero.  This is a schema test; only from_lean binds a factory output.
    one = deepcopy(payload)
    one.update(coordinates=coordinates(1), structural={"h": 1},
               matrix=[[1, 1, 0, 0], [1, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]],
               inverse_matrix=[[0, 1, 0, 0], [1, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]])
    validate(wrap(one))
    count += 1
    for bad_index in (False, 0.0, "0", -1, 1):
        p = deepcopy(one)
        p["coordinates"][2]["index"] = bad_index
        try:
            validate(wrap(p))
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid coordinate-table index accepted")
    for text in ['{"payload":0,"payload":1}', canonical_json(obj).replace('"STAGED"', '"APPROVED"'),
                 canonical_json(obj).replace(obj["template_hash"], "0"*64),
                 canonical_json(obj).replace('"h":0', '"h":0,"h":0'),
                 canonical_json(obj).replace('"op":"zero"', '"op":"zero","op":"zero"'),
                 "[]", "NaN", "Infinity", "-Infinity"]:
        try:
            loads(text)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid phase envelope accepted")
    print(f"PHASE_TOOL_SELF_TEST_PASS|{count}")
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
        if args.h < 0:
            raise TemplateError("handle rank must be nonnegative")
        if "general-certificate-staged" not in args.out.resolve().parts:
            raise TemplateError("phase output must be inside general-certificate-staged")
        obj = from_lean(args.lean_runner, args.h)
        args.out.mkdir(parents=True, exist_ok=True)
        base = args.out / f"compact-phase-h{args.h}"
        base.with_suffix(".phase.json").write_text(canonical_json(obj)+"\n")
        base.with_suffix(".phase.tex").write_text(render_tex(obj))
        print(f"STAGED_PHASE_GENERATED|{args.h}|{obj['template_hash']}")
    else:
        paths = sorted(args.directory.glob("*.phase.json"))
        if not paths:
            raise TemplateError("no staged phase artifacts found")
        for path in paths:
            obj = loads(path.read_text())
            h = obj["payload"]["structural"]["h"]
            if path.name != f"compact-phase-h{h}.phase.json":
                raise TemplateError("noncanonical phase filename")
            if path.with_suffix(".tex").read_text() != render_tex(obj):
                raise TemplateError("generated phase TeX drift")
            if args.lean_runner and from_lean(args.lean_runner, h) != obj:
                raise TemplateError("phase artifact differs from the actual Lean tree")
            mode = "Lean-replayed" if args.lean_runner else "artifact-only; NOT Lean-synchronized"
            print(f"STAGED_PHASE_CHECK|{mode}|{path.name}|{obj['template_hash']}")


if __name__ == "__main__":
    try:
        main()
    except (TemplateError, OSError, ValueError, RecursionError) as exc:
        raise SystemExit(f"phase artifact error: {exc}") from exc
