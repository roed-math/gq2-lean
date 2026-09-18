#!/usr/bin/env python3
"""STAGED item-8 normal-form Gauss display (ledger item 8, normal-form half).

Lean owns the data: `scripts/w366_ln_gauss_export.lean` serializes it and carries the
signature theorems. This module validates that serialization and renders it.

W363-PUB2 left item 8 split: its coordinate half binds at `record_target` against the change
of variables' own `Equiv` fields, and its normal-form half was `named_but_unbound` because
the Gauss sign and exponent the normal-form records establish on the way were not named
standalone theorems anywhere. `GQ2/Dyadic/Instances/GaussPhaseValues.lean` names them, and
this exporter wires the five item-8 sector rows to them.

Two bridge kinds live in one artifact and the validator refuses to let either be relabelled:

* the printed sign and the printed exponent are `record_target`, each `rfl` against a field
  of `GaussValCell`, which is data with explicit fields;
* the value equation is `restated_identity`, because its carrier is a theorem and not a
  record: the driver restates it through the named cell and discharges it by the tree's own
  theorem, so a wrong cell does not compile.

The normal-form RECORDS stay `named_but_unbound`. Nothing here reaches them, and the
validator enforces that the label stays. Naming is not binding.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from w361_general_word_tex import TemplateError, canonical_json, fields, integer, reject_duplicates
from w363_ln_stokes_tex import tex_escape

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "gq2.w366.ln-gauss.v1.staged"
DOMAIN = b"GQ2-W366-LN-GAUSS\0"
PREFIX = "W366_LN_GAUSS_JSON="
LEAN_FILE = "scripts/w366_ln_gauss_export.lean"
BRIDGE = "GQ2.Dyadic.W366LNGauss."
RECORD_TARGET = "record_target"
RESTATED = "restated_identity"
UNBOUND = "named_but_unbound"

GPV = "GQ2.Dyadic.Instances.GaussPhaseValues."
LSQ = "GQ2.Dyadic.LSquare."
WPH = "GQ2.Dyadic.Instances.WordPhase."
WWH = "GQ2.Dyadic.Instances.WordPhaseWallHandleCertificates."
LHC = "GQ2.Dyadic.Instances.LHessianCertificates."
CNH = "GQ2.Dyadic.Instances.CompactNHessianCertificates."
NHC = "GQ2.Dyadic.Instances.NpcHessianCertificates."

CELL_STRUCTURE = {"bridge_kind": RECORD_TARGET, "record": GPV + "GaussValCell",
                  "value_bridge": BRIDGE + "cellValue",
                  "value_def": GPV + "GaussValCell.value"}

PROVENANCE_FILES = (
    LEAN_FILE,
    "GQ2/Dyadic/Instances/GaussPhaseValues.lean",
    "GQ2/Dyadic/Instances/GammaLUnramifiedPhase.lean",
    "GQ2/Dyadic/Instances/WordPhase.lean",
    "GQ2/Dyadic/Instances/WordPhaseWallHandleCertificates.lean",
    "GQ2/Dyadic/Instances/LHessianCertificates.lean",
    "GQ2/Dyadic/Instances/CompactNHessianCertificates.lean",
    "GQ2/Dyadic/Instances/NpcHessianCertificates.lean",
    "scripts/w366_ln_gauss_tex.py",
)

# Per row: the odd-degree L rows print 2h+1, the three even-degree rows print 2h+2. The
# validator recomputes the degree from the handle rank, so a wrong printed exponent is
# refused rather than trusted.
ODD, EVEN = "odd", "even"


def _row(row, sector, cell, endpoint, record, sign_stem, degree_stem, value_stem,
         display, value, second_sign, sign, parity):
    return {"row": row, "sector": sector, "cell": GPV + cell, "endpoint": endpoint,
            "normal_form_record": record, "sign_bridge": BRIDGE + sign_stem,
            "degree_bridge": BRIDGE + degree_stem, "value_bridge": BRIDGE + value_stem,
            "display_theorem": GPV + display, "value_theorem": GPV + value,
            "second_sign_route": second_sign, "sign": sign, "parity": parity}


FAMILIES = {
    "L": {"parameters": ("h", "q"),
          "rows": [
              _row("graph_normal_form_unramified", "graph_normal_form", "gaussValLUnramCell",
                   LSQ + "lSqWallHandlePhase", LHC + "unramifiedHessian",
                   "lUnramSign", "lUnramDegree", "lUnramValue",
                   "gaussValLUnramifiedDisplay", "gaussValLUnramifiedCell",
                   LHC + "unramifiedHessian_baseSign", -1, ODD),
              _row("graph_normal_form_ramified", "graph_normal_form", "gaussValLRamCell",
                   LSQ + "lSqWallHandlePhase", LHC + "ramifiedHessian",
                   "lRamSign", "lRamDegree", "lRamValue",
                   "gaussValLRamifiedDisplay", "gaussValLRamifiedCell",
                   LHC + "ramifiedHessian_baseSign", 1, ODD)]},
    "N0": {"parameters": ("h", "q"),
           "rows": [
               _row("compact_normal_form", "compact_normal_form", "gaussValCompactCell",
                    WPH + "wPhCompactWallHandlePhase", CNH + "compactNUnramifiedHessian",
                    "compactSign", "compactDegree", "compactValue",
                    "gaussValCompactDisplay", "gaussValCompactCellEq", None, 1, EVEN)]},
    "Npc": {"parameters": ("h", "q", "r"),
            "rows": [
                _row("unramified_full_offset", "unramified_full_offset",
                     "gaussValCompactCell", WWH + "wallHandlePhase",
                     NHC + "npcUnramifiedHeadHessian", "compactSign", "compactDegree",
                     "npcValue", "gaussValNpcDisplay", "gaussValNpcCellEq", None, 1, EVEN),
                _row("ramified_full_offset", "ramified_full_offset", "gaussValCompactCell",
                     WWH + "wallHandlePhase", NHC + "nonempty_npcRamifiedHeadHessian",
                     "compactSign", "compactDegree", "npcValue", "gaussValNpcDisplay",
                     "gaussValNpcCellEq", None, 1, EVEN)]},
}

ROW_KEYS = {"cell", "degree", "degree_bridge", "degree_record_route", "display_theorem",
            "endpoint", "normal_form_record", "record_binding", "row", "second_sign_route",
            "sector", "sign", "sign_bridge", "value_bridge", "value_theorem"}

CERTIFICATE_CONDITIONS = {
    "L": "L is the only family whose two branches print DIFFERENT signs, because its degree "
         "2h+1 is odd: the unramified row prints -1 and the ramified row prints +1. It is "
         "also the only family with a second, independent record_target route for the sign, "
         "through the pre-existing baseSign theorems, so a validator may check that the two "
         "routes agree.",
    "N0": "N0's degree 2h+2 is even, so both compact branches print the same integer and one "
          "cell serves them. The compact-M rows, which item 8 does not list but which share "
          "the compact endpoint, are served by the same cell.",
    "Npc": "Both Npc rows share one endpoint, wallHandlePhase, and one cell: the sign does "
           "not depend on the projected diagonal d0. The ramified row's normal-form record "
           "is a Nonempty and not a record value, so that row cannot gain a second sign "
           "route even if a baseSign theorem were added to the module.",
}


def digest(payload):
    return hashlib.sha256(DOMAIN + canonical_json(payload).encode()).hexdigest()


def expected_degree(parity, h):
    return 2 * h + (1 if parity == ODD else 2)


def validate_parameters(family, parameters):
    if not isinstance(family, str) or family not in FAMILIES:
        raise TemplateError("family must be L, N0 or Npc")
    fields(parameters, set(FAMILIES[family]["parameters"]), "LN gauss structural parameters")
    for name, value in parameters.items():
        integer(value, name, natural=True)


def validate(envelope):
    fields(envelope, {"payload", "status", "template_hash"}, "LN gauss envelope")
    if envelope["status"] != "STAGED":
        raise TemplateError("LN gauss artifacts must remain STAGED")
    p = envelope["payload"]
    fields(p, {"application_scope", "cell_note", "cell_structure", "family", "hash_scope",
               "rows", "schema", "sign_binding", "structural", "todos", "value_binding",
               "warning"}, "LN gauss payload")
    if p["schema"] != SCHEMA:
        raise TemplateError("LN gauss schema mismatch")
    validate_parameters(p["family"], p["structural"])
    meta = FAMILIES[p["family"]]
    h = p["structural"]["h"]
    for key in ("application_scope", "cell_note", "hash_scope", "warning"):
        if not isinstance(p[key], str) or not p[key]:
            raise TemplateError("LN gauss " + key + " must be a nonempty string")
    # The two halves of a cell do NOT carry the same kind, and neither may be relabelled.
    if p["sign_binding"] != RECORD_TARGET:
        raise TemplateError("the printed sign and exponent are rfl record targets")
    if p["value_binding"] != RESTATED:
        raise TemplateError("the value equation's carrier is a theorem, not a record, and "
                            "may not be presented as a record target")
    if canonical_json(p["cell_structure"]) != canonical_json(CELL_STRUCTURE):
        raise TemplateError("LN gauss cell structure is not the tree's own")
    todos = p["todos"]
    if not isinstance(todos, list) or len(todos) != 2:
        raise TemplateError("LN gauss artifacts carry both standing TODOs")
    for todo in todos:
        if not isinstance(todo, str) or not todo.startswith("TODO: "):
            raise TemplateError("LN gauss TODO must be a marked nonempty string")
    rows = p["rows"]
    if not isinstance(rows, list) or len(rows) != len(meta["rows"]):
        raise TemplateError("LN gauss row count does not match the family")
    for row, expected in zip(rows, meta["rows"]):
        fields(row, ROW_KEYS, "LN gauss row")
        for key in ("row", "sector", "cell", "endpoint", "normal_form_record", "sign_bridge",
                    "degree_bridge", "value_bridge", "display_theorem", "value_theorem"):
            if row[key] != expected[key]:
                raise TemplateError("LN gauss row is not bound to the expected declarations")
        # naming is not binding, and the artifact may not say otherwise
        if row["record_binding"] != UNBOUND:
            raise TemplateError("the normal-form records carry no binding here and may not "
                                "be presented as if they did")
        # no named baseDim theorem exists anywhere in the tree
        if row["degree_record_route"] is not None:
            raise TemplateError("no record route exists for the printed exponent")
        if row["second_sign_route"] != expected["second_sign_route"]:
            raise TemplateError("LN gauss second sign route is not the row's own")
        if integer(row["sign"], "printed sign") != expected["sign"]:
            raise TemplateError("LN gauss printed sign is not the row's own")
        if (integer(row["degree"], "printed exponent degree", natural=True)
                != expected_degree(expected["parity"], h)):
            raise TemplateError("LN gauss printed exponent is not the row's own degree")
    if envelope["template_hash"] != digest(p):
        raise TemplateError("LN gauss envelope hash mismatch")
    return p


def loads(text):
    obj = json.loads(text, object_pairs_hook=reject_duplicates,
                     parse_constant=lambda x: (_ for _ in ()).throw(TemplateError(x)))
    validate(obj)
    return obj


def from_lean(runner, family, parameters):
    validate_parameters(family, parameters)
    args = [family] + [str(parameters[name]) for name in FAMILIES[family]["parameters"]]
    result = subprocess.run(["bash", str(Path(runner).resolve()), "--run", LEAN_FILE] + args,
                            cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise TemplateError("Lean LN gauss exporter failed:\n" + result.stdout + result.stderr)
    records = [line[len(PREFIX):] for line in result.stdout.splitlines()
               if line.startswith(PREFIX)]
    if len(records) != 1:
        raise TemplateError("Lean LN gauss exporter must emit one marked artifact")
    obj = loads(records[0])
    if canonical_json(obj) != records[0]:
        raise TemplateError("Lean/Python LN gauss canonical JSON mismatch")
    if obj["payload"]["family"] != family or obj["payload"]["structural"] != parameters:
        raise TemplateError("Lean LN gauss exporter returned different parameters")
    return obj


def provenance(envelope):
    return {"schema": SCHEMA + ".provenance", "status": "STAGED",
            "template_hash": envelope["template_hash"],
            "scope": "Direct source bytes only; not a transitive build, coefficient module, "
                     "or certificate attestation.",
            "sha256": {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                       for name in PROVENANCE_FILES}}


# ---------------------------------------------------------------- rendering


def sign_tex(sign):
    return "-1" if sign < 0 else "+1"


def row_tex(row):
    endpoint = row["endpoint"].rsplit(".", 1)[-1]
    return (r"\mathrm{gaussSum}\bigl(\mathrm{" + endpoint + r"}\bigr)="
            + sign_tex(row["sign"]) + r"\cdot 2^{m\cdot " + str(row["degree"]) + "}")


def render_tex(envelope):
    p = validate(envelope)
    family = p["family"]
    lines = [
        "% STAGED item-8 normal-form Gauss display; ledger item 8, normal-form half only.",
        "% ln-gauss-hash: " + envelope["template_hash"],
        "% family: " + family + "; structural: " + canonical_json(p["structural"]),
        "% " + p["application_scope"],
        "% " + p["warning"],
        "% " + p["cell_note"],
        "% " + p["hash_scope"],
        "% " + CERTIFICATE_CONDITIONS[family],
        "% cell record (" + p["cell_structure"]["bridge_kind"] + "): "
        + p["cell_structure"]["record"] + "; value " + p["cell_structure"]["value_def"]
        + " bound by " + p["cell_structure"]["value_bridge"],
        r"\[\mathrm{value}(c,m)=c.\mathrm{sign}\cdot 2^{m\cdot c.\mathrm{degree}}.\]",
    ]
    for row in p["rows"]:
        lines += [r"\paragraph{" + tex_escape(row["row"].replace("_", " ")) + "}",
                  "% cell: " + row["cell"],
                  "% endpoint: " + row["endpoint"],
                  "% sign (" + p["sign_binding"] + "): " + row["sign_bridge"],
                  "% exponent (" + p["sign_binding"] + "): " + row["degree_bridge"],
                  "% value (" + p["value_binding"] + "): " + row["value_bridge"]
                  + " discharged by " + row["value_theorem"],
                  "% display: " + row["display_theorem"],
                  r"\[" + row_tex(row) + r".\]",
                  "Printed sign " + sign_tex(row["sign"]) + ", printed exponent degree "
                  + str(row["degree"]) + ". Normal-form record named but NOT bound here ("
                  + tex_escape(row["record_binding"].replace("_", " ")) + r"): \texttt{"
                  + tex_escape(row["normal_form_record"]) + "}.",
                  (r"Second \texttt{" + tex_escape(RECORD_TARGET) + r"} route for the sign: "
                   r"\texttt{" + tex_escape(row["second_sign_route"]) + "}."
                   if row["second_sign_route"] else
                   "No second route for the sign in this row.")
                  + " No record route for the exponent in any row."]
    for todo in p["todos"]:
        lines.append(r"\par\noindent\textbf{[" + tex_escape(todo) + "]}")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------- self-test


def self_test():
    def build(family, structural):
        meta = FAMILIES[family]
        rows = [{"cell": r["cell"],
                 "degree": expected_degree(r["parity"], structural["h"]),
                 "degree_bridge": r["degree_bridge"], "degree_record_route": None,
                 "display_theorem": r["display_theorem"], "endpoint": r["endpoint"],
                 "normal_form_record": r["normal_form_record"], "record_binding": UNBOUND,
                 "row": r["row"], "second_sign_route": r["second_sign_route"],
                 "sector": r["sector"], "sign": r["sign"], "sign_bridge": r["sign_bridge"],
                 "value_bridge": r["value_bridge"], "value_theorem": r["value_theorem"]}
                for r in meta["rows"]]
        return {"application_scope": "scope", "cell_note": "cell note",
                "cell_structure": dict(CELL_STRUCTURE), "family": family,
                "hash_scope": "hash scope", "rows": rows, "schema": SCHEMA,
                "sign_binding": RECORD_TARGET, "structural": structural,
                "todos": ["TODO: one", "TODO: two"], "value_binding": RESTATED,
                "warning": "warning"}

    def wrap(p):
        return {"payload": p, "status": "STAGED", "template_hash": digest(p)}

    base = build("L", {"h": 4, "q": 2})
    obj = wrap(base)
    assert loads(canonical_json(obj)) == obj
    assert "ln-gauss-hash" in render_tex(obj)
    assert r"\mathrm{lSqWallHandlePhase}\bigr)=-1\cdot 2^{m\cdot 9}" in render_tex(obj)
    assert r"+1\cdot 2^{m\cdot 9}" in render_tex(obj)
    assert "named but NOT bound here" in render_tex(obj)
    assert "unramifiedHessian" in render_tex(obj)
    nobj = wrap(build("Npc", {"h": 3, "q": 2, "r": 2}))
    assert loads(canonical_json(nobj)) == nobj
    assert r"\mathrm{wallHandlePhase}\bigr)=+1\cdot 2^{m\cdot 8}" in render_tex(nobj)
    assert "No second route for the sign in this row." in render_tex(nobj)
    count = 8

    def mutated(mutate):
        p = json.loads(canonical_json(base))
        mutate(p)
        return wrap(p)

    mutations = [
        lambda p: p.update(schema="bad"),
        lambda p: p.update(family="M0"),
        lambda p: p.update(family=[]),
        lambda p: p.update(extra=1),
        lambda p: p.update(application_scope=""),
        lambda p: p.update(cell_note=3),
        lambda p: p.pop("warning"),
        # the two halves of a cell do not carry the same kind
        lambda p: p.update(sign_binding=RESTATED),
        lambda p: p.update(sign_binding=UNBOUND),
        lambda p: p.update(value_binding=RECORD_TARGET),
        lambda p: p.update(value_binding="field_statement_identity"),
        lambda p: p["cell_structure"].update(record=GPV + "Other"),
        lambda p: p["cell_structure"].update(bridge_kind=RESTATED),
        lambda p: p["cell_structure"].pop("value_def"),
        lambda p: p.update(todos=["TODO: one"]),
        lambda p: p.update(todos=["one", "two"]),
        lambda p: p.update(todos="TODO: one"),
        lambda p: p["structural"].update(h=-1),
        lambda p: p["structural"].pop("q"),
        lambda p: p["rows"].pop(),
        lambda p: p["rows"].reverse(),
        lambda p: p["rows"][0].update(cell=GPV + "gaussValLRamCell"),
        lambda p: p["rows"][0].update(endpoint=WPH + "wPhCompactWallHandlePhase"),
        lambda p: p["rows"][0].update(sign_bridge=BRIDGE + "other"),
        lambda p: p["rows"][0].update(degree_bridge=BRIDGE + "other"),
        lambda p: p["rows"][0].update(value_bridge=BRIDGE + "other"),
        lambda p: p["rows"][0].update(value_theorem=GPV + "other"),
        lambda p: p["rows"][0].update(display_theorem=GPV + "other"),
        lambda p: p["rows"][0].update(normal_form_record=LHC + "ramifiedHessian"),
        # naming is not binding
        lambda p: p["rows"][0].update(record_binding=RECORD_TARGET),
        lambda p: p["rows"][0].update(record_binding=RESTATED),
        # the exponent has no record route anywhere, and one may not be invented
        lambda p: p["rows"][0].update(degree_record_route=LHC + "unramifiedHessian_baseDim"),
        # nor may a second sign route be invented where none exists
        lambda p: p["rows"][0].update(second_sign_route=None),
        lambda p: p["rows"][1].update(second_sign_route=LHC + "unramifiedHessian_baseSign"),
        # the printed numbers are recomputed, never trusted
        lambda p: p["rows"][0].update(sign=1),
        lambda p: p["rows"][0].update(sign=-2),
        lambda p: p["rows"][0].update(sign=True),
        lambda p: p["rows"][0].update(degree=10),
        lambda p: p["rows"][0].update(degree=-9),
        lambda p: p["rows"][0].pop("sector"),
    ]
    for mutate in mutations:
        try:
            validate(mutated(mutate))
        except TemplateError:
            count += 1
        else:
            raise AssertionError("malformed LN gauss artifact accepted")
    npc = build("Npc", {"h": 0, "q": 2, "r": 1})
    for mutate in (lambda p: p["rows"][0].update(second_sign_route=NHC + "invented"),
                   lambda p: p["rows"][1].update(
                       normal_form_record=NHC + "npcUnramifiedHeadHessian")):
        p = json.loads(canonical_json(npc))
        mutate(p)
        try:
            validate(wrap(p))
        except TemplateError:
            count += 1
        else:
            raise AssertionError("malformed LN gauss Npc artifact accepted")
    for bad in ("[]", "null", "NaN", "Infinity", '{"payload":0,"payload":0}',
                canonical_json(obj).replace('"h":4', '"h":4,"h":4'),
                canonical_json(obj).replace('"STAGED"', '"APPROVED"'),
                canonical_json(obj).replace(obj["template_hash"], "0" * 64),
                canonical_json(obj).replace('"second_sign_route"', '"secondSignRoute"', 1)):
        try:
            loads(bad)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("malformed LN gauss JSON accepted")
    for family, parameters in (("L", {"h": 0}), ("Npc", {"h": 0, "q": 2}),
                               ("M0", {"h": 0, "q": 2}), ("L", {"h": -1, "q": 2})):
        try:
            validate_parameters(family, parameters)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid LN gauss parameters accepted")
    print(f"LN_GAUSS_SELF_TEST_PASS|{count}")
    return count


def artifact_name(payload):
    family, s = payload["family"], payload["structural"]
    return family + "-gauss-" + "-".join(
        name + str(s[name]) for name in FAMILIES[family]["parameters"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("self-test")
    generate = sub.add_parser("generate")
    generate.add_argument("family", choices=FAMILIES)
    generate.add_argument("parameters", nargs="+", type=int)
    generate.add_argument("--lean-runner", type=Path, required=True)
    generate.add_argument("--out", type=Path,
                          default=Path("generated") / "general-ln-certificate-staged")
    check = sub.add_parser("check")
    check.add_argument("directory", type=Path)
    check.add_argument("--lean-runner", type=Path)
    args = parser.parse_args()
    if args.command == "self-test":
        self_test()
        return
    if args.command == "generate":
        names = FAMILIES[args.family]["parameters"]
        if len(args.parameters) != len(names):
            raise TemplateError("expected parameters: " + " ".join(names))
        parameters = dict(zip(names, args.parameters))
        if "general-ln-certificate-staged" not in args.out.resolve().parts:
            raise TemplateError(
                "LN gauss output must be inside general-ln-certificate-staged")
        obj = from_lean(args.lean_runner, args.family, parameters)
        args.out.mkdir(parents=True, exist_ok=True)
        base = args.out / artifact_name(obj["payload"])
        base.with_suffix(".gauss.json").write_text(canonical_json(obj) + "\n")
        base.with_suffix(".gauss.tex").write_text(render_tex(obj))
        base.with_suffix(".gauss.provenance.json").write_text(
            canonical_json(provenance(obj)) + "\n")
        print(f"STAGED_LN_GAUSS_GENERATED|{base.name}|{obj['template_hash']}")
        return
    paths = sorted(args.directory.glob("*.gauss.json"))
    if not paths:
        raise TemplateError("no staged LN gauss artifacts found")
    for path in paths:
        obj = loads(path.read_text())
        p = obj["payload"]
        name = artifact_name(p)
        if path.name != name + ".gauss.json":
            raise TemplateError("noncanonical LN gauss filename")
        base = path.parent / name
        if base.with_suffix(".gauss.tex").read_text() != render_tex(obj):
            raise TemplateError("generated LN gauss TeX drift")
        recorded = json.loads(base.with_suffix(".gauss.provenance.json").read_text(),
                              object_pairs_hook=reject_duplicates)
        if recorded != provenance(obj):
            raise TemplateError("LN gauss direct-source provenance drift")
        replayed = "syntax-only"
        if args.lean_runner:
            if from_lean(args.lean_runner, p["family"], p["structural"]) != obj:
                raise TemplateError("Lean LN gauss replay disagrees with the staged artifact")
            replayed = "Lean-replayed"
        print(f"STAGED_LN_GAUSS_CHECK|{replayed}|{name}|{obj['template_hash']}")


if __name__ == "__main__":
    main()
