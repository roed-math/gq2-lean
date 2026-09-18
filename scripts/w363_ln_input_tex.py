#!/usr/bin/env python3
"""STAGED L/N0/Npc evaluated Fox Jacobian, before any operation (ledger item 3).

Lean owns the data: `scripts/w363_ln_input_export.lean` serializes the actual evaluated
rows and carries the signature theorems binding them to the records. This module
validates that serialization and renders it. It builds no row of its own, reads no
frozen manifest or generated appendix, and is not an approved appendix section, gate,
or migration.

Two kinds of bridge occur and the artifact distinguishes them, because they are not the
same strength of claim:

* `record_target` -- the row is definitionally the `target` field of an existing
  `FoxRowCertificate` whose `colOps` is empty, i.e. of a record that certifies the
  evaluated Fox derivative of the actual word with nothing applied to it. Nine of the
  fourteen rows are of this kind.
* `denotation_theorem` -- the tree carries no such record for that row, and the
  exporter driver states the denotation itself from the existing `foxD_tameRelW_*` and
  `*_toHom_apply` lemmas. Five of the fourteen rows are of this kind: the L tame row at
  all three sectors, and the N0 and Npc tame rows at the ramified sector.

The pair/mobile renderers in `w361_general_fox_tex.py` are NOT reused, for the reason
recorded in `w362_ln_fox_tex.py`: their payload is splice-specific.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from w361_general_word_tex import TemplateError, canonical_json, fields, integer, reject_duplicates
from w362_ln_fox_tex import (coeff_tex, expected_columns, row_tex, validate_col_op,
                             validate_row)

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "gq2.w363.ln-input-rows.v1.staged"
DOMAIN = b"GQ2-W363-LN-INPUT-ROWS\0"
PREFIX = "W363_LN_INPUT_JSON="
LEAN_FILE = "scripts/w363_ln_input_export.lean"
CERT = "GQ2.Dyadic.Certificates."
BRIDGE = "GQ2.Dyadic.W363LNInput."

RECORD_TARGET = "record_target"
DENOTATION = "denotation_theorem"

PROVENANCE_FILES = (
    LEAN_FILE,
    "GQ2/Dyadic/Word/FoxCert.lean",
    "GQ2/Dyadic/Certificates/LFox.lean",
    "GQ2/Dyadic/Certificates/LJacobian.lean",
    "GQ2/Dyadic/Certificates/N0Fox.lean",
    "GQ2/Dyadic/Certificates/NpcFox.lean",
    "scripts/w363_ln_input_tex.py",
)


def _sector(name, record, projector, projector_bridge, tame, wild):
    """One expected sector: the record, the projector reading, and the two row bridges.

    `tame` and `wild` are (bridge stem, bridge kind) pairs. A payload naming a different
    record, projector or bridge is rejected: matching shapes are not a certificate
    identity, only these declarations are.
    """
    return {"sector": name, "record": CERT + record, "projector": projector,
            "projector_bridge": BRIDGE + projector_bridge,
            "tame_bridge": BRIDGE + tame[0], "tame_bridge_kind": tame[1],
            "wild_bridge": BRIDGE + wild[0], "wild_bridge_kind": wild[1]}


FAMILIES = {
    "L": {"parameters": ("h", "q"), "alphabet": "TameSym",
          "degree": lambda s: 2 * s["h"] + 1,
          "sectors": [
              _sector("unramified", "LSq.lSqWildRowCertUnram", "one", "tameSplit_projector",
                      ("tameUnramInput_denote", DENOTATION),
                      ("lSqUnramWild_target", RECORD_TARGET)),
              _sector("ramified", "LSq.lSqWildRowCertRam", "zero", "tameRamified_projector",
                      ("tameRamInput_denote", DENOTATION),
                      ("lSqRamWild_target", RECORD_TARGET)),
              _sector("scalar", "LSq.lSqWildRowCertSplit", "one", "tameSplit_projector",
                      ("tameUnramInput_denote", DENOTATION),
                      ("lSqScalarWild_target", RECORD_TARGET))]},
    "N0": {"parameters": ("h", "q"), "alphabet": "TameSym",
           "degree": lambda s: 2 + 2 * s["h"],
           "sectors": [
               _sector("unramified", "nCompactWildRowCertUnram", "one", "tameSplit_projector",
                       ("nCompactUnramTame_target", RECORD_TARGET),
                       ("nCompactUnramWild_target", RECORD_TARGET)),
               _sector("ramified", "nCompactWildRowCertRam", "zero", "tameRamified_projector",
                       ("tameRamInput_denote", DENOTATION),
                       ("nCompactRamWild_target", RECORD_TARGET))]},
    "Npc": {"parameters": ("h", "q", "r"), "alphabet": "NpcSym",
            "degree": lambda s: 2 + 2 * s["h"],
            "sectors": [
                _sector("unramified", "Npc.npcWildRowCertUnram", "one", "npcSplit_projector",
                        ("npcUnramTame_target", RECORD_TARGET),
                        ("npcUnramWild_target", RECORD_TARGET)),
                _sector("ramified", "Npc.npcWildRowCertRam", "zero", "npcRamified_projector",
                        ("npcTameRamInput_denote", DENOTATION),
                        ("npcRamWild_target", RECORD_TARGET))]},
}

# Conditions the exported syntax does NOT establish; printed with every artifact.
CERTIFICATE_CONDITIONS = {
    "L": "The evaluated rows need only the listed coefficient hypotheses; the completed L "
         "word certificate additionally requires q = 2^f with f odd. The L family carries no "
         "tame-row record at any sector, so all three L tame rows are denotation theorems "
         "stated in the exporter driver.",
    "N0": "The N0 rows need 1 <= alpha; the complete N0 certificate requires alpha >= 2 and "
          "nonzero even q. The ramified tame row has no record and is a denotation theorem.",
    "Npc": "The Npc rows need 1 <= alpha; the complete Npc certificate requires alpha >= 2, "
           "nonzero even q and an exact NpcDisplayFor for the semantic unit. The ramified "
           "tame row has no record and is a denotation theorem. The Npc tame relator is a "
           "SECOND declaration Certificates.Npc.tameRelW, not Certificates.tameRelW; the "
           "driver's Npc denotation theorems are stated over the Npc one.",
}

PROJECTORS = {"one": r"\Pi=I", "zero": r"\Pi=0"}


def digest(payload):
    return hashlib.sha256(DOMAIN + canonical_json(payload).encode()).hexdigest()


def validate_parameters(family, parameters):
    if not isinstance(family, str) or family not in FAMILIES:
        raise TemplateError("family must be L, N0 or Npc")
    fields(parameters, set(FAMILIES[family]["parameters"]), "LN input structural parameters")
    for name, value in parameters.items():
        integer(value, name, natural=True)


def validate_input_row(row, alphabet, degree, bridge, kind):
    fields(row, {"bridge", "bridge_kind", "row"}, "LN evaluated row")
    if row["bridge"] != bridge or row["bridge_kind"] != kind:
        raise TemplateError("LN evaluated row is not bound to the expected Lean bridge")
    validate_row(row["row"], alphabet, degree)


def validate(envelope):
    fields(envelope, {"payload", "status", "template_hash"}, "LN input envelope")
    if envelope["status"] != "STAGED":
        raise TemplateError("LN input artifacts must remain STAGED")
    p = envelope["payload"]
    fields(p, {"alphabet", "application_scope", "family", "hash_scope", "interpretation",
               "schema", "sectors", "structural"}, "LN input payload")
    if p["schema"] != SCHEMA:
        raise TemplateError("LN input schema mismatch")
    validate_parameters(p["family"], p["structural"])
    meta = FAMILIES[p["family"]]
    structural = p["structural"]
    degree = meta["degree"](structural)
    fields(p["alphabet"], {"degree", "h", "wild_count"}, "LN input alphabet")
    if (integer(p["alphabet"]["degree"], "alphabet degree", natural=True) != degree
            or p["alphabet"]["h"] != structural["h"]
            or p["alphabet"]["wild_count"] != degree + 1):
        raise TemplateError("LN input alphabet does not match the declared rank")
    for key in ("application_scope", "hash_scope", "interpretation"):
        if not isinstance(p[key], str) or not p[key]:
            raise TemplateError("LN input " + key + " must be a nonempty string")
    sectors = p["sectors"]
    if not isinstance(sectors, list) or len(sectors) != len(meta["sectors"]):
        raise TemplateError("LN input sector count does not match the family")
    for sector, expected in zip(sectors, meta["sectors"]):
        fields(sector, {"column_operations", "projector", "projector_bridge", "record",
                        "sector", "symbol_alphabet", "tame_row", "wild_row"},
               "LN input sector")
        if (sector["sector"] != expected["sector"] or sector["record"] != expected["record"]
                or sector["projector"] != expected["projector"]
                or sector["projector_bridge"] != expected["projector_bridge"]):
            raise TemplateError("LN input sector is not bound to the expected record/bridges")
        if sector["symbol_alphabet"] != meta["alphabet"]:
            raise TemplateError("LN input sector uses the wrong atom alphabet")
        if not isinstance(sector["column_operations"], list):
            raise TemplateError("LN input operation list must be an array")
        if sector["column_operations"]:
            # Item 3 is the Jacobian BEFORE any operation. A nonempty list would mean the
            # serialized rows had already been transformed, which is item 4/5's business.
            raise TemplateError("LN input rows must carry no column operations")
        for op in sector["column_operations"]:
            validate_col_op(op, meta["alphabet"], degree)
        validate_input_row(sector["tame_row"], meta["alphabet"], degree,
                           expected["tame_bridge"], expected["tame_bridge_kind"])
        validate_input_row(sector["wild_row"], meta["alphabet"], degree,
                           expected["wild_bridge"], expected["wild_bridge_kind"])
    if envelope["template_hash"] != digest(p):
        raise TemplateError("LN input envelope hash mismatch")
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
        raise TemplateError("Lean LN input exporter failed:\n" + result.stdout + result.stderr)
    records = [line[len(PREFIX):] for line in result.stdout.splitlines()
               if line.startswith(PREFIX)]
    if len(records) != 1:
        raise TemplateError("Lean LN input exporter must emit exactly one marked artifact")
    obj = loads(records[0])
    if canonical_json(obj) != records[0]:
        raise TemplateError("Lean/Python LN input canonical JSON mismatch")
    if obj["payload"]["family"] != family or obj["payload"]["structural"] != parameters:
        raise TemplateError("Lean LN input exporter returned different parameters")
    return obj


def provenance(envelope):
    return {"schema": SCHEMA + ".provenance", "status": "STAGED",
            "template_hash": envelope["template_hash"],
            "scope": "Direct source bytes only; not a transitive build, coefficient module, "
                     "or certificate attestation.",
            "sha256": {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                       for name in PROVENANCE_FILES}}


# ---------------------------------------------------------------- rendering


def jacobian_tex(sector):
    return (r"\begin{pmatrix}" + row_tex(sector["tame_row"]["row"]) + r"\\"
            + row_tex(sector["wild_row"]["row"]) + r"\end{pmatrix}")


def bridge_comment(label, row):
    return ("% " + label + " row bridge (" + row["bridge_kind"] + "): " + row["bridge"])


def render_tex(envelope):
    p = validate(envelope)
    family = p["family"]
    lines = [
        "% STAGED L/N evaluated Fox Jacobian; ledger item 3 only.",
        "% ln-input-hash: " + envelope["template_hash"],
        "% family: " + family + "; structural: " + canonical_json(p["structural"]),
        "% " + p["application_scope"],
        "% " + p["interpretation"],
        "% " + p["hash_scope"],
        "% " + CERTIFICATE_CONDITIONS[family],
        "% S, T, W_i are generator actions; S_2 is the omega2 action, not S squared;"
        " A is the eta-hat conjugator action, not an independently chosen scalar;"
        " Pi is the projector atom P.",
        "% Rows are identities on ALL cochains, not only on the cocycle kernel."
        " Unprinted columns carry the coefficient 0.",
        "% record_target means the row IS the target field of that record, whose colOps is"
        " empty; denotation_theorem means the driver states the denotation itself.",
        "% Syntax, hash and render agreement is NOT Lean synchronization;"
        " replay Lean for strong checking.",
    ]
    for sector in p["sectors"]:
        lines += [r"\paragraph{" + sector["sector"] + " sector}",
                  "% record: " + sector["record"],
                  "% projector reading: " + sector["projector"]
                  + "; bridge: " + sector["projector_bridge"],
                  bridge_comment("tame", sector["tame_row"]),
                  bridge_comment("wild", sector["wild_row"]),
                  r"\[" + jacobian_tex(sector) + r"\qquad(" + PROJECTORS[sector["projector"]]
                  + r").\]"]
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------- self-test


def self_test():
    def row(entries, degree=1):
        return {"columns": [{"coefficient": entries.get(i, {"op": "zero"}), "generator": g}
                            for i, g in enumerate(expected_columns(degree))]}

    unit = {"op": "atom", "symbol": {"generator": {"kind": "sigma"},
                                     "kind": "generator_power", "power": -1}}
    proj = {"op": "atom", "symbol": {"kind": "projector"}}
    base = {"alphabet": {"degree": 1, "h": 0, "wild_count": 2},
            "application_scope": "scope", "family": "L", "hash_scope": "hash scope",
            "interpretation": "interpretation", "schema": SCHEMA, "sectors": [],
            "structural": {"h": 0, "q": 2}}
    for spec in FAMILIES["L"]["sectors"]:
        base["sectors"].append({
            "column_operations": [], "projector": spec["projector"],
            "projector_bridge": spec["projector_bridge"], "record": spec["record"],
            "sector": spec["sector"], "symbol_alphabet": "TameSym",
            "tame_row": {"bridge": spec["tame_bridge"],
                         "bridge_kind": spec["tame_bridge_kind"], "row": row({1: unit})},
            "wild_row": {"bridge": spec["wild_bridge"],
                         "bridge_kind": spec["wild_bridge_kind"], "row": row({1: proj})}})

    def wrap(p):
        return {"payload": p, "status": "STAGED", "template_hash": digest(p)}

    obj = wrap(base)
    assert loads(canonical_json(obj)) == obj
    assert "ln-input-hash" in render_tex(obj)
    assert r"S^{-1}\bigl(a_{\tau}\bigr)" in render_tex(obj)
    assert r"\Pi\bigl(a_{\tau}\bigr)" in render_tex(obj)
    assert "record_target" in render_tex(obj) and "denotation_theorem" in render_tex(obj)
    count = 4

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
        lambda p: p.update(interpretation=3),
        lambda p: p.pop("hash_scope"),
        lambda p: p["structural"].update(h=1),
        lambda p: p["structural"].update(q=-1),
        lambda p: p["structural"].update(q=True),
        lambda p: p["structural"].update(r=2),
        lambda p: p["alphabet"].update(degree=2),
        lambda p: p["alphabet"].update(wild_count=3),
        lambda p: p["alphabet"].update(h=1),
        lambda p: p["sectors"].pop(),
        lambda p: p["sectors"][0].update(sector="ramified"),
        lambda p: p["sectors"][0].update(record=CERT + "other"),
        lambda p: p["sectors"][0].update(projector="zero"),
        lambda p: p["sectors"][0].update(projector_bridge=BRIDGE + "other"),
        lambda p: p["sectors"][0].update(symbol_alphabet="NpcSym"),
        lambda p: p["sectors"][0].update(column_operations={}),
        # item 3 is the Jacobian before any operation: a well-formed op is still refused
        lambda p: p["sectors"][0]["column_operations"].append(
            {"op": "scale", "generator": {"index": 0, "kind": "wild"},
             "forward": {"op": "one"}, "inverse": {"op": "one"}}),
        lambda p: p["sectors"][0]["tame_row"].update(bridge=BRIDGE + "other"),
        # the strength of the claim is part of the artifact, so a relabelled bridge kind
        # is rejected exactly like a wrong declaration name
        lambda p: p["sectors"][0]["tame_row"].update(bridge_kind=RECORD_TARGET),
        lambda p: p["sectors"][0]["wild_row"].update(bridge_kind=DENOTATION),
        lambda p: p["sectors"][0]["wild_row"].update(extra=1),
        lambda p: p["sectors"][0]["tame_row"]["row"]["columns"].pop(),
        lambda p: p["sectors"][0]["tame_row"]["row"]["columns"].reverse(),
        lambda p: p["sectors"][0]["wild_row"]["row"]["columns"][0].update(
            coefficient={"op": "x"}),
        lambda p: p["sectors"][0]["wild_row"]["row"]["columns"][0].update(
            coefficient={"op": "atom", "symbol": {"kind": "eta_conjugator_power", "power": 1}}),
        lambda p: p["sectors"][0].pop("wild_row"),
    ]
    for mutate in mutations:
        try:
            validate(mutated(mutate))
        except TemplateError:
            count += 1
        else:
            raise AssertionError("malformed LN input artifact accepted")
    for bad in ("[]", "null", "NaN", "Infinity", '{"payload":0,"payload":0}',
                canonical_json(obj).replace('"h":0', '"h":0,"h":0'),
                canonical_json(obj).replace('"STAGED"', '"APPROVED"'),
                canonical_json(obj).replace(obj["template_hash"], "0" * 64),
                canonical_json(obj).replace('"op":"zero"', '"op":"zeroed"', 1)):
        try:
            loads(bad)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("malformed LN input JSON accepted")
    for family, parameters in (("L", {"h": 0}), ("Npc", {"h": 0, "q": 2}),
                               ("M0", {"h": 0, "q": 2}), ("L", {"h": -1, "q": 2})):
        try:
            validate_parameters(family, parameters)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid LN input parameters accepted")
    print(f"LN_INPUT_SELF_TEST_PASS|{count}")
    return count


def artifact_name(payload):
    family, s = payload["family"], payload["structural"]
    return family + "-input-" + "-".join(name + str(s[name])
                                         for name in FAMILIES[family]["parameters"])


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
            raise TemplateError("LN input output must be inside general-ln-certificate-staged")
        obj = from_lean(args.lean_runner, args.family, parameters)
        args.out.mkdir(parents=True, exist_ok=True)
        base = args.out / artifact_name(obj["payload"])
        base.with_suffix(".input.json").write_text(canonical_json(obj) + "\n")
        base.with_suffix(".input.tex").write_text(render_tex(obj))
        base.with_suffix(".input.provenance.json").write_text(
            canonical_json(provenance(obj)) + "\n")
        print(f"STAGED_LN_INPUT_GENERATED|{base.name}|{obj['template_hash']}")
        return
    paths = sorted(args.directory.glob("*.input.json"))
    if not paths:
        raise TemplateError("no staged LN input artifacts found")
    for path in paths:
        obj = loads(path.read_text())
        p = obj["payload"]
        name = artifact_name(p)
        if path.name != name + ".input.json":
            raise TemplateError("noncanonical LN input filename")
        base = path.parent / name
        if base.with_suffix(".input.tex").read_text() != render_tex(obj):
            raise TemplateError("generated LN input TeX drift")
        recorded = json.loads(base.with_suffix(".input.provenance.json").read_text(),
                              object_pairs_hook=reject_duplicates)
        if recorded != provenance(obj):
            raise TemplateError("LN input direct-source provenance drift")
        replayed = "syntax-only"
        if args.lean_runner:
            if from_lean(args.lean_runner, p["family"], p["structural"]) != obj:
                raise TemplateError("Lean LN input replay disagrees with the staged artifact")
            replayed = "Lean-replayed"
        print(f"STAGED_LN_INPUT_CHECK|{replayed}|{name}|{obj['template_hash']}")


if __name__ == "__main__":
    main()
