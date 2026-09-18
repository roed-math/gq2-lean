#!/usr/bin/env python3
"""STAGED L/N0/Npc change of variables to the quadratic normal form (ledger item 8).

Lean owns the data: `scripts/w363_ln_coordinate_export.lean` serializes it and carries the
signature theorems. This module validates that serialization and renders it.

Item 8 splits and only one half is reachable from an exporter lane. The change of variables
is a genuine Equiv with an explicit toFun and invFun, so it is data and the bindings are
`rfl` against the Equiv's own fields: the `record_target` strength of items 3, 4 and 5. The
quadratic normal form RECORD itself, SourceOddHessian, is not bound: the declarations that
build it take a descent datum, a factor set, a projection, a coefficient module with its
topology and action, a simplicity hypothesis and a cardinality, so a rfl signature theorem
against one would require selecting a coefficient module, which this lane is forbidden to
do. Those records are named with the bridge kind `named_but_unbound`, and the validator
refuses to let that be relabelled: naming is not binding.

The content worth publishing is the head. All four sectors share the same handle
regrouping; L carries one head coordinate and leaves it alone, N0 carries two and leaves
both alone, and both Npc sectors carry two and replace the first by its image under Phi.
Only the Npc sectors are a change of variables in the ledger item's sense.
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
SCHEMA = "gq2.w363.ln-coordinate.v1.staged"
DOMAIN = b"GQ2-W363-LN-COORDINATE\0"
PREFIX = "W363_LN_COORDINATE_JSON="
LEAN_FILE = "scripts/w363_ln_coordinate_export.lean"
BRIDGE = "GQ2.Dyadic.W363LNCoordinate."
RECORD_TARGET = "record_target"
UNBOUND = "named_but_unbound"
REGROUPING = "finTwoProdAddEquiv"

LGN = "GQ2.Dyadic.LSquare."
WPM = "GQ2.Dyadic.Instances.WordPhaseModel."
NUC = "GQ2.Dyadic.Instances.NpcUnramifiedComparison."
NRC = "GQ2.Dyadic.Instances.NpcRamifiedComparisonBase."
LHC = "GQ2.Dyadic.Instances.LHessianCertificates."
CNH = "GQ2.Dyadic.Instances.CompactNHessianCertificates."
NHC = "GQ2.Dyadic.Instances.NpcHessianCertificates."

PROVENANCE_FILES = (
    LEAN_FILE,
    "GQ2/Dyadic/Instances/GammaLGraphNormalForm.lean",
    "GQ2/Dyadic/Instances/WordPhaseModel.lean",
    "GQ2/Dyadic/Instances/NpcUnramifiedComparison.lean",
    "GQ2/Dyadic/Instances/NpcRamifiedComparisonBase.lean",
    "GQ2/Dyadic/Instances/LHessianCertificates.lean",
    "GQ2/Dyadic/Instances/CompactNHessianCertificates.lean",
    "GQ2/Dyadic/Instances/NpcHessianCertificates.lean",
    "scripts/w363_ln_coordinate_tex.py",
)


def _sector(name, equiv, stem, transform, heads, records):
    return {"sector": name, "equiv": equiv,
            "forward_bridge": BRIDGE + stem + "_toFun",
            "inverse_bridge": BRIDGE + stem + "_invFun",
            "head_transform": transform, "head_coordinates": heads,
            "normal_form_records": tuple(records)}


FAMILIES = {
    "L": {"parameters": ("h", "q"),
          "sectors": [_sector("graph_normal_form", LGN + "lSqPhaseCoordsEquiv", "lCoords",
                              "identity", 1,
                              (LHC + "unramifiedHessian", LHC + "ramifiedHessian"))]},
    "N0": {"parameters": ("h", "q"),
           "sectors": [_sector("compact_normal_form", WPM + "wPmCompactCoordsEquiv",
                               "n0Coords", "identity", 2,
                               (CNH + "compactNUnramifiedHessian",
                                CNH + "compactNRamifiedHessian"))]},
    "Npc": {"parameters": ("h", "q", "r"),
            "sectors": [
                _sector("unramified_full_offset", NUC + "wPnpcPhiCoordsEquiv",
                        "npcUnramCoords", "phi", 2,
                        (NHC + "npcUnramifiedHeadHessian",)),
                _sector("ramified_full_offset", NRC + "wPnpcRamifiedCoordsEquiv",
                        "npcRamCoords", "phi", 2,
                        (NHC + "nonempty_npcRamifiedHeadHessian",))]},
}

HEAD_TRANSFORMS = ("identity", "phi")

CERTIFICATE_CONDITIONS = {
    "L": "L is the only family with a single head coordinate, and it carries it through "
         "unchanged: this sector is a rebracketing of the handle coordinates, not a change "
         "of variables.",
    "N0": "N0 carries two head coordinates and leaves both alone, so this sector is also a "
          "rebracketing. Note the naming: the equiv the compact-N data uses is named "
          "wPmCompactCoordsEquiv, with an m, and lives in WordPhaseModel; the name does not "
          "say which family uses it.",
    "Npc": "Both Npc sectors replace the first head coordinate by its image under the "
           "normal-form operator Phi, so these are the only two sectors that are a change "
           "of variables in the ledger item's sense. The inverse applies Phi.symm, which is "
           "why the operator has to be an equivalence and not merely a map.",
}


def digest(payload):
    return hashlib.sha256(DOMAIN + canonical_json(payload).encode()).hexdigest()


def validate_parameters(family, parameters):
    if not isinstance(family, str) or family not in FAMILIES:
        raise TemplateError("family must be L, N0 or Npc")
    fields(parameters, set(FAMILIES[family]["parameters"]),
           "LN coordinate structural parameters")
    for name, value in parameters.items():
        integer(value, name, natural=True)


def validate(envelope):
    fields(envelope, {"payload", "status", "template_hash"}, "LN coordinate envelope")
    if envelope["status"] != "STAGED":
        raise TemplateError("LN coordinate artifacts must remain STAGED")
    p = envelope["payload"]
    fields(p, {"application_scope", "family", "handle_regrouping", "hash_scope", "head_note",
               "record_binding", "schema", "sectors", "structural", "warning"},
           "LN coordinate payload")
    if p["schema"] != SCHEMA:
        raise TemplateError("LN coordinate schema mismatch")
    validate_parameters(p["family"], p["structural"])
    meta = FAMILIES[p["family"]]
    for key in ("application_scope", "hash_scope", "head_note", "warning"):
        if not isinstance(p[key], str) or not p[key]:
            raise TemplateError("LN coordinate " + key + " must be a nonempty string")
    # naming is not binding, and the artifact may not say otherwise
    if p["record_binding"] != UNBOUND:
        raise TemplateError("the normal-form records carry no binding here and may not "
                            "be presented as if they did")
    fields(p["handle_regrouping"], {"bridge_kind", "planes", "via"},
           "LN coordinate handle regrouping")
    if p["handle_regrouping"]["bridge_kind"] != RECORD_TARGET:
        raise TemplateError("the coordinate components are rfl record targets")
    if p["handle_regrouping"]["via"] != REGROUPING:
        raise TemplateError("LN coordinate regrouping is not the expected equivalence")
    if (integer(p["handle_regrouping"]["planes"], "handle planes", natural=True)
            != p["structural"]["h"]):
        raise TemplateError("LN coordinate handle-plane count is not the handle rank")
    sectors = p["sectors"]
    if not isinstance(sectors, list) or len(sectors) != len(meta["sectors"]):
        raise TemplateError("LN coordinate sector count does not match the family")
    for sector, expected in zip(sectors, meta["sectors"]):
        fields(sector, {"equiv", "forward_bridge", "head_coordinates", "head_transform",
                        "inverse_bridge", "normal_form_records", "sector"},
               "LN coordinate sector")
        for key in ("sector", "equiv", "forward_bridge", "inverse_bridge"):
            if sector[key] != expected[key]:
                raise TemplateError("LN coordinate sector is not bound to the expected "
                                    "declarations")
        if sector["head_transform"] != expected["head_transform"]:
            raise TemplateError("LN coordinate head transform does not match the sector")
        if sector["head_transform"] not in HEAD_TRANSFORMS:
            raise TemplateError("unexpected LN coordinate head transform")
        if (integer(sector["head_coordinates"], "head coordinates", natural=True)
                != expected["head_coordinates"]):
            raise TemplateError("LN coordinate head count does not match the sector")
        if list(sector["normal_form_records"]) != list(expected["normal_form_records"]):
            raise TemplateError("LN coordinate normal-form records are not the sector's own")
    if envelope["template_hash"] != digest(p):
        raise TemplateError("LN coordinate envelope hash mismatch")
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
        raise TemplateError("Lean LN coordinate exporter failed:\n"
                            + result.stdout + result.stderr)
    records = [line[len(PREFIX):] for line in result.stdout.splitlines()
               if line.startswith(PREFIX)]
    if len(records) != 1:
        raise TemplateError("Lean LN coordinate exporter must emit one marked artifact")
    obj = loads(records[0])
    if canonical_json(obj) != records[0]:
        raise TemplateError("Lean/Python LN coordinate canonical JSON mismatch")
    if obj["payload"]["family"] != family or obj["payload"]["structural"] != parameters:
        raise TemplateError("Lean LN coordinate exporter returned different parameters")
    return obj


def provenance(envelope):
    return {"schema": SCHEMA + ".provenance", "status": "STAGED",
            "template_hash": envelope["template_hash"],
            "scope": "Direct source bytes only; not a transitive build, coefficient module, "
                     "or certificate attestation.",
            "sha256": {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                       for name in PROVENANCE_FILES}}


# ---------------------------------------------------------------- rendering


def head_tex(sector):
    if sector["head_transform"] == "phi":
        return (r"(c_0,c_1)\mapsto(\Phi c_0,c_1)"
                r"\quad[\text{inverse applies }\Phi^{-1}]")
    if sector["head_coordinates"] == 1:
        return r"c_0\mapsto c_0"
    return r"(c_0,c_1)\mapsto(c_0,c_1)"


def render_tex(envelope):
    p = validate(envelope)
    family = p["family"]
    planes = p["handle_regrouping"]["planes"]
    lines = [
        "% STAGED L/N change of variables to the quadratic normal form; ledger item 8 only.",
        "% ln-coordinate-hash: " + envelope["template_hash"],
        "% family: " + family + "; structural: " + canonical_json(p["structural"]),
        "% " + p["application_scope"],
        "% " + p["warning"],
        "% " + p["head_note"],
        "% " + p["hash_scope"],
        "% " + CERTIFICATE_CONDITIONS[family],
        "% handle regrouping (" + p["handle_regrouping"]["bridge_kind"] + ") via "
        + p["handle_regrouping"]["via"],
        r"\[\bigl(\mathrm{Fin}\," + str(planes) + r"\times\mathrm{Fin}\,2\to A\bigr)"
        r"\;\longrightarrow\;\bigl(\mathrm{Fin}\," + str(planes) + r"\to A\times A\bigr).\]",
    ]
    for sector in p["sectors"]:
        lines += [r"\paragraph{" + tex_escape(sector["sector"].replace("_", " ")) + "}",
                  "% equiv: " + sector["equiv"],
                  "% forward (" + RECORD_TARGET + "): " + sector["forward_bridge"],
                  "% inverse (" + RECORD_TARGET + "): " + sector["inverse_bridge"],
                  r"\[" + head_tex(sector) + r".\]",
                  "Head coordinates: " + str(sector["head_coordinates"])
                  + ". Normal-form records named but NOT bound here ("
                  + tex_escape(p["record_binding"].replace("_", " ")) + "): "
                  + ", ".join(r"\texttt{" + tex_escape(r) + "}"
                              for r in sector["normal_form_records"]) + "."]
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------- self-test


def self_test():
    def build(family, structural):
        meta = FAMILIES[family]
        sectors = [{"equiv": s["equiv"], "forward_bridge": s["forward_bridge"],
                    "head_coordinates": s["head_coordinates"],
                    "head_transform": s["head_transform"],
                    "inverse_bridge": s["inverse_bridge"],
                    "normal_form_records": list(s["normal_form_records"]),
                    "sector": s["sector"]} for s in meta["sectors"]]
        return {"application_scope": "scope", "family": family,
                "handle_regrouping": {"bridge_kind": RECORD_TARGET,
                                      "planes": structural["h"], "via": REGROUPING},
                "hash_scope": "hash scope", "head_note": "head note",
                "record_binding": UNBOUND, "schema": SCHEMA, "sectors": sectors,
                "structural": structural, "warning": "warning"}

    def wrap(p):
        return {"payload": p, "status": "STAGED", "template_hash": digest(p)}

    base = build("Npc", {"h": 2, "q": 2, "r": 1})
    obj = wrap(base)
    assert loads(canonical_json(obj)) == obj
    assert "ln-coordinate-hash" in render_tex(obj)
    assert r"\Phi c_0" in render_tex(obj)
    assert "named but NOT bound here" in render_tex(obj)
    lobj = wrap(build("L", {"h": 1, "q": 2}))
    assert loads(canonical_json(lobj)) == lobj
    assert r"c_0\mapsto c_0" in render_tex(lobj)
    count = 5

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
        lambda p: p.update(head_note=3),
        lambda p: p.pop("warning"),
        # naming is not binding
        lambda p: p.update(record_binding=RECORD_TARGET),
        lambda p: p.update(record_binding="field_statement_identity"),
        lambda p: p["structural"].update(h=-1),
        lambda p: p["structural"].pop("r"),
        lambda p: p["handle_regrouping"].update(planes=3),
        lambda p: p["handle_regrouping"].update(via="finProdAddEquiv"),
        lambda p: p["handle_regrouping"].update(bridge_kind=UNBOUND),
        lambda p: p["sectors"].pop(),
        lambda p: p["sectors"].reverse(),
        lambda p: p["sectors"][0].update(equiv=NRC + "other"),
        lambda p: p["sectors"][0].update(forward_bridge=BRIDGE + "other"),
        lambda p: p["sectors"][0].update(inverse_bridge=BRIDGE + "other"),
        # the head transform is the whole difference between a change of variables and a
        # rebracketing, so it may not be relabelled
        lambda p: p["sectors"][0].update(head_transform="identity"),
        lambda p: p["sectors"][0].update(head_transform="psi"),
        lambda p: p["sectors"][0].update(head_coordinates=1),
        lambda p: p["sectors"][0].update(normal_form_records=[]),
        lambda p: p["sectors"][0]["normal_form_records"].append(LHC + "unramifiedHessian"),
        lambda p: p["sectors"][0].pop("equiv"),
    ]
    for mutate in mutations:
        try:
            validate(mutated(mutate))
        except TemplateError:
            count += 1
        else:
            raise AssertionError("malformed LN coordinate artifact accepted")
    for bad in ("[]", "null", "NaN", "Infinity", '{"payload":0,"payload":0}',
                canonical_json(obj).replace('"h":2', '"h":2,"h":2'),
                canonical_json(obj).replace('"STAGED"', '"APPROVED"'),
                canonical_json(obj).replace(obj["template_hash"], "0" * 64),
                canonical_json(obj).replace('"head_transform"', '"headTransform"', 1)):
        try:
            loads(bad)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("malformed LN coordinate JSON accepted")
    for family, parameters in (("L", {"h": 0}), ("Npc", {"h": 0, "q": 2}),
                               ("M0", {"h": 0, "q": 2}), ("L", {"h": -1, "q": 2})):
        try:
            validate_parameters(family, parameters)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid LN coordinate parameters accepted")
    print(f"LN_COORDINATE_SELF_TEST_PASS|{count}")
    return count


def artifact_name(payload):
    family, s = payload["family"], payload["structural"]
    return family + "-coordinate-" + "-".join(
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
                "LN coordinate output must be inside general-ln-certificate-staged")
        obj = from_lean(args.lean_runner, args.family, parameters)
        args.out.mkdir(parents=True, exist_ok=True)
        base = args.out / artifact_name(obj["payload"])
        base.with_suffix(".coordinate.json").write_text(canonical_json(obj) + "\n")
        base.with_suffix(".coordinate.tex").write_text(render_tex(obj))
        base.with_suffix(".coordinate.provenance.json").write_text(
            canonical_json(provenance(obj)) + "\n")
        print(f"STAGED_LN_COORDINATE_GENERATED|{base.name}|{obj['template_hash']}")
        return
    paths = sorted(args.directory.glob("*.coordinate.json"))
    if not paths:
        raise TemplateError("no staged LN coordinate artifacts found")
    for path in paths:
        obj = loads(path.read_text())
        p = obj["payload"]
        name = artifact_name(p)
        if path.name != name + ".coordinate.json":
            raise TemplateError("noncanonical LN coordinate filename")
        base = path.parent / name
        if base.with_suffix(".coordinate.tex").read_text() != render_tex(obj):
            raise TemplateError("generated LN coordinate TeX drift")
        recorded = json.loads(base.with_suffix(".coordinate.provenance.json").read_text(),
                              object_pairs_hook=reject_duplicates)
        if recorded != provenance(obj):
            raise TemplateError("LN coordinate direct-source provenance drift")
        replayed = "syntax-only"
        if args.lean_runner:
            if from_lean(args.lean_runner, p["family"], p["structural"]) != obj:
                raise TemplateError(
                    "Lean LN coordinate replay disagrees with the staged artifact")
            replayed = "Lean-replayed"
        print(f"STAGED_LN_COORDINATE_CHECK|{replayed}|{name}|{obj['template_hash']}")


if __name__ == "__main__":
    main()
