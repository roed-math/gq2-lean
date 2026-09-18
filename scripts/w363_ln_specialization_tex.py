#!/usr/bin/env python3
"""STAGED L/N0/Npc two specializations: pro-two factors and the tame field (item 2).

Lean owns the data: `scripts/w363_ln_specialization_export.lean` serializes it and carries
the signature theorems. This module validates that serialization and renders it.

Item 2 splits, and the split is the content. The pro-two half is a syntactic identity
between PWord values, restated in the driver as a factor list and discharged by the tree's
own theorem, so a wrong factor list does not compile: the `restated_identity` bridge kind
item 7 introduced. The tame half is a Prop carried as the `tameSpecialization` field of the
word certificate record, so proof irrelevance makes its binding a statement identity: the
`field_statement_identity` kind of items 6 and 9. The validator pins both kinds and the
factor kinds, and refuses a relabelling in either direction.

Item 2 is also where the three field-selection adapters are pinned, and those are NOT
standard-three: each carries four documented standing arithmetic and reciprocity inputs.
Nothing in this artifact touches them or weakens that class, and every artifact says so.
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
SCHEMA = "gq2.w363.ln-specialization.v1.staged"
DOMAIN = b"GQ2-W363-LN-SPECIALIZATION\0"
PREFIX = "W363_LN_SPECIALIZATION_JSON="
LEAN_FILE = "scripts/w363_ln_specialization_export.lean"
BRIDGE = "GQ2.Dyadic.W363LNSpecialization."
RESTATED = "restated_identity"
STATEMENT = "field_statement_identity"

W = "GQ2.Dyadic.Words."
LSQ = "GQ2.Dyadic.LSquare."
CN = "GQ2.Dyadic.Instances.WordPhaseCompactNFinal."
NPCR = "GQ2.Dyadic.Instances.NpcCandidateRN."
NPCD = "GQ2.Dyadic.Instances.NpcDeterminantFinal."

PROVENANCE_FILES = (
    LEAN_FILE,
    "GQ2/Dyadic/Words/Alphabet.lean",
    "GQ2/Dyadic/Words/L.lean",
    "GQ2/Dyadic/Words/N0.lean",
    "GQ2/Dyadic/Words/Npc.lean",
    "GQ2/Dyadic/TameBoundary.lean",
    "GQ2/Dyadic/Instances/GammaLReconstruction.lean",
    "GQ2/Dyadic/Instances/WordPhaseCompactNFinal.lean",
    "GQ2/Dyadic/Instances/NpcCandidateRN.lean",
    "GQ2/Dyadic/Instances/NpcDeterminantFinal.lean",
    "scripts/w363_ln_specialization_tex.py",
)

# The exact table. Factor KINDS are pinned because they are the structural claim; the
# descriptions are prose and only have to be nonempty. A payload naming a different source
# theorem, record or bridge is rejected.
FAMILIES = {
    "L": {"parameters": ("h", "q"),
          "bridge": BRIDGE + "lPro2_shape", "source": W + "LSq.pro2_lSqCore",
          "factors": ("inverse_conjugate", "collapsed_a_letter", "integer_power",
                      "commutator"),
          "tame_binding": BRIDGE + "lTame_field",
          "tame_producer": LSQ + "lCanonicalTameSpecialization",
          "tame_record": LSQ + "wordCertificateRN_lSq_of_actionImage"},
    "N0": {"parameters": ("h", "q"),
           "bridge": BRIDGE + "n0Pro2_shape", "source": W + "pro2_nCompact",
           "factors": ("integer_power", "commutator", "inverse_conjugate",
                       "collapsed_tau"),
           "tame_binding": BRIDGE + "n0Tame_field",
           "tame_producer": "GQ2.Dyadic.genCertNTameSpecializes",
           "tame_record": CN + "wPcNWordCertificateRN"},
    "Npc": {"parameters": ("h", "q", "r"),
            "bridge": BRIDGE + "npcPro2_shape", "source": W + "Npc.pro2_npcW",
            "factors": ("integer_power", "commutator_with_eta_power",
                        "inverse_conjugate_twisted", "collapsed_tau", "folded_block"),
            "tame_binding": BRIDGE + "npcTame_field",
            "tame_producer": NPCR + "npcCandidate_tameSpecializes",
            "tame_record": NPCD + "npcWordCertificateRN"},
}

FACTOR_KINDS = ("inverse_conjugate", "collapsed_a_letter", "integer_power", "commutator",
                "collapsed_tau", "commutator_with_eta_power",
                "inverse_conjugate_twisted", "folded_block")

CERTIFICATE_CONDITIONS = {
    "L": "The L whole-word pro-two equation is assembled in the exporter driver from the "
         "tree's core-list equation and a one-line handle-tail lemma: unlike N0 and Npc, the "
         "tree states the core list and the evaluated form but no whole-word syntactic "
         "equation of its own. The driver's assembly is named in the bridge, and the "
         "handle-tail step is named in the tail description.",
    "N0": "The N0 equation is the tree's own whole-word theorem, with no assembly step.",
    "Npc": "The Npc equation is the tree's own whole-word theorem. Two things Gate C "
           "deliberately does NOT collapse survive into the factor list, the profinite "
           "eta-hat power and the integer two-power conjugator, and the correction block "
           "stays folded because what matters about it is its value, not its pro-two "
           "syntax. Nothing here expands what the Lean leaves folded.",
}


def digest(payload):
    return hashlib.sha256(DOMAIN + canonical_json(payload).encode()).hexdigest()


def validate_parameters(family, parameters):
    if not isinstance(family, str) or family not in FAMILIES:
        raise TemplateError("family must be L, N0 or Npc")
    fields(parameters, set(FAMILIES[family]["parameters"]),
           "LN specialization structural parameters")
    for name, value in parameters.items():
        integer(value, name, natural=True)


def validate_factors(recorded, expected):
    if not isinstance(recorded, list) or len(recorded) != len(expected):
        raise TemplateError("LN specialization factor list does not match the family")
    for position, (factor, kind) in enumerate(zip(recorded, expected), start=1):
        fields(factor, {"description", "kind", "position"}, "LN specialization factor")
        if factor["kind"] != kind or factor["position"] != position:
            raise TemplateError("LN specialization factors are not the family's own, in order")
        if factor["kind"] not in FACTOR_KINDS:
            raise TemplateError("unexpected LN specialization factor kind")
        if not isinstance(factor["description"], str) or not factor["description"]:
            raise TemplateError("LN specialization factor description must be nonempty")


def validate(envelope):
    fields(envelope, {"payload", "status", "template_hash"}, "LN specialization envelope")
    if envelope["status"] != "STAGED":
        raise TemplateError("LN specialization artifacts must remain STAGED")
    p = envelope["payload"]
    fields(p, {"application_scope", "family", "gate", "hash_scope", "pro_two", "schema",
               "structural", "tame", "warning"}, "LN specialization payload")
    if p["schema"] != SCHEMA:
        raise TemplateError("LN specialization schema mismatch")
    validate_parameters(p["family"], p["structural"])
    meta = FAMILIES[p["family"]]
    for key in ("application_scope", "gate", "hash_scope", "warning"):
        if not isinstance(p[key], str) or not p[key]:
            raise TemplateError("LN specialization " + key + " must be a nonempty string")
    fields(p["pro_two"], {"bridge", "bridge_kind", "factors", "source", "tail"},
           "LN specialization pro-two half")
    if (p["pro_two"]["bridge"] != meta["bridge"]
            or p["pro_two"]["source"] != meta["source"]):
        raise TemplateError("LN pro-two half is not bound to the expected declarations")
    if p["pro_two"]["bridge_kind"] != RESTATED:
        raise TemplateError("the LN pro-two bridge is a restated identity, nothing stronger")
    if not isinstance(p["pro_two"]["tail"], str) or not p["pro_two"]["tail"]:
        raise TemplateError("LN pro-two tail description must be a nonempty string")
    validate_factors(p["pro_two"]["factors"], meta["factors"])
    fields(p["tame"], {"binding", "binding_kind", "field", "producer", "record"},
           "LN specialization tame half")
    if (p["tame"]["binding"] != meta["tame_binding"]
            or p["tame"]["producer"] != meta["tame_producer"]
            or p["tame"]["record"] != meta["tame_record"]):
        raise TemplateError("LN tame half is not bound to the expected declarations")
    if p["tame"]["binding_kind"] != STATEMENT:
        raise TemplateError("the LN tame binding is a statement identity, nothing stronger")
    if p["tame"]["field"] != "tameSpecialization":
        raise TemplateError("LN tame half must name the tameSpecialization field")
    if envelope["template_hash"] != digest(p):
        raise TemplateError("LN specialization envelope hash mismatch")
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
        raise TemplateError("Lean LN specialization exporter failed:\n"
                            + result.stdout + result.stderr)
    records = [line[len(PREFIX):] for line in result.stdout.splitlines()
               if line.startswith(PREFIX)]
    if len(records) != 1:
        raise TemplateError("Lean LN specialization exporter must emit one marked artifact")
    obj = loads(records[0])
    if canonical_json(obj) != records[0]:
        raise TemplateError("Lean/Python LN specialization canonical JSON mismatch")
    if obj["payload"]["family"] != family or obj["payload"]["structural"] != parameters:
        raise TemplateError("Lean LN specialization exporter returned different parameters")
    return obj


def provenance(envelope):
    return {"schema": SCHEMA + ".provenance", "status": "STAGED",
            "template_hash": envelope["template_hash"],
            "scope": "Direct source bytes only; not a transitive build, coefficient module, "
                     "or certificate attestation.",
            "sha256": {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                       for name in PROVENANCE_FILES}}


# ---------------------------------------------------------------- rendering


def render_tex(envelope):
    p = validate(envelope)
    family = p["family"]
    pro_two, tame = p["pro_two"], p["tame"]
    lines = [
        "% STAGED L/N two specializations; ledger item 2 only.",
        "% ln-specialization-hash: " + envelope["template_hash"],
        "% family: " + family + "; structural: " + canonical_json(p["structural"]),
        "% " + p["application_scope"],
        "% " + p["warning"],
        "% " + p["gate"],
        "% " + p["hash_scope"],
        "% " + CERTIFICATE_CONDITIONS[family],
        r"\paragraph{The pro-two specialization}",
        "% source: " + pro_two["source"],
        "% bridge (" + pro_two["bridge_kind"] + "): " + pro_two["bridge"],
        r"\begin{enumerate}",
    ]
    for factor in pro_two["factors"]:
        lines.append(r"\item[(" + str(factor["position"]) + r")] \textbf{"
                     + tex_escape(factor["kind"].replace("_", " ")) + "} "
                     + tex_escape(factor["description"]))
    lines += [r"\end{enumerate}",
              "Tail: " + tex_escape(pro_two["tail"]) + ".",
              r"\paragraph{The tame specialization}",
              "% producer: " + tame["producer"],
              "% consumer: " + tame["record"] + ", field " + tame["field"],
              "% binding (" + tame["binding_kind"] + "): " + tame["binding"],
              "The tame half is a proposition carried as the "
              + r"\texttt{" + tex_escape(tame["field"]) + "} field of the word certificate "
              "record, so its binding is a statement identity and not a proof identity."]
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------- self-test


def self_test():
    def build(family, structural):
        meta = FAMILIES[family]
        return {"application_scope": "scope", "family": family, "gate": "gate",
                "hash_scope": "hash scope",
                "pro_two": {"bridge": meta["bridge"], "bridge_kind": RESTATED,
                            "factors": [{"description": "d", "kind": kind,
                                         "position": i}
                                        for i, kind in enumerate(meta["factors"], start=1)],
                            "source": meta["source"], "tail": "tail"},
                "schema": SCHEMA, "structural": structural,
                "tame": {"binding": meta["tame_binding"], "binding_kind": STATEMENT,
                         "field": "tameSpecialization",
                         "producer": meta["tame_producer"], "record": meta["tame_record"]},
                "warning": "warning"}

    def wrap(p):
        return {"payload": p, "status": "STAGED", "template_hash": digest(p)}

    base = build("Npc", {"h": 1, "q": 2, "r": 1})
    obj = wrap(base)
    assert loads(canonical_json(obj)) == obj
    assert "ln-specialization-hash" in render_tex(obj)
    assert "folded block" in render_tex(obj)
    assert "statement identity and not a proof identity" in render_tex(obj)
    lobj = wrap(build("L", {"h": 0, "q": 2}))
    assert loads(canonical_json(lobj)) == lobj
    assert "collapsed a letter" in render_tex(lobj)
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
        lambda p: p.update(gate=3),
        lambda p: p.pop("warning"),
        lambda p: p["structural"].update(h=-1),
        lambda p: p["structural"].update(q=-1),
        lambda p: p["structural"].pop("r"),
        lambda p: p["pro_two"].update(source="GQ2.Dyadic.Words.pro2_nCompact"),
        lambda p: p["pro_two"].update(bridge=BRIDGE + "other"),
        # the pro-two bridge is a restatement and may not be dressed up as a record target
        lambda p: p["pro_two"].update(bridge_kind="record_target"),
        lambda p: p["pro_two"].update(bridge_kind=STATEMENT),
        lambda p: p["pro_two"].update(tail=""),
        lambda p: p["pro_two"]["factors"].pop(),
        lambda p: p["pro_two"]["factors"].reverse(),
        lambda p: p["pro_two"]["factors"][0].update(kind="commutator"),
        lambda p: p["pro_two"]["factors"][0].update(position=2),
        lambda p: p["pro_two"]["factors"][0].update(description=""),
        lambda p: p["pro_two"]["factors"][4].update(kind="collapsed_tau"),
        lambda p: p["pro_two"]["factors"].append({"description": "d", "kind": "commutator",
                                                  "position": 6}),
        lambda p: p["tame"].update(producer=LSQ + "other"),
        lambda p: p["tame"].update(record=CN + "other"),
        lambda p: p["tame"].update(binding=BRIDGE + "other"),
        # and the tame binding may not be dressed up either
        lambda p: p["tame"].update(binding_kind=RESTATED),
        lambda p: p["tame"].update(binding_kind="record_target"),
        lambda p: p["tame"].update(field="stokes"),
        lambda p: p["tame"].pop("producer"),
    ]
    for mutate in mutations:
        try:
            validate(mutated(mutate))
        except TemplateError:
            count += 1
        else:
            raise AssertionError("malformed LN specialization artifact accepted")
    for bad in ("[]", "null", "NaN", "Infinity", '{"payload":0,"payload":0}',
                canonical_json(obj).replace('"h":1', '"h":1,"h":1'),
                canonical_json(obj).replace('"STAGED"', '"APPROVED"'),
                canonical_json(obj).replace(obj["template_hash"], "0" * 64),
                canonical_json(obj).replace('"position":1', '"position":7', 1)):
        try:
            loads(bad)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("malformed LN specialization JSON accepted")
    for family, parameters in (("L", {"h": 0}), ("Npc", {"h": 0, "q": 2}),
                               ("M0", {"h": 0, "q": 2}), ("L", {"h": -1, "q": 2})):
        try:
            validate_parameters(family, parameters)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid LN specialization parameters accepted")
    print(f"LN_SPECIALIZATION_SELF_TEST_PASS|{count}")
    return count


def artifact_name(payload):
    family, s = payload["family"], payload["structural"]
    return family + "-specialization-" + "-".join(
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
                "LN specialization output must be inside general-ln-certificate-staged")
        obj = from_lean(args.lean_runner, args.family, parameters)
        args.out.mkdir(parents=True, exist_ok=True)
        base = args.out / artifact_name(obj["payload"])
        base.with_suffix(".specialization.json").write_text(canonical_json(obj) + "\n")
        base.with_suffix(".specialization.tex").write_text(render_tex(obj))
        base.with_suffix(".specialization.provenance.json").write_text(
            canonical_json(provenance(obj)) + "\n")
        print(f"STAGED_LN_SPECIALIZATION_GENERATED|{base.name}|{obj['template_hash']}")
        return
    paths = sorted(args.directory.glob("*.specialization.json"))
    if not paths:
        raise TemplateError("no staged LN specialization artifacts found")
    for path in paths:
        obj = loads(path.read_text())
        p = obj["payload"]
        name = artifact_name(p)
        if path.name != name + ".specialization.json":
            raise TemplateError("noncanonical LN specialization filename")
        base = path.parent / name
        if base.with_suffix(".specialization.tex").read_text() != render_tex(obj):
            raise TemplateError("generated LN specialization TeX drift")
        recorded = json.loads(base.with_suffix(".specialization.provenance.json").read_text(),
                              object_pairs_hook=reject_duplicates)
        if recorded != provenance(obj):
            raise TemplateError("LN specialization direct-source provenance drift")
        replayed = "syntax-only"
        if args.lean_runner:
            if from_lean(args.lean_runner, p["family"], p["structural"]) != obj:
                raise TemplateError(
                    "Lean LN specialization replay disagrees with the staged artifact")
            replayed = "Lean-replayed"
        print(f"STAGED_LN_SPECIALIZATION_CHECK|{replayed}|{name}|{obj['template_hash']}")


if __name__ == "__main__":
    main()
