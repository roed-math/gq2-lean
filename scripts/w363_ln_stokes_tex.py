#!/usr/bin/env python3
"""STAGED L/N0/Npc Stokes chain: wiring, clause structure, multipliers (ledger item 6).

Lean owns the data: `scripts/w363_ln_stokes_export.lean` serializes it and carries the
signature theorems. This module validates that serialization and renders it.

What this display is NOT. `StokesDualityCertificate` is a `Prop`, a four-fold conjunction
of universally quantified counting and separation statements; there is no matrix, chain
complex object or coefficient tree to serialize, and none is invented here. The generated
display carries the three parts of item 6 that genuinely are data -- which declaration
proves the chain, which record field consumes it, the four clauses in their actual order,
and the literal `standardNumerics` exponents the two counting clauses assert -- and says
so in every artifact. The clause statements themselves stay in the packet's stored proofs
transcript.

What a field binding certifies. Lean has definitional proof irrelevance, so
`record.stokes = producer` is `rfl` for any producer whose type is the field's type. The
binding therefore certifies a STATEMENT identity: the producer proves exactly the statement
the record's field demands, at the record's own parameters. It does not certify that the
record was built from that proof term. The artifact's `binding_kind` is
`field_statement_identity`, deliberately not the `record_target` that the item 3 and item
4/5 exporters use for a genuine data field.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from w361_general_word_tex import TemplateError, canonical_json, fields, integer, reject_duplicates

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "gq2.w363.ln-stokes-chain.v1.staged"
DOMAIN = b"GQ2-W363-LN-STOKES-CHAIN\0"
PREFIX = "W363_LN_STOKES_JSON="
LEAN_FILE = "scripts/w363_ln_stokes_export.lean"
BRIDGE = "GQ2.Dyadic.W363LNStokes."
CLAUSE_RECORD = "GQ2.Dyadic.StokesDualityCertificate"
NUMERICS_RECORD = "GQ2.Dyadic.standardNumerics"

STATEMENT = "field_statement_identity"
NORMALIZED = "degree_normalized_field"

PROVENANCE_FILES = (
    LEAN_FILE,
    "GQ2/Dyadic/CertificateMain.lean",
    "GQ2/Dyadic/SourceDataRN.lean",
    "GQ2/Dyadic/Recursion/Numerics.lean",
    "GQ2/Dyadic/Instances/GammaLAnalyticLeaves.lean",
    "GQ2/Dyadic/Instances/GammaLReconstruction.lean",
    "GQ2/Dyadic/Instances/WordPhase.lean",
    "GQ2/Dyadic/Instances/WordPhaseCompactNFinal.lean",
    "GQ2/Dyadic/Instances/NpcCandidateStokes.lean",
    "GQ2/Dyadic/Instances/NpcCandidateRN.lean",
    "scripts/w363_ln_stokes_tex.py",
)

I = "GQ2.Dyadic.Instances."

# The exact wiring table. A payload naming a different producer, record or bridge is
# rejected: matching shapes are not a certificate identity, only these declarations are.
FAMILIES = {
    "L": {"parameters": ("h", "q"), "degree": lambda s: 2 * s["h"] + 1,
          "producer": "GQ2.Dyadic.LSquare.stokesDualityCertificate_of_actionImage",
          "producer_degree": lambda s: 2 * s["h"] + 1,
          "record": "GQ2.Dyadic.LSquare.wordCertificateRN_lSq_of_actionImage",
          "binding": BRIDGE + "lStokes_field", "binding_kind": STATEMENT,
          "normalization": None},
    "N0": {"parameters": ("h", "q"), "degree": lambda s: 2 + 2 * s["h"],
           "producer": I + "WordPhase.wPh_nCand_stokes",
           "producer_degree": lambda s: 2 + 2 * s["h"],
           "record": I + "WordPhaseCompactNFinal.wPcNWordCertificateRN",
           "binding": BRIDGE + "n0Stokes_field", "binding_kind": STATEMENT,
           "normalization": None},
    "Npc": {"parameters": ("h", "q", "r"), "degree": lambda s: 2 + 2 * s["h"],
            "producer": I + "NpcCandidateStokes.npcCand_stokes",
            # stated at 2h+2, which is numerically equal at every instance but is a
            # different spelling; the record's field is at 2+2h
            "producer_degree": lambda s: 2 * s["h"] + 2,
            "record": I + "NpcCandidateRN.npcWordCertificateRN_of_determinant",
            "binding": BRIDGE + "npcStokes_typeNormalization",
            "binding_kind": NORMALIZED,
            "normalization": BRIDGE + "npcStokes_degreeNormalization"},
}

# The four conjuncts of StokesDualityCertificate, in their actual order. Two carry a count
# whose degree-dependence is a standardNumerics multiplier; two do not.
CLAUSES = [
    (1, "tcocycle_count", "t_mult"),
    (2, "separation", None),
    (3, "nondegeneracy", None),
    (4, "vcocycle_count", "h1_mult"),
]

MULTIPLIERS = {
    "t_mult": ("card T", BRIDGE + "standardNumerics_tMult", lambda n: n + 1),
    "h1_mult": ("card V", BRIDGE + "standardNumerics_h1Mult", lambda n: n),
}

MULTIPLIER_TEX = {"t_mult": ("tMult", "T"), "h1_mult": ("h1Mult", "V")}

CERTIFICATE_CONDITIONS = {
    "L": "The L chain is produced by the direct action-image route; its scope is the "
         "record's own, and the selected field endpoint retains the ramified-i hypothesis.",
    "N0": "The N0 producer binds 2 <= alpha, q nonzero AND Even q; it is not unconditional "
          "in the literal sense, and the module's own header records that correction.",
    "Npc": "The Npc producer is stated at degree 2h+2 and the record's stokes field at "
           "2+2h. Those two spellings agree at every numeric instance, so the exported "
           "degrees look equal, but they are NOT definitionally equal at a variable h: the "
           "record's field is filled by rewriting along the normalization named below. That "
           "is why the Npc binding kind differs from the L and N0 one.",
}


def digest(payload):
    return hashlib.sha256(DOMAIN + canonical_json(payload).encode()).hexdigest()


def validate_parameters(family, parameters):
    if not isinstance(family, str) or family not in FAMILIES:
        raise TemplateError("family must be L, N0 or Npc")
    fields(parameters, set(FAMILIES[family]["parameters"]), "LN Stokes structural parameters")
    for name, value in parameters.items():
        integer(value, name, natural=True)


def validate_multiplier(entry, name, degree):
    fields(entry, {"argument", "bridge", "exponent"}, "LN Stokes multiplier")
    argument, bridge, exponent = MULTIPLIERS[name]
    if entry["argument"] != argument or entry["bridge"] != bridge:
        raise TemplateError("LN Stokes multiplier is not bound to the expected Lean bridge")
    if integer(entry["exponent"], "multiplier exponent", natural=True) != exponent(degree):
        raise TemplateError("LN Stokes multiplier exponent does not match the degree")


def validate_chain(chain):
    if not isinstance(chain, list) or len(chain) != len(CLAUSES):
        raise TemplateError("LN Stokes chain must carry every clause exactly once")
    for clause, (position, identifier, multiplier) in zip(chain, CLAUSES):
        fields(clause, {"count", "id", "position", "role"}, "LN Stokes clause")
        if clause["id"] != identifier or clause["position"] != position:
            raise TemplateError("LN Stokes clauses are not in the conjunction's own order")
        if not isinstance(clause["role"], str) or not clause["role"]:
            raise TemplateError("LN Stokes clause role must be a nonempty string")
        if multiplier is None:
            if clause["count"] is not None:
                raise TemplateError("a noncounting LN Stokes clause carries no count")
            continue
        fields(clause["count"], {"multiplier", "shape"}, "LN Stokes clause count")
        if clause["count"]["multiplier"] != multiplier:
            raise TemplateError("LN Stokes counting clause names the wrong multiplier")
        if not isinstance(clause["count"]["shape"], str) or not clause["count"]["shape"]:
            raise TemplateError("LN Stokes count shape must be a nonempty string")


def validate(envelope):
    fields(envelope, {"payload", "status", "template_hash"}, "LN Stokes envelope")
    if envelope["status"] != "STAGED":
        raise TemplateError("LN Stokes artifacts must remain STAGED")
    p = envelope["payload"]
    fields(p, {"application_scope", "chain", "clause_record", "consumer", "family",
               "hash_scope", "numerics", "producer", "schema", "structural", "warning"},
           "LN Stokes payload")
    if p["schema"] != SCHEMA:
        raise TemplateError("LN Stokes schema mismatch")
    validate_parameters(p["family"], p["structural"])
    meta = FAMILIES[p["family"]]
    structural = p["structural"]
    degree = meta["degree"](structural)
    if p["clause_record"] != CLAUSE_RECORD:
        raise TemplateError("LN Stokes clause record is not StokesDualityCertificate")
    for key in ("application_scope", "hash_scope", "warning"):
        if not isinstance(p[key], str) or not p[key]:
            raise TemplateError("LN Stokes " + key + " must be a nonempty string")
    validate_chain(p["chain"])
    fields(p["producer"], {"declaration", "degree"}, "LN Stokes producer")
    if p["producer"]["declaration"] != meta["producer"]:
        raise TemplateError("LN Stokes producer is not the expected declaration")
    if (integer(p["producer"]["degree"], "producer degree", natural=True)
            != meta["producer_degree"](structural)):
        raise TemplateError("LN Stokes producer degree does not match the family")
    fields(p["consumer"], {"binding", "binding_kind", "field", "normalization", "record",
                           "record_degree"}, "LN Stokes consumer")
    if (p["consumer"]["record"] != meta["record"]
            or p["consumer"]["binding"] != meta["binding"]
            or p["consumer"]["binding_kind"] != meta["binding_kind"]
            or p["consumer"]["normalization"] != meta["normalization"]):
        raise TemplateError("LN Stokes consumer is not bound to the expected record/bridges")
    if p["consumer"]["field"] != "stokes":
        raise TemplateError("LN Stokes consumer must name the stokes field")
    if integer(p["consumer"]["record_degree"], "record degree", natural=True) != degree:
        raise TemplateError("LN Stokes record degree does not match the declared rank")
    fields(p["numerics"], {"h1_mult", "record", "t_mult"}, "LN Stokes numerics")
    if p["numerics"]["record"] != NUMERICS_RECORD:
        raise TemplateError("LN Stokes numerics record is not standardNumerics")
    for name in ("h1_mult", "t_mult"):
        validate_multiplier(p["numerics"][name], name, degree)
    if envelope["template_hash"] != digest(p):
        raise TemplateError("LN Stokes envelope hash mismatch")
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
        raise TemplateError("Lean LN Stokes exporter failed:\n" + result.stdout + result.stderr)
    records = [line[len(PREFIX):] for line in result.stdout.splitlines()
               if line.startswith(PREFIX)]
    if len(records) != 1:
        raise TemplateError("Lean LN Stokes exporter must emit exactly one marked artifact")
    obj = loads(records[0])
    if canonical_json(obj) != records[0]:
        raise TemplateError("Lean/Python LN Stokes canonical JSON mismatch")
    if obj["payload"]["family"] != family or obj["payload"]["structural"] != parameters:
        raise TemplateError("Lean LN Stokes exporter returned different parameters")
    return obj


def provenance(envelope):
    return {"schema": SCHEMA + ".provenance", "status": "STAGED",
            "template_hash": envelope["template_hash"],
            "scope": "Direct source bytes only; not a transitive build, coefficient module, "
                     "or certificate attestation.",
            "sha256": {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                       for name in PROVENANCE_FILES}}


# ---------------------------------------------------------------- rendering


def tex_escape(text):
    for old, new in (("\\", r"\textbackslash{}"), ("_", r"\_"), ("&", r"\&"),
                     ("%", r"\%"), ("$", r"\$"), ("#", r"\#"), ("{", r"\{"),
                     ("}", r"\}"), ("~", r"\textasciitilde{}"), ("^", r"\textasciicircum{}")):
        text = text.replace(old, new)
    return text


def multiplier_tex(name, entry):
    call, symbol = MULTIPLIER_TEX[name]
    exponent = entry["exponent"]
    body = (r"\lvert " + symbol + r"\rvert") + ("" if exponent == 1 else "^{" + str(exponent) + "}")
    return r"\mathrm{" + call + r"}\bigl(\lvert " + symbol + r"\rvert\bigr)=" + body


def render_tex(envelope):
    p = validate(envelope)
    family = p["family"]
    lines = [
        "% STAGED L/N Stokes chain; ledger item 6 only.",
        "% ln-stokes-hash: " + envelope["template_hash"],
        "% family: " + family + "; structural: " + canonical_json(p["structural"]),
        "% " + p["application_scope"],
        "% " + p["warning"],
        "% " + p["hash_scope"],
        "% " + CERTIFICATE_CONDITIONS[family],
        "% clause record: " + p["clause_record"],
        "% producer: " + p["producer"]["declaration"]
        + " (stated at degree " + str(p["producer"]["degree"]) + ")",
        "% consumer: " + p["consumer"]["record"] + ", field " + p["consumer"]["field"]
        + " (at degree " + str(p["consumer"]["record_degree"]) + ")",
        "% binding (" + p["consumer"]["binding_kind"] + "): " + p["consumer"]["binding"],
    ]
    if p["consumer"]["normalization"]:
        lines.append("% degree normalization: " + p["consumer"]["normalization"])
    lines += ["% numerics record: " + p["numerics"]["record"]]
    for name in ("t_mult", "h1_mult"):
        lines.append("% " + name + " bridge: " + p["numerics"][name]["bridge"])
    lines += [r"\begin{enumerate}"]
    for clause in p["chain"]:
        item = (r"\item[(" + str(clause["position"]) + r")] \textbf{"
                + tex_escape(clause["id"].replace("_", " ")) + "} "
                + tex_escape(clause["role"]))
        if clause["count"] is not None:
            item += (" The degree enters only through $"
                     + multiplier_tex(clause["count"]["multiplier"],
                                      p["numerics"][clause["count"]["multiplier"]]) + "$.")
        lines.append(item)
    lines += [r"\end{enumerate}"]
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------- self-test


def self_test():
    def build(family, structural):
        meta = FAMILIES[family]
        degree = meta["degree"](structural)
        chain = []
        for position, identifier, multiplier in CLAUSES:
            count = None if multiplier is None else {"multiplier": multiplier,
                                                     "shape": "shape"}
            chain.append({"count": count, "id": identifier, "position": position,
                          "role": "role"})
        numerics = {"record": NUMERICS_RECORD}
        for name, (argument, bridge, exponent) in MULTIPLIERS.items():
            numerics[name] = {"argument": argument, "bridge": bridge,
                              "exponent": exponent(degree)}
        return {"application_scope": "scope", "chain": chain,
                "clause_record": CLAUSE_RECORD,
                "consumer": {"binding": meta["binding"],
                             "binding_kind": meta["binding_kind"], "field": "stokes",
                             "normalization": meta["normalization"],
                             "record": meta["record"], "record_degree": degree},
                "family": family, "hash_scope": "hash scope", "numerics": numerics,
                "producer": {"declaration": meta["producer"],
                             "degree": meta["producer_degree"](structural)},
                "schema": SCHEMA, "structural": structural, "warning": "warning"}

    def wrap(p):
        return {"payload": p, "status": "STAGED", "template_hash": digest(p)}

    base = build("L", {"h": 0, "q": 2})
    obj = wrap(base)
    assert loads(canonical_json(obj)) == obj
    assert "ln-stokes-hash" in render_tex(obj)
    assert "field_statement_identity" in render_tex(obj)
    assert r"\mathrm{tMult}" in render_tex(obj) and r"\mathrm{h1Mult}" in render_tex(obj)
    npc = wrap(build("Npc", {"h": 2, "q": 2, "r": 1}))
    assert loads(canonical_json(npc)) == npc
    assert BRIDGE + "npcStokes_degreeNormalization" in render_tex(npc)
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
        lambda p: p.update(warning=3),
        lambda p: p.pop("hash_scope"),
        lambda p: p.update(clause_record="GQ2.Dyadic.ScalarHilbertCertificate"),
        lambda p: p["structural"].update(h=1),
        lambda p: p["structural"].update(q=-1),
        lambda p: p["structural"].update(r=2),
        lambda p: p["chain"].pop(),
        lambda p: p["chain"].reverse(),
        lambda p: p["chain"][0].update(id="separation"),
        lambda p: p["chain"][0].update(position=2),
        lambda p: p["chain"][0].update(role=""),
        lambda p: p["chain"][0].update(count=None),
        lambda p: p["chain"][0]["count"].update(multiplier="h1_mult"),
        # a noncounting clause may not acquire a count
        lambda p: p["chain"][1].update(count={"multiplier": "t_mult", "shape": "s"}),
        lambda p: p["producer"].update(declaration=I + "other"),
        lambda p: p["producer"].update(degree=4),
        lambda p: p["consumer"].update(record=I + "other"),
        lambda p: p["consumer"].update(binding=BRIDGE + "other"),
        # the strength of the claim is part of the artifact: L may not be relabelled as a
        # degree-normalized binding, and a normalization may not appear from nowhere
        lambda p: p["consumer"].update(binding_kind=NORMALIZED),
        lambda p: p["consumer"].update(normalization=BRIDGE + "npcStokes_degreeNormalization"),
        lambda p: p["consumer"].update(field="scalar"),
        lambda p: p["consumer"].update(record_degree=3),
        lambda p: p["numerics"].update(record="GQ2.Dyadic.SourceNumerics"),
        lambda p: p["numerics"]["t_mult"].update(exponent=3),
        lambda p: p["numerics"]["h1_mult"].update(exponent=2),
        lambda p: p["numerics"]["t_mult"].update(bridge=BRIDGE + "other"),
        lambda p: p["numerics"]["t_mult"].update(argument="card V"),
        lambda p: p["numerics"].pop("h1_mult"),
    ]
    for mutate in mutations:
        try:
            validate(mutated(mutate))
        except TemplateError:
            count += 1
        else:
            raise AssertionError("malformed LN Stokes artifact accepted")
    for bad in ("[]", "null", "NaN", "Infinity", '{"payload":0,"payload":0}',
                canonical_json(obj).replace('"h":0', '"h":0,"h":0'),
                canonical_json(obj).replace('"STAGED"', '"APPROVED"'),
                canonical_json(obj).replace(obj["template_hash"], "0" * 64),
                canonical_json(obj).replace('"position":1', '"position":9', 1)):
        try:
            loads(bad)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("malformed LN Stokes JSON accepted")
    for family, parameters in (("L", {"h": 0}), ("Npc", {"h": 0, "q": 2}),
                               ("M0", {"h": 0, "q": 2}), ("L", {"h": -1, "q": 2})):
        try:
            validate_parameters(family, parameters)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid LN Stokes parameters accepted")
    print(f"LN_STOKES_SELF_TEST_PASS|{count}")
    return count


def artifact_name(payload):
    family, s = payload["family"], payload["structural"]
    return family + "-stokes-" + "-".join(name + str(s[name])
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
            raise TemplateError("LN Stokes output must be inside general-ln-certificate-staged")
        obj = from_lean(args.lean_runner, args.family, parameters)
        args.out.mkdir(parents=True, exist_ok=True)
        base = args.out / artifact_name(obj["payload"])
        base.with_suffix(".stokes.json").write_text(canonical_json(obj) + "\n")
        base.with_suffix(".stokes.tex").write_text(render_tex(obj))
        base.with_suffix(".stokes.provenance.json").write_text(
            canonical_json(provenance(obj)) + "\n")
        print(f"STAGED_LN_STOKES_GENERATED|{base.name}|{obj['template_hash']}")
        return
    paths = sorted(args.directory.glob("*.stokes.json"))
    if not paths:
        raise TemplateError("no staged LN Stokes artifacts found")
    for path in paths:
        obj = loads(path.read_text())
        p = obj["payload"]
        name = artifact_name(p)
        if path.name != name + ".stokes.json":
            raise TemplateError("noncanonical LN Stokes filename")
        base = path.parent / name
        if base.with_suffix(".stokes.tex").read_text() != render_tex(obj):
            raise TemplateError("generated LN Stokes TeX drift")
        recorded = json.loads(base.with_suffix(".stokes.provenance.json").read_text(),
                              object_pairs_hook=reject_duplicates)
        if recorded != provenance(obj):
            raise TemplateError("LN Stokes direct-source provenance drift")
        replayed = "syntax-only"
        if args.lean_runner:
            if from_lean(args.lean_runner, p["family"], p["structural"]) != obj:
                raise TemplateError("Lean LN Stokes replay disagrees with the staged artifact")
            replayed = "Lean-replayed"
        print(f"STAGED_LN_STOKES_CHECK|{replayed}|{name}|{obj['template_hash']}")


if __name__ == "__main__":
    main()
