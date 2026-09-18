#!/usr/bin/env python3
"""STAGED L/N0/Npc affine phase-cover certificate: wiring, clauses, Gauss multipliers (item 9).

Lean owns the data: `scripts/w363_ln_cover_export.lean` serializes it and carries the
signature theorems. This module validates that serialization and renders it.

Item 9 is item 6's shape with the multipliers the item-6 artifact left out.
`AffineDeterminantCertificate` is, like `StokesDualityCertificate`, a `Prop` defined by a
conjunction of quantified clauses, consumed as the `determinant` field of the same word
certificate records. It has two clauses, not four, and its multipliers are the Gauss
residues `gaussUnram m = (-1)^n * 2^(n*m)` and `gaussRam m = 2^(n*m)`. Those carry a SIGN
as well as an exponent, which the item-6 multipliers do not, and the sign is a function of
the degree parity alone: minus one for L at odd degree 2h+1, plus one for N0 and Npc at
even degree 2+2h.

What a field binding certifies. As in item 6, proof irrelevance makes
`record.determinant = producer` a STATEMENT identity, not proof identity, and the bridge
kind is `field_statement_identity`.

Where the proof comes from is a separate axis, and the artifact keeps it separate. At N0
and Npc the field is filled by a theorem of the tree. At L it is filled from a field of an
analytic-leaves record supplied as a parameter, and the theorem behind that field is
available only at q = 2^f with f odd. That is the `supply` field, not the bridge kind.
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
SCHEMA = "gq2.w363.ln-phase-cover.v1.staged"
DOMAIN = b"GQ2-W363-LN-PHASE-COVER\0"
PREFIX = "W363_LN_COVER_JSON="
LEAN_FILE = "scripts/w363_ln_cover_export.lean"
BRIDGE = "GQ2.Dyadic.W363LNCover."
CLAUSE_RECORD = "GQ2.Dyadic.AffineDeterminantCertificate"
NUMERICS_RECORD = "GQ2.Dyadic.standardNumerics"
STATEMENT = "field_statement_identity"

LSQ = "GQ2.Dyadic.LSquare."
CN = "GQ2.Dyadic.Instances.WordPhaseCompactNFinal."
NPC = "GQ2.Dyadic.Instances.NpcDeterminantFinal."

PROVENANCE_FILES = (
    LEAN_FILE,
    "GQ2/Dyadic/CertificateMain.lean",
    "GQ2/Dyadic/SourceDataRN.lean",
    "GQ2/Dyadic/Recursion/Numerics.lean",
    "GQ2/Dyadic/Instances/GammaLAnalyticLeaves.lean",
    "GQ2/Dyadic/Instances/GammaLReconstruction.lean",
    "GQ2/Dyadic/Instances/GammaLSourceArfGeneral.lean",
    "GQ2/Dyadic/Instances/WordPhaseCompactNFinal.lean",
    "GQ2/Dyadic/Instances/NpcDeterminantFinal.lean",
    "scripts/w363_ln_cover_tex.py",
)

# The exact wiring table. `supply` records WHERE the proof comes from, which is a different
# axis from `binding_kind`, which records what the equality certifies.
FAMILIES = {
    "L": {"parameters": ("h", "q"), "degree": lambda s: 2 * s["h"] + 1,
          "producer": LSQ + "determinantResidue_lSq_pow",
          "via_field": BRIDGE + "lDeterminant_leaves",
          "record": LSQ + "wordCertificateRN_lSq_of_actionImage",
          "binding": BRIDGE + "lDeterminant_field",
          "supply": "analytic_leaves_record_field"},
    "N0": {"parameters": ("h", "q"), "degree": lambda s: 2 + 2 * s["h"],
           "producer": CN + "wPcN_affineDeterminantCertificate",
           "via_field": None,
           "record": CN + "wPcNWordCertificateRN",
           "binding": BRIDGE + "n0Determinant_field", "supply": "theorem"},
    "Npc": {"parameters": ("h", "q", "r"), "degree": lambda s: 2 + 2 * s["h"],
            "producer": NPC + "npcAffineDeterminantCertificate",
            "via_field": None,
            "record": NPC + "npcWordCertificateRN",
            "binding": BRIDGE + "npcDeterminant_field", "supply": "theorem"},
}

SUPPLIES = ("theorem", "analytic_leaves_record_field")

# The two conjuncts of AffineDeterminantCertificate, in their actual order.
CLAUSES = [(1, "gauss_unramified", "gauss_unram"), (2, "gauss_ramified", "gauss_ram")]

MULTIPLIERS = {
    "gauss_unram": (BRIDGE + "standardNumerics_gaussUnram", lambda n: (-1) ** n),
    "gauss_ram": (BRIDGE + "standardNumerics_gaussRam", lambda n: 1),
}

EXPONENT = "degree_factor * m"
HALF_DIMENSION = "m, with block order 2^(2m) and 1 <= m"

CERTIFICATE_CONDITIONS = {
    "L": "The L determinant is the only one of the three whose scope is a power of two with "
         "an odd exponent rather than a condition on alpha and q, and the only one that "
         "reaches the word certificate through a record field supplied as a parameter "
         "rather than through a theorem. Its unramified Gauss sign is minus one, because "
         "the L degree 2h+1 is odd.",
    "N0": "The N0 determinant is a theorem of the tree at 2 <= alpha with q nonzero and "
          "even. Its unramified Gauss sign is plus one, because the degree 2+2h is even.",
    "Npc": "The Npc determinant is a theorem of the tree at 2 <= alpha with q nonzero and "
           "even and an exact NpcDisplayFor for the semantic unit. Unlike the Npc Stokes "
           "chain, no degree normalization is needed here: producer and record field are "
           "both at 2+2h. Its unramified Gauss sign is plus one.",
}


def digest(payload):
    return hashlib.sha256(DOMAIN + canonical_json(payload).encode()).hexdigest()


def validate_parameters(family, parameters):
    if not isinstance(family, str) or family not in FAMILIES:
        raise TemplateError("family must be L, N0 or Npc")
    fields(parameters, set(FAMILIES[family]["parameters"]), "LN cover structural parameters")
    for name, value in parameters.items():
        integer(value, name, natural=True)


def validate_multiplier(entry, name, degree):
    fields(entry, {"bridge", "degree_factor", "exponent", "sign"}, "LN cover multiplier")
    bridge, sign = MULTIPLIERS[name]
    if entry["bridge"] != bridge:
        raise TemplateError("LN cover multiplier is not bound to the expected Lean bridge")
    if integer(entry["degree_factor"], "degree factor", natural=True) != degree:
        raise TemplateError("LN cover multiplier degree factor is not the degree")
    if entry["exponent"] != EXPONENT:
        raise TemplateError("LN cover multiplier exponent shape is not the expected one")
    if integer(entry["sign"], "multiplier sign") != sign(degree):
        raise TemplateError("LN cover multiplier sign does not follow from the degree parity")


def validate_chain(chain):
    if not isinstance(chain, list) or len(chain) != len(CLAUSES):
        raise TemplateError("LN cover chain must carry every clause exactly once")
    for clause, (position, identifier, multiplier) in zip(chain, CLAUSES):
        fields(clause, {"head_condition", "id", "multiplier", "position", "role"},
               "LN cover clause")
        if clause["id"] != identifier or clause["position"] != position:
            raise TemplateError("LN cover clauses are not in the conjunction's own order")
        if clause["multiplier"] != multiplier:
            raise TemplateError("LN cover clause names the wrong Gauss multiplier")
        for key in ("head_condition", "role"):
            if not isinstance(clause[key], str) or not clause[key]:
                raise TemplateError("LN cover clause " + key + " must be a nonempty string")


def validate(envelope):
    fields(envelope, {"payload", "status", "template_hash"}, "LN cover envelope")
    if envelope["status"] != "STAGED":
        raise TemplateError("LN cover artifacts must remain STAGED")
    p = envelope["payload"]
    fields(p, {"application_scope", "chain", "clause_record", "consumer", "family",
               "hash_scope", "numerics", "producer", "schema", "structural", "warning"},
           "LN cover payload")
    if p["schema"] != SCHEMA:
        raise TemplateError("LN cover schema mismatch")
    validate_parameters(p["family"], p["structural"])
    meta = FAMILIES[p["family"]]
    degree = meta["degree"](p["structural"])
    if p["clause_record"] != CLAUSE_RECORD:
        raise TemplateError("LN cover clause record is not AffineDeterminantCertificate")
    for key in ("application_scope", "hash_scope", "warning"):
        if not isinstance(p[key], str) or not p[key]:
            raise TemplateError("LN cover " + key + " must be a nonempty string")
    validate_chain(p["chain"])
    fields(p["producer"], {"declaration", "degree", "scope", "via_field"}, "LN cover producer")
    if p["producer"]["declaration"] != meta["producer"]:
        raise TemplateError("LN cover producer is not the expected declaration")
    if integer(p["producer"]["degree"], "producer degree", natural=True) != degree:
        raise TemplateError("LN cover producer degree does not match the family")
    if p["producer"]["via_field"] != meta["via_field"]:
        raise TemplateError("LN cover producer supply route is not the expected one")
    if not isinstance(p["producer"]["scope"], str) or not p["producer"]["scope"]:
        raise TemplateError("LN cover producer scope must be a nonempty string")
    fields(p["consumer"], {"binding", "binding_kind", "field", "record", "record_degree",
                           "supply"}, "LN cover consumer")
    if (p["consumer"]["record"] != meta["record"]
            or p["consumer"]["binding"] != meta["binding"]
            or p["consumer"]["supply"] != meta["supply"]):
        raise TemplateError("LN cover consumer is not bound to the expected record/bridges")
    if p["consumer"]["supply"] not in SUPPLIES:
        raise TemplateError("unexpected LN cover supply route")
    if p["consumer"]["binding_kind"] != STATEMENT:
        raise TemplateError("LN cover field bindings are statement identities, nothing more")
    if p["consumer"]["field"] != "determinant":
        raise TemplateError("LN cover consumer must name the determinant field")
    if integer(p["consumer"]["record_degree"], "record degree", natural=True) != degree:
        raise TemplateError("LN cover record degree does not match the declared rank")
    fields(p["numerics"], {"gauss_ram", "gauss_unram", "half_dimension", "record"},
           "LN cover numerics")
    if p["numerics"]["record"] != NUMERICS_RECORD:
        raise TemplateError("LN cover numerics record is not standardNumerics")
    if p["numerics"]["half_dimension"] != HALF_DIMENSION:
        raise TemplateError("LN cover half-dimension description is not the expected one")
    for name in ("gauss_ram", "gauss_unram"):
        validate_multiplier(p["numerics"][name], name, degree)
    if envelope["template_hash"] != digest(p):
        raise TemplateError("LN cover envelope hash mismatch")
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
        raise TemplateError("Lean LN cover exporter failed:\n" + result.stdout + result.stderr)
    records = [line[len(PREFIX):] for line in result.stdout.splitlines()
               if line.startswith(PREFIX)]
    if len(records) != 1:
        raise TemplateError("Lean LN cover exporter must emit exactly one marked artifact")
    obj = loads(records[0])
    if canonical_json(obj) != records[0]:
        raise TemplateError("Lean/Python LN cover canonical JSON mismatch")
    if obj["payload"]["family"] != family or obj["payload"]["structural"] != parameters:
        raise TemplateError("Lean LN cover exporter returned different parameters")
    return obj


def provenance(envelope):
    return {"schema": SCHEMA + ".provenance", "status": "STAGED",
            "template_hash": envelope["template_hash"],
            "scope": "Direct source bytes only; not a transitive build, coefficient module, "
                     "or certificate attestation.",
            "sha256": {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                       for name in PROVENANCE_FILES}}


# ---------------------------------------------------------------- rendering


def multiplier_tex(name, entry):
    call = "gaussUnram" if name == "gauss_unram" else "gaussRam"
    sign = "-" if entry["sign"] < 0 else ""
    return (r"\mathrm{" + call + r"}(m)=" + sign + "2^{" + str(entry["degree_factor"])
            + "m}")


def render_tex(envelope):
    p = validate(envelope)
    family = p["family"]
    lines = [
        "% STAGED L/N affine phase-cover certificate; ledger item 9 only.",
        "% ln-cover-hash: " + envelope["template_hash"],
        "% family: " + family + "; structural: " + canonical_json(p["structural"]),
        "% " + p["application_scope"],
        "% " + p["warning"],
        "% " + p["hash_scope"],
        "% " + CERTIFICATE_CONDITIONS[family],
        "% clause record: " + p["clause_record"],
        "% producer: " + p["producer"]["declaration"]
        + " (degree " + str(p["producer"]["degree"]) + "; scope: "
        + p["producer"]["scope"] + ")",
        "% consumer: " + p["consumer"]["record"] + ", field " + p["consumer"]["field"]
        + " (degree " + str(p["consumer"]["record_degree"]) + ")",
        "% supply route: " + p["consumer"]["supply"],
        "% binding (" + p["consumer"]["binding_kind"] + "): " + p["consumer"]["binding"],
    ]
    if p["producer"]["via_field"]:
        lines.append("% record field carrying the producer: " + p["producer"]["via_field"])
    lines += ["% numerics record: " + p["numerics"]["record"],
              "% half-dimension: " + p["numerics"]["half_dimension"]]
    for name in ("gauss_unram", "gauss_ram"):
        lines.append("% " + name + " bridge: " + p["numerics"][name]["bridge"])
    lines += [r"\begin{enumerate}"]
    for clause in p["chain"]:
        entry = p["numerics"][clause["multiplier"]]
        lines.append(r"\item[(" + str(clause["position"]) + r")] \textbf{"
                     + tex_escape(clause["id"].replace("_", " ")) + "} "
                     + tex_escape(clause["role"])
                     + " Head condition: " + tex_escape(clause["head_condition"]) + ". "
                     + "The degree enters only through $" + multiplier_tex(
                         clause["multiplier"], entry) + "$.")
    lines += [r"\end{enumerate}"]
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------- self-test


def self_test():
    def build(family, structural):
        meta = FAMILIES[family]
        degree = meta["degree"](structural)
        chain = [{"head_condition": "head", "id": identifier, "multiplier": multiplier,
                  "position": position, "role": "role"}
                 for position, identifier, multiplier in CLAUSES]
        numerics = {"record": NUMERICS_RECORD, "half_dimension": HALF_DIMENSION}
        for name, (bridge, sign) in MULTIPLIERS.items():
            numerics[name] = {"bridge": bridge, "degree_factor": degree,
                              "exponent": EXPONENT, "sign": sign(degree)}
        return {"application_scope": "scope", "chain": chain,
                "clause_record": CLAUSE_RECORD,
                "consumer": {"binding": meta["binding"], "binding_kind": STATEMENT,
                             "field": "determinant", "record": meta["record"],
                             "record_degree": degree, "supply": meta["supply"]},
                "family": family, "hash_scope": "hash scope", "numerics": numerics,
                "producer": {"declaration": meta["producer"], "degree": degree,
                             "scope": "scope", "via_field": meta["via_field"]},
                "schema": SCHEMA, "structural": structural, "warning": "warning"}

    def wrap(p):
        return {"payload": p, "status": "STAGED", "template_hash": digest(p)}

    base = build("L", {"h": 0, "q": 2})
    obj = wrap(base)
    assert loads(canonical_json(obj)) == obj
    assert "ln-cover-hash" in render_tex(obj)
    assert "analytic_leaves_record_field" in render_tex(obj)
    # the odd L degree makes the unramified Gauss sign negative; the even families' is not
    assert r"\mathrm{gaussUnram}(m)=-2^{1m}" in render_tex(obj)
    n0 = wrap(build("N0", {"h": 0, "q": 2}))
    assert loads(canonical_json(n0)) == n0
    assert r"\mathrm{gaussUnram}(m)=2^{2m}" in render_tex(n0)
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
        lambda p: p.update(clause_record="GQ2.Dyadic.StokesDualityCertificate"),
        lambda p: p["structural"].update(h=1),
        lambda p: p["structural"].update(q=-1),
        lambda p: p["structural"].update(r=2),
        lambda p: p["chain"].pop(),
        lambda p: p["chain"].reverse(),
        lambda p: p["chain"][0].update(id="gauss_ramified"),
        lambda p: p["chain"][0].update(position=2),
        lambda p: p["chain"][0].update(multiplier="gauss_ram"),
        lambda p: p["chain"][0].update(head_condition=""),
        lambda p: p["producer"].update(declaration=LSQ + "other"),
        lambda p: p["producer"].update(degree=3),
        lambda p: p["producer"].update(scope=""),
        # the supply route is a separate axis from the bridge kind and is pinned per family
        lambda p: p["producer"].update(via_field=None),
        lambda p: p["consumer"].update(supply="theorem"),
        lambda p: p["consumer"].update(record=CN + "other"),
        lambda p: p["consumer"].update(binding=BRIDGE + "other"),
        lambda p: p["consumer"].update(binding_kind="record_target"),
        lambda p: p["consumer"].update(field="stokes"),
        lambda p: p["consumer"].update(record_degree=2),
        lambda p: p["numerics"].update(record="GQ2.Dyadic.SourceNumerics"),
        lambda p: p["numerics"].update(half_dimension="m"),
        # the sign follows from the degree parity and may not be asserted independently
        lambda p: p["numerics"]["gauss_unram"].update(sign=1),
        lambda p: p["numerics"]["gauss_ram"].update(sign=-1),
        lambda p: p["numerics"]["gauss_unram"].update(degree_factor=2),
        lambda p: p["numerics"]["gauss_unram"].update(exponent="n * m"),
        lambda p: p["numerics"]["gauss_ram"].update(bridge=BRIDGE + "other"),
        lambda p: p["numerics"].pop("gauss_ram"),
    ]
    for mutate in mutations:
        try:
            validate(mutated(mutate))
        except TemplateError:
            count += 1
        else:
            raise AssertionError("malformed LN cover artifact accepted")
    for bad in ("[]", "null", "NaN", "Infinity", '{"payload":0,"payload":0}',
                canonical_json(obj).replace('"h":0', '"h":0,"h":0'),
                canonical_json(obj).replace('"STAGED"', '"APPROVED"'),
                canonical_json(obj).replace(obj["template_hash"], "0" * 64),
                canonical_json(obj).replace('"position":1', '"position":3', 1)):
        try:
            loads(bad)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("malformed LN cover JSON accepted")
    for family, parameters in (("L", {"h": 0}), ("Npc", {"h": 0, "q": 2}),
                               ("M0", {"h": 0, "q": 2}), ("L", {"h": -1, "q": 2})):
        try:
            validate_parameters(family, parameters)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid LN cover parameters accepted")
    print(f"LN_COVER_SELF_TEST_PASS|{count}")
    return count


def artifact_name(payload):
    family, s = payload["family"], payload["structural"]
    return family + "-cover-" + "-".join(name + str(s[name])
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
            raise TemplateError("LN cover output must be inside general-ln-certificate-staged")
        obj = from_lean(args.lean_runner, args.family, parameters)
        args.out.mkdir(parents=True, exist_ok=True)
        base = args.out / artifact_name(obj["payload"])
        base.with_suffix(".cover.json").write_text(canonical_json(obj) + "\n")
        base.with_suffix(".cover.tex").write_text(render_tex(obj))
        base.with_suffix(".cover.provenance.json").write_text(
            canonical_json(provenance(obj)) + "\n")
        print(f"STAGED_LN_COVER_GENERATED|{base.name}|{obj['template_hash']}")
        return
    paths = sorted(args.directory.glob("*.cover.json"))
    if not paths:
        raise TemplateError("no staged LN cover artifacts found")
    for path in paths:
        obj = loads(path.read_text())
        p = obj["payload"]
        name = artifact_name(p)
        if path.name != name + ".cover.json":
            raise TemplateError("noncanonical LN cover filename")
        base = path.parent / name
        if base.with_suffix(".cover.tex").read_text() != render_tex(obj):
            raise TemplateError("generated LN cover TeX drift")
        recorded = json.loads(base.with_suffix(".cover.provenance.json").read_text(),
                              object_pairs_hook=reject_duplicates)
        if recorded != provenance(obj):
            raise TemplateError("LN cover direct-source provenance drift")
        replayed = "syntax-only"
        if args.lean_runner:
            if from_lean(args.lean_runner, p["family"], p["structural"]) != obj:
                raise TemplateError("Lean LN cover replay disagrees with the staged artifact")
            replayed = "Lean-replayed"
        print(f"STAGED_LN_COVER_CHECK|{replayed}|{name}|{obj['template_hash']}")


if __name__ == "__main__":
    main()
