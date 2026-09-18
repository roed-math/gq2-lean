#!/usr/bin/env python3
"""STAGED all-parameter L/N word export/replay, reusing frozen S1.1 read-only.

No second word grammar or Python family factory is introduced. Lean emits the
existing canonical RawWord AST; dyadic_word_tex validates/renders that AST.
The old word hash stays unchanged. A new envelope hash binds the exact requested
parameters and rank-uniform semantic bridge. This is not a ten-item certificate
packet or approval to migrate the frozen manifest/appendices.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re
import subprocess

import dyadic_word_tex as legacy
from w361_general_word_tex import TemplateError, canonical_json, fields, integer, reject_duplicates

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "gq2.w361.ln-word.v1.staged"
DOMAIN = b"GQ2-W361-LN-WORD\0"
PREFIX = "W361_LN_WORD_JSON="
LEAN_FILE = "GQ2/Dyadic/Word/GeneralTemplateLNExport.lean"
OUTPUT_COMPONENT = "general-ln-template-staged"
PROVENANCE_SCHEMA = "gq2.w361.ln-word-provenance.v1.staged"
BRIDGE_ROOT = "GQ2.Dyadic.GeneralTemplateLN."
WORDS_ROOT = "GQ2.Dyadic.Words."
FAMILIES = {
    "L": {"parameters": ("h",), "factory": WORDS_ROOT+"LSq.rawLsq",
          "binding": WORDS_ROOT+"LSq.denoteCtx", "bridge": BRIDGE_ROOT+"denote_canon_rawLsq",
          "semantic_target": WORDS_ROOT+"LSq.lSqW", "unit_bridge": None,
          "auxiliary": {"a", "c", "y1", "sigma2"}},
    "N0": {"parameters": ("alpha", "h"), "factory": WORDS_ROOT+"rawNCompact",
           "binding": WORDS_ROOT+"denoteCtx", "bridge": BRIDGE_ROOT+"denote_canon_rawNCompact",
           "semantic_target": WORDS_ROOT+"nCompactW", "unit_bridge": None, "auxiliary": set()},
    "Npc": {"parameters": ("alpha", "r", "h", "num", "den"), "factory": WORDS_ROOT+"Npc.rawNpc",
            "binding": WORDS_ROOT+"denoteCtx", "bridge": BRIDGE_ROOT+"denote_canon_rawNpc",
            "semantic_target": WORDS_ROOT+"Npc.npcW",
            "unit_bridge": BRIDGE_ROOT+"denote_canon_rawNpc_display", "auxiliary": {"d0", "u0"}},
}
PROVENANCE_FILES = (
    LEAN_FILE, "GQ2/Dyadic/Word/GeneralTemplateLNCanonical.lean",
    "GQ2/Dyadic/Word/GeneralTemplateLN.lean", "GQ2/Dyadic/Word/Export.lean",
    "GQ2/Dyadic/Word/Syntax.lean", "GQ2/Dyadic/Words/L.lean",
    "GQ2/Dyadic/Words/N0.lean", "GQ2/Dyadic/Words/Npc.lean", "GQ2/Dyadic/SelectedEta.lean",
    "scripts/dyadic_word_tex.py", "scripts/w361_general_word_tex.py",
    "scripts/w361_general_ln_word_tex.py",
)


def digest(payload):
    return hashlib.sha256(DOMAIN + canonical_json(payload).encode()).hexdigest()


def validate_parameters(family, parameters):
    if not isinstance(family, str) or family not in FAMILIES:
        raise TemplateError("family must be L, N0 or Npc")
    fields(parameters, set(FAMILIES[family]["parameters"]), "LN structural parameters")
    for name, value in parameters.items():
        integer(value, name, natural=name not in ("num", "den"))
    if family == "Npc" and any(parameters[name] % 2 == 0 for name in ("num", "den")):
        raise TemplateError("Npc requires exact odd numerator and denominator")


def validate_tree(tree, family, parameters, degree):
    try:
        normalized = legacy.canon_word(tree)
    except (legacy.WordError, TypeError, KeyError) as exc:
        raise TemplateError("invalid legacy AST: " + str(exc)) from exc
    if normalized != tree:
        raise TemplateError("exported legacy AST must already be constructor-canonical")
    handles = 0
    h = parameters["h"]
    for node in legacy.walk(normalized):
        op = node["op"]
        if op in ("Shadow", "OrbitNorm"):
            raise TemplateError("unresolved/unused derived syntax is not allowed in L/N exports")
        if op == "Generator":
            name = node["name"]
            if name not in ("sigma", "tau"):
                if re.fullmatch(r"x(?:0|[1-9][0-9]*)", name) is None or int(name[1:]) > degree:
                    raise TemplateError("generator is outside the declared L/N alphabet")
        elif op == "Auxiliary":
            if node["name"] not in FAMILIES[family]["auxiliary"]:
                raise TemplateError("unexpected L/N auxiliary name")
        elif op == "IntegerPower":
            if node["exponent"]["type"] != "Int":
                raise TemplateError("actual raw factories use concrete integer exponents")
        elif op == "ZhatPower":
            spec = node["exponent_spec"]
            if family != "Npc" or spec["type"] != "EtaHat":
                raise TemplateError("unexpected L/N profinite exponent")
            expected = legacy.canon_spec({"type": "EtaHat", "num": parameters["num"], "den": parameters["den"]})
            if spec != expected:
                raise TemplateError("EtaHat does not represent the exact requested display")
        elif op == "HyperbolicHandles":
            handles += 1
            if (node["start_index"] != (2 if family == "L" else 3)
                    or node["count"] != {"type": "Int", "value": h}):
                raise TemplateError("handle block does not match the actual rank/alphabet")
    if handles != (0 if family == "L" and h == 0 else 1):
        raise TemplateError("wrong number of raw handle blocks")
    # Reject ambiguous reused auxiliary names through the frozen renderer too.
    try:
        legacy.render_word(normalized)
    except legacy.LatexError as exc:
        raise TemplateError(str(exc)) from exc


def validate(envelope):
    fields(envelope, {"payload", "status", "template_hash"}, "LN envelope")
    if envelope["status"] != "STAGED":
        raise TemplateError("LN artifacts must remain STAGED")
    p = envelope["payload"]
    fields(p, {"alphabet_degree", "ast_schema_version", "binding", "bridge", "factory", "family",
               "schema", "semantic_target", "structural", "tree", "unit_bridge", "word_hash"}, "LN payload")
    if p["schema"] != SCHEMA or integer(p["ast_schema_version"], "AST schema") != legacy.AST_SCHEMA_VERSION:
        raise TemplateError("LN or legacy AST schema mismatch")
    validate_parameters(p["family"], p["structural"])
    family, parameters = p["family"], p["structural"]
    metadata = FAMILIES[family]
    for name in ("binding", "bridge", "factory", "semantic_target", "unit_bridge"):
        if p[name] != metadata[name]:
            raise TemplateError("LN semantic identity mismatch: " + name)
    degree = integer(p["alphabet_degree"], "alphabet degree", natural=True)
    if degree != 2*parameters["h"] + (1 if family == "L" else 2):
        raise TemplateError("LN alphabet degree/rank mismatch")
    validate_tree(p["tree"], family, parameters, degree)
    if p["word_hash"] != legacy.content_hash(p["tree"]):
        raise TemplateError("legacy word hash mismatch")
    if envelope["template_hash"] != digest(p):
        raise TemplateError("LN envelope hash mismatch")
    return p


def loads(text):
    obj = json.loads(text, object_pairs_hook=reject_duplicates,
                     parse_constant=lambda x: (_ for _ in ()).throw(TemplateError(x)))
    validate(obj)
    return obj


def from_lean(runner, family, parameters):
    validate_parameters(family, parameters)
    args = [family] + [str(parameters[name]) for name in FAMILIES[family]["parameters"]]
    result = subprocess.run(["bash", str(Path(runner).resolve()), "--run", LEAN_FILE]+args,
                            cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise TemplateError("Lean LN exporter failed:\n"+result.stdout+result.stderr)
    records = [line[len(PREFIX):] for line in result.stdout.splitlines() if line.startswith(PREFIX)]
    if len(records) != 1:
        raise TemplateError("Lean LN exporter must emit exactly one marked artifact")
    obj = loads(records[0])
    if canonical_json(obj) != records[0]:
        raise TemplateError("Lean/Python LN canonical JSON mismatch")
    if obj["payload"]["family"] != family or obj["payload"]["structural"] != parameters:
        raise TemplateError("Lean LN exporter returned different parameters")
    return obj


def artifact_name(payload):
    family, p = payload["family"], payload["structural"]
    return family + "-" + "-".join(name+str(p[name]) for name in FAMILIES[family]["parameters"])


def provenance(envelope):
    return {"schema": PROVENANCE_SCHEMA, "status": "STAGED",
            "template_hash": envelope["template_hash"],
            "scope": "Direct source bytes only; not a transitive build or coefficient/certificate attestation.",
            "sha256": {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in PROVENANCE_FILES}}


def render_tex(envelope):
    p = validate(envelope)
    family, params, tree = p["family"], p["structural"], p["tree"]
    lines = ["% STAGED unchanged legacy L/N factory export, not a ten-item certificate packet.",
             "% envelope-hash: "+envelope["template_hash"], "% ast-hash: "+p["word_hash"],
             "% factory: "+p["factory"], "% binding: "+p["binding"], "% exact bridge: "+p["bridge"],
             "% requested parameters: "+canonical_json(params),
             "% Hashes include the unexpanded handle/auxiliary tree, not only the displayed formula."]
    for name, body in legacy.auxiliary_definitions(tree):
        lines.append(r"\["+name+"="+body+r".\]")
    lines.append(r"\[R="+legacy.render_word(tree)+r".\]")
    if family == "L":
        lines.append("% Syntax is valid for every h; the existing full L certificate additionally requires q=2^f with odd f.")
    elif family == "N0":
        lines.append("% Syntax allows every natural alpha,h; the complete N0 certificate requires alpha>=2 and nonzero even q.")
    else:
        canonical_eta = legacy.canon_spec({"type": "EtaHat", "num": params["num"], "den": params["den"]})
        lines += [r"\[\eta=\frac{"+str(params["num"])+"}{"+str(params["den"])+"}="+
                  r"\frac{"+str(canonical_eta["num"])+"}{"+str(canonical_eta["den"])+r"}\in\mathbf Z_2^\times.\]",
                  "% EtaHat has this exact two-adic component and odd-primary components one.",
                  "% exact semantic-unit bridge: "+p["unit_bridge"],
                  "% Requires an exact NpcDisplayFor to identify an external eta, not congruence modulo 2^r.",
                  "% Full certificate: alpha>=2, nonzero even q, exact odd display; selected procyclic branches also r>=1."]
    lines.append("% A zero-count handle product is empty, equal to one; L omits that node at h=0.")
    return "\n".join(lines)+"\n"


def self_test():
    # This is only a tiny schema-valid test tree, not a Python L-family factory.
    payload = {"alphabet_degree": 1, "ast_schema_version": 1, "binding": FAMILIES["L"]["binding"],
               "bridge": FAMILIES["L"]["bridge"], "factory": FAMILIES["L"]["factory"], "family": "L",
               "schema": SCHEMA, "semantic_target": FAMILIES["L"]["semantic_target"],
               "structural": {"h": 0}, "tree": {"op": "Generator", "name": "x0"}, "unit_bridge": None}
    def wrap(p):
        p["word_hash"] = legacy.content_hash(p["tree"])
        return {"payload": p, "status": "STAGED", "template_hash": digest(p)}
    obj = wrap(payload)
    assert loads(canonical_json(obj)) == obj
    assert r"\[R=x_0.\]" in render_tex(obj)
    count = 2
    mutations = [
        lambda p: p.update(schema="bad"), lambda p: p.update(family="M0"),
        lambda p: p.update(family=[]), lambda p: p.update(extra=1),
        lambda p: p.update(ast_schema_version=True), lambda p: p.update(ast_schema_version=1.0),
        lambda p: p.update(alphabet_degree=True), lambda p: p.update(alphabet_degree=2),
        lambda p: p["structural"].update(h=True), lambda p: p["structural"].update(h=-1),
        lambda p: p["structural"].update(h=0.0), lambda p: p["structural"].update(extra=1),
        lambda p: p.update(binding="bad"), lambda p: p.update(bridge="bad"),
        lambda p: p.update(factory="bad"), lambda p: p.update(semantic_target="bad"),
        lambda p: p.update(unit_bridge="bad"),
        lambda p: p.update(tree={"op": "Generator", "name": "x2"}),
        lambda p: p.update(tree={"op": "Generator", "name": "x01"}),
        lambda p: p.update(tree={"op": "Generator", "name": r"\input{bad}"}),
        lambda p: p.update(tree={"op": "HyperbolicHandles", "start_index": 2, "count": {"type": "Int", "value": 0}}),
        lambda p: p.update(tree={"op": "IntegerPower", "word": {"op": "Generator", "name": "x0"},
                                 "exponent": {"type": "Param", "name": "unbound"}}),
        lambda p: p.update(tree={"op": "Auxiliary", "name": "other", "definition": {"op": "Identity"}}),
        lambda p: p.update(tree={"op": "Shadow", "kind": "other", "parameters": [], "word": {"op": "Identity"}}),
    ]
    for mutate in mutations:
        p = deepcopy(payload)
        mutate(p)
        try:
            validate(wrap(p))
        except (TemplateError, legacy.WordError):
            count += 1
        else:
            raise AssertionError("malformed LN artifact accepted")
    for bad in ('[]','null','NaN','Infinity','{"payload":0,"payload":0}',
                canonical_json(obj).replace('"h":0','"h":0,"h":0'),
                canonical_json(obj).replace('"STAGED"','"APPROVED"'),
                canonical_json(obj).replace(obj['template_hash'],'0'*64),
                canonical_json(obj).replace('"op":"Generator"','"op":[]'),
                canonical_json(obj).replace('"name":"x0"','"name":true')):
        try:
            loads(bad)
        except (TemplateError, legacy.WordError):
            count += 1
        else:
            raise AssertionError("malformed LN JSON accepted")
    for args in ({"alpha":2,"r":1,"h":0,"num":2,"den":1},
                 {"alpha":2,"r":1,"h":0,"num":1,"den":0},
                 {"alpha":2,"r":1,"h":0,"num":True,"den":1}):
        try:
            validate_parameters("Npc",args)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid Npc display accepted")
    print(f"LN_WORD_SELF_TEST_PASS|{count}")
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command",required=True)
    sub.add_parser("self-test")
    generate = sub.add_parser("generate")
    generate.add_argument("family", choices=FAMILIES)
    generate.add_argument("parameters", nargs="+", type=int)
    generate.add_argument("--lean-runner", type=Path, required=True)
    generate.add_argument("--out", type=Path, default=Path("generated")/OUTPUT_COMPONENT)
    check = sub.add_parser("check")
    check.add_argument("directory", type=Path)
    check.add_argument("--lean-runner", type=Path)
    args = parser.parse_args()
    if args.command == "self-test":
        self_test()
    elif args.command == "generate":
        names = FAMILIES[args.family]["parameters"]
        if len(args.parameters) != len(names):
            raise TemplateError("expected parameters: "+" ".join(names))
        parameters = dict(zip(names,args.parameters))
        validate_parameters(args.family,parameters)
        if OUTPUT_COMPONENT not in args.out.resolve().parts:
            raise TemplateError("LN output must be inside "+OUTPUT_COMPONENT)
        obj = from_lean(args.lean_runner,args.family,parameters)
        args.out.mkdir(parents=True,exist_ok=True)
        base = args.out/artifact_name(obj["payload"])
        base.with_suffix(".ln.json").write_text(canonical_json(obj)+"\n")
        base.with_suffix(".tex").write_text(render_tex(obj))
        base.with_suffix(".provenance.json").write_text(canonical_json(provenance(obj))+"\n")
        print(f"STAGED_LN_GENERATED|{base.name}|{obj['payload']['word_hash']}|{obj['template_hash']}")
    else:
        paths = sorted(args.directory.glob("*.ln.json"))
        if not paths:
            raise TemplateError("no staged LN word artifacts found")
        for path in paths:
            obj = loads(path.read_text())
            p = obj["payload"]
            name = artifact_name(p)
            if path.name != name+".ln.json":
                raise TemplateError("noncanonical LN filename")
            base = path.parent/name
            if base.with_suffix(".tex").read_text() != render_tex(obj):
                raise TemplateError("generated LN TeX drift")
            recorded = json.loads(base.with_suffix(".provenance.json").read_text(), object_pairs_hook=reject_duplicates)
            if recorded != provenance(obj):
                raise TemplateError("LN direct-source provenance drift")
            if args.lean_runner and from_lean(args.lean_runner,p["family"],p["structural"]) != obj:
                raise TemplateError("LN artifact differs from the actual Lean factory")
            mode = "Lean-replayed" if args.lean_runner else "artifact-only; NOT Lean-synchronized"
            print(f"STAGED_LN_CHECK|{mode}|{name}|{p['word_hash']}")


if __name__ == "__main__":
    try:
        main()
    except (TemplateError, legacy.WordError, legacy.LatexError, OSError, ValueError, RecursionError) as exc:
        raise SystemExit(f"LN word artifact error: {exc}") from exc
