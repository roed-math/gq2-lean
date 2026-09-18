#!/usr/bin/env python3
"""STAGED L/N0/Npc Fox operation lists and reduced normal matrices (ledger items 4, 5).

Lean owns the data: `scripts/w362_ln_fox_export.lean` serializes the actual
`FoxCertificate` fields and carries `rfl` signature theorems binding them to the
records. This module validates that serialization and renders it. It builds no
matrix of its own, reads no frozen manifest or generated appendix, and is not an
approved appendix section, gate, or migration.

The pair/mobile renderers in `w361_general_fox_tex.py` are NOT reused: their
payload is splice-specific (`_pair_signature` / `_mobile_signature`), and reusing
them for L/N would substitute one family's symbolic profile for another's.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from w361_general_word_tex import TemplateError, canonical_json, fields, integer, reject_duplicates

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "gq2.w362.ln-fox.v1.staged"
DOMAIN = b"GQ2-W362-LN-FOX\0"
PREFIX = "W362_LN_FOX_JSON="
LEAN_FILE = "scripts/w362_ln_fox_export.lean"
CERT = "GQ2.Dyadic.Certificates."
BRIDGE = "GQ2.Dyadic.W362LNFox."

PROVENANCE_FILES = (
    LEAN_FILE,
    "GQ2/Dyadic/Word/FoxCert.lean",
    "GQ2/Dyadic/Certificates/LJacobian.lean",
    "GQ2/Dyadic/Certificates/LFox.lean",
    "GQ2/Dyadic/Certificates/N0Fox.lean",
    "GQ2/Dyadic/Certificates/NpcFox.lean",
    "scripts/w362_ln_fox_tex.py",
)


def _sector(name, record, stem):
    return {"sector": name, "record": CERT + record,
            "signature_bridges": {"column_operations": BRIDGE + stem + "_colOps",
                                  "row_operations": BRIDGE + stem + "_rowOps",
                                  "target": BRIDGE + stem + "_target"}}


# The exact sector table. A payload that names a different record or bridge is rejected:
# matching shapes are not a certificate identity, only these declarations are.
FAMILIES = {
    "L": {"parameters": ("h", "q"), "alphabet": "TameSym",
          "degree": lambda s: 2 * s["h"] + 1,
          "sectors": [_sector("unramified", "LSq.lSqJacobianCertUnram", "lSqUnram"),
                      _sector("ramified", "LSq.lSqJacobianCertRam", "lSqRam"),
                      _sector("scalar", "LSq.lSqJacobianCertScalar", "lSqScalar")]},
    "N0": {"parameters": ("h", "q"), "alphabet": "TameSym",
           "degree": lambda s: 2 + 2 * s["h"],
           "sectors": [_sector("unramified", "nCompactJacobianCertUnram", "nCompactUnram"),
                       _sector("ramified", "nCompactJacobianCertRam", "nCompactRam")]},
    "Npc": {"parameters": ("h", "q", "r"), "alphabet": "NpcSym",
            "degree": lambda s: 2 + 2 * s["h"],
            "sectors": [_sector("unramified", "Npc.npcJacobianCertUnram", "npcUnram"),
                        _sector("ramified", "Npc.npcJacobianCertRam", "npcRam")]},
}

# Conditions the exported syntax does NOT establish; printed with every artifact.
CERTIFICATE_CONDITIONS = {
    "L": "Fox rows need only the listed coefficient hypotheses; the completed L word "
         "certificate additionally requires q = 2^f with f odd.",
    "N0": "The N0 Fox records need 1 <= alpha; the complete N0 certificate requires "
          "alpha >= 2 and nonzero even q.",
    "Npc": "The Npc Fox records need 1 <= alpha; the complete Npc certificate requires "
           "alpha >= 2, nonzero even q and an exact NpcDisplayFor for the semantic unit. "
           "The unramified target intentionally stops at two blocks and does not claim "
           "either block is a unit.",
}


def digest(payload):
    return hashlib.sha256(DOMAIN + canonical_json(payload).encode()).hexdigest()


def validate_parameters(family, parameters):
    if not isinstance(family, str) or family not in FAMILIES:
        raise TemplateError("family must be L, N0 or Npc")
    fields(parameters, set(FAMILIES[family]["parameters"]), "LN Fox structural parameters")
    for name, value in parameters.items():
        integer(value, name, natural=True)


def expected_columns(degree):
    return ([{"kind": "sigma"}, {"kind": "tau"}]
            + [{"index": i, "kind": "wild"} for i in range(degree + 1)])


def validate_symbol(symbol, alphabet):
    if not isinstance(symbol, dict) or "kind" not in symbol:
        raise TemplateError("malformed coefficient atom")
    kind = symbol["kind"]
    if alphabet == "NpcSym":
        if kind == "standard":
            fields(symbol, {"kind", "symbol"}, "standard Npc atom")
            return validate_symbol(symbol["symbol"], "TameSym")
        if kind == "eta_conjugator_power":
            fields(symbol, {"kind", "power"}, "eta conjugator atom")
            integer(symbol["power"], "eta conjugator power")
            return
        raise TemplateError("unexpected NpcSym atom kind")
    if kind == "generator_power":
        fields(symbol, {"generator", "kind", "power"}, "generator power atom")
        validate_generator(symbol["generator"])
        integer(symbol["power"], "generator power")
        return
    if kind == "sigma2_power":
        fields(symbol, {"kind", "power"}, "sigma2 power atom")
        integer(symbol["power"], "sigma2 power")
        return
    if kind == "projector":
        fields(symbol, {"kind"}, "projector atom")
        return
    raise TemplateError("unexpected TameSym atom kind")


def validate_generator(g):
    if not isinstance(g, dict) or "kind" not in g:
        raise TemplateError("malformed generator")
    if g["kind"] in ("sigma", "tau"):
        fields(g, {"kind"}, "tame generator")
        return
    if g["kind"] != "wild":
        raise TemplateError("unexpected generator kind")
    fields(g, {"index", "kind"}, "wild generator")
    integer(g["index"], "wild generator index", natural=True)


def validate_coeff(c, alphabet):
    if not isinstance(c, dict) or "op" not in c:
        raise TemplateError("malformed coefficient tree")
    op = c["op"]
    if op in ("zero", "one"):
        fields(c, {"op"}, "constant coefficient")
    elif op == "atom":
        fields(c, {"op", "symbol"}, "atomic coefficient")
        validate_symbol(c["symbol"], alphabet)
    elif op == "add":
        fields(c, {"left", "op", "right"}, "sum coefficient")
        validate_coeff(c["left"], alphabet)
        validate_coeff(c["right"], alphabet)
    elif op == "comp":
        fields(c, {"inner", "op", "outer"}, "composite coefficient")
        validate_coeff(c["outer"], alphabet)
        validate_coeff(c["inner"], alphabet)
    elif op == "neg":
        fields(c, {"op", "value"}, "negated coefficient")
        validate_coeff(c["value"], alphabet)
    else:
        raise TemplateError("unexpected coefficient operation")


def validate_row_op(op, alphabet):
    if not isinstance(op, dict) or "op" not in op:
        raise TemplateError("malformed row operation")
    kind = op["op"]
    if kind == "swap":
        fields(op, {"op"}, "row swap")
    elif kind in ("add_fst", "add_snd"):
        fields(op, {"coefficient", "op"}, "row transvection")
        validate_coeff(op["coefficient"], alphabet)
    elif kind in ("scale_fst", "scale_snd"):
        fields(op, {"forward", "inverse", "op"}, "row scaling")
        validate_coeff(op["forward"], alphabet)
        validate_coeff(op["inverse"], alphabet)
    else:
        raise TemplateError("unexpected row operation")


def validate_col_op(op, alphabet, degree):
    if not isinstance(op, dict) or "op" not in op:
        raise TemplateError("malformed column operation")
    kind = op["op"]
    if kind == "swap":
        fields(op, {"left", "op", "right"}, "column swap")
        slots = (op["left"], op["right"])
    elif kind == "transvect":
        fields(op, {"coefficient", "op", "source", "target"}, "column transvection")
        validate_coeff(op["coefficient"], alphabet)
        slots = (op["source"], op["target"])
    elif kind == "scale":
        fields(op, {"forward", "generator", "inverse", "op"}, "column scaling")
        validate_coeff(op["forward"], alphabet)
        validate_coeff(op["inverse"], alphabet)
        slots = (op["generator"],)
    else:
        raise TemplateError("unexpected column operation")
    for g in slots:
        validate_generator(g)
        if g["kind"] == "wild" and g["index"] > degree:
            raise TemplateError("column operation leaves the declared alphabet")


def validate_row(row, alphabet, degree):
    fields(row, {"columns"}, "normal-form row")
    columns = row["columns"]
    if not isinstance(columns, list) or len(columns) != degree + 3:
        raise TemplateError("normal-form row must carry every column slot exactly once")
    for entry, slot in zip(columns, expected_columns(degree)):
        fields(entry, {"coefficient", "generator"}, "normal-form entry")
        if entry["generator"] != slot:
            raise TemplateError("normal-form columns are not the canonical alphabet order")
        validate_coeff(entry["coefficient"], alphabet)


def validate(envelope):
    fields(envelope, {"payload", "status", "template_hash"}, "LN Fox envelope")
    if envelope["status"] != "STAGED":
        raise TemplateError("LN Fox artifacts must remain STAGED")
    p = envelope["payload"]
    fields(p, {"alphabet", "application_scope", "composition", "family", "hash_scope",
               "schema", "sectors", "structural"}, "LN Fox payload")
    if p["schema"] != SCHEMA:
        raise TemplateError("LN Fox schema mismatch")
    validate_parameters(p["family"], p["structural"])
    meta = FAMILIES[p["family"]]
    structural = p["structural"]
    degree = meta["degree"](structural)
    fields(p["alphabet"], {"degree", "h", "wild_count"}, "LN Fox alphabet")
    if (integer(p["alphabet"]["degree"], "alphabet degree", natural=True) != degree
            or p["alphabet"]["h"] != structural["h"]
            or p["alphabet"]["wild_count"] != degree + 1):
        raise TemplateError("LN Fox alphabet does not match the declared rank")
    for key in ("application_scope", "composition", "hash_scope"):
        if not isinstance(p[key], str) or not p[key]:
            raise TemplateError("LN Fox " + key + " must be a nonempty string")
    sectors = p["sectors"]
    if not isinstance(sectors, list) or len(sectors) != len(meta["sectors"]):
        raise TemplateError("LN Fox sector count does not match the family")
    for sector, expected in zip(sectors, meta["sectors"]):
        fields(sector, {"column_operations", "record", "row_operations", "sector",
                        "signature_bridges", "symbol_alphabet", "target"}, "LN Fox sector")
        if (sector["sector"] != expected["sector"] or sector["record"] != expected["record"]
                or sector["signature_bridges"] != expected["signature_bridges"]):
            raise TemplateError("LN Fox sector is not bound to the expected record/bridges")
        if sector["symbol_alphabet"] != meta["alphabet"]:
            raise TemplateError("LN Fox sector uses the wrong atom alphabet")
        if not isinstance(sector["row_operations"], list) or not isinstance(
                sector["column_operations"], list):
            raise TemplateError("LN Fox operation lists must be arrays")
        for op in sector["row_operations"]:
            validate_row_op(op, meta["alphabet"])
        for op in sector["column_operations"]:
            validate_col_op(op, meta["alphabet"], degree)
        fields(sector["target"], {"fst", "snd"}, "LN Fox target")
        validate_row(sector["target"]["fst"], meta["alphabet"], degree)
        validate_row(sector["target"]["snd"], meta["alphabet"], degree)
    if envelope["template_hash"] != digest(p):
        raise TemplateError("LN Fox envelope hash mismatch")
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
        raise TemplateError("Lean LN Fox exporter failed:\n" + result.stdout + result.stderr)
    records = [line[len(PREFIX):] for line in result.stdout.splitlines()
               if line.startswith(PREFIX)]
    if len(records) != 1:
        raise TemplateError("Lean LN Fox exporter must emit exactly one marked artifact")
    obj = loads(records[0])
    if canonical_json(obj) != records[0]:
        raise TemplateError("Lean/Python LN Fox canonical JSON mismatch")
    if obj["payload"]["family"] != family or obj["payload"]["structural"] != parameters:
        raise TemplateError("Lean LN Fox exporter returned different parameters")
    return obj


def provenance(envelope):
    return {"schema": SCHEMA + ".provenance", "status": "STAGED",
            "template_hash": envelope["template_hash"],
            "scope": "Direct source bytes only; not a transitive build, coefficient module, "
                     "or certificate attestation.",
            "sha256": {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                       for name in PROVENANCE_FILES}}


# ---------------------------------------------------------------- rendering


def generator_tex(g, *, action=False):
    if g["kind"] == "sigma":
        return "S" if action else r"\sigma"
    if g["kind"] == "tau":
        return "T" if action else r"\tau"
    return ("W" if action else "w") + "_{" + str(g["index"]) + "}"


def cochain_tex(g):
    slot = ("x_{" + str(g["index"]) + "}") if g["kind"] == "wild" else generator_tex(g)
    return "a_{" + slot + "}"


def coeff_tex(c):
    op = c["op"]
    if op == "zero":
        return "0"
    if op == "one":
        return "I"
    if op == "atom":
        s = c["symbol"]
        if s["kind"] == "standard":
            return coeff_tex({"op": "atom", "symbol": s["symbol"]})
        if s["kind"] == "eta_conjugator_power":
            return "A" if s["power"] == 1 else "A^{" + str(s["power"]) + "}"
        if s["kind"] == "projector":
            return r"\Pi"
        base = "S_2" if s["kind"] == "sigma2_power" else generator_tex(s["generator"], action=True)
        return base if s["power"] == 1 else base + "^{" + str(s["power"]) + "}"
    if op == "add":
        # A sum whose right summand is a formal negation prints as a difference; the tree
        # itself is unchanged, and the hash is taken over the tree, not over this display.
        right = c["right"]
        if right["op"] == "neg":
            return r"\bigl(" + coeff_tex(c["left"]) + "-" + coeff_tex(right["value"]) + r"\bigr)"
        return r"\bigl(" + coeff_tex(c["left"]) + "+" + coeff_tex(right) + r"\bigr)"
    if op == "neg":
        return "-" + coeff_tex(c["value"])
    return coeff_tex(c["outer"]) + r"\circ " + coeff_tex(c["inner"])


def row_tex(row):
    terms = [coeff_tex(e["coefficient"]) + r"\bigl(" + cochain_tex(e["generator"]) + r"\bigr)"
             for e in row["columns"] if e["coefficient"]["op"] != "zero"]
    return "0" if not terms else "+".join(terms)


def row_op_tex(op):
    kind = op["op"]
    if kind == "swap":
        return r"R_1\leftrightarrow R_2"
    if kind in ("add_fst", "add_snd"):
        i, j = (1, 2) if kind == "add_fst" else (2, 1)
        return (f"R_{i}" + r"\leftarrow R_" + str(i) + "+" + coeff_tex(op["coefficient"])
                + r"\circ R_" + str(j))
    i = 1 if kind == "scale_fst" else 2
    return (f"R_{i}" + r"\leftarrow " + coeff_tex(op["forward"]) + r"\circ R_" + str(i)
            + r"\quad[\text{carried inverse: }" + coeff_tex(op["inverse"]) + "]")


def col_op_tex(op):
    kind = op["op"]
    if kind == "swap":
        return cochain_tex(op["left"]) + r"\leftrightarrow " + cochain_tex(op["right"])
    if kind == "transvect":
        x, c = cochain_tex(op["target"]), op["coefficient"]
        sign, body = ("-", c["value"]) if c["op"] == "neg" else ("+", c)
        return (x + r"\leftarrow " + x + sign + coeff_tex(body)
                + r"\bigl(" + cochain_tex(op["source"]) + r"\bigr)")
    x = cochain_tex(op["generator"])
    return (x + r"\leftarrow " + coeff_tex(op["forward"]) + r"\bigl(" + x + r"\bigr)"
            + r"\quad[\text{carried inverse: }" + coeff_tex(op["inverse"]) + "]")


def operations_tex(sector):
    lines = []
    for key, label, renderer in (("row_operations", "R", row_op_tex),
                                 ("column_operations", "C", col_op_tex)):
        ops = sector[key]
        if not ops:
            lines.append(r"\mathcal " + label + r"&=\mathrm{id}")
        for i, op in enumerate(ops, 1):
            lines.append(r"\mathcal " + label + "_{" + str(i) + r"}&:\quad " + renderer(op))
    return r"\begin{aligned}" + r"\\".join(lines) + r"\end{aligned}"


def target_tex(sector):
    return (r"\begin{pmatrix}" + row_tex(sector["target"]["fst"]) + r"\\"
            + row_tex(sector["target"]["snd"]) + r"\end{pmatrix}")


def render_tex(envelope):
    p = validate(envelope)
    family = p["family"]
    lines = [
        "% STAGED L/N Fox operations and reduced matrices; ledger items 4 and 5 only.",
        "% ln-fox-hash: " + envelope["template_hash"],
        "% family: " + family + "; structural: " + canonical_json(p["structural"]),
        "% " + p["application_scope"],
        "% " + p["composition"],
        "% " + p["hash_scope"],
        "% " + CERTIFICATE_CONDITIONS[family],
        "% S, T, W_i are generator actions; S_2 is the omega2 action, not S squared;"
        " A is the eta-hat conjugator action, not an independently chosen scalar.",
        "% Rows are identities on ALL cochains, not only on the cocycle kernel."
        " Unprinted columns carry the coefficient 0.",
        "% Syntax, hash and render agreement is NOT Lean synchronization;"
        " replay Lean for strong checking.",
    ]
    for sector in p["sectors"]:
        lines += [r"\paragraph{" + sector["sector"] + " sector}",
                  "% record: " + sector["record"],
                  "% signature bridges: "
                  + ", ".join(sector["signature_bridges"][k]
                              for k in ("row_operations", "column_operations", "target")),
                  r"\[" + operations_tex(sector) + r"\]",
                  r"\[" + target_tex(sector) + r".\]"]
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------- self-test


def self_test():
    base = {"payload": {
        "alphabet": {"degree": 1, "h": 0, "wild_count": 2},
        "application_scope": "scope", "composition": "composition", "family": "L",
        "hash_scope": "hash scope", "schema": SCHEMA,
        "sectors": [], "structural": {"h": 0, "q": 2}}}

    def row(entries):
        return {"columns": [{"coefficient": entries.get(i, {"op": "zero"}), "generator": g}
                            for i, g in enumerate(expected_columns(1))]}

    unit = {"op": "atom", "symbol": {"generator": {"kind": "sigma"},
                                     "kind": "generator_power", "power": -1}}
    for spec in FAMILIES["L"]["sectors"]:
        base["payload"]["sectors"].append(dict(spec, symbol_alphabet="TameSym",
                                               row_operations=[], column_operations=[],
                                               target={"fst": row({1: unit}), "snd": row({})}))

    def wrap(p):
        return {"payload": p, "status": "STAGED", "template_hash": digest(p)}

    obj = wrap(base["payload"])
    assert loads(canonical_json(obj)) == obj
    assert "ln-fox-hash" in render_tex(obj)
    assert r"S^{-1}\bigl(a_{\tau}\bigr)" in render_tex(obj)
    count = 3

    def mutated(mutate):
        p = json.loads(canonical_json(base["payload"]))
        mutate(p)
        return wrap(p)

    mutations = [
        lambda p: p.update(schema="bad"),
        lambda p: p.update(family="M0"),
        lambda p: p.update(family=[]),
        lambda p: p.update(extra=1),
        lambda p: p.update(application_scope=""),
        lambda p: p.update(composition=3),
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
        lambda p: p["sectors"][0]["signature_bridges"].update(target=BRIDGE + "other"),
        lambda p: p["sectors"][0].update(symbol_alphabet="NpcSym"),
        lambda p: p["sectors"][0].update(row_operations={}),
        lambda p: p["sectors"][0]["row_operations"].append({"op": "rotate"}),
        lambda p: p["sectors"][0]["row_operations"].append(
            {"op": "add_snd", "coefficient": {"op": "atom", "symbol": {"kind": "bogus"}}}),
        lambda p: p["sectors"][0]["row_operations"].append(
            {"op": "add_snd", "coefficient": {"op": "atom", "symbol": {
                "generator": {"kind": "sigma"}, "kind": "generator_power", "power": 1.0}}}),
        lambda p: p["sectors"][0]["column_operations"].append(
            {"op": "scale", "generator": {"index": 9, "kind": "wild"},
             "forward": {"op": "one"}, "inverse": {"op": "one"}}),
        lambda p: p["sectors"][0]["target"]["fst"]["columns"].pop(),
        lambda p: p["sectors"][0]["target"]["fst"]["columns"].reverse(),
        lambda p: p["sectors"][0]["target"]["fst"]["columns"][0].update(coefficient={"op": "x"}),
        lambda p: p["sectors"][0]["target"]["fst"]["columns"][0].update(
            coefficient={"op": "atom", "symbol": {"kind": "eta_conjugator_power", "power": 1}}),
        lambda p: p["sectors"][0]["target"].update(extra=1),
    ]
    for mutate in mutations:
        try:
            validate(mutated(mutate))
        except TemplateError:
            count += 1
        else:
            raise AssertionError("malformed LN Fox artifact accepted")
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
            raise AssertionError("malformed LN Fox JSON accepted")
    for family, parameters in (("L", {"h": 0}), ("Npc", {"h": 0, "q": 2}),
                               ("M0", {"h": 0, "q": 2}), ("L", {"h": -1, "q": 2})):
        try:
            validate_parameters(family, parameters)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid LN Fox parameters accepted")
    print(f"LN_FOX_SELF_TEST_PASS|{count}")
    return count


def artifact_name(payload):
    family, s = payload["family"], payload["structural"]
    return family + "-fox-" + "-".join(name + str(s[name])
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
            raise TemplateError("LN Fox output must be inside general-ln-certificate-staged")
        obj = from_lean(args.lean_runner, args.family, parameters)
        args.out.mkdir(parents=True, exist_ok=True)
        base = args.out / artifact_name(obj["payload"])
        base.with_suffix(".fox.json").write_text(canonical_json(obj) + "\n")
        base.with_suffix(".fox.tex").write_text(render_tex(obj))
        base.with_suffix(".fox.provenance.json").write_text(canonical_json(provenance(obj)) + "\n")
        print(f"STAGED_LN_FOX_GENERATED|{base.name}|{obj['template_hash']}")
        return
    paths = sorted(args.directory.glob("*.fox.json"))
    if not paths:
        raise TemplateError("no staged LN Fox artifacts found")
    for path in paths:
        obj = loads(path.read_text())
        p = obj["payload"]
        name = artifact_name(p)
        if path.name != name + ".fox.json":
            raise TemplateError("noncanonical LN Fox filename")
        base = path.parent / name
        if base.with_suffix(".fox.tex").read_text() != render_tex(obj):
            raise TemplateError("generated LN Fox TeX drift")
        recorded = json.loads(base.with_suffix(".fox.provenance.json").read_text(),
                              object_pairs_hook=reject_duplicates)
        if recorded != provenance(obj):
            raise TemplateError("LN Fox direct-source provenance drift")
        if args.lean_runner and from_lean(args.lean_runner, p["family"], p["structural"]) != obj:
            raise TemplateError("LN Fox artifact differs from the actual Lean records")
        mode = "Lean-replayed" if args.lean_runner else "artifact-only; NOT Lean-synchronized"
        print(f"STAGED_LN_FOX_CHECK|{mode}|{name}|{obj['template_hash']}")


if __name__ == "__main__":
    try:
        main()
    except (TemplateError, OSError, ValueError, RecursionError) as exc:
        raise SystemExit(f"LN Fox artifact error: {exc}") from exc
