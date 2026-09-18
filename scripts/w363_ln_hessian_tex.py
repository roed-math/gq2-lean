#!/usr/bin/env python3
"""STAGED L/N0/Npc extraspecial Hessian: the decomposition and its hypotheses (item 7).

Lean owns the data: `scripts/w363_ln_hessian_export.lean` serializes it and carries the
signature theorems. This module validates that serialization and renders it.

A third kind of bridge. Item 7's carriers are theorems, not records with data fields, so
neither earlier kind applies. The driver restates each identity through a named
decomposition `hessShape leading cross planes = leading + cross + sum_j planes j` and
discharges the restatement by the tree's own theorem, so a wrong decomposition does not
compile. What is certified is the decomposition and its three subterms; the human labels
for those subterms are prose, exactly like item 6's clause roles, and the artifact says so
in its own `warning` field.

The content worth publishing is what the four identities do NOT share. L and N0 are
resolver-immune and read an x-slot-zero slice. The two Npc identities are the full-offset
route, with no vanishing slot, and each needs its own extra input. The validator pins the
hypothesis list per sector, so a sector cannot silently lose or gain one.
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
SCHEMA = "gq2.w363.ln-hessian.v1.staged"
DOMAIN = b"GQ2-W363-LN-HESSIAN\0"
PREFIX = "W363_LN_HESSIAN_JSON="
LEAN_FILE = "scripts/w363_ln_hessian_export.lean"
BRIDGE = "GQ2.Dyadic.W363LNHessian."
RESTATED = "restated_identity"
SHAPE = BRIDGE + "hessShape"

CERT = "GQ2.Dyadic.Certificates."
NPC_UNRAM = "GQ2.Dyadic.Instances.NpcUnramifiedFullOffsetHessian."
NPC_RAM = "GQ2.Dyadic.Instances.NpcRamifiedFullOffsetHessian."

PROVENANCE_FILES = (
    LEAN_FILE,
    "GQ2/Dyadic/Word/Hessian.lean",
    "GQ2/QuadraticFp2.lean",
    "GQ2/Dyadic/Certificates/L.lean",
    "GQ2/Dyadic/Certificates/N0.lean",
    "GQ2/Dyadic/Instances/NpcUnramifiedFullOffsetHessian.lean",
    "GQ2/Dyadic/Instances/NpcRamifiedFullOffsetHessian.lean",
    "scripts/w363_ln_hessian_tex.py",
)


def _sector(name, bridge, source, leading_kind, vanishing, hypotheses):
    return {"sector": name, "bridge": BRIDGE + bridge, "source": source,
            "leading_kind": leading_kind, "vanishing_slot": vanishing,
            "hypotheses": tuple(hypotheses)}


# The exact sector table. A payload naming a different source theorem, a different leading
# kind, a different vanishing slot or a different hypothesis list is rejected. The
# hypothesis list is pinned because the asymmetry between the families IS the content.
FAMILIES = {
    "L": {"parameters": ("h", "q"), "degree": lambda s: 2 * s["h"] + 1,
          "sectors": [_sector("slice", "lHessian_shape",
                              CERT + "LSqStokes.hessRelZ_lSq", "quadratic_slot", "x0",
                              ("char_two", "x0_slot_zero"))]},
    "N0": {"parameters": ("h", "q"), "degree": lambda s: 2 + 2 * s["h"],
           "sectors": [_sector("slice", "n0Hessian_shape",
                               CERT + "hessRelZ_nCompact", "quadratic_slot", "x2",
                               ("char_two", "alpha_at_least_two", "x2_slot_zero"))]},
    "Npc": {"parameters": ("h", "q", "r"), "degree": lambda s: 2 + 2 * s["h"],
            "sectors": [
                _sector("unramified_full_offset", "npcUnramHessian_shape",
                        NPC_UNRAM + "hessRelZ_npcW_evenPhiNormal", "named_diagonal", None,
                        ("char_two", "omega2_residue_pin", "finite_discrete_marking")),
                _sector("ramified_full_offset", "npcRamHessian_shape",
                        NPC_RAM + "hessRelZ_npcW_evenTwistedNormal", "named_diagonal", None,
                        ("char_two", "quadratic_form", "odd_fixed_point_free_u",
                         "resolver_lifts"))]},
}

LEADING_KINDS = ("quadratic_slot", "named_diagonal")

CERTIFICATE_CONDITIONS = {
    "L": "The L identity is resolver-immune: it needs no pin on E(omega2) at all, and reads "
         "the x0-slot-zero slice. The cross term is the Wall doubling of the x1 slot by the "
         "omega2-operator, which is why the omega2-power appears in it without any pin on "
         "its value.",
    "N0": "The N0 identity is resolver-immune in the same exact sense, reads the "
          "x2-slot-zero slice, and uses 2 <= alpha exactly once, through the leading-power "
          "law. Its cross term is the plain polar pairing of x0 against x1.",
    "Npc": "Both Npc identities are the FULL-OFFSET route, which is the completed proof. "
           "The older Gate-E slice with an invertible Lc is not what these bridges name and "
           "must not be displayed as the completed normal-coordinate proof. Neither sector "
           "hypothesises a vanishing slot, and each needs an input the L and N0 identities "
           "do not: a residue pin E(omega2) = e with e congruent to 1 mod 4 unramified, and "
           "quadraticity of q with an odd-order fixed-point-free u and a resolver-lifting "
           "hypothesis ramified.",
}


def digest(payload):
    return hashlib.sha256(DOMAIN + canonical_json(payload).encode()).hexdigest()


def validate_parameters(family, parameters):
    if not isinstance(family, str) or family not in FAMILIES:
        raise TemplateError("family must be L, N0 or Npc")
    fields(parameters, set(FAMILIES[family]["parameters"]), "LN Hessian structural parameters")
    for name, value in parameters.items():
        integer(value, name, natural=True)


def validate_hypotheses(recorded, expected):
    if not isinstance(recorded, list) or len(recorded) != len(expected):
        raise TemplateError("LN Hessian hypothesis list does not match the sector")
    for entry, identifier in zip(recorded, expected):
        fields(entry, {"id", "role"}, "LN Hessian hypothesis")
        if entry["id"] != identifier:
            raise TemplateError("LN Hessian hypotheses are not the sector's own, in order")
        if not isinstance(entry["role"], str) or not entry["role"]:
            raise TemplateError("LN Hessian hypothesis role must be a nonempty string")


def validate(envelope):
    fields(envelope, {"payload", "status", "template_hash"}, "LN Hessian envelope")
    if envelope["status"] != "STAGED":
        raise TemplateError("LN Hessian artifacts must remain STAGED")
    p = envelope["payload"]
    fields(p, {"application_scope", "decomposition", "degree", "family", "hash_scope",
               "schema", "sectors", "structural", "warning"}, "LN Hessian payload")
    if p["schema"] != SCHEMA:
        raise TemplateError("LN Hessian schema mismatch")
    validate_parameters(p["family"], p["structural"])
    meta = FAMILIES[p["family"]]
    structural = p["structural"]
    if integer(p["degree"], "degree", natural=True) != meta["degree"](structural):
        raise TemplateError("LN Hessian degree does not match the declared rank")
    for key in ("application_scope", "hash_scope", "warning"):
        if not isinstance(p[key], str) or not p[key]:
            raise TemplateError("LN Hessian " + key + " must be a nonempty string")
    fields(p["decomposition"], {"bridge", "note", "planes"}, "LN Hessian decomposition")
    if p["decomposition"]["bridge"] != SHAPE:
        raise TemplateError("LN Hessian decomposition is not bound to hessShape")
    if integer(p["decomposition"]["planes"], "handle planes", natural=True) != structural["h"]:
        raise TemplateError("LN Hessian handle-plane count is not the handle rank")
    if not isinstance(p["decomposition"]["note"], str) or not p["decomposition"]["note"]:
        raise TemplateError("LN Hessian decomposition note must be a nonempty string")
    sectors = p["sectors"]
    if not isinstance(sectors, list) or len(sectors) != len(meta["sectors"]):
        raise TemplateError("LN Hessian sector count does not match the family")
    for sector, expected in zip(sectors, meta["sectors"]):
        fields(sector, {"bridge", "bridge_kind", "cross", "hypotheses", "leading",
                        "leading_kind", "sector", "source", "vanishing_slot"},
               "LN Hessian sector")
        if (sector["sector"] != expected["sector"] or sector["bridge"] != expected["bridge"]
                or sector["source"] != expected["source"]):
            raise TemplateError("LN Hessian sector is not bound to the expected declarations")
        if sector["bridge_kind"] != RESTATED:
            raise TemplateError("LN Hessian bridges are restated identities, nothing stronger")
        if sector["leading_kind"] != expected["leading_kind"]:
            raise TemplateError("LN Hessian leading term is not of the expected kind")
        if sector["leading_kind"] not in LEADING_KINDS:
            raise TemplateError("unexpected LN Hessian leading kind")
        if sector["vanishing_slot"] != expected["vanishing_slot"]:
            raise TemplateError("LN Hessian vanishing slot does not match the sector")
        for key in ("cross", "leading"):
            if not isinstance(sector[key], str) or not sector[key]:
                raise TemplateError("LN Hessian " + key + " must be a nonempty string")
        validate_hypotheses(sector["hypotheses"], expected["hypotheses"])
    if envelope["template_hash"] != digest(p):
        raise TemplateError("LN Hessian envelope hash mismatch")
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
        raise TemplateError("Lean LN Hessian exporter failed:\n" + result.stdout + result.stderr)
    records = [line[len(PREFIX):] for line in result.stdout.splitlines()
               if line.startswith(PREFIX)]
    if len(records) != 1:
        raise TemplateError("Lean LN Hessian exporter must emit exactly one marked artifact")
    obj = loads(records[0])
    if canonical_json(obj) != records[0]:
        raise TemplateError("Lean/Python LN Hessian canonical JSON mismatch")
    if obj["payload"]["family"] != family or obj["payload"]["structural"] != parameters:
        raise TemplateError("Lean LN Hessian exporter returned different parameters")
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
    planes = p["decomposition"]["planes"]
    lines = [
        "% STAGED L/N extraspecial Hessian; ledger item 7 only.",
        "% ln-hessian-hash: " + envelope["template_hash"],
        "% family: " + family + "; structural: " + canonical_json(p["structural"])
        + "; degree: " + str(p["degree"]),
        "% " + p["application_scope"],
        "% " + p["warning"],
        "% " + p["hash_scope"],
        "% " + CERTIFICATE_CONDITIONS[family],
        "% decomposition bridge: " + p["decomposition"]["bridge"],
        "% " + p["decomposition"]["note"],
        r"\[\mathrm{hess}(R)=\underbrace{L}_{\text{leading}}"
        r"+\underbrace{X}_{\text{cross}}"
        r"+\sum_{j=1}^{" + str(planes) + r"}\underbrace{P_j}_{\text{handle plane}}.\]",
    ]
    for sector in p["sectors"]:
        lines += [r"\paragraph{" + tex_escape(sector["sector"].replace("_", " ")) + " sector}",
                  "% source: " + sector["source"],
                  "% bridge (" + sector["bridge_kind"] + "): " + sector["bridge"],
                  r"\begin{description}",
                  r"\item[$L$ (" + tex_escape(sector["leading_kind"].replace("_", " ")) + ")] "
                  + tex_escape(sector["leading"]),
                  r"\item[$X$] " + tex_escape(sector["cross"]),
                  r"\item[$P_j$] the polar pairing of the two vectors of handle plane $j$, "
                  r"for the " + str(planes) + " planes",
                  r"\item[vanishing slot] "
                  + (tex_escape(sector["vanishing_slot"]) + " is hypothesised zero"
                     if sector["vanishing_slot"] else
                     "none: this is the full-offset route, no slot is set to zero"),
                  r"\item[hypotheses] " + "; ".join(
                      tex_escape(e["id"].replace("_", " ")) + ": " + tex_escape(e["role"])
                      for e in sector["hypotheses"]),
                  r"\end{description}"]
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------- self-test


def self_test():
    def build(family, structural):
        meta = FAMILIES[family]
        sectors = []
        for spec in meta["sectors"]:
            sectors.append({
                "bridge": spec["bridge"], "bridge_kind": RESTATED, "cross": "cross",
                "hypotheses": [{"id": i, "role": "role"} for i in spec["hypotheses"]],
                "leading": "leading", "leading_kind": spec["leading_kind"],
                "sector": spec["sector"], "source": spec["source"],
                "vanishing_slot": spec["vanishing_slot"]})
        return {"application_scope": "scope",
                "decomposition": {"bridge": SHAPE, "note": "note",
                                  "planes": structural["h"]},
                "degree": meta["degree"](structural), "family": family,
                "hash_scope": "hash scope", "schema": SCHEMA, "sectors": sectors,
                "structural": structural, "warning": "warning"}

    def wrap(p):
        return {"payload": p, "status": "STAGED", "template_hash": digest(p)}

    base = build("N0", {"h": 2, "q": 2})
    obj = wrap(base)
    assert loads(canonical_json(obj)) == obj
    assert "ln-hessian-hash" in render_tex(obj)
    assert "restated_identity" in render_tex(obj)
    assert "x2 is hypothesised zero" in render_tex(obj)
    npc = wrap(build("Npc", {"h": 1, "q": 2, "r": 1}))
    assert loads(canonical_json(npc)) == npc
    assert "full-offset route, no slot is set to zero" in render_tex(npc)
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
        lambda p: p.update(degree=5),
        lambda p: p["structural"].update(h=1),
        lambda p: p["structural"].update(q=-1),
        lambda p: p["structural"].update(r=2),
        lambda p: p["decomposition"].update(bridge=BRIDGE + "other"),
        lambda p: p["decomposition"].update(planes=3),
        lambda p: p["decomposition"].update(note=""),
        lambda p: p["sectors"].pop(),
        lambda p: p["sectors"][0].update(sector="unramified_full_offset"),
        lambda p: p["sectors"][0].update(source=CERT + "other"),
        lambda p: p["sectors"][0].update(bridge=BRIDGE + "other"),
        # the bridge is a restated identity and may not be dressed up as anything stronger
        lambda p: p["sectors"][0].update(bridge_kind="record_target"),
        lambda p: p["sectors"][0].update(bridge_kind="field_statement_identity"),
        # the leading term's kind and the vanishing slot are the families' real asymmetry
        lambda p: p["sectors"][0].update(leading_kind="named_diagonal"),
        lambda p: p["sectors"][0].update(vanishing_slot=None),
        lambda p: p["sectors"][0].update(vanishing_slot="x0"),
        lambda p: p["sectors"][0].update(leading=""),
        lambda p: p["sectors"][0].update(cross=3),
        # so is the hypothesis list: a sector may not quietly lose or gain one
        lambda p: p["sectors"][0]["hypotheses"].pop(),
        lambda p: p["sectors"][0]["hypotheses"].reverse(),
        lambda p: p["sectors"][0]["hypotheses"][0].update(id="omega2_residue_pin"),
        lambda p: p["sectors"][0]["hypotheses"][0].update(role=""),
        lambda p: p["sectors"][0]["hypotheses"].append({"id": "resolver_lifts", "role": "r"}),
        lambda p: p["sectors"][0].pop("cross"),
    ]
    for mutate in mutations:
        try:
            validate(mutated(mutate))
        except TemplateError:
            count += 1
        else:
            raise AssertionError("malformed LN Hessian artifact accepted")
    for bad in ("[]", "null", "NaN", "Infinity", '{"payload":0,"payload":0}',
                canonical_json(obj).replace('"h":2', '"h":2,"h":2'),
                canonical_json(obj).replace('"STAGED"', '"APPROVED"'),
                canonical_json(obj).replace(obj["template_hash"], "0" * 64),
                canonical_json(obj).replace('"leading_kind"', '"leadingKind"', 1)):
        try:
            loads(bad)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("malformed LN Hessian JSON accepted")
    for family, parameters in (("L", {"h": 0}), ("Npc", {"h": 0, "q": 2}),
                               ("M0", {"h": 0, "q": 2}), ("L", {"h": -1, "q": 2})):
        try:
            validate_parameters(family, parameters)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid LN Hessian parameters accepted")
    print(f"LN_HESSIAN_SELF_TEST_PASS|{count}")
    return count


def artifact_name(payload):
    family, s = payload["family"], payload["structural"]
    return family + "-hessian-" + "-".join(name + str(s[name])
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
            raise TemplateError("LN Hessian output must be inside general-ln-certificate-staged")
        obj = from_lean(args.lean_runner, args.family, parameters)
        args.out.mkdir(parents=True, exist_ok=True)
        base = args.out / artifact_name(obj["payload"])
        base.with_suffix(".hessian.json").write_text(canonical_json(obj) + "\n")
        base.with_suffix(".hessian.tex").write_text(render_tex(obj))
        base.with_suffix(".hessian.provenance.json").write_text(
            canonical_json(provenance(obj)) + "\n")
        print(f"STAGED_LN_HESSIAN_GENERATED|{base.name}|{obj['template_hash']}")
        return
    paths = sorted(args.directory.glob("*.hessian.json"))
    if not paths:
        raise TemplateError("no staged LN Hessian artifacts found")
    for path in paths:
        obj = loads(path.read_text())
        p = obj["payload"]
        name = artifact_name(p)
        if path.name != name + ".hessian.json":
            raise TemplateError("noncanonical LN Hessian filename")
        base = path.parent / name
        if base.with_suffix(".hessian.tex").read_text() != render_tex(obj):
            raise TemplateError("generated LN Hessian TeX drift")
        recorded = json.loads(base.with_suffix(".hessian.provenance.json").read_text(),
                              object_pairs_hook=reject_duplicates)
        if recorded != provenance(obj):
            raise TemplateError("LN Hessian direct-source provenance drift")
        replayed = "syntax-only"
        if args.lean_runner:
            if from_lean(args.lean_runner, p["family"], p["structural"]) != obj:
                raise TemplateError("Lean LN Hessian replay disagrees with the staged artifact")
            replayed = "Lean-replayed"
        print(f"STAGED_LN_HESSIAN_CHECK|{replayed}|{name}|{obj['template_hash']}")


if __name__ == "__main__":
    main()
