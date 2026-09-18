#!/usr/bin/env python3
"""STAGED symbolic Fox rows and operations, rendered from the typed Lean tree.

The hash identifies a symbolic template, NOT an instantiated word, coefficient
space, source residue size q, or action-dependent half-period k. Strong checks
replay Lean; artifact-only checks establish syntax/hash/render consistency only.
No frozen word grammar, fixture, or hash manifest is read or changed.
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

SCHEMA = "gq2.w361.fox-template.v1.staged"
DOMAIN = b"GQ2-W361-FOX-TEMPLATE\0"
LEAN_FILE = "GQ2/Dyadic/Word/GeneralFoxTemplateExport.lean"
PREFIX = "W361_FOX_TEMPLATE_JSON="
NAMESPACE = "GQ2.Dyadic.GeneralFoxTemplate."
SECTORS = ("scalar", "unramified", "ramified")
APPLICATION_SCOPE = ("Actual pair/mobile splice certificates under their stated "
                     "hypotheses; pair also requires a selected handle.")
COMPOSITION = ("comp(outer,inner) applies inner first; row list applies head first; "
               "column list denotes head composed with tail.")
HASH_SCOPE = ("Symbolic template identity only; no q, k, finite coefficient space, "
              "marking, or source exponent values are selected.")
PARAMETERS = {
    "k": {"domain": "Nat", "role": "Coefficient-action-dependent half-period: actual odd action order equals 2*k+1. Not handle rank."},
    "q": {"domain": "Nat", "role": "Source residue size, nonzero and even in certified uses; norm sum has q terms."},
}
K_BINDINGS = {
    "scalar": "unused (certificate bridge chooses 0)",
    "unramified": "sigmaActionHalfPeriod(t,A) = orderOf(actual sigma action)/2",
    "ramified": "tauActionHalfPeriod(t,A) = orderOf(actual tau action)/2",
}


def digest(payload):
    return hashlib.sha256(DOMAIN + canonical_json(payload).encode()).hexdigest()


def node_kind(node, key, where):
    if not isinstance(node, dict) or not isinstance(node.get(key), str):
        raise TemplateError(f"{where}: expected an object with a string {key}")
    return node[key]


def validate_generator(g, n):
    kind = node_kind(g, "kind", "Fox generator")
    if kind in ("sigma", "tau"):
        fields(g, {"kind"}, "tame generator")
    elif kind == "wild":
        fields(g, {"kind", "index"}, "wild generator")
        if integer(g["index"], "wild index", natural=True) > n:
            raise TemplateError("wild generator is outside the actual alphabet")
    else:
        raise TemplateError("unknown Fox generator")


def validate_symbol(s, n):
    kind = node_kind(s, "kind", "Fox symbol")
    if kind == "generator_power":
        fields(s, {"kind", "generator", "power"}, "generator power")
        validate_generator(s["generator"], n)
        integer(s["power"], "generator exponent")
    elif kind == "sigma2_power":
        fields(s, {"kind", "power"}, "sigma2 power")
        integer(s["power"], "sigma2 exponent")
    elif kind == "projector":
        fields(s, {"kind"}, "projector")
    else:
        raise TemplateError("unknown original Fox symbol")


def validate_coeff(c, n):
    op = node_kind(c, "op", "Fox coefficient")
    if op in ("zero", "one"):
        fields(c, {"op"}, "constant coefficient")
    elif op == "atom":
        fields(c, {"op", "symbol"}, "atom coefficient")
        validate_symbol(c["symbol"], n)
    elif op == "add":
        fields(c, {"op", "left", "right"}, "coefficient addition")
        validate_coeff(c["left"], n)
        validate_coeff(c["right"], n)
    elif op == "neg":
        fields(c, {"op", "value"}, "coefficient negation")
        validate_coeff(c["value"], n)
    elif op == "comp":
        fields(c, {"op", "outer", "inner"}, "ordered coefficient composition")
        validate_coeff(c["outer"], n)
        validate_coeff(c["inner"], n)
    elif op == "odd_power_sum":
        fields(c, {"op", "generator", "parameter", "sign"}, "odd-power sum")
        validate_generator(c["generator"], n)
        integer(c["sign"], "odd-power exponent multiplier")
        if c["parameter"] != "k":
            raise TemplateError("odd-power sum must use action half-period k")
    elif op == "norm_power_sum":
        fields(c, {"op", "generator", "parameter"}, "norm-power sum")
        validate_generator(c["generator"], n)
        if c["parameter"] != "q":
            raise TemplateError("norm-power sum must use source residue size q")
    else:
        raise TemplateError("unknown Fox coefficient; opaque inverses are not supported")


def validate_row_op(op, n):
    kind = node_kind(op, "op", "Fox row operation")
    if kind == "swap":
        fields(op, {"op"}, "row swap")
    elif kind in ("add_fst", "add_snd"):
        fields(op, {"op", "coefficient"}, "row addition")
        validate_coeff(op["coefficient"], n)
    elif kind in ("scale_fst", "scale_snd"):
        fields(op, {"op", "forward", "inverse"}, "row scaling with carried inverse")
        validate_coeff(op["forward"], n)
        validate_coeff(op["inverse"], n)
    else:
        raise TemplateError("unknown Fox row operation")


def validate_col_op(op, n):
    kind = node_kind(op, "op", "Fox column operation")
    if kind == "swap":
        fields(op, {"op", "left", "right"}, "column swap")
        validate_generator(op["left"], n)
        validate_generator(op["right"], n)
    elif kind == "transvect":
        fields(op, {"op", "target", "source", "coefficient"}, "column transvection")
        validate_generator(op["target"], n)
        validate_generator(op["source"], n)
        validate_coeff(op["coefficient"], n)
        if op["target"] == op["source"]:
            raise TemplateError("certified column transvections require distinct slots")
    elif kind == "scale":
        fields(op, {"op", "generator", "forward", "inverse"}, "column scaling")
        validate_generator(op["generator"], n)
        validate_coeff(op["forward"], n)
        validate_coeff(op["inverse"], n)
    else:
        raise TemplateError("unknown Fox column operation")


def validate_row(row, n, *, target=False):
    op = node_kind(row, "op", "Fox row")
    if op == "zero_row":
        fields(row, {"op"}, "zero row")
    elif op == "identity_pivot" and target:
        fields(row, {"op", "generator"}, "identity pivot row")
        validate_generator(row["generator"], n)
    elif op == "term" and not target:
        fields(row, {"op", "coefficient", "generator"}, "input row term")
        validate_coeff(row["coefficient"], n)
        validate_generator(row["generator"], n)
    elif op == "add" and not target:
        fields(row, {"op", "left", "right"}, "input row addition")
        validate_row(row["left"], n)
        validate_row(row["right"], n)
    else:
        raise TemplateError("unknown Fox input/target row constructor")


def validate_profile(profile, n, sector):
    fields(profile, {"sector", "interpretation", "k_binding", "denotation_bridge",
                     "certificate_bridges", "input_evaluation_bridge", "tree"}, "Fox profile")
    if (profile["sector"] != sector
            or profile["interpretation"] != ("TameSym.ramifiedEnd" if sector == "ramified" else "TameSym.splitEnd")
            or profile["k_binding"] != K_BINDINGS[sector]
            or profile["denotation_bridge"] != NAMESPACE + "denote_" + sector
            or profile["input_evaluation_bridge"] != NAMESPACE + sector + "_input_apply"):
        raise TemplateError("Fox sector, interpretation, period, or bridge mismatch")
    fields(profile["certificate_bridges"], {"pair", "mobile"}, "certificate bridges")
    for family in ("pair", "mobile"):
        if profile["certificate_bridges"][family] != NAMESPACE + sector + "_" + family + "_signature":
            raise TemplateError("actual source certificate bridge mismatch")
    tree = profile["tree"]
    fields(tree, {"row_ops", "column_ops", "input_rows", "target_rows"}, "Fox profile tree")
    for name, validator in (("row_ops", validate_row_op), ("column_ops", validate_col_op)):
        if not isinstance(tree[name], list):
            raise TemplateError("Fox operation list must be a list")
        for op in tree[name]:
            validator(op, n)
    for name, target in (("input_rows", False), ("target_rows", True)):
        if not isinstance(tree[name], list) or len(tree[name]) != 2:
            raise TemplateError("Fox profile must have exactly two input and target rows")
        for row in tree[name]:
            validate_row(row, n, target=target)


def validate(envelope):
    """Validate syntax, declared bindings, alphabet, and hash; not Lean provenance."""
    fields(envelope, {"payload", "status", "template_hash"}, "Fox envelope")
    if envelope["status"] != "STAGED":
        raise TemplateError("Fox artifacts must remain STAGED")
    p = envelope["payload"]
    fields(p, {"alphabet", "application_scope", "composition", "hash_scope",
               "parameters", "profiles", "schema"}, "Fox payload")
    if (p["schema"] != SCHEMA or p["application_scope"] != APPLICATION_SCOPE
            or p["composition"] != COMPOSITION or p["hash_scope"] != HASH_SCOPE):
        raise TemplateError("Fox schema/scope/composition mismatch")
    fields(p["parameters"], {"q", "k"}, "Fox symbolic parameters")
    for name in ("q", "k"):
        fields(p["parameters"][name], {"domain", "role"}, "Fox parameter metadata")
        if p["parameters"][name] != PARAMETERS[name]:
            raise TemplateError("source q and action-dependent k roles must be retained")
    a = p["alphabet"]
    fields(a, {"h", "n", "wild_count", "x2"}, "Fox alphabet")
    for name, value in a.items():
        integer(value, "alphabet " + name, natural=True)
    if a["n"] != 2+2*a["h"] or a["wild_count"] != a["n"]+1 or a["x2"] != 2:
        raise TemplateError("Fox alphabet/rank/pivot mismatch")
    if not isinstance(p["profiles"], list) or len(p["profiles"]) != 3:
        raise TemplateError("exactly scalar, unramified, and ramified profiles are required")
    for profile, sector in zip(p["profiles"], SECTORS):
        validate_profile(profile, a["n"], sector)
    if envelope["template_hash"] != digest(p):
        raise TemplateError("Fox symbolic template hash mismatch")
    return p


def loads(text):
    value = json.loads(text, object_pairs_hook=reject_duplicates,
                       parse_constant=lambda x: (_ for _ in ()).throw(TemplateError(x)))
    validate(value)
    return value


def from_lean(runner, h):
    integer(h, "requested handle rank", natural=True)
    result = subprocess.run(["bash", str(Path(runner).resolve()), "--run", LEAN_FILE, "all", str(h)],
                            text=True, capture_output=True)
    if result.returncode:
        raise TemplateError("Lean Fox exporter failed:\n" + result.stdout + result.stderr)
    records = [line[len(PREFIX):] for line in result.stdout.splitlines() if line.startswith(PREFIX)]
    if len(records) != 1:
        raise TemplateError("Lean Fox exporter must emit exactly one marked artifact")
    obj = loads(records[0])
    if canonical_json(obj) != records[0]:
        raise TemplateError("Lean/Python Fox canonical JSON mismatch")
    if obj["payload"]["alphabet"]["h"] != h:
        raise TemplateError("Lean Fox exporter returned a different rank")
    return obj


def generator_tex(g, *, action=False):
    if g["kind"] == "sigma":
        return "S" if action else r"\sigma"
    if g["kind"] == "tau":
        return "T" if action else r"\tau"
    return ("W" if action else "w") + "_{" + str(g["index"]) + "}"


def cochain_tex(g):
    # x_i denotes the wild offset, while x_sigma and x_tau are tame offsets.
    return "x_{" + (str(g["index"]) if g["kind"] == "wild" else generator_tex(g)) + "}"


def coeff_tex(c):
    op = c["op"]
    if op in ("zero", "one"):
        return "0" if op == "zero" else "I"
    if op == "atom":
        s = c["symbol"]
        if s["kind"] == "projector":
            return r"\Pi"
        base = "S_2" if s["kind"] == "sigma2_power" else generator_tex(s["generator"], action=True)
        return base if s["power"] == 1 else base + "^{" + str(s["power"]) + "}"
    if op == "add":
        return r"\bigl(" + coeff_tex(c["left"]) + "+" + coeff_tex(c["right"]) + r"\bigr)"
    if op == "neg":
        return r"\bigl(-" + coeff_tex(c["value"]) + r"\bigr)"
    if op == "comp":
        return r"\bigl(" + coeff_tex(c["outer"]) + r"\circ " + coeff_tex(c["inner"]) + r"\bigr)"
    if op == "odd_power_sum":
        sign = c["sign"]
        power = "2j+1" if sign == 1 else "-(2j+1)" if sign == -1 else str(sign) + "(2j+1)"
        return r"\left(\sum_{j=0}^{k-1}" + generator_tex(c["generator"], action=True) + "^{" + power + r"}\right)"
    if op == "norm_power_sum":
        return r"\left(\sum_{j=0}^{q-1}" + generator_tex(c["generator"], action=True) + r"^{j}\right)"
    raise TemplateError("cannot render unknown Fox coefficient")


def row_tex(row):
    op = row["op"]
    if op == "zero_row":
        return "0"
    if op == "identity_pivot":
        return cochain_tex(row["generator"])
    if op == "term":
        x = cochain_tex(row["generator"])
        return x if row["coefficient"]["op"] == "one" else coeff_tex(row["coefficient"]) + r"\bigl(" + x + r"\bigr)"
    if op == "add":
        return r"\bigl(" + row_tex(row["left"]) + "+" + row_tex(row["right"]) + r"\bigr)"
    raise TemplateError("cannot render unknown Fox row")


def input_rows_tex(profile):
    """Sparse full-cochain row vector; every unlisted column is zero."""
    return r"\begin{pmatrix}" + r"\\".join(map(row_tex, profile["tree"]["input_rows"])) + r"\end{pmatrix}"


def target_rows_tex(profile):
    return r"\begin{pmatrix}" + r"\\".join(map(row_tex, profile["tree"]["target_rows"])) + r"\end{pmatrix}"


def row_op_tex(op):
    kind = op["op"]
    if kind == "swap":
        return r"R_1\leftrightarrow R_2"
    if kind in ("add_fst", "add_snd"):
        i, j = (1, 2) if kind == "add_fst" else (2, 1)
        return f"R_{i} " + r"\leftarrow " + f"R_{i}+" + coeff_tex(op["coefficient"]) + r"\circ " + f"R_{j}"
    if kind in ("scale_fst", "scale_snd"):
        i = 1 if kind == "scale_fst" else 2
        return (f"R_{i} " + r"\leftarrow " + coeff_tex(op["forward"]) + r"\circ " + f"R_{i}"
                + r"\quad[\text{carried inverse: }" + coeff_tex(op["inverse"]) + "]")
    raise TemplateError("cannot render unknown row operation")


def col_op_tex(op):
    kind = op["op"]
    if kind == "swap":
        return cochain_tex(op["left"]) + r"\leftrightarrow " + cochain_tex(op["right"])
    if kind == "transvect":
        x = cochain_tex(op["target"])
        return x + r"\leftarrow " + x + "+" + coeff_tex(op["coefficient"]) + r"\bigl(" + cochain_tex(op["source"]) + r"\bigr)"
    if kind == "scale":
        x = cochain_tex(op["generator"])
        return (x + r"\leftarrow " + coeff_tex(op["forward"]) + r"\bigl(" + x + r"\bigr)"
                + r"\quad[\text{carried inverse: }" + coeff_tex(op["inverse"]) + "]")
    raise TemplateError("cannot render unknown column operation")


def operations_tex(profile):
    """Ordered row operations and input substitutions, including inverse data."""
    lines = []
    for name, label, renderer in (("row_ops", "R", row_op_tex), ("column_ops", "C", col_op_tex)):
        ops = profile["tree"][name]
        if not ops:
            lines.append(r"\mathcal " + label + r"&=\mathrm{id}")
        for i, op in enumerate(ops, 1):
            lines.append(r"\mathcal " + label + "_{" + str(i) + r"}&:\quad " + renderer(op))
    return r"\begin{aligned}" + r"\\".join(lines) + r"\end{aligned}"


def render_tex(envelope):
    p = validate(envelope)
    lines = [
        "% STAGED symbolic Fox template; no concrete word/action/resolver/parameter values are hashed.",
        "% fox-template-hash: " + envelope["template_hash"],
        "% Syntax/hash/render agreement alone is NOT Lean synchronization. Replay Lean for strong checking.",
        "% " + p["hash_scope"], "% " + p["application_scope"], "% " + p["composition"],
        "% q: " + p["parameters"]["q"]["role"], "% k: " + p["parameters"]["k"]["role"],
        "% alphabet: " + canonical_json(p["alphabet"]),
        "% S,T,W_i denote generator actions; S_2 denotes the omega2 action, not S squared.",
        "% Rows below are full-cochain formulas; unlisted columns are zero. Empty finite sums are zero.",
        "% Row list applies head first. Column list is C_1 composed with ... composed with C_m.",
        "% Printed column arrows are input substitutions; the rightmost substitution acts first.",
    ]
    for profile in p["profiles"]:
        lines += ["% sector: " + profile["sector"],
                  "% interpretation: " + profile["interpretation"], "% k binding: " + profile["k_binding"],
                  "% input evaluation: " + profile["input_evaluation_bridge"],
                  "% operation denotation: " + profile["denotation_bridge"],
                  "% actual certificate fields: " + canonical_json(profile["certificate_bridges"]),
                  r"\[D_{\mathrm{" + profile["sector"] + r"}}(x)=" + input_rows_tex(profile) + r".\]",
                  r"\[" + operations_tex(profile) + r".\]",
                  r"\[D_{\mathrm{" + profile["sector"] + r"}}^{\mathrm{reduced}}(x)=" + target_rows_tex(profile) + r".\]"]
    return "\n".join(lines) + "\n"


def _test_envelope():
    """Synthetic grammar fixture only; never used by generation or synchronization."""
    sigma, tau, pivot = {"kind": "sigma"}, {"kind": "tau"}, {"kind": "wild", "index": 2}
    def atom(g, power):
        return {"op": "atom", "symbol": {"kind": "generator_power", "generator": g, "power": power}}
    s, si = atom(sigma, 1), atom(sigma, -1)
    odd = {"op": "odd_power_sum", "generator": tau, "parameter": "k", "sign": 1}
    norm = {"op": "norm_power_sum", "generator": tau, "parameter": "q"}
    tree = {"row_ops": [{"op": "scale_fst", "forward": {"op": "comp", "outer": odd, "inner": s}, "inverse": si},
                        {"op": "add_snd", "coefficient": {"op": "neg", "value": {"op": "one"}}}],
            "column_ops": [{"op": "transvect", "target": sigma, "source": tau, "coefficient": norm}],
            "input_rows": [{"op": "term", "coefficient": si, "generator": tau},
                           {"op": "add", "left": {"op": "zero_row"}, "right": {"op": "term", "coefficient": {"op": "one"}, "generator": pivot}}],
            "target_rows": [{"op": "identity_pivot", "generator": tau}, {"op": "zero_row"}]}
    profiles = []
    for sector in SECTORS:
        profiles.append({"sector": sector, "interpretation": "TameSym.ramifiedEnd" if sector == "ramified" else "TameSym.splitEnd",
                         "k_binding": K_BINDINGS[sector], "denotation_bridge": NAMESPACE + "denote_" + sector,
                         "input_evaluation_bridge": NAMESPACE + sector + "_input_apply",
                         "certificate_bridges": {family: NAMESPACE + sector + "_" + family + "_signature" for family in ("pair", "mobile")},
                         "tree": deepcopy(tree)})
    payload = {"schema": SCHEMA, "alphabet": {"h": 0, "n": 2, "wild_count": 3, "x2": 2},
               "application_scope": APPLICATION_SCOPE, "composition": COMPOSITION, "hash_scope": HASH_SCOPE,
               "parameters": deepcopy(PARAMETERS), "profiles": profiles}
    return {"payload": payload, "status": "STAGED", "template_hash": digest(payload)}


def self_test():
    obj = _test_envelope()
    assert loads(canonical_json(obj)) == obj
    profile = obj["payload"]["profiles"][0]
    assert r"S^{-1}\bigl(x_{\tau}\bigr)" in input_rows_tex(profile)
    assert "carried inverse" in operations_tex(profile)
    comp = profile["tree"]["row_ops"][0]["forward"]
    assert coeff_tex(comp).index(r"\sum") < coeff_tex(comp).index(r"\circ S")
    assert r"\sum_{j=0}^{q-1}" in operations_tex(profile)
    assert "NOT Lean synchronization" in render_tex(obj)
    assert target_rows_tex(profile) == r"\begin{pmatrix}x_{\tau}\\0\end{pmatrix}"
    count = 7
    def rejected(mutate):
        nonlocal count
        bad = deepcopy(obj)
        mutate(bad["payload"])
        bad["template_hash"] = digest(bad["payload"])
        try:
            validate(bad)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid Fox artifact accepted")
    def tree(p):
        return p["profiles"][0]["tree"]
    mutations = [
        lambda p: p.update(schema="approved"), lambda p: p.update(extra=0),
        lambda p: p.update(composition="commutative"), lambda p: p.update(hash_scope="actual word"),
        lambda p: p.update(application_scope="unconditional"),
        lambda p: p["alphabet"].update(h=True), lambda p: p["alphabet"].update(h=0.0),
        lambda p: p["alphabet"].update(h=-1), lambda p: p["alphabet"].update(h=1),
        lambda p: p["alphabet"].update(n=2.0), lambda p: p["alphabet"].update(n=False),
        lambda p: p["alphabet"].update(x2=1), lambda p: p["alphabet"].update(wild_count=4),
        lambda p: p["parameters"].update(k=0), lambda p: p["parameters"]["k"].update(value=3),
        lambda p: p["parameters"]["k"].update(role="handle rank"),
        lambda p: p["parameters"]["q"].update(domain="Int"),
        lambda p: p.update(profiles=[]), lambda p: p.update(profiles={}),
        lambda p: p["profiles"].reverse(), lambda p: p["profiles"][0].update(sector="ramified"),
        lambda p: p["profiles"][0].update(interpretation="TameSym.ramifiedEnd"),
        lambda p: p["profiles"][0].update(k_binding="ambient group order/2"),
        lambda p: p["profiles"][0].update(denotation_bridge="other"),
        lambda p: p["profiles"][0].update(input_evaluation_bridge="other"),
        lambda p: p["profiles"][0]["certificate_bridges"].update(pair="other"),
        lambda p: tree(p).update(row_ops={}), lambda p: tree(p).update(column_ops={}),
        lambda p: tree(p).update(input_rows=[]), lambda p: tree(p).update(target_rows=[]),
        lambda p: tree(p)["row_ops"][0].pop("inverse"),
        lambda p: tree(p)["row_ops"][0].update(op="opaque_inverse"),
        lambda p: tree(p)["row_ops"][0].update(op=[]),
        lambda p: tree(p)["row_ops"][0]["forward"].update(extra=0),
        lambda p: tree(p)["row_ops"][0]["forward"].pop("inner"),
        lambda p: tree(p)["row_ops"][0]["forward"]["outer"].update(parameter="q"),
        lambda p: tree(p)["row_ops"][0]["forward"]["outer"].update(sign=True),
        lambda p: tree(p)["column_ops"][0]["coefficient"].update(parameter="k"),
        lambda p: tree(p)["column_ops"][0].update(source={"kind": "sigma"}),
        lambda p: tree(p)["column_ops"][0].update(target={"kind": "other"}),
        lambda p: tree(p)["input_rows"][0]["coefficient"]["symbol"].update(power=1.0),
        lambda p: tree(p)["input_rows"][0]["coefficient"]["symbol"].update(power=False),
        lambda p: tree(p)["input_rows"][0]["coefficient"].update(op="inverse"),
        lambda p: tree(p)["input_rows"][0].update(generator={"kind": "tau", "index": 0}),
        lambda p: tree(p)["input_rows"][1]["left"].update(extra=0),
        lambda p: tree(p)["target_rows"][0].update(op="term"),
    ]
    for mutate in mutations:
        rejected(mutate)
    for index in (True, 2.0, "2", -1, 3):
        rejected(lambda p, i=index: tree(p)["input_rows"][1]["right"]["generator"].update(index=i))
    # Exercise the generic grammar's other nodes without claiming factory provenance.
    for coeff in ({"op": "zero"}, {"op": "one"},
                  {"op": "add", "left": {"op": "zero"}, "right": {"op": "one"}},
                  {"op": "atom", "symbol": {"kind": "sigma2_power", "power": -2}},
                  {"op": "atom", "symbol": {"kind": "projector"}}):
        validate_coeff(coeff, 2)
        assert coeff_tex(coeff)
        count += 1
    for row_op in ({"op": "swap"}, {"op": "add_fst", "coefficient": {"op": "one"}},
                   {"op": "scale_snd", "forward": {"op": "one"}, "inverse": {"op": "one"}}):
        validate_row_op(row_op, 2)
        assert row_op_tex(row_op)
        count += 1
    for col_op in ({"op": "swap", "left": {"kind": "sigma"}, "right": {"kind": "tau"}},
                   {"op": "scale", "generator": {"kind": "wild", "index": 2}, "forward": {"op": "one"}, "inverse": {"op": "one"}}):
        validate_col_op(col_op, 2)
        assert col_op_tex(col_op)
        count += 1
    # Legal rehashed changes are intentionally not provenance-checked by validate.
    # The strong CLI check compares the complete artifact to a fresh Lean export.
    altered = deepcopy(obj)
    c = altered["payload"]["profiles"][0]["tree"]["row_ops"][0]["forward"]
    c["outer"], c["inner"] = c["inner"], c["outer"]
    altered["template_hash"] = digest(altered["payload"])
    validate(altered)
    assert altered != obj and render_tex(altered) != render_tex(obj)
    count += 1
    for text in ("[]", "NaN", "Infinity", "-Infinity", '{"payload":0,"payload":1}',
                 canonical_json(obj).replace('"STAGED"', '"APPROVED"'),
                 canonical_json(obj).replace(obj["template_hash"], "0"*64),
                 canonical_json(obj).replace('"h":0', '"h":0,"h":0'),
                 canonical_json(obj).replace('"op":"one"', '"op":"one","op":"one"')):
        try:
            loads(text)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid Fox envelope accepted")
    for h in (True, -1, 0.0):
        try:
            from_lean("does-not-run", h)
        except TemplateError:
            count += 1
        else:
            raise AssertionError("invalid requested rank accepted")
    print(f"FOX_TOOL_SELF_TEST_PASS|{count}")
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
        integer(args.h, "handle rank", natural=True)
        if "general-certificate-staged" not in args.out.resolve().parts:
            raise TemplateError("Fox output must be inside general-certificate-staged")
        obj = from_lean(args.lean_runner, args.h)
        args.out.mkdir(parents=True, exist_ok=True)
        base = args.out / f"tame-splice-h{args.h}"
        base.with_suffix(".fox.json").write_text(canonical_json(obj)+"\n")
        base.with_suffix(".fox.tex").write_text(render_tex(obj))
        print(f"STAGED_FOX_GENERATED|{args.h}|{obj['template_hash']}")
    else:
        paths = sorted(args.directory.glob("*.fox.json"))
        if not paths:
            raise TemplateError("no staged Fox artifacts found")
        for path in paths:
            obj = loads(path.read_text())
            h = obj["payload"]["alphabet"]["h"]
            if path.name != f"tame-splice-h{h}.fox.json":
                raise TemplateError("noncanonical Fox filename")
            if path.with_suffix(".tex").read_text() != render_tex(obj):
                raise TemplateError("generated Fox TeX drift")
            if args.lean_runner and from_lean(args.lean_runner, h) != obj:
                raise TemplateError("Fox artifact differs from the actual Lean tree")
            mode = "Lean-replayed" if args.lean_runner else "artifact-only; NOT Lean-synchronized"
            print(f"STAGED_FOX_CHECK|{mode}|{path.name}|{obj['template_hash']}")


if __name__ == "__main__":
    try:
        main()
    except (TemplateError, OSError, ValueError, RecursionError) as exc:
        raise SystemExit(f"Fox artifact error: {exc}") from exc
