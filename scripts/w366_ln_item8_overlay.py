#!/usr/bin/env python3
"""STAGED item-8 OVERLAY for the six W362 L/N0/Npc certificate packets.

This is the second composer, not a change to the first. It never opens a packet file for
writing, never touches `scripts/w362_ln_certificate_packet.py`, and never recomputes a packet
hash into a new value: it reads each packet, PINS the packet hash it was built against, and
writes its regenerated item-8 section beside the packet as `*.item8-w366.tex`.

W363-PUB2 T9 declined to regenerate the packets, because doing so means either modifying the
W362 composer, which changes its recorded packet hashes, or adding a second composer that
owns the same paths, which w362-pub-note T3.a fact 6 rules out. This lane honours both: the
overlay owns paths NO other producer writes, and it fails loudly if a packet it overlays ever
changes underneath it.

What the overlay regenerates is item 8 WHOLE, both halves, from the two checked exporters:

* the coordinate half from `w363_ln_coordinate_tex`, bridge kind `record_target`;
* the normal-form half from `w366_ln_gauss_tex`, whose printed sign and printed exponent are
  `record_target` and whose value equation is `restated_identity`.

Nothing is retyped: every paragraph, reference and superseded TODO is read out of the packet
itself, and both displays are re-rendered from the validated artifact JSON rather than copied
from the generated TeX.

What it does NOT change: the normal-form RECORDS are still `named_but_unbound`. The overlay
carries that as a residual TODO and the validator refuses to let it be dropped.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from w361_general_word_tex import TemplateError, canonical_json, fields, reject_duplicates
from w363_ln_stokes_tex import tex_escape
import w362_ln_certificate_packet as packet
import w363_ln_coordinate_tex as coordinate
import w366_ln_gauss_tex as gauss

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "gq2.w366.ln-item8-overlay.v1.staged"
DOMAIN = b"GQ2-W366-LN-ITEM8-OVERLAY\0"
SUFFIX = ".item8-w366"
ITEM = 8
RECORD_TARGET = "record_target"
RESTATED = "restated_identity"
UNBOUND = "named_but_unbound"

# Item 8's binding kinds before this lane (W363-PUB2 T6) and after it. The overlay pins both
# so that the artifact itself, and not only a note, records what changed.
BRIDGE_KINDS = {
    "before": {"coordinate_half": RECORD_TARGET,
               "gauss_exponent": UNBOUND,
               "gauss_sign": UNBOUND,
               "gauss_value_equation": UNBOUND,
               "normal_form_records": UNBOUND},
    "after": {"coordinate_half": RECORD_TARGET,
              "gauss_exponent": RECORD_TARGET,
              "gauss_sign": RECORD_TARGET,
              "gauss_value_equation": RESTATED,
              "normal_form_records": UNBOUND},
}

RECORDS_TODO = (
    "TODO: the quadratic normal form RECORDS themselves are still named_but_unbound, and "
    "this overlay does not change that. SourceOddHessian, SourceCompactHessian and "
    "SourceWallHessian remain unreachable without instantiating a coefficient module, which "
    "no exporter lane may do. What changed is that the Gauss cells no longer wait for them: "
    "they are supplied by theorems about the endpoint phase function, which is quantified "
    "over the coefficient group. Naming is not binding.")

SCOPE = (
    "Ledger item 8 only, both halves, for one W362 packet. This is an OVERLAY: it is written "
    "beside the packet, it does not modify the packet or any of the four files the packet's "
    "own manifest covers, and it does not change the recorded W362 packet hash, which it "
    "pins instead. No coefficient module, marking, field, resolver, eta or source "
    "certificate is selected.")

WARNING = (
    "The packet this overlay names is NOT regenerated and its hash is NOT recomputed into a "
    "new value: the hash below is the packet's own recorded hash, reproduced from the "
    "packet's stored payload by the W362 composer's own digest, and the overlay check fails "
    "if it ever stops reproducing. The overlay supersedes the packet's item-8 TODO for a "
    "reader who has both files; it does not edit the packet's text, so the packet still "
    "carries that TODO and should be read together with this file. Whether the packets are "
    "instead regenerated in place remains W363-PUB2 owner decision 13. STAGED proposal: not "
    "owner approval, not a manifest entry, not a gate.")

PROVENANCE_FILES = tuple(sorted(
    set(gauss.PROVENANCE_FILES) | set(coordinate.PROVENANCE_FILES)
    | {"scripts/w362_ln_certificate_packet.py", "scripts/w366_ln_item8_overlay.py"}))


def digest(payload):
    return hashlib.sha256(DOMAIN + canonical_json(payload).encode()).hexdigest()


def read_json(path):
    return json.loads(path.read_text(), object_pairs_hook=reject_duplicates)


def packet_item8(packet_obj):
    """The packet's own item-8 section, checked against the packet's recorded hash."""
    fields(packet_obj, {"payload", "status", "packet_hash"}, "W362 packet envelope")
    if packet_obj["status"] != "STAGED":
        raise TemplateError("W362 packets must remain STAGED")
    p = packet_obj["payload"]
    if packet.digest(p) != packet_obj["packet_hash"]:
        raise TemplateError("W362 packet hash does not reproduce: the overlay refuses to "
                            "pin a packet it cannot re-derive")
    matches = [s for s in p["sections"] if s["number"] == ITEM]
    if len(matches) != 1:
        raise TemplateError("W362 packet does not carry exactly one item-8 section")
    return p, matches[0]


def build_overlay(directory, stem):
    packet_obj = read_json(directory / (stem + ".packet.json"))
    p, section = packet_item8(packet_obj)
    family = p["family"]
    structural = p["fox"]["payload"]["structural"]
    gauss_obj = gauss.loads((directory / (gauss.artifact_name(
        {"family": family, "structural": structural}) + ".gauss.json")).read_text())
    coordinate_obj = coordinate.loads((directory / (coordinate.artifact_name(
        {"family": family, "structural": structural}) + ".coordinate.json")).read_text())
    if gauss_obj["payload"]["structural"] != structural:
        raise TemplateError("overlay gauss artifact is at other parameters than the packet")
    if coordinate_obj["payload"]["structural"] != structural:
        raise TemplateError("overlay coordinate artifact is at other parameters than the "
                            "packet")
    payload = {
        "application_scope": SCOPE,
        "bridge_kinds": BRIDGE_KINDS,
        "coordinate_artifact": coordinate.artifact_name(coordinate_obj["payload"]),
        "coordinate_hash": coordinate_obj["template_hash"],
        "family": family,
        "gauss_artifact": gauss.artifact_name(gauss_obj["payload"]),
        "gauss_hash": gauss_obj["template_hash"],
        "packet": stem,
        "packet_hash": packet_obj["packet_hash"],
        "residual_todos": [RECORDS_TODO] + list(gauss_obj["payload"]["todos"]),
        "schema": SCHEMA,
        "section": {"number": ITEM, "paragraphs": section["paragraphs"],
                    "references": section["references"],
                    "standing_axiom_references": section["standing_axiom_references"],
                    "title": section["title"]},
        "structural": structural,
        "superseded_todos": section["todos"],
        "warning": WARNING,
    }
    return {"payload": payload, "status": "STAGED", "template_hash": digest(payload)}


def validate(envelope, directory):
    fields(envelope, {"payload", "status", "template_hash"}, "LN item-8 overlay envelope")
    if envelope["status"] != "STAGED":
        raise TemplateError("LN item-8 overlays must remain STAGED")
    p = envelope["payload"]
    fields(p, {"application_scope", "bridge_kinds", "coordinate_artifact", "coordinate_hash",
               "family", "gauss_artifact", "gauss_hash", "packet", "packet_hash",
               "residual_todos", "schema", "section", "structural", "superseded_todos",
               "warning"}, "LN item-8 overlay payload")
    if p["schema"] != SCHEMA:
        raise TemplateError("LN item-8 overlay schema mismatch")
    if canonical_json(p["bridge_kinds"]) != canonical_json(BRIDGE_KINDS):
        raise TemplateError("LN item-8 overlay bridge kinds may not be relabelled")
    if p["bridge_kinds"]["after"]["normal_form_records"] != UNBOUND:
        raise TemplateError("the normal-form records are still unbound after this lane")
    todos = p["residual_todos"]
    if not isinstance(todos, list) or len(todos) != 3 or todos[0] != RECORDS_TODO:
        raise TemplateError("the residual TODOs may not be dropped or reordered")
    for todo in todos:
        if not isinstance(todo, str) or not todo.startswith("TODO: "):
            raise TemplateError("LN item-8 overlay TODO must be a marked nonempty string")
    if not isinstance(p["superseded_todos"], list) or not p["superseded_todos"]:
        raise TemplateError("the overlay must name the packet TODO it supersedes")
    # Everything else is re-derived from the packet and the two artifacts on disk, so a
    # drift in any of the three, or in this overlay's own text, is refused.
    rebuilt = build_overlay(directory, p["packet"])
    if canonical_json(rebuilt) != canonical_json(envelope):
        raise TemplateError("LN item-8 overlay does not re-derive from its packet and "
                            "artifacts: one of them has drifted")
    if envelope["template_hash"] != digest(p):
        raise TemplateError("LN item-8 overlay envelope hash mismatch")
    return p


def provenance(envelope):
    return {"schema": SCHEMA + ".provenance", "status": "STAGED",
            "template_hash": envelope["template_hash"],
            "scope": "Direct source bytes only; not a transitive build, coefficient module, "
                     "or certificate attestation.",
            "sha256": {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                       for name in PROVENANCE_FILES}}


# ---------------------------------------------------------------- rendering


def render_tex(envelope, directory):
    p = validate(envelope, directory)
    gauss_obj = gauss.loads(
        (directory / (p["gauss_artifact"] + ".gauss.json")).read_text())
    coordinate_obj = coordinate.loads(
        (directory / (p["coordinate_artifact"] + ".coordinate.json")).read_text())
    lines = [
        "% STAGED W366 item-8 OVERLAY for " + p["packet"] + ". It is written BESIDE the "
        "packet and modifies nothing the packet's own manifest covers.",
        "% item8-overlay-hash: " + envelope["template_hash"],
        "% pinned W362 packet hash, unchanged by this lane: " + p["packet_hash"],
        "% coordinate half: " + p["coordinate_artifact"] + " " + p["coordinate_hash"],
        "% normal-form half: " + p["gauss_artifact"] + " " + p["gauss_hash"],
        "% " + p["application_scope"],
        "% " + p["warning"],
        r"\subsection*{" + str(ITEM) + ". " + tex_escape(p["section"]["title"]) + "}",
    ]
    lines += [tex_escape(text) + "\n" for text in p["section"]["paragraphs"]]
    for todo in p["superseded_todos"]:
        lines.append(r"\par\noindent\textbf{[SUPERSEDED BY THIS OVERLAY: "
                     + tex_escape(todo["text"]) + "]}")
        if todo.get("missing_declaration"):
            lines.append(r"\par\noindent The declaration it named, \path{"
                         + todo["missing_declaration"] + "}, still does not exist. The two "
                         r"displays below come from \path{scripts/w363_ln_coordinate_export"
                         r".lean} and \path{scripts/w366_ln_gauss_export.lean} instead.")
    lines += [r"\paragraph{Item 8, first half: the change of variables (generated)}",
              coordinate.render_tex(coordinate_obj).rstrip("\n"),
              r"\paragraph{Item 8, second half: the normal-form Gauss display (generated)}",
              gauss.render_tex(gauss_obj).rstrip("\n"),
              r"\paragraph{Binding kinds, before and after this overlay}",
              r"\begin{itemize}"]
    for key in sorted(BRIDGE_KINDS["before"]):
        lines.append(r"\item \texttt{" + tex_escape(key.replace("_", " ")) + "}: "
                     + tex_escape(p["bridge_kinds"]["before"][key].replace("_", " "))
                     + r" $\to$ "
                     + tex_escape(p["bridge_kinds"]["after"][key].replace("_", " ")))
    lines.append(r"\end{itemize}")
    # Only the overlay's own residual TODO is printed here: the other two are the
    # normal-form display's own and are already printed with it above. All three are
    # carried in this overlay's JSON, under residual_todos.
    lines.append(r"\par\noindent\textbf{[" + tex_escape(p["residual_todos"][0]) + "]}")
    lines.append(r"\par\noindent The two further residual TODOs, on the absent second sign "
                 r"route and on the absent record route for the exponent, are printed with "
                 r"the normal-form display above and are carried in this overlay's JSON.")
    if p["section"]["references"]:
        lines += [r"\paragraph{Checked declarations (standard three axioms)}",
                  r"\begin{itemize}"]
        lines += [r"\item \path{" + ref + "}" for ref in p["section"]["references"]]
        lines.append(r"\end{itemize}")
    if p["section"]["standing_axiom_references"]:
        lines += [r"\paragraph{Standing-axiom declarations}", r"\begin{itemize}"]
        lines += [r"\item \path{" + ref + "}"
                  for ref in p["section"]["standing_axiom_references"]]
        lines.append(r"\end{itemize}")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------- self-test


def self_test():
    count = 0
    # The two tables the overlay pins are the content, so check them directly rather than
    # only through a round trip.
    assert set(BRIDGE_KINDS["before"]) == set(BRIDGE_KINDS["after"])
    assert BRIDGE_KINDS["before"]["gauss_sign"] == UNBOUND
    assert BRIDGE_KINDS["after"]["gauss_sign"] == RECORD_TARGET
    assert BRIDGE_KINDS["after"]["gauss_exponent"] == RECORD_TARGET
    assert BRIDGE_KINDS["after"]["gauss_value_equation"] == RESTATED
    assert BRIDGE_KINDS["before"]["normal_form_records"] == UNBOUND
    assert BRIDGE_KINDS["after"]["normal_form_records"] == UNBOUND
    assert BRIDGE_KINDS["before"]["coordinate_half"] == RECORD_TARGET
    count += 8
    assert RECORDS_TODO.startswith("TODO: ")
    assert "SourceOddHessian" in RECORDS_TODO and "named_but_unbound" in RECORDS_TODO
    assert "is NOT regenerated" in WARNING and "owner decision 13" in WARNING
    assert "OVERLAY" in SCOPE and "does not modify the packet" in SCOPE
    count += 4
    assert "scripts/w366_ln_item8_overlay.py" in PROVENANCE_FILES
    assert "scripts/w366_ln_gauss_export.lean" in PROVENANCE_FILES
    assert LEAN_COORDINATE in PROVENANCE_FILES
    count += 3

    base = {"application_scope": SCOPE, "bridge_kinds": BRIDGE_KINDS,
            "coordinate_artifact": "L-coordinate-h0-q2", "coordinate_hash": "0" * 64,
            "family": "L", "gauss_artifact": "L-gauss-h0-q2", "gauss_hash": "1" * 64,
            "packet": "packet-L-h0", "packet_hash": "2" * 64,
            "residual_todos": [RECORDS_TODO, "TODO: a", "TODO: b"], "schema": SCHEMA,
            "section": {"number": ITEM, "paragraphs": ["p"], "references": ["r"],
                        "standing_axiom_references": [], "title": "t"},
            "structural": {"h": 0, "q": 2},
            "superseded_todos": [{"text": "TODO: old", "missing_declaration": "X"}],
            "warning": WARNING}

    class NoDirectory:
        """A directory that cannot be read, so validate() must fail before re-deriving."""

        def __truediv__(self, other):
            raise TemplateError("no such staged directory")

    def wrap(p):
        return {"payload": p, "status": "STAGED", "template_hash": digest(p)}

    mutations = [
        lambda p: p.update(schema="bad"),
        lambda p: p.update(extra=1),
        lambda p: p.pop("warning"),
        # the before/after table is the claim, and may not be relabelled
        lambda p: p.update(bridge_kinds={"before": {}, "after": {}}),
        lambda p: p["bridge_kinds"]["after"].update(normal_form_records=RECORD_TARGET),
        lambda p: p["bridge_kinds"]["after"].update(gauss_value_equation=RECORD_TARGET),
        lambda p: p["bridge_kinds"]["before"].update(gauss_sign=RECORD_TARGET),
        # the residual TODOs may not be dropped, reordered or unmarked
        lambda p: p.update(residual_todos=[RECORDS_TODO, "TODO: a"]),
        lambda p: p.update(residual_todos=["TODO: a", "TODO: b", RECORDS_TODO]),
        lambda p: p.update(residual_todos=[RECORDS_TODO, "a", "TODO: b"]),
        lambda p: p.update(residual_todos=RECORDS_TODO),
        lambda p: p.update(superseded_todos=[]),
        lambda p: p.update(superseded_todos="TODO: old"),
    ]
    for mutate in mutations:
        payload = json.loads(canonical_json(base))
        mutate(payload)
        try:
            validate(wrap(payload), NoDirectory())
        except TemplateError:
            count += 1
        else:
            raise AssertionError("malformed LN item-8 overlay accepted")
    for envelope in ({"payload": json.loads(canonical_json(base)), "status": "APPROVED",
                      "template_hash": digest(base)},
                     {"payload": json.loads(canonical_json(base)), "status": "STAGED"},
                     {"payload": json.loads(canonical_json(base)), "status": "STAGED",
                      "template_hash": "0" * 64, "extra": 1}):
        try:
            validate(envelope, NoDirectory())
        except TemplateError:
            count += 1
        else:
            raise AssertionError("malformed LN item-8 overlay envelope accepted")
    # A well-formed overlay still has to re-derive from the directory, so the same payload
    # against an unreadable directory is refused too: nothing is taken on trust.
    try:
        validate(wrap(json.loads(canonical_json(base))), NoDirectory())
    except TemplateError:
        count += 1
    else:
        raise AssertionError("un-derived LN item-8 overlay accepted")
    print(f"LN_ITEM8_OVERLAY_SELF_TEST_PASS|{count}")
    return count


LEAN_COORDINATE = coordinate.LEAN_FILE


def packet_stems(directory):
    return sorted(path.name[:-len(".packet.json")]
                  for path in directory.glob("packet-*.packet.json"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("self-test")
    generate = sub.add_parser("generate")
    generate.add_argument("directory", type=Path)
    check = sub.add_parser("check")
    check.add_argument("directory", type=Path)
    args = parser.parse_args()
    if args.command == "self-test":
        self_test()
        return
    directory = args.directory
    if "general-ln-certificate-staged" not in directory.resolve().parts:
        raise TemplateError("LN item-8 overlays live inside general-ln-certificate-staged")
    stems = packet_stems(directory)
    if not stems:
        raise TemplateError("no W362 packets found to overlay")
    if args.command == "generate":
        for stem in stems:
            envelope = build_overlay(directory, stem)
            base = directory / (stem + SUFFIX)
            base.with_suffix(SUFFIX + ".json").write_text(canonical_json(envelope) + "\n")
            base.with_suffix(SUFFIX + ".tex").write_text(render_tex(envelope, directory))
            base.with_suffix(SUFFIX + ".provenance.json").write_text(
                canonical_json(provenance(envelope)) + "\n")
            print(f"STAGED_LN_ITEM8_OVERLAY_GENERATED|{stem}|"
                  f"{envelope['template_hash']}|packet {envelope['payload']['packet_hash']}")
        return
    paths = sorted(directory.glob("*" + SUFFIX + ".json"))
    paths = [path for path in paths if not path.name.endswith(SUFFIX + ".provenance.json")]
    if len(paths) != len(stems):
        raise TemplateError("every W362 packet must carry exactly one item-8 overlay")
    for path in paths:
        envelope = read_json(path)
        p = validate(envelope, directory)
        if path.name != p["packet"] + SUFFIX + ".json":
            raise TemplateError("noncanonical LN item-8 overlay filename")
        base = directory / (p["packet"] + SUFFIX)
        if base.with_suffix(SUFFIX + ".tex").read_text() != render_tex(envelope, directory):
            raise TemplateError("generated LN item-8 overlay TeX drift")
        if read_json(base.with_suffix(SUFFIX + ".provenance.json")) != provenance(envelope):
            raise TemplateError("LN item-8 overlay direct-source provenance drift")
        print(f"STAGED_LN_ITEM8_OVERLAY_CHECK|{p['packet']}|{envelope['template_hash']}"
              f"|packet {p['packet_hash']} unchanged")


if __name__ == "__main__":
    main()
