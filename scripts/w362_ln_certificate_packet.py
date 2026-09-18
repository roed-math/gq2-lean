#!/usr/bin/env python3
"""Compose STAGED ten-item L/N0/Npc certificate packets from checked Lean exports.

This is an additive publication experiment. It is not a frozen gate, an appendix
migration, a census amendment, or owner approval, and it does not touch
`generated/hash-manifest.json` or `generated/appendix/*.tex`.

What is synchronized and what is not, stated per item rather than in general:

* items 1 and 10 come from the existing L/N word exporter and its uniform Lean
  denotation bridges;
* items 4 and 5 come from `w362_ln_fox_tex`, whose data Lean serializes out of the
  actual `FoxCertificate` records under `rfl` signature theorems;
* items 2, 3, 6, 7, 8 and 9 are carried by **checked declarations**: the probe proves
  each cited declaration exists, has at most the standard three axioms, and prints its
  elaborated statement, and the check compares that transcript on replay. They have
  **no generated display**, and each such section names the exporter declaration that
  would produce one and that does not exist. No formula is retyped from prose.

The prose is reviewable exposition of the checked objects, not itself a theorem.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

import w361_general_ln_word_tex as word
import w362_ln_fox_tex as fox
from w361_general_word_tex import TemplateError, canonical_json, fields, reject_duplicates

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "gq2.w362.ln-certificate-packet.v1.staged"
DOMAIN = b"GQ2-W362-LN-CERTIFICATE-PACKET\0"
OUTPUT_COMPONENT = "general-ln-certificate-staged"

D = "GQ2.Dyadic."
W = D + "Words."
I = D + "Instances."
C = D + "Certificates."
G = D + "GeneralTemplateLN."
LSQ = D + "LSquare."
MISSING = "does not exist in this tree"

COMMON_IMPORTS = [D + "Word.GeneralTemplateLN", D + "Word.GeneralTemplateLNCanonical",
                  I + "FieldFamilyCampaignBoundary"]

IMPORTS = {
    "L": COMMON_IMPORTS + [
        W + "L", C + "LFox", C + "LJacobian", C + "L",
        I + "GammaLReconstruction", I + "GammaLAnalyticLeaves", I + "GammaLSourceArfGeneral",
        I + "GammaLOddDegreeGrandAssembly", I + "LHessianCertificates",
        I + "LBoundaryHessianCertificates"],
    "N0": COMMON_IMPORTS + [
        W + "N0", D + "GeneralCertificates", C + "N0Fox", C + "N0",
        I + "WordPhase", I + "WordPhaseCompactNFinal", I + "CompactNHessianCertificates",
        I + "CompactNBoundaryHessianCertificates"],
    "Npc": COMMON_IMPORTS + [
        W + "Npc", D + "SelectedEta", C + "NpcFox", I + "NpcCore",
        I + "NpcCandidateRN", I + "NpcCandidateStokes", I + "NpcDeterminantFinal",
        I + "NpcUnramifiedFullOffsetHessian", I + "NpcRamifiedFullOffsetHessian",
        I + "NpcUnramifiedComparison", I + "NpcHessianCertificates",
        I + "NpcBoundaryHessianCertificates"],
}

# Per family: the exact declarations that carry each ledger item.
TREE = {
    "L": {
        1: [W + "LSq.rawLsq", W + "LSq.lSqW", G + "canon_rawLsq", G + "denote_canon_rawLsq",
            G + "denote_rawLsq", W + "LSq.wf_rawLsq"],
        2: [W + "LSq.eval_pro2_lSqW_eq_sqRelWord", LSQ + "lCanonicalTameSpecialization",
            LSQ + "wordCertificateRN_lSq_pow", LSQ + "wordCertificateRN_lSq_qOf",],
        3: [C + "LSq.foxD_lSq_unram", C + "LSq.foxD_lSq_ram"],
        4: [C + "LSq.lSqJacobianCertUnram", C + "LSq.lSqJacobianCertRam",
            C + "LSq.lSqJacobianCertScalar"],
        5: [C + "LSq.lSqUnramNormalForm", C + "LSq.lSqRamNormalForm", C + "LSq.lSqRamOps"],
        6: [LSQ + "stokesDualityCertificate_of_actionImage"],
        7: [C + "LSqStokes.hessRelZ_lSq"],
        8: [I + "LHessianCertificates.unramifiedHessian",
            I + "LHessianCertificates.ramifiedHessian",
            I + "LHessianCertificates.unramifiedHessian_baseSign",
            I + "LHessianCertificates.ramifiedHessian_baseSign"],
        9: [I + "LBoundaryHessianCertificates.lBoundaryHessian",
            LSQ + "determinantResidue_lSq_pow", LSQ + "lSquareAnalyticLeavesRN_pow"],
        10: [],
    },
    "N0": {
        1: [W + "rawNCompact", W + "nCompactW", G + "canon_rawNCompact",
            G + "denote_canon_rawNCompact", G + "denote_rawNCompact",
            W + "wf_rawNCompact"],
        2: [W + "pro2_nCompact", W + "eval_pro2_nCompact", D + "genCertNProTwoWord",
            D + "genCertNTameSpecializes",
            I + "WordPhaseCompactNFinal.wPcNWordCertificateRN",],
        3: [C + "foxD_nCompact_unram", C + "foxD_nCompact_ram"],
        4: [C + "nCompactJacobianCertUnram", C + "nCompactJacobianCertRam"],
        5: [C + "nCompactUnramNormalForm", C + "nCompactRamNormalForm",
            C + "nCompactUnramOps", C + "nCompactRamOps"],
        6: [I + "WordPhase.wPh_nCand_stokes"],
        7: [C + "hessRelZ_nCompact"],
        8: [I + "CompactNHessianCertificates.compactNUnramifiedHessian",
            I + "CompactNHessianCertificates.compactNRamifiedHessian",
            I + "CompactNHessianCertificates.compactNUnramifiedComparison_add",
            I + "CompactNHessianCertificates.compactNRamifiedComparison_add"],
        9: [I + "CompactNBoundaryHessianCertificates.compactNBoundaryHessian",
            I + "WordPhaseCompactNFinal.wPcN_affineDeterminantCertificate"],
        10: [],
    },
    "Npc": {
        1: [W + "Npc.rawNpc", W + "Npc.npcW", W + "Npc.npcWUnit", G + "canon_rawNpc",
            G + "denote_canon_rawNpc", G + "denote_canon_rawNpc_display",
            G + "denote_rawNpc", G + "denote_rawNpc_display", G + "wf_rawNpc_display",
            W + "Npc.wf_rawNpc"],
        2: [W + "Npc.eval_pro2_npcW", I + "NProcyclicCore.npcProTwoWordUnit",
            W + "Npc.npcWUnit_eq_display",
            I + "NpcDeterminantFinal.npcWordCertificateRN",
            I + "NpcCandidateRN.npcWordCertificateRN_of_determinant",],
        3: [C + "Npc.foxD_npc_unram", C + "Npc.foxD_npc_ram"],
        4: [C + "Npc.npcJacobianCertUnram", C + "Npc.npcJacobianCertRam"],
        5: [C + "Npc.npcUnramOps", C + "Npc.npcRamOps", C + "Npc.npcBlockRow",
            C + "Npc.tameUnramRow", C + "Npc.tameRow"],
        6: [I + "NpcCandidateStokes.npcCand_stokes",
            I + "NpcCandidateStokes.npcCand_stokes_displayed"],
        7: [I + "NpcUnramifiedFullOffsetHessian.hessRelZ_npcW_evenPhiNormal",
            I + "NpcRamifiedFullOffsetHessian.hessRelZ_npcW_evenTwistedNormal"],
        8: [I + "NpcHessianCertificates.npcUnramifiedHeadHessian",
            I + "NpcHessianCertificates.nonempty_npcRamifiedHeadHessian",
            I + "NpcUnramifiedComparison.wPnpcPhiCoordsEquiv"],
        9: [I + "NpcBoundaryHessianCertificates.npcBoundaryHessian",
            I + "NpcDeterminantFinal.npcAffineDeterminantCertificate"],
        10: [],
    },
}

TITLES = {
    1: "Exact syntax tree and semantic binding",
    2: "The two specialization reductions",
    3: "The evaluated Fox Jacobian",
    4: "Ordered invertible operations and carried inverses",
    5: "The reduced normal matrix",
    6: "The Stokes chain identity",
    7: "The extraspecial Hessian",
    8: "Change of variables to quadratic normal form",
    9: "The affine phase-cover certificate",
    10: "Same-tree hashes, replay and trust boundary",
}

# Declarations that legitimately carry MORE than the standard three axioms: the field
# selection adapters inherit the documented standing arithmetic/reciprocity inputs. They are
# pinned for existence and their full axiom list is printed, never silently folded into the
# standard-three claim. See literature-axioms-dyadic.md.
STANDING = {
    "L": {2: [I + "FieldFamilyCampaignBoundary.hasSelectedRowResidualRN_l"]},
    "N0": {2: [I + "FieldFamilyCampaignBoundary.hasSelectedRowResidualRN_n0"]},
    "Npc": {2: [I + "FieldFamilyCampaignBoundary.hasSelectedRowResidualRN_npc"]},
}

STANDING_PROSE = (
    "The field-selection adapter below is NOT standard-three: it inherits the documented "
    "standing arithmetic and reciprocity inputs, and the probe prints its full axiom list "
    "rather than gating it. Standard-three analytic word certificates do not make the field "
    "theorem axiom-free.")

# Items whose display is generated and synchronized, and how.
GENERATED = {1: "the L/N word exporter", 4: "the L/N Fox exporter",
             5: "the L/N Fox exporter", 10: "the packet hashes"}

# For each non-generated item, the exporter declaration that would supply a display and
# that does not exist. These names are proposals, not references to existing code.
MISSING_EXPORTERS = {
    2: D + "W362LNSpecialization.specializationTemplate",
    3: D + "W362LNFox.inputRowsTemplate",
    6: D + "W362LNStokes.chainTemplate",
    7: D + "W362LNPhase.hessianTemplate",
    8: D + "W362LNPhase.coordinateTemplate",
    9: D + "W362LNCover.phaseCoverTemplate",
}

FAMILY_PROSE = {
    "L": {
        1: ["The word below is rendered from the exact Lean-exported canonical tree, not from a "
            "formula. It is the square-core word at degree 2h+1, not the retired collector word. "
            "The handle block is the unexpanded node; L omits it at rank zero, which is the "
            "original syntax convention and not an empty display."],
        2: ["The pro-two specialization is the evaluated square relator; the tame specialization "
            "is the canonical one, both uniformly in h. The final word certificate carries them "
            "as its own fields. Its scope is q = 2^f with Odd f: the producer is not stated for "
            "arbitrary even q, and the selected field endpoint retains the ramified-i hypothesis. "
            "The field adapter proves the required odd residue degree from the selected odd field "
            "degree; it is not an extension of the field scope."],
        3: ["Both rows are identities on ALL cochains, not only on the cocycle kernel, and every "
            "handle column vanishes at first order. Unramified: wild row a_tau + (1+S^-1) a_x0. "
            "Ramified: S^-1 a_x0, with tau fixed-point-free and trivial omega2 action. The "
            "universal tame row under the actual tame relation is S^-1(T-1) a_sigma + "
            "(S^-1 - N_q(T)) a_tau."],
        4: ["The lists below are Lean's own record fields, re-emitted by the exporter and bound to "
            "the records by rfl signature theorems. Every scale carries a formal inverse as data. "
            "Unramified uses wild += S*tame; sigma fixed-point-freeness is not required for that "
            "equality. Ramified scales the x0 column by S and needs the actual tame relation, tau "
            "fixed-point-freeness and trivial tau-omega2 action, but no wild-relator death."],
        5: ["Replay of the preceding lists gives these literal targets. The unramified pivot is at "
            "x0, not at the even families' x2 slot. Scalar degeneracy stays visible: with all "
            "actions trivial the two rows are tau over zero, not two independent pivots."],
        6: ["The certificate's stokes field is a StokesDualityCertificate for the actual word, "
            "supplied from the action-image route at even q. It is a statement about every finite "
            "elementary coefficient module pushed from the actual source, not a dimension count on "
            "simple modules."],
        7: ["At x0 = 0 the evaluated class-two value is the Wall head qDouble q_V U with "
            "U = (S^E(omega2))^-1, plus the handle planes. This is not the compact N plus form. "
            "The factor set is the full extraspecial (f,m), not only the polar form B_V. L's Gauss "
            "sign needs the action/Arf argument."],
        8: ["The all-rank original source Hessian records retain the actual comparison map, proved "
            "additive and then F2-linear, with the full quadratic identity and the original affine "
            "phase fields. L uses its actual qDouble/graph operator, not a plus-form substitution. "
            "The unramified and ramified base signs are minus and plus respectively."],
        9: ["The boundary producer derives the head-model and SourceArfData inputs at the actual "
            "relevant boundary, for q = 2^f with odd f, and returns the original record with both "
            "precise sign equivalences. A base Gauss sign alone would not be sufficient."],
    },
    "N0": {
        1: ["The word below is rendered from the exact Lean-exported canonical tree. Its "
            "conjugator is sigma, not sigma2, and its degree is 2+2h. The zero-count handle node "
            "is retained at rank zero and denotes the empty product."],
        2: ["Pro-two evaluation and the canonical tame specialization both hold at every rank and "
            "are the certificate's own fields. The complete certificate requires alpha >= 2 and "
            "nonzero even q; the word syntax alone allows every natural alpha and h."],
        3: ["Unramified wild row a_tau + (1-S^-1) a_x2; ramified wild row -S^-1 a_x2. The rows "
            "need only 1 <= alpha for their parity calculation, which does not weaken the final "
            "certificate's alpha >= 2 requirement."],
        4: ["Unramified: one row operation wild += S*tame. Ramified: one column scaling of the x2 "
            "column by S with carried inverse S^-1. Both lists are the records' own fields."],
        5: ["Unramified leaves the diagonal pivots S^-1 on tau and 1-S^-1 on x2. Ramified leaves "
            "the universal tame row intact and the wild row an x2 unit pivot."],
        6: ["The certificate's stokes field is supplied uniformly in alpha, h and q from the "
            "compact-N phase route."],
        7: ["At x2 = 0 and 2 <= alpha the evaluated value is q_V(c0) + B_V(c0,c1) plus the handle "
            "planes. The branch-free supply connects this to the actual source quotient at every "
            "h."],
        8: ["The all-rank original source Hessian records carry the actual comparison map, proved "
            "additive and then F2-linear, together with the full quadratic identity and the "
            "original affine phase fields."],
        9: ["The boundary producer derives all head-sector premises at every actual relevant "
            "boundary lift, and the affine determinant certificate is a separate theorem for "
            "every required cover and character."],
    },
    "Npc": {
        1: ["The word below is rendered from the exact Lean-exported canonical tree. The exporter "
            "canonicalizes EtaHat before serializing, so equivalent rational spellings share the "
            "word hash but not the envelope hash. An exact NpcDisplayFor is what ties the tree to "
            "a prescribed two-adic unit; no claim is made that every externally prescribed unit "
            "has a finite rational display."],
        2: ["The correction [D,x1] disappears in the pro-two specialization. The semantic "
            "arbitrary-displayed-unit specialization and the actual tame map come from the "
            "procyclic core. Npc is NOT omega2-only: the genuine eta exponent must not be "
            "replaced by the omega resolver, and expressions using A mean its actual resolved "
            "action, not an independently guessed scalar."],
        3: ["Unramified wild row (A^-1-1) a_x0 + a_tau + (1-B^-1) a_x2; ramified wild row "
            "(A^-1-1) a_x0 - B^-1 a_x2. Here B = sigma^(2^r) is the standard sigma-power atom, so "
            "one formal row covers every r."],
        4: ["Unramified: the same single row addition. Ramified: the x2 column is scaled by "
            "B = S^(2^r) with carried inverse, and only then is the x0 entry cleared by a "
            "transvection, which is why the scaling must come first and why no invertibility of "
            "the x0 block is assumed."],
        5: ["The unramified target intentionally STOPS at two blocks, A^-1+1 and 1+B^-1. It does "
            "not certify that either block is a unit in the unrestricted operator algebra; the "
            "exact finite-module tests are isUnit_x0Block_iff and isUnit_x2Block_iff. The "
            "ramified replay gives the x2 unit pivot over the untouched universal tame row."],
        6: ["The certificate's stokes field is supplied uniformly in alpha, r, h and q, for an "
            "exact displayed unit."],
        7: ["The completed proof follows the FULL-OFFSET route, not the old two-coordinate Gate-E "
            "slice. Unramified uses the genuine cocycle coordinate x2 = Phi(c0) with "
            "(1-B^-1)Phi(c0) = (A^-1-1)c0; ramified uses x2 = B(A^-1-1)c0, whose actual cross term "
            "is B_V(c1, A^-1 c0) because B(A^-1-1)+Lc = A^-1 in characteristic two, so the "
            "coordinate change is invertible with NO inverse-Lc hypothesis. Displaying the old "
            "Gate-E polynomial with an invertible Lc as the completed normal-coordinate proof "
            "would be a content error, not merely a missing transcription. The old slice "
            "calculation remains valid in its own stated scope."],
        8: ["The first coordinate is changed by the proved additive equivalence Phi; the resulting "
            "diagonal is proved quadratic, including its omega/power charge. The retained "
            "uniform-Hsimp input is already supplied for the selected exact displays, and the "
            "record's d0 stays explicit or existential; it is not identified with qbar."],
        9: ["The boundary producer derives the head-sector premises at every actual relevant "
            "boundary lift. The fixed-point-free power conditions are derived at the actual "
            "boundary and are not retained in the final supply."],
    },
}

ITEM10_PROSE = [
    "The word hash identifies the unexpanded canonical AST; the Fox hash identifies the "
    "serialized operation lists and normal matrices at the stated discrete parameters; the "
    "packet hash additionally binds the generated section content, the cited declaration names "
    "and the direct source bytes. None of them hashes a coefficient module, a marking, a field, "
    "a resolver, an eta value, or a completed certificate.",
    "Strong checking re-emits both Lean exports, checks that every cited declaration exists with "
    "at most the standard three axioms, and compares the stored declaration transcript against a "
    "fresh replay. It does not assert independently authored expected signatures, and a matching "
    "declaration NAME is not a word-identity proof. The probe imports existing olean artifacts, "
    "so direct source hashes alone do not prove that those bytes produced those artifacts or came "
    "from an atomic filesystem snapshot; a separate isolated build is required. This STAGED "
    "packet does not enter the frozen five-fixture manifest, complete or supersede the five old "
    "appendix skeletons, activate a merge gate, or approve any release.",
]


def sections(family):
    tree = TREE[family]
    standing = STANDING[family]
    out = []
    for number in range(1, 11):
        paragraphs = list(ITEM10_PROSE) if number == 10 else list(FAMILY_PROSE[family][number])
        if number in standing:
            paragraphs.append(STANDING_PROSE)
        todos = []
        if number in MISSING_EXPORTERS:
            todos.append(
                "TODO: this section has NO generated display. The checked declarations below "
                "carry the item, and their elaborated statements are stored in the packet's "
                "proofs transcript, but no exporter serializes them into synchronized TeX. The "
                "declaration that would do so is `" + MISSING_EXPORTERS[number] + "`, which "
                + MISSING + ". No formula is substituted for it here.")
        if number == 4:
            todos.append(
                "TODO: the rfl signature theorems that bind the exported lists to the records "
                "live in the exporter driver `scripts/w362_ln_fox_export.lean`, which has no "
                "olean and therefore cannot be cited by the declaration probe. They are checked "
                "only by the Fox replay, which recompiles that driver.")
        if number == 5 and family == "Npc":
            todos.append(
                "TODO: the two surviving unramified blocks are not certified units. A generated "
                "unit claim would require the finite-module criteria, which this packet does not "
                "export.")
        out.append({"number": number, "title": TITLES[number],
                    "generated_display": GENERATED.get(number),
                    "paragraphs": paragraphs, "references": sorted(tree[number]),
                    "standing_axiom_references": sorted(standing.get(number, [])),
                    "todos": todos})
    return out


def references(family):
    return sorted({ref for s in sections(family) for ref in s["references"]})


def standing_references(family):
    return sorted({ref for s in sections(family)
                   for ref in s["standing_axiom_references"]})


def all_references(family):
    return references(family) + standing_references(family)


def source_provenance():
    paths = set(word.PROVENANCE_FILES) | set(fox.PROVENANCE_FILES) | {
        "scripts/w362_ln_certificate_packet.py"}
    return {"scope": "direct-sources-only-not-transitive-build-provenance",
            "sha256": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
                       for p in sorted(paths)}}


def digest(payload):
    return hashlib.sha256(DOMAIN + canonical_json(payload).encode()).hexdigest()


def stem(word_payload):
    return "packet-" + word.artifact_name(word_payload)


def make_packet(w, f):
    family = word.validate(w)["family"]
    payload = {"schema": SCHEMA, "family": family, "word": w, "fox": f,
               "sections": sections(family), "source_provenance": source_provenance()}
    packet = {"payload": payload, "status": "STAGED", "packet_hash": digest(payload)}
    validate(packet)
    return packet


def validate(packet, *, current_sources=True):
    fields(packet, {"payload", "status", "packet_hash"}, "LN certificate packet")
    p = packet["payload"]
    fields(p, {"schema", "family", "word", "fox", "sections", "source_provenance"},
           "LN packet payload")
    if packet["status"] != "STAGED" or p["schema"] != SCHEMA:
        raise TemplateError("packet identity or staged status mismatch")
    wp, fp = word.validate(p["word"]), fox.validate(p["fox"])
    if p["family"] != wp["family"] or p["family"] != fp["family"]:
        raise TemplateError("packet word/Fox families disagree")
    if fp["structural"]["h"] != wp["structural"]["h"]:
        raise TemplateError("packet word/Fox handle ranks disagree")
    if fp["alphabet"]["degree"] != wp["alphabet_degree"]:
        raise TemplateError("packet word/Fox alphabet degrees disagree")
    if p["family"] == "Npc" and fp["structural"]["r"] != wp["structural"]["r"]:
        raise TemplateError("packet word/Fox procyclic exponents disagree")
    if canonical_json(p["sections"]) != canonical_json(sections(p["family"])):
        raise TemplateError("generated section content, references or TODO list drifted")
    if current_sources and p["source_provenance"] != source_provenance():
        raise TemplateError("direct packet source provenance drift")
    if packet["packet_hash"] != digest(p):
        raise TemplateError("combined LN packet hash mismatch")
    return p


def proof_probe(family):
    refs, standing = references(family), standing_references(family)
    if not all(re.fullmatch(r"GQ2(?:\.[A-Za-z0-9_]+)+", ref) for ref in refs + standing):
        raise TemplateError("unsafe or malformed declaration name")
    lines = ["import " + module for module in IMPORTS[family]]
    lines += ["", "open Lean", "", "private def packetPins : List Name := ["]
    lines += [("  " if i == 0 else "  , ") + "``" + ref for i, ref in enumerate(refs)]
    lines += ["  ]", "", "private def standingPins : List Name := ["]
    lines += [("  " if i == 0 else "  , ") + "``" + ref for i, ref in enumerate(standing)]
    lines += ["  ]", "", "run_cmd do", "  let env ← getEnv",
              "  for decl in packetPins do", "    unless env.contains decl do",
              '      throwError "packet declaration missing: {decl}"',
              "    let axioms ← collectAxioms decl",
              "    let extra := axioms.filter (fun a => "
              "!([``propext, ``Classical.choice, ``Quot.sound].contains a))",
              "    unless extra.isEmpty do",
              '      throwError "packet nonstandard axioms: {decl}: {extra}"',
              '    IO.println s!"PACKET_PIN_OK|{decl}|{axioms.size}"',
              "  for decl in standingPins do", "    unless env.contains decl do",
              '      throwError "packet standing declaration missing: {decl}"',
              "    let axioms ← collectAxioms decl",
              "    let extra := axioms.filter (fun a => "
              "!([``propext, ``Classical.choice, ``Quot.sound].contains a))",
              '    IO.println s!"PACKET_STANDING_PIN|{decl}|{extra.size}|{extra}"',
              '  IO.println s!"LN_PACKET_PROOF_REPLAY_PASS|{packetPins.length}|'
              '{standingPins.length}"', ""]
    lines += ["#check @" + ref for ref in refs + standing]
    return "\n".join(lines) + "\n"


def check_proofs(runner, family):
    with tempfile.TemporaryDirectory(prefix="gq2-w362-packet-probe-") as directory:
        path = Path(directory) / "Probe.lean"
        path.write_text(proof_probe(family))
        result = subprocess.run(["bash", str(Path(runner).resolve()), str(path)],
                                cwd=ROOT, text=True, capture_output=True)
    marker = (f"LN_PACKET_PROOF_REPLAY_PASS|{len(references(family))}"
              f"|{len(standing_references(family))}")
    if result.returncode or marker not in result.stdout:
        raise TemplateError("LN packet proof replay failed:\n" + result.stdout + result.stderr)
    return result.stdout


def tex_escape(text):
    replacements = {"\\": r"\textbackslash{}", "_": r"\_", "&": r"\&", "%": r"\%",
                    "#": r"\#", "$": r"\$", "{": r"\{", "}": r"\}",
                    "^": r"\textasciicircum{}", "~": r"\textasciitilde{}"}
    return "".join(replacements.get(char, char) for char in text)


def render_tex(packet):
    p = validate(packet)
    wp, fp = p["word"]["payload"], p["fox"]["payload"]
    title = stem(wp)
    lines = ["% STAGED generated ten-item L/N appendix. No owner approval, manifest entry,"
             " gate activation or migration of the frozen appendix skeletons.",
             "% ln-packet-sha256: " + packet["packet_hash"],
             r"\section*{STAGED certificate: " + tex_escape(title) + "}",
             "Family " + tex_escape(p["family"]) + ", word structure "
             + tex_escape(canonical_json(wp["structural"])) + ", Fox structure "
             + tex_escape(canonical_json(fp["structural"])) + ".",
             "", r"\noindent Exact semantic binding: \path{" + wp["binding"] + "}."
             + r" Semantic target: \path{" + wp["semantic_target"] + "}."
             + r" Uniform denotation bridge: \path{" + wp["bridge"] + "}.",
             r"\par\noindent " + tex_escape(fox.CERTIFICATE_CONDITIONS[p["family"]]), ""]
    for section in p["sections"]:
        n = section["number"]
        lines += [r"\subsection*{" + str(n) + ". " + tex_escape(section["title"]) + "}"]
        lines += [tex_escape(text) + "\n" for text in section["paragraphs"]]
        if n == 1:
            lines += ["\\begin{verbatim}", word.render_tex(p["word"]).rstrip("\n"),
                      "\\end{verbatim}"]
        elif n in (4, 5):
            renderer = fox.operations_tex if n == 4 else fox.target_tex
            for sector in fp["sectors"]:
                lines += [r"\paragraph{" + tex_escape(sector["sector"]) + " sector}",
                          r"\[" + renderer(sector) + r"\]"]
        elif n == 10:
            for label, obj, key in (("word", p["word"], "template_hash"),
                                    ("Fox", p["fox"], "template_hash")):
                lines += [label + r" template: \path{" + obj[key] + "}."]
            lines += [r"legacy one-tree word hash: \path{" + wp["word_hash"] + "}.",
                      r"\par Combined packet: \path{" + packet["packet_hash"] + "}."]
        if section["generated_display"]:
            lines += [r"\par\noindent\emph{Generated display source: "
                      + tex_escape(section["generated_display"]) + ".}"]
        for todo in section["todos"]:
            lines += [r"\par\noindent\textbf{[" + tex_escape(todo) + "]}"]
        if section["references"]:
            lines += [r"\paragraph{Checked declarations (standard three axioms)}",
                      r"\begin{itemize}"]
            lines += [r"\item \path{" + ref + "}" for ref in section["references"]]
            lines += [r"\end{itemize}"]
        if section["standing_axiom_references"]:
            lines += [r"\paragraph{Checked declarations carrying documented standing inputs}",
                      r"\begin{itemize}"]
            lines += [r"\item \path{" + ref + "}"
                      for ref in section["standing_axiom_references"]]
            lines += [r"\end{itemize}"]
        lines += [""]
    return "\n".join(lines)


def emit(packet, directory, proof_output):
    if OUTPUT_COMPONENT not in directory.resolve().parts:
        raise TemplateError("packet output must be inside " + OUTPUT_COMPONENT)
    directory.mkdir(parents=True, exist_ok=True)
    p = validate(packet)
    base = stem(p["word"]["payload"])
    artifacts = {base + ".packet.json": canonical_json(packet) + "\n",
                 base + ".appendix.tex": render_tex(packet),
                 base + ".proofs.lean": proof_probe(p["family"]),
                 base + ".proofs.txt": proof_output}
    for name, content in artifacts.items():
        (directory / name).write_text(content)
    manifest = {"schema": SCHEMA + ".files", "packet_hash": packet["packet_hash"],
                "sha256": {name: hashlib.sha256(content.encode()).hexdigest()
                           for name, content in artifacts.items()}}
    (directory / (base + ".files.json")).write_text(canonical_json(manifest) + "\n")
    return base


def fox_parameters(word_payload, q):
    s = word_payload["structural"]
    parameters = {"h": s["h"], "q": q}
    if word_payload["family"] == "Npc":
        parameters["r"] = s["r"]
    return parameters


def build(requests, output, runner):
    proof_results = {}
    for family, parameters, q in requests:
        w = word.from_lean(runner, family, parameters)
        f = fox.from_lean(runner, family, fox_parameters(w["payload"], q))
        if family not in proof_results:
            proof_results[family] = check_proofs(runner, family)
        packet = make_packet(w, f)
        name = emit(packet, output, proof_results[family])
        print(f"STAGED_LN_PACKET_BUILT|{name}|{packet['packet_hash']}", flush=True)


def check(directory, runner=None):
    paths = sorted(directory.glob("*.packet.json"))
    if not paths:
        raise TemplateError("no LN certificate packets found")
    replayed_families, replayed_fox = {}, {}
    for path in paths:
        obj = json.loads(path.read_text(), object_pairs_hook=reject_duplicates)
        p = validate(obj)
        wp, fp = p["word"]["payload"], p["fox"]["payload"]
        base = stem(wp)
        if path.name != base + ".packet.json":
            raise TemplateError("noncanonical LN packet filename")
        if (directory / (base + ".appendix.tex")).read_text() != render_tex(obj):
            raise TemplateError("generated LN appendix TeX drift")
        if (directory / (base + ".proofs.lean")).read_text() != proof_probe(p["family"]):
            raise TemplateError("generated LN proof-probe drift")
        manifest = json.loads((directory / (base + ".files.json")).read_text(),
                              object_pairs_hook=reject_duplicates)
        fields(manifest, {"schema", "packet_hash", "sha256"}, "LN packet file manifest")
        expected = {base + suffix for suffix in
                    (".packet.json", ".appendix.tex", ".proofs.lean", ".proofs.txt")}
        fields(manifest["sha256"], expected, "LN packet file hashes")
        if manifest["schema"] != SCHEMA + ".files" or manifest["packet_hash"] != obj["packet_hash"]:
            raise TemplateError("LN packet file manifest identity mismatch")
        for name, recorded in manifest["sha256"].items():
            if hashlib.sha256((directory / name).read_bytes()).hexdigest() != recorded:
                raise TemplateError("LN packet file hash mismatch: " + name)
        if runner:
            if word.from_lean(runner, p["family"], wp["structural"]) != p["word"]:
                raise TemplateError("LN packet word replay mismatch")
            key = (p["family"], canonical_json(fp["structural"]))
            if key not in replayed_fox:
                replayed_fox[key] = fox.from_lean(runner, p["family"], fp["structural"])
            if replayed_fox[key] != p["fox"]:
                raise TemplateError("LN packet Fox replay mismatch")
            if p["family"] not in replayed_families:
                replayed_families[p["family"]] = check_proofs(runner, p["family"])
            if replayed_families[p["family"]] != (directory / (base + ".proofs.txt")).read_text():
                raise TemplateError(
                    "stored declaration type/axiom transcript differs from strong replay")
        mode = "Lean-replayed" if runner else "artifact-only; NOT Lean-synchronized"
        print(f"STAGED_LN_PACKET_CHECK|{mode}|{base}|{obj['packet_hash']}", flush=True)
    return len(paths)


def self_test():
    count = 0
    for family in TREE:
        s = sections(family)
        assert [x["number"] for x in s] == list(range(1, 11))
        assert all(x["references"] or x["number"] == 10 for x in s)
        assert all(x["todos"] for x in s if x["number"] in MISSING_EXPORTERS)
        assert all(not x["todos"] for x in s if x["number"] in (1, 10))
        probe = proof_probe(family)
        assert "sorry" not in probe and "native_decide" not in probe
        assert all(("``" + ref) in probe for ref in all_references(family))
        assert "standingPins" in probe and "PACKET_STANDING_PIN" in probe
        assert standing_references(family), "the field adapter must stay pinned"
        assert not set(references(family)) & set(standing_references(family))
        count += 7
    for bad in ("GQ2.Dyadic.Bad; open Foo", "GQ2..Dyadic", "Dyadic.Foo", "GQ2.Dyadic.é"):
        saved = TREE["L"][10]
        TREE["L"][10] = [bad]
        try:
            proof_probe("L")
        except TemplateError:
            count += 1
        else:
            raise AssertionError("unsafe declaration name accepted")
        finally:
            TREE["L"][10] = saved
    print(f"LN_PACKET_SELF_TEST_PASS|{count}")
    return count


REQUESTS = [
    ("L", {"h": 0}, 2),
    ("L", {"h": 4}, 2),
    ("N0", {"alpha": 5, "h": 3}, 2),
    ("Npc", {"alpha": 2, "r": 1, "h": 0, "num": 1, "den": 1}, 2),
    ("Npc", {"alpha": 3, "r": 2, "h": 3, "num": 3, "den": 9}, 2),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("self-test")
    build_parser = sub.add_parser("build")
    build_parser.add_argument("--out", type=Path, default=Path("generated") / OUTPUT_COMPONENT)
    build_parser.add_argument("--lean-runner", type=Path, required=True)
    check_parser = sub.add_parser("check")
    check_parser.add_argument("directory", type=Path)
    check_parser.add_argument("--lean-runner", type=Path)
    args = parser.parse_args()
    if args.command == "self-test":
        self_test()
    elif args.command == "build":
        build(REQUESTS, args.out, args.lean_runner)
    else:
        check(args.directory, args.lean_runner)


if __name__ == "__main__":
    try:
        main()
    except (TemplateError, OSError, ValueError, RecursionError) as exc:
        raise SystemExit(f"LN certificate packet error: {exc}") from exc
