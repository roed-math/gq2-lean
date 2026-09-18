#!/usr/bin/env python3
"""Compose STAGED ten-item certificate appendices from checked Lean exports.

This is an additive publication experiment, not a frozen gate or owner approval.
Word, Fox and quadratic trees are independently re-emitted by Lean and tied by
the actual handle rank. Their uniform certificate bindings are checked together.
The prose is reviewable exposition, not itself a theorem or generated proof term.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

import w361_general_word_tex as word
import w361_general_phase_tex as phase
import w361_general_fox_tex as fox
import w361_general_cover_tex as cover

SCHEMA = "gq2.w361.certificate-packet.v1.staged"
DOMAIN = b"GQ2-W361-CERTIFICATE-PACKET\0"
ROOT = Path(__file__).resolve().parent.parent
D = "GQ2.Dyadic."
I = D + "Instances."
FT = D + "GeneralFoxTemplate."
PT = D + "GeneralPhaseTemplate."
IMPORTS = [
    D + "Word.GeneralTemplateSplice", D + "Word.GeneralTemplateEval",
    D + "Word.GeneralPhaseTemplate", D + "Word.GeneralPhaseCoverTemplate",
    I + "TameSpliceFoxTemplateBinding",
    I + "TameSpliceFoxTemplateInputBinding",
    I + "TameSpliceBoundaryHessianCertificates",
]


def sections(family):
    pair = family == "pair"
    prefix = "pairSplice" if pair else "mobileSplice"
    core = (I + "EvenMHeadHandlePairSpliceSupply.flexibleCore_headHandlePairSplice" if pair else
            I + "MpcMobileSpliceSupply.mpcMobileTameSplice_core")
    tame = (I + "EvenMHeadHandlePairSpliceSupply.headHandlePairSpliceW_specializes" if pair else
            I + "MpcMobileNuSource.mpcMobileTameCorrectedW_specializes")
    stokes = (I + "EvenMHeadHandlePairSpliceSupply.uniformStokesSupply_headHandlePairSplice" if pair else
              I + "MpcMobileSpliceSupply.mpcMobileTameSplice_uniformStokesSupply")
    boundary = I + "TameSpliceBoundaryHessianCertificates." + family + "BoundaryHessian"
    determinant = (I + "EvenMHeadHandlePairSpliceBoundary.headHandlePairSplice_determinant" if pair else
                   I + "MpcMobileSpliceBoundary.mpcMobileTameSplice_determinant")
    rows = [I + "TameSpliceScalarFoxNormal." + prefix + "_scalar_rows",
            I + "TameSpliceUnramifiedFoxRows." + prefix + "_unramified_rows",
            I + "TameSpliceRamifiedFoxNormal.tameSplice_ramified_rows"]
    bindings = [FT + s + "_" + family + "_signature" for s in ("scalar", "unramified", "ramified")]
    return [
        {"number": 1, "title": "Exact syntax tree and binding", "references": [
            D + "GeneralTemplate.denote_" + ("pairSplice" if pair else "mobileSplice"),
            D + "GeneralTemplate.Tree.eval_eq_pinned"],
         "paragraphs": ["The following word is rendered from the exact Lean-exported tree. All continuous "
            "parameters remain symbolic. The named environment binds them to the actual source constructor; "
            "arbitrary assignments to these symbols do not automatically satisfy a source certificate."]},
        {"number": 2, "title": "Tame and pro-two specialization reductions", "references": [
            D + "eval_pro2_tameSplice", D + "tameSpecializes_tameSplice", core, tame],
         "paragraphs": ["Write W=Shadow(Rcorr) H Shadow(H)^(-1), with the literal corrected normalized "
            "word Rcorr and compact template H from item 1. On pro-two targets with tau=1, shadow is "
            "the identity, the prime-to-two correction vanishes, and the proved Nielsen normalization "
            "transports the complete presented core. On the canonical tame marking, the correction "
            "removes the actual defect and the splice specializes to one.",
            ("The pair core certificate retains the exact condition nuP(U_j)=1; the selected handle exists." if pair else
             "The mobile core certificate retains the exact actual-unit equation for nuP(D), with arbitrary "
             "actual eta. When obtained from field selection, eta also retains that selector's proved "
             "congruence; it is not replaced by the representative.")]},
        {"number": 3, "title": "Evaluated Fox Jacobian", "references": rows + [
            FT + s + "_" + family + "_input" for s in ("scalar", "unramified", "ramified")],
         "paragraphs": ["All three profiles use a finite base group C and finite exponent-two coefficient "
            "module A. These are identities on all cochains, not just cycles. Columns not displayed vanish. "
            "The resolver is pinned at 4 times the finite base-group exponent and is valid at WordLift level.",
            "Scalar: every generator action is trivial. Unramified: finite exponent-two coefficients, "
            "wild and tau actions trivial, sigma fixed-point-free with trivial two-primary action, and "
            "death of the actual pinned changed-word family. Ramified: explicit finite surjective head "
            "projection with compatible action, wild head one, actual tame relation, and tau fixed-point-free "
            "with trivial two-primary action. No raw-word death or commuting sigma/tau premise is inserted."]},
        {"number": 4, "title": "Ordered invertible operations and carried inverses", "references": bindings,
         "paragraphs": ["The following lists are exported from the same typed profile as the input and target "
            "rows. Their denotations are definitionally the lists in the original FoxCertificate records. "
            "Every scale carries a formal inverse; the actual records prove both inverse products.",
            "In each nonscalar sector k is the half-period of the actual coefficient action, so its odd "
            "order is 2k+1. It is not the handle rank, not an assumed ambient group order, and not a fixed "
            "source parameter. q is the source residue size. Composition applies the inner operator first."]},
        {"number": 5, "title": "Reduced normal matrices", "references": bindings,
         "paragraphs": ["Replay of the preceding invertible lists gives these literal identity-pivot targets "
            "on all cochains. The scalar second row is zero. The ramified sigma pivot is obtained after "
            "the displayed column shear; it must not be read as an identity for the unsheared input."]},
        {"number": 6, "title": "Stokes chain identity and all coefficients", "references": [stokes],
         "paragraphs": ["The actual word supplies a single coefficient-independent UniformStokesSupply. "
            "It includes pinned resolution, endpoint and full Stokes duality for every finite elementary "
            "coefficient module pushed from the actual source. The simple-action profiles feed the proved "
            "composition-series exact-diagram extension; checking dimensions only on simple modules is not "
            "substituted for that argument. The statement is uniform in all source parameters and h."]},
        {"number": 7, "title": "Full extraspecial Hessian", "references": [
            D + "hessEvalZ_tameSplice_ramified", PT + "denote_compactPhase", PT + "sourcePhase_eq_denote",
            (I + "EvenMHeadHandlePairProjectedPhase.QZero_headHandlePairSplice_unramified_compactPhase" if pair else
             I + "MpcMobileUnramifiedPhase.hessRelZ_mpcUnit_unramified_compactPhase_of_sigma2_one")],
         "paragraphs": ["The exported quadratic expression below is the full endpoint phase. Here q_0 is "
            "the coefficient quadratic form and B=polar(q_0), distinct from the residue size q in the Fox rows. "
            "It is not inferred from its polar matrix. The unramified comparison retains the factor-set "
            "charge until its proved faithful-head vanishing; the ramified splice retains the complete "
            "extraspecial evaluation and then uses the existing head swap. This is not a claim that the raw "
            "ramified expression equals the displayed form before changing coordinates."]},
        {"number": 8, "title": "Linear normal coordinates and polar inverse", "references": [
            I + "WordPhaseCompactCertificates.sourceCompactHessianOfComparison_cov_apply",
            PT + "sourceHessian_cov_eq_denote", PT + "polar_denote_compactPhase",
            I + "WordPhasePolarNormal.reducedCoefficientMatrix_mul_inverse", boundary],
         "paragraphs": ["The original source comparison map is proved additive, then upgraded to an F2-linear "
            "equivalence with exactly the same forward and inverse functions. Its domain is the actual "
            "source cocycle quotient. The original Hessian record proves QZeroBar(x)=Q(cov(x)), and "
            "the two inverse equations. The matrices below are relative to the coefficient pairing B; "
            "B itself is not declared to be the identity matrix."]},
        {"number": 9, "title": "Original affine phase-cover record", "references": [
            I + "WordPhaseCompactCertificates.compactPhaseCover", PT + "compactPhaseCover_tree",
            D + "GeneralPhaseCoverTemplate.compactTemplate_agrees",
            boundary, determinant],
         "paragraphs": ["The original Hessian record contains the original PhaseCoverCertificate. For "
            "|V|=2^d, its base dimension is (h+1)d and its base sign is +1. The diagonal and cross "
            "embeddings put v into the first and second head slots respectively and zero in every other "
            "slot. It proves the full diagonal identity Q(j0(v))=dat.f(v,v), the cross-polar identity, "
            "the endpoint cardinality and the signed Gauss sum.",
            "At every relevant actual boundary lift, the named boundary producer derives the projected "
            "head hypotheses internally and returns this original record. The downstream affine "
            "determinant remains a theorem for every required cover and character, not just an "
            "unshifted Gauss value."]},
        {"number": 10, "title": "Same-tree hashes, replay and trust boundary", "references": [],
         "paragraphs": ["The word, Fox, phase and phase-cover hashes identify symbolic templates. They do not hash actual "
            "q, nuP, eta, shear, correction, coefficient-space or action-period values. Uniform Lean "
            "denotation and certificate-signature bridges bind their semantic uses. This combined packet "
            "additionally binds the generated section content and direct source bytes.",
            "Strong checking re-emits all four Lean exports and checks every cited declaration's existence "
            "and standard-three axiom footprint, and compares the printed type transcript on replay. "
            "It does not assert independently authored expected signatures. The probe imports existing "
            "olean artifacts; direct source hashes alone do not prove that those bytes produced those "
            "artifacts or came from an atomic filesystem snapshot. A separate isolated build is required. "
            "External dependency artifacts are reused. Prose remains an editorial exposition of the checked "
            "objects. This STAGED packet does not approve the changed source selection, replace the frozen "
            "five-fixture manifest, activate a merge gate, or certify the original frozen-M theorem."]},
    ]


def references(family):
    return sorted({ref for s in sections(family) for ref in s["references"]})


def source_provenance():
    # Direct source bytes only: this is deliberately NOT a transitive-build hash.
    paths = set(word.PROVENANCE_FILES) | {
        "scripts/w361_general_phase_tex.py", "scripts/w361_general_fox_tex.py",
        "scripts/w361_general_cover_tex.py",
        "scripts/w361_certificate_packet.py",
        "GQ2/Dyadic/Word/GeneralPhaseTemplate.lean",
        "GQ2/Dyadic/Word/GeneralPhaseTemplateExport.lean",
        "GQ2/Dyadic/Word/GeneralPhaseCoverTemplate.lean",
        "GQ2/Dyadic/Word/GeneralPhaseCoverTemplateExport.lean",
        "GQ2/Dyadic/Word/GeneralFoxTemplate.lean",
        "GQ2/Dyadic/Word/GeneralFoxTemplateExport.lean",
        "GQ2/Dyadic/Instances/TameSpliceFoxTemplateBinding.lean",
        "GQ2/Dyadic/Instances/TameSpliceFoxTemplateInputBinding.lean",
        "GQ2/Dyadic/Instances/TameSpliceBoundaryHessianCertificates.lean",
        "GQ2/Dyadic/Instances/TameSpliceFoxCertificates.lean",
        "GQ2/Dyadic/Instances/TameSplicePolynomialFoxCertificates.lean",
        "GQ2/Dyadic/Instances/TameSpliceRamifiedPolynomialFoxCertificates.lean",
        "GQ2/Dyadic/Instances/TameSpliceHessianCertificates.lean",
        "GQ2/Dyadic/Instances/WordPhaseCompactCertificates.lean",
    }
    return {"scope": "direct-sources-only-not-transitive-build-provenance",
            "sha256": {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}}


def digest(payload):
    return hashlib.sha256(DOMAIN + word.canonical_json(payload).encode()).hexdigest()


def make_packet(w, f, p, c):
    family = word.validate_envelope(w)["family"]
    payload = {"schema": SCHEMA, "word": w, "fox": f, "phase": p, "cover": c,
               "sections": sections(family), "source_provenance": source_provenance()}
    result = {"payload": payload, "status": "STAGED", "packet_hash": digest(payload)}
    validate(result)
    return result


def validate(packet, *, current_sources=True):
    word.fields(packet, {"payload", "status", "packet_hash"}, "certificate packet")
    p = packet["payload"]
    word.fields(p, {"schema", "word", "fox", "phase", "cover", "sections", "source_provenance"}, "packet payload")
    if packet["status"] != "STAGED" or p["schema"] != SCHEMA:
        raise word.TemplateError("packet identity or staged status mismatch")
    wp, fp, pp = word.validate_envelope(p["word"]), fox.validate(p["fox"]), phase.validate(p["phase"])
    cp = cover.validate(p["cover"])
    h = wp["structural"]["h"]
    if fp["alphabet"]["h"] != h or pp["structural"]["h"] != h:
        raise word.TemplateError("word/Fox/phase ranks disagree")
    if fp["alphabet"]["n"] != wp["alphabet_degree"]:
        raise word.TemplateError("word/Fox alphabet degrees disagree")
    if (cp["structural"]["h"] != h or cp["phase_template_hash"] != p["phase"]["template_hash"]
            or word.canonical_json(cp["phase_tree"]) != word.canonical_json(pp["tree"])):
        raise word.TemplateError("phase-cover is not bound to this exact phase tree/hash/rank")
    if wp["structural"]["alpha"] < 2:
        raise word.TemplateError("certificate packet requires alpha >= 2; a syntax-only word is insufficient")
    if word.canonical_json(p["sections"]) != word.canonical_json(sections(wp["family"])):
        raise word.TemplateError("generated section content or proof references drifted")
    if current_sources and p["source_provenance"] != source_provenance():
        raise word.TemplateError("direct certificate source provenance drift")
    if packet["packet_hash"] != digest(p):
        raise word.TemplateError("combined certificate packet hash mismatch")
    return p


def proof_probe(family):
    refs = references(family)
    if not all(re.fullmatch(r"GQ2(?:\.[A-Za-z0-9_]+)+", ref) for ref in refs):
        raise word.TemplateError("unsafe or malformed declaration name")
    lines = ["import " + module for module in IMPORTS]
    lines += ["", "open Lean", "", "private def packetPins : List Name := ["]
    lines += [("  " if i == 0 else "  , ") + "``" + ref for i, ref in enumerate(refs)]
    lines += ["  ]", "", "run_cmd do", "  let env ← getEnv",
              "  for decl in packetPins do", "    unless env.contains decl do",
              '      throwError "packet declaration missing: {decl}"',
              "    let axioms ← collectAxioms decl",
              "    let extra := axioms.filter (fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a))",
              "    unless extra.isEmpty do", '      throwError "packet nonstandard axioms: {decl}: {extra}"',
              '    IO.println s!"PACKET_PIN_OK|{decl}|{axioms.size}"',
              '  IO.println s!"PACKET_PROOF_REPLAY_PASS|{packetPins.length}"', ""]
    lines += ["#check " + ref for ref in refs]
    return "\n".join(lines) + "\n"


def check_proofs(runner, family):
    with tempfile.TemporaryDirectory(prefix="gq2-w361-packet-probe-") as directory:
        path = Path(directory)/"Probe.lean"
        path.write_text(proof_probe(family))
        result = subprocess.run(["bash", str(Path(runner).resolve()), str(path)],
                                cwd=ROOT, text=True, capture_output=True)
    if result.returncode or f"PACKET_PROOF_REPLAY_PASS|{len(references(family))}" not in result.stdout:
        raise word.TemplateError("packet proof replay failed:\n" + result.stdout + result.stderr)
    return result.stdout


def tex_escape(text):
    replacements = {"\\": r"\textbackslash{}", "_": r"\_", "&": r"\&", "%": r"\%",
                    "#": r"\#", "$": r"\$", "{": r"\{", "}": r"\}", "^": r"\textasciicircum{}",
                    "~": r"\textasciitilde{}"}
    return "".join(replacements.get(char, char) for char in text)


def render_tex(packet):
    p = validate(packet)
    wp = p["word"]["payload"]
    title = word.stem(wp)
    lines = ["% STAGED generated ten-item appendix. No owner approval or frozen-gate migration.",
             "% packet-sha256: " + packet["packet_hash"],
             r"\section*{STAGED certificate: " + tex_escape(title) + "}",
             "This is a parameterized certificate display for a changed source, not a certificate for the frozen M word.",
             "Source structure: " + tex_escape(word.canonical_json(wp["structural"])) + ".",
             "", r"\noindent Exact semantic binding: \path{" + wp["binding"] + "}.", ""]
    for section in p["sections"]:
        n = section["number"]
        lines += [r"\subsection*{" + str(n) + ". " + tex_escape(section["title"]) + "}"]
        lines += [tex_escape(text) + "\n" for text in section["paragraphs"]]
        if n == 1:
            lines += [word.render_tex(p["word"])]
        elif n in (3, 4, 5):
            render = {3: fox.input_rows_tex, 4: fox.operations_tex, 5: fox.target_rows_tex}[n]
            for profile in p["fox"]["payload"]["profiles"]:
                lines += [r"\paragraph{" + tex_escape(profile["sector"]) + "}",
                          r"\[" + render(profile) + r"\]"]
        elif n == 7:
            lines += [r"\[Q=" + phase.tree_tex(p["phase"]["payload"]["tree"]) + r".\]"]
        elif n == 8:
            pp = p["phase"]["payload"]
            lines += [r"\[J=" + phase.matrix_tex(pp["matrix"]) + r",\qquad J^{-1}=" +
                      phase.matrix_tex(pp["inverse_matrix"]) + r".\]",
                      "Coordinate order: " + ", ".join("$" + phase.coordinate_tex(c) + "$" for c in pp["coordinates"]) + "."]
        elif n == 9:
            lines += [cover.render_tex(p["cover"]),
                      r"\[Q(j_0(v))=\operatorname{dat}.f(v,v),\qquad B_Q(j_0(v),j_1(w))=\operatorname{dat}.f(v,w)+\operatorname{dat}.f(w,v).\]"]
        elif n == 10:
            for label, obj in (("word", p["word"]), ("Fox", p["fox"]), ("phase", p["phase"]),
                               ("phase cover", p["cover"])):
                lines += [label + " template: " + r"\path{" + obj["template_hash"] + "}."]
            lines += [r"\par Combined packet: \path{" + packet["packet_hash"] + "}."]
        if section["references"]:
            lines += [r"\paragraph{Checked declarations}", r"\begin{itemize}"]
            lines += [r"\item \path{" + ref + "}" for ref in section["references"]]
            lines += [r"\end{itemize}"]
        lines += [""]
    return "\n".join(lines)


def emit(packet, directory, proof_output):
    if "general-certificate-staged" not in directory.resolve().parts:
        raise word.TemplateError("packet output must be inside general-certificate-staged")
    directory.mkdir(parents=True, exist_ok=True)
    p = validate(packet)
    base = word.stem(p["word"]["payload"])
    artifacts = {base+".packet.json": word.canonical_json(packet)+"\n",
                 base+".appendix.tex": render_tex(packet),
                 base+".proofs.lean": proof_probe(p["word"]["payload"]["family"]),
                 base+".proofs.txt": proof_output}
    for name, content in artifacts.items():
        (directory/name).write_text(content)
    manifest = {"schema": SCHEMA+".files", "packet_hash": packet["packet_hash"],
                "sha256": {name: hashlib.sha256(content.encode()).hexdigest() for name, content in artifacts.items()}}
    (directory/(base+".files.json")).write_text(word.canonical_json(manifest)+"\n")
    return base


def build(template_dir, output, runner):
    paths = sorted(template_dir.glob("*.template.json"))
    if not paths:
        raise word.TemplateError("no staged word templates found")
    cache_fox, cache_phase, cache_cover, proof_results = {}, {}, {}, {}
    for path in paths:
        w = word.loads(path.read_text())
        wp = w["payload"]
        if word.from_lean(runner, word.lean_args(wp)) != w:
            raise word.TemplateError("word template differs from the actual Lean factory")
        h = wp["structural"]["h"]
        if h not in cache_fox:
            cache_fox[h], cache_phase[h] = fox.from_lean(runner, h), phase.from_lean(runner, h)
            cache_cover[h] = cover.from_lean(runner, h)
        family = wp["family"]
        if family not in proof_results:
            proof_results[family] = check_proofs(runner, family)
        packet = make_packet(w, cache_fox[h], cache_phase[h], cache_cover[h])
        name = emit(packet, output, proof_results[family])
        print(f"STAGED_PACKET_BUILT|{name}|{packet['packet_hash']}", flush=True)


def check(directory, runner=None):
    paths = sorted(directory.glob("*.packet.json"))
    if not paths:
        raise word.TemplateError("no certificate packets found")
    checked_families, checked_fox, checked_phase, checked_cover = {}, {}, {}, {}
    for path in paths:
        obj = json.loads(path.read_text(), object_pairs_hook=word.reject_duplicates)
        p = validate(obj)
        wp, h = p["word"]["payload"], p["phase"]["payload"]["structural"]["h"]
        base = word.stem(wp)
        if path.name != base+".packet.json":
            raise word.TemplateError("noncanonical certificate packet filename")
        if (directory/(base+".appendix.tex")).read_text() != render_tex(obj):
            raise word.TemplateError("generated appendix TeX drift")
        if (directory/(base+".proofs.lean")).read_text() != proof_probe(wp["family"]):
            raise word.TemplateError("generated proof-probe drift")
        manifest = json.loads((directory/(base+".files.json")).read_text(), object_pairs_hook=word.reject_duplicates)
        word.fields(manifest, {"schema", "packet_hash", "sha256"}, "packet file manifest")
        expected_names = {base+suffix for suffix in (".packet.json", ".appendix.tex", ".proofs.lean", ".proofs.txt")}
        word.fields(manifest["sha256"], expected_names, "packet file hashes")
        if (manifest["schema"] != SCHEMA+".files" or manifest["packet_hash"] != obj["packet_hash"]
                or set(manifest["sha256"]) != expected_names):
            raise word.TemplateError("packet file manifest identity mismatch")
        for name, recorded in manifest["sha256"].items():
            if hashlib.sha256((directory/name).read_bytes()).hexdigest() != recorded:
                raise word.TemplateError("packet file hash mismatch: "+name)
        if runner:
            if word.from_lean(runner, word.lean_args(wp)) != p["word"]:
                raise word.TemplateError("packet word replay mismatch")
            if h not in checked_fox:
                checked_fox[h], checked_phase[h] = fox.from_lean(runner, h), phase.from_lean(runner, h)
                checked_cover[h] = cover.from_lean(runner, h)
            if checked_fox[h] != p["fox"] or checked_phase[h] != p["phase"]:
                raise word.TemplateError("packet Fox/phase replay mismatch")
            if checked_cover[h] != p["cover"]:
                raise word.TemplateError("packet phase-cover replay mismatch")
            if wp["family"] not in checked_families:
                checked_families[wp["family"]] = check_proofs(runner, wp["family"])
            if checked_families[wp["family"]] != (directory/(base+".proofs.txt")).read_text():
                raise word.TemplateError("stored declaration type/axiom transcript differs from strong replay")
        mode = "Lean-replayed" if runner else "artifact-only; NOT Lean-synchronized"
        print(f"STAGED_PACKET_CHECK|{mode}|{base}|{obj['packet_hash']}", flush=True)
    return len(paths)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    build_parser = sub.add_parser("build")
    build_parser.add_argument("--templates", type=Path, default=Path("generated/general-template-staged"))
    build_parser.add_argument("--out", type=Path, default=Path("generated/general-certificate-staged"))
    build_parser.add_argument("--lean-runner", type=Path, required=True)
    check_parser = sub.add_parser("check")
    check_parser.add_argument("directory", type=Path)
    check_parser.add_argument("--lean-runner", type=Path)
    args = parser.parse_args()
    if args.command == "build":
        build(args.templates, args.out, args.lean_runner)
    else:
        check(args.directory, args.lean_runner)


if __name__ == "__main__":
    try:
        main()
    except (word.TemplateError, OSError, ValueError, RecursionError) as exc:
        raise SystemExit(f"certificate packet error: {exc}") from exc
