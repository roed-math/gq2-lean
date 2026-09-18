#!/usr/bin/env python3
"""Check a recorded isolated build against current sources and replay STAGED artifacts.

This checks content consistency with an observed build; it is not signed build
attestation, atomic snapshotting, or a rebuild of external dependency artifacts.
The complete GQ2 local closure is required. No artifact or source is overwritten.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MODULE = re.compile(r"GQ2(?:\.[A-Za-z0-9_]+)*\Z")
HEX = re.compile(r"[0-9a-f]{64}\Z")
REPLAY_SOURCES = (
    "scripts/w361_verify_fresh.py", "scripts/w361_check_staged.sh",
    "scripts/w361_fresh_build.py",
    "scripts/w361_verify_fresh_test.py", "scripts/w361_staged_certificates.tex",
    "scripts/w361_lean_runner.sh", "scripts/w361_general_axiom_audit.lean",
    "scripts/w361_artifact_axiom_audit.lean", "scripts/w361_certificate_packet.py",
    "scripts/w361_certificate_packet_test.py", "scripts/w361_general_word_tex.py",
    "scripts/w361_general_fox_tex.py", "scripts/w361_general_phase_tex.py",
    "scripts/w361_general_cover_tex.py", "scripts/dyadic_word_tex.py",
    "scripts/w361_general_ln_word_tex.py",
    "GQ2/Dyadic/Word/GeneralTemplateExport.lean",
    "GQ2/Dyadic/Word/GeneralFoxTemplateExport.lean",
    "GQ2/Dyadic/Word/GeneralPhaseTemplateExport.lean",
    "GQ2/Dyadic/Word/GeneralPhaseCoverTemplateExport.lean",
    "GQ2/Dyadic/Word/GeneralTemplateLNExport.lean",
)


class VerificationError(ValueError):
    pass


def fail_unless(condition, message):
    if not condition:
        raise VerificationError(message)


def no_duplicates(pairs):
    result = {}
    for key, value in pairs:
        fail_unless(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def read_json(path):
    return json.loads(path.read_text(), object_pairs_hook=no_duplicates,
                     parse_constant=lambda x: (_ for _ in ()).throw(VerificationError(x)))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_digest(value):
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return hashlib.sha256(encoded.encode()).hexdigest()


def validate_record(provenance, result):
    fail_unless(isinstance(provenance, dict) and isinstance(result, dict), "build records must be objects")
    fail_unless(provenance.get("target") == "GQ2", "a complete GQ2 umbrella build is required")
    fail_unless(type(provenance.get("local_artifacts_reused")) is int
                and provenance["local_artifacts_reused"] == 0, "build reused local artifacts")
    fail_unless(provenance.get("import_parser") == "pinned Lean --deps", "wrong dependency parser")
    fail_unless(provenance.get("snapshot_atomic") is False, "snapshot claim is not the supported non-atomic contract")
    fail_unless(provenance.get("local_output_inventory") == "all-local-output-files-v1",
                "build predates complete local companion-file inventory")
    fail_unless(result.get("failed") == [] and result.get("unbuilt") == [], "build failed or was incomplete")
    fail_unless(type(result.get("completed")) is int and type(result.get("total")) is int
                and result["completed"] == result["total"] > 0, "invalid completed/total counts")
    fail_unless(result.get("live_manifest_drift") is False, "manifest drift recorded during build")
    fail_unless(result.get("local_output_file_drift") == [], "local output drift recorded during build")
    sources, outputs = provenance.get("source_sha256"), result.get("olean_sha256")
    fail_unless(isinstance(sources, dict) and isinstance(outputs, dict), "missing source/output hashes")
    fail_unless(set(sources) == set(outputs) and "GQ2" in sources
                and len(sources) == result["total"], "source/output/module counts disagree")
    for module in sources:
        fail_unless(isinstance(module, str) and MODULE.fullmatch(module) is not None,
                    "unsafe local module name")
        for value in (sources[module], outputs[module]):
            fail_unless(isinstance(value, str) and HEX.fullmatch(value) is not None,
                        "malformed source/output digest")
    files = result.get("output_file_sha256")
    fail_unless(isinstance(files, dict), "missing complete output inventory")
    for name, value in files.items():
        fail_unless(isinstance(name, str) and isinstance(value, str) and HEX.fullmatch(value) is not None,
                    "malformed output file entry")
        suffix = next((s for s in (".olean.private", ".olean.server", ".olean", ".ilean", ".ir")
                       if name.endswith(s)), None)
        fail_unless(suffix is not None, "unexpected output file extension")
        stem = name[:-len(suffix)]
        fail_unless(stem.replace("/", ".") in sources and "." not in stem
                    and not stem.startswith("/") and "//" not in stem,
                    "unsafe or unknown output path")
    for module in sources:
        stem = module.replace(".", "/")
        fail_unless(files.get(stem+".olean") == outputs[module] and stem+".ilean" in files,
                    "mandatory output missing or primary digest disagrees")
        companions = [stem+s for s in (".olean.private", ".olean.server", ".ir")]
        fail_unless(not any(name in files for name in companions) or all(name in files for name in companions),
                    "incomplete module-system companion inventory")
    return sources, outputs


def check_snapshot(snapshot, packages, lean):
    fail_unless(lean.parent.name == "bin" and (lean.parent.parent/"bin/lean").resolve() == lean,
                "selected compiler must be the exact bin/lean executable used by the replay runner")
    provenance = read_json(snapshot/"provenance.json")
    result = read_json(snapshot/"result.json")
    sources, outputs = validate_record(provenance, result)
    fail_unless(provenance.get("driver_sha256") == sha(ROOT/"scripts/w361_fresh_build.py"),
                "recorded build producer differs from the current reviewed driver")
    fail_unless(Path(provenance.get("workspace", "")).resolve() == ROOT,
                "recorded workspace differs from this checkout")
    source_root, artifact_root = snapshot/"source", snapshot/"lib/lean"
    manifest = ROOT/"lake-manifest.json"
    manifest_bytes = manifest.read_bytes()
    fail_unless((source_root/"lake-manifest.json").read_bytes() == manifest_bytes
                == (packages.parent.parent/"lake-manifest.json").read_bytes(),
                "snapshot/live/dependency manifests differ")
    fail_unless(provenance.get("manifest_sha256") == sha(manifest), "recorded manifest hash mismatch")
    pin = (ROOT/"lean-toolchain").read_text().strip()
    fail_unless(pin.startswith("leanprover/lean4:v") and provenance.get("toolchain_pin") == pin,
                "toolchain pin mismatch")
    fail_unless(Path(provenance.get("lean", "")).resolve() == lean,
                "recorded compiler differs from explicitly selected compiler")
    fail_unless(provenance.get("lean_sha256") == sha(lean), "compiler executable hash mismatch")
    version = subprocess.run([str(lean), "--version"], text=True, capture_output=True, check=False)
    fail_unless(version.returncode == 0 and version.stdout.strip() == provenance.get("lean_version")
                and version.stdout.startswith("Lean (version " + pin.removeprefix("leanprover/lean4:v") + ","),
                "compiler version mismatch")
    dependency_roots, missing = [], []
    names = []
    for entry in read_json(manifest)["packages"]:
        name = entry["name"].removeprefix("«").removesuffix("»")
        fail_unless(re.fullmatch(r"[A-Za-z0-9_-]+", name) is not None and name not in names,
                    "invalid or duplicate dependency name")
        names.append(name)
        path = packages/name/".lake/build/lib/lean"
        if path.is_dir():
            fail_unless(not (path/"GQ2").exists() and not (path/"GQ2.olean").exists(),
                        "external dependency contains local GQ2 artifacts")
            dependency_roots.append(str(path))
        else:
            missing.append(str(path))
    fail_unless(provenance.get("dependency_artifact_roots") == dependency_roots
                and provenance.get("declared_dependency_roots_without_artifacts") == missing,
                "declared dependency artifact roots drifted")
    for module in sources:
        relative = Path(module.replace(".", "/") + ".lean")
        fail_unless(sha(source_root/relative) == sources[module], "snapshotted source drift: " + module)
        fail_unless(sha(ROOT/relative) == sources[module], "live source differs from build: " + module)
        output = artifact_root/relative.with_suffix(".olean")
        fail_unless(output.is_file() and output.stat().st_size > 0
                    and sha(output) == outputs[module], "compiled artifact drift: " + module)
        index = output.with_suffix(".ilean")
        fail_unless(index.is_file() and index.stat().st_size > 0, "missing index artifact: " + module)
    actual_outputs = {".".join(path.relative_to(artifact_root).with_suffix("").parts)
                      for path in artifact_root.rglob("*.olean")}
    fail_unless(actual_outputs == set(outputs), "unexpected local artifact outside recorded closure")
    actual_files = {str(path.relative_to(artifact_root)): sha(path)
                    for path in artifact_root.rglob("*") if path.is_file()}
    fail_unless(actual_files == result["output_file_sha256"],
                "local output-file inventory/hash drift (including companions/indexes)")
    return {
        "snapshot": str(snapshot), "modules": len(sources),
        "provenance_sha256": sha(snapshot/"provenance.json"),
        "result_sha256": sha(snapshot/"result.json"),
        "local_source_set_sha256": canonical_digest(sources),
        "local_output_set_sha256": canonical_digest(outputs),
        "local_output_file_set_sha256": canonical_digest(result["output_file_sha256"]),
        "local_output_files": len(result["output_file_sha256"]),
        "manifest_sha256": sha(manifest), "lean_sha256": sha(lean),
        "recorded_live_source_drift": result.get("live_source_drift"),
        "current_live_source_match": True,
        "dependency_assurance": "manifest-matching external artifacts reused, not rebuilt or byte-attested",
        "snapshot_atomic": False,
    }


def replay_source_hashes():
    return {name: sha(ROOT/name) for name in REPLAY_SOURCES}


def staged_content_hashes():
    result = {}
    for directory in ("general-template-staged", "general-certificate-staged", "general-ln-template-staged"):
        path = ROOT/"generated"/directory
        fail_unless(path.is_dir(), "missing staged directory: " + directory)
        for item in sorted(path.rglob("*")):
            if item.is_file():
                result[str(item.relative_to(ROOT))] = sha(item)
    pdf = ROOT/"output/pdf/w361-staged-certificates.pdf"
    result[str(pdf.relative_to(ROOT))] = sha(pdf)
    return result


def check_report_location(destination, snapshot, packages, lean):
    for protected in (snapshot, ROOT, packages, lean.parent.parent):
        fail_unless(not destination.is_relative_to(protected),
                    "report directory must be outside the snapshot, workspace, dependencies and toolchain")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("snapshot", type=Path)
    parser.add_argument("--packages", type=Path, required=True)
    parser.add_argument("--lean", type=Path, required=True,
                        help="explicit pinned Lean executable; never taken from snapshot metadata")
    parser.add_argument("--replay", action="store_true", help="also run the complete read-only staged suite")
    parser.add_argument("--report-dir", type=Path,
                        help="new report directory; must not already exist (default: fresh /private/tmp directory)")
    args = parser.parse_args()
    snapshot, packages, lean = args.snapshot.resolve(), args.packages.resolve(), args.lean.resolve()
    requested_report = args.report_dir.resolve() if args.report_dir else None
    if requested_report is not None:
        check_report_location(requested_report, snapshot, packages, lean)
    started = datetime.now(timezone.utc).isoformat()
    state = check_snapshot(snapshot, packages, lean)
    before = replay_source_hashes()
    content_before = staged_content_hashes()
    print("FRESH_CONTENT_CHECK_PASS|" + str(state["modules"]), flush=True)
    if args.report_dir:
        report_dir = requested_report
        report_dir.mkdir(parents=True, exist_ok=False)
    else:
        report_dir = Path(tempfile.mkdtemp(prefix="gq2-w361-fresh-verified-", dir="/private/tmp"))
    if args.replay:
        log = report_dir/"staged-replay.log"
        env = dict(os.environ, GQ2_W361_PACKAGES=str(packages),
                   GQ2_W361_ARTIFACTS=str(snapshot/"lib/lean"),
                   GQ2_W361_TOOLCHAIN=str(lean.parent.parent))
        with log.open("w") as stream:
            process = subprocess.run(["bash", "scripts/w361_check_staged.sh"], cwd=ROOT,
                                     env=env, stdout=stream, stderr=subprocess.STDOUT)
        fail_unless(process.returncode == 0, "staged replay failed; see " + str(log))
        fail_unless("W361_STAGED_CHECK_PASS (not owner approval or a transitive fresh-build certificate)"
                    in log.read_text().splitlines(), "staged suite did not complete")
        after = check_snapshot(snapshot, packages, lean)
        fail_unless(after == state, "snapshot evidence changed during replay")
        fail_unless(replay_source_hashes() == before, "live replay sources changed during replay")
        fail_unless(staged_content_hashes() == content_before, "staged files changed during replay")
        state["replay_log_sha256"] = sha(log)
    state.update(schema="gq2.w361.fresh-content-check.v1.staged", status="PASS",
                 replayed=args.replay, started_utc=started,
                 finished_utc=datetime.now(timezone.utc).isoformat(), replay_sources_sha256=before,
                 staged_content_sha256=content_before,
                 assurance="Content consistency with the recorded observed build; not signed attestation, "
                 "atomic snapshotting, owner approval, or proof of editorial prose.")
    (report_dir/"report.json").write_text(json.dumps(state, indent=2, sort_keys=True)+"\n")
    print("FRESH_VERIFICATION_REPORT|" + str(report_dir/"report.json"), flush=True)


if __name__ == "__main__":
    try:
        main()
    except (VerificationError, OSError, ValueError, KeyError, TypeError) as exc:
        raise SystemExit("fresh verification error: " + str(exc)) from exc
