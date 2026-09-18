#!/usr/bin/env python3
"""Compile a frozen local import closure without reusing any GQ2 artifacts.

Mathlib/dependency artifacts are reused only after checking the exact package manifest.
All local sources are snapshotted before compilation, and all outputs remain in a new
temporary directory. No source, shared cache, or existing build output is overwritten.
"""

from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import time


def manifest_package_names(manifest):
    """Only declared dependencies belong on the search path, not neighboring caches."""
    names = [entry["name"].removeprefix("«").removesuffix("»")
             for entry in json.loads(manifest)["packages"]]
    if len(set(names)) != len(names) or any(
            not re.fullmatch(r"[A-Za-z0-9_-]+", name) for name in names):
        raise ValueError("Unexpected or duplicate manifest package name")
    return names


def compiler_local_imports(lean, source, source_root, env):
    """Use Lean's real header parser; --deps does not require local oleans."""
    result = subprocess.run([str(lean), "--deps", str(source)], cwd=source_root,
                            env=env, text=True, capture_output=True)
    if result.returncode:
        raise ValueError(f"Lean dependency parsing failed for {source}:\n"
                         f"{result.stdout}{result.stderr}")
    local = []
    for line in result.stdout.splitlines():
        path = Path(line.strip())
        if path.is_relative_to(source_root):
            relative = path.relative_to(source_root)
            if relative.suffix != ".olean":
                raise ValueError(f"Unexpected local dependency: {path}")
            module = ".".join(relative.with_suffix("").parts)
            if module == "GQ2" or module.startswith("GQ2."):
                local.append(module)
            else:
                raise ValueError(f"Unexpected local namespace: {module}")
        elif "GQ2" in path.parts or path.name == "GQ2.olean":
            raise ValueError(f"GQ2 artifact outside fresh source root: {path}")
    return sorted(set(local))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packages", type=Path, required=True)
    parser.add_argument("--lean", type=Path, required=True)
    parser.add_argument("--target", default="GQ2")
    parser.add_argument("--jobs", type=int, default=3)
    parser.add_argument("--require-live-match", action="store_true",
                        help="also fail if a compiled source differs in the live worktree at finish")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("jobs must be positive")
    root = Path(__file__).resolve().parent.parent
    packages = args.packages.resolve()
    lean = args.lean.resolve()
    manifest = (root / "lake-manifest.json").read_bytes()
    if manifest != (packages.parent.parent / "lake-manifest.json").read_bytes():
        parser.error("dependency package manifest differs from this workspace")
    if not lean.is_file() or not os.access(lean, os.X_OK):
        parser.error("Lean executable does not exist or is not executable")
    toolchain_pin = (root / "lean-toolchain").read_text().strip()
    if not toolchain_pin.startswith("leanprover/lean4:v"):
        parser.error("unexpected Lean toolchain pin")
    expected_version = toolchain_pin.removeprefix("leanprover/lean4:v")
    version_result = subprocess.run([str(lean), "--version"], text=True,
                                    capture_output=True)
    lean_version = version_result.stdout.strip()
    if version_result.returncode or not lean_version.startswith(
            f"Lean (version {expected_version},"):
        parser.error(f"Lean version does not match {toolchain_pin}: {lean_version!r}")
    lean_sha256 = hashlib.sha256(lean.read_bytes()).hexdigest()
    declared_paths = [packages / name / ".lake/build/lib/lean"
                      for name in manifest_package_names(manifest)]
    dependency_paths = [path for path in declared_paths if path.is_dir()]
    missing_dependency_paths = [str(path) for path in declared_paths if not path.is_dir()]
    for path in dependency_paths:
        if (path / "GQ2").exists() or (path / "GQ2.olean").exists():
            parser.error(f"declared dependency contains local GQ2 artifacts: {path}")
    if shutil.disk_usage("/private/tmp").free < 6 * 2**30:
        parser.error("less than 6 GiB free; declining a fresh artifact build")
    run = Path(tempfile.mkdtemp(prefix="gq2-w361-fresh-", dir="/private/tmp"))
    source_root, output_root, logs = (run / name for name in ("source", "lib/lean", "logs"))
    for directory in (source_root, output_root, logs):
        directory.mkdir(parents=True)
    graph, hashes = {}, {}

    def path_for(module):
        if not re.fullmatch(r"GQ2(?:\.[A-Za-z0-9_]+)*", module):
            raise ValueError(f"Unexpected local module name: {module!r}")
        return Path(module.replace(".", "/") + ".lean")

    snapshot_started = datetime.now(timezone.utc).isoformat()
    all_hashes = {}
    # Copy bytes first. This is a frozen collection, not an atomic filesystem epoch.
    # The successful build proves precisely these bytes; live drift is reported below.
    for original in [root / "GQ2.lean", *sorted((root / "GQ2").rglob("*.lean"))]:
        relative = original.relative_to(root)
        content = original.read_bytes()
        destination = source_root / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(content)
        module = ".".join(relative.with_suffix("").parts)
        all_hashes[module] = hashlib.sha256(content).hexdigest()
    snapshot_finished = datetime.now(timezone.utc).isoformat()
    parse_env = dict(os.environ, LEAN_PATH=":".join(map(str,
        [source_root, *dependency_paths, lean.parent.parent / "lib/lean"])))
    frontier = {args.target}
    with ThreadPoolExecutor(max_workers=args.jobs) as parser_pool:
        while frontier:
            names = sorted(frontier)
            results = parser_pool.map(lambda name: compiler_local_imports(
                lean, source_root / path_for(name), source_root, parse_env), names)
            for module, imports in zip(names, results):
                if module not in all_hashes:
                    raise ValueError(f"Missing snapshotted source: {module}")
                graph[module] = imports
                hashes[module] = all_hashes[module]
            frontier = {dep for module in names for dep in graph[module] if dep not in graph}

    (source_root / "lake-manifest.json").write_bytes(manifest)
    metadata = {
        "workspace": str(root), "lean": str(lean),
        "lean_version": lean_version, "lean_sha256": lean_sha256,
        "toolchain_pin": toolchain_pin,
        "manifest_sha256": hashlib.sha256(manifest).hexdigest(),
        "source_sha256": hashes, "target": args.target,
        "local_artifacts_reused": 0, "jobs": args.jobs,
        "import_parser": "pinned Lean --deps",
        "dependency_artifact_roots": list(map(str, dependency_paths)),
        "declared_dependency_roots_without_artifacts": missing_dependency_paths,
        "dependency_assurance": "manifest matched; external artifacts reused, not rebuilt",
        "snapshot_started_utc": snapshot_started,
        "snapshot_finished_utc": snapshot_finished,
        "snapshot_atomic": False,
        "driver_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "local_output_inventory": "all-local-output-files-v1",
    }
    (run / "provenance.json").write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n")
    lean_path = [output_root, *dependency_paths, lean.parent.parent / "lib/lean"]
    env = dict(os.environ, LEAN_PATH=":".join(map(str, lean_path)))
    print(f"Fresh snapshot: {run}\nLocal modules: {len(graph)}; reused: 0", flush=True)

    def build(module):
        if shutil.disk_usage(run).free < 4 * 2**30:
            return 1, 0, "Disk space dropped below 4 GiB; stopped safely.", {}
        destination = output_root / path_for(module).with_suffix(".olean")
        destination.parent.mkdir(parents=True, exist_ok=True)
        log = logs / f"{module}.log"
        start = time.monotonic()
        with log.open("w") as stream:
            result = subprocess.run(
                [str(lean), "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
                 "-Dpp.unicode.fun=true", "-o", str(destination),
                 "-i", str(destination.with_suffix(".ilean")), str(path_for(module))],
                cwd=source_root, env=env, stdout=stream, stderr=subprocess.STDOUT)
            if result.returncode == 0:
                companions = [destination.with_suffix(suffix) for suffix in
                              (".olean.private", ".olean.server", ".ir")]
                expected = [destination, destination.with_suffix(".ilean")]
                if any(path.exists() for path in companions):
                    expected += companions
                missing = [str(path) for path in expected
                           if not path.is_file() or path.stat().st_size == 0]
                if missing:
                    stream.write("\nCompiler reported success without nonempty outputs: "
                                 + ", ".join(missing) + "\n")
                    return 1, time.monotonic() - start, str(log), {}
                files = {str(path.relative_to(output_root)): hashlib.sha256(path.read_bytes()).hexdigest()
                         for path in expected}
            else:
                files = {}
        return result.returncode, time.monotonic() - start, str(log), files

    pending, done, running, failed = set(graph), set(), {}, []
    built_file_hashes = {}
    started = time.monotonic()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            ready = sorted(module for module in pending if set(graph[module]) <= done)
            while ready and len(running) < args.jobs and not failed:
                module = ready.pop(0)
                pending.remove(module)
                running[pool.submit(build, module)] = module
            if not running:
                break
            completed, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in completed:
                module = running.pop(future)
                code, elapsed, log, file_hashes = future.result()
                if code:
                    failed.append(module)
                    print(f"FAIL {module} ({elapsed:.1f}s): {log}", flush=True)
                else:
                    done.add(module)
                    built_file_hashes.update(file_hashes)
                    print(f"[{len(done)}/{len(graph)}] {module} ({elapsed:.1f}s)", flush=True)
    drift = [module for module, digest in hashes.items()
             if not (root / path_for(module)).is_file()
             or hashlib.sha256((root / path_for(module)).read_bytes()).hexdigest() != digest]
    manifest_drift = (root / "lake-manifest.json").read_bytes() != manifest
    actual_files = {str(path.relative_to(output_root)): hashlib.sha256(path.read_bytes()).hexdigest()
                    for path in output_root.rglob("*") if path.is_file()}
    output_drift = sorted(name for name in set(actual_files) | set(built_file_hashes)
                          if actual_files.get(name) != built_file_hashes.get(name))
    result = {"completed": len(done), "total": len(graph), "failed": failed,
              "unbuilt": sorted(pending), "seconds": time.monotonic() - started,
              "live_source_drift": sorted(drift), "live_manifest_drift": manifest_drift,
              "local_output_file_drift": output_drift,
              "output_file_sha256": dict(sorted(built_file_hashes.items())),
              "olean_sha256": {module: hashlib.sha256(
                  (output_root / path_for(module).with_suffix(".olean")).read_bytes()).hexdigest()
                  for module in sorted(done)}}
    (run / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: value for key, value in result.items()
                      if key not in {"olean_sha256", "output_file_sha256"}}), flush=True)
    if failed or pending or output_drift:
        raise SystemExit(1)
    print("FRESH BUILD COMPLETE", flush=True)
    if drift or manifest_drift:
        print("LIVE SOURCE DRIFT: successful build certifies the frozen snapshot only", flush=True)
        if args.require_live_match:
            raise SystemExit(2)


if __name__ == "__main__":
    main()
