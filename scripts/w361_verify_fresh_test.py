#!/usr/bin/env python3
"""Structural regression tests for fresh-build records, not build attestation."""
from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest

import w361_verify_fresh as verify


class FreshRecordTests(unittest.TestCase):
    def setUp(self):
        self.provenance = {
            "target": "GQ2", "local_artifacts_reused": 0,
            "import_parser": "pinned Lean --deps", "snapshot_atomic": False,
            "local_output_inventory": "all-local-output-files-v1",
            "source_sha256": {"GQ2": "0"*64, "GQ2.Sanity": "1"*64},
        }
        self.result = {
            "completed": 2, "total": 2, "failed": [], "unbuilt": [],
            "live_manifest_drift": False,
            "local_output_file_drift": [],
            "olean_sha256": {"GQ2": "2"*64, "GQ2.Sanity": "3"*64},
            "output_file_sha256": {"GQ2.olean": "2"*64, "GQ2.ilean": "4"*64,
                "GQ2/Sanity.olean": "3"*64, "GQ2/Sanity.ilean": "5"*64},
        }

    def reject(self, mutate):
        p, r = deepcopy(self.provenance), deepcopy(self.result)
        mutate(p, r)
        with self.assertRaises(verify.VerificationError):
            verify.validate_record(p, r)

    def test_valid_record(self):
        self.assertEqual(verify.validate_record(self.provenance, self.result),
                         (self.provenance["source_sha256"], self.result["olean_sha256"]))

    def test_partial_target(self):
        self.reject(lambda p, r: p.update(target="GQ2.Sanity"))

    def test_reused_artifact(self):
        self.reject(lambda p, r: p.update(local_artifacts_reused=1))

    def test_reuse_bool(self):
        self.reject(lambda p, r: p.update(local_artifacts_reused=False))

    def test_reuse_float(self):
        self.reject(lambda p, r: p.update(local_artifacts_reused=0.0))

    def test_wrong_parser(self):
        self.reject(lambda p, r: p.update(import_parser="regex"))

    def test_atomic_claim(self):
        self.reject(lambda p, r: p.update(snapshot_atomic=True))

    def test_atomic_zero_not_false(self):
        self.reject(lambda p, r: p.update(snapshot_atomic=0))

    def test_failed(self):
        self.reject(lambda p, r: r.update(failed=["GQ2"]))

    def test_unbuilt(self):
        self.reject(lambda p, r: r.update(unbuilt=["GQ2"]))

    def test_missing_completion(self):
        self.reject(lambda p, r: r.pop("completed"))

    def test_mismatched_counts(self):
        self.reject(lambda p, r: r.update(completed=1))

    def test_float_count(self):
        self.reject(lambda p, r: r.update(completed=2.0))

    def test_bool_count(self):
        self.reject(lambda p, r: r.update(completed=True))

    def test_zero_count(self):
        self.reject(lambda p, r: r.update(completed=0, total=0))

    def test_manifest_drift(self):
        self.reject(lambda p, r: r.update(live_manifest_drift=True))

    def test_manifest_zero_not_false(self):
        self.reject(lambda p, r: r.update(live_manifest_drift=0))

    def test_missing_source_map(self):
        self.reject(lambda p, r: p.pop("source_sha256"))

    def test_missing_output(self):
        self.reject(lambda p, r: r["olean_sha256"].pop("GQ2.Sanity"))

    def test_extra_output(self):
        self.reject(lambda p, r: r["olean_sha256"].update({"GQ2.Extra": "4"*64}))

    def test_no_umbrella(self):
        def mutate(p, r):
            p["source_sha256"]["GQ2.Other"] = p["source_sha256"].pop("GQ2")
            r["olean_sha256"]["GQ2.Other"] = r["olean_sha256"].pop("GQ2")
        self.reject(mutate)

    def test_unsafe_module(self):
        def mutate(p, r):
            p["source_sha256"]["GQ2/../escape"] = p["source_sha256"].pop("GQ2.Sanity")
            r["olean_sha256"]["GQ2/../escape"] = r["olean_sha256"].pop("GQ2.Sanity")
        self.reject(mutate)

    def test_malformed_hashes(self):
        for value in (None, 0, True, "F"*64, "0"*63, "0"*65, "z"*64):
            with self.subTest(value=value):
                self.reject(lambda p, r: p["source_sha256"].update(GQ2=value))

    def test_old_inventory(self):
        self.reject(lambda p, r: p.pop("local_output_inventory"))

    def test_output_drift(self):
        self.reject(lambda p, r: r.update(local_output_file_drift=["GQ2.olean.private"]))

    def test_missing_inventory(self):
        self.reject(lambda p, r: r.pop("output_file_sha256"))

    def test_partial_companions(self):
        self.reject(lambda p, r: r["output_file_sha256"].update({"GQ2.olean.private": "6"*64}))

    def test_complete_companions(self):
        self.result["output_file_sha256"].update({"GQ2"+s: "6"*64 for s in (".olean.private", ".olean.server", ".ir")})
        verify.validate_record(self.provenance, self.result)

    def test_output_traversal(self):
        self.reject(lambda p, r: r["output_file_sha256"].update({"GQ2/../escape.olean": "6"*64}))

    def test_output_unknown_module(self):
        self.reject(lambda p, r: r["output_file_sha256"].update({"GQ2/Unknown.ir": "6"*64}))

    def test_output_unknown_extension(self):
        self.reject(lambda p, r: r["output_file_sha256"].update({"GQ2.bad": "6"*64}))

    def test_primary_digest_disagrees(self):
        self.reject(lambda p, r: r["output_file_sha256"].update({"GQ2.olean": "6"*64}))

    def test_missing_index(self):
        self.reject(lambda p, r: r["output_file_sha256"].pop("GQ2.ilean"))

    def test_record_type(self):
        with self.assertRaises(verify.VerificationError):
            verify.validate_record([], self.result)

    def test_json_rejects_duplicates_and_nonfinite(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/"data.json"
            for text in ('{"a":0,"a":1}', '{"a":NaN}', '{"a":Infinity}', '{"a":-Infinity}'):
                path.write_text(text)
                with self.subTest(text=text):
                    with self.assertRaises(verify.VerificationError):
                        verify.read_json(path)

    def test_canonical_digest(self):
        self.assertEqual(verify.canonical_digest({"b":1,"a":2}), verify.canonical_digest({"a":2,"b":1}))
        self.assertNotEqual(verify.canonical_digest({"a":1}), verify.canonical_digest({"a":True}))
        self.assertNotEqual(verify.canonical_digest({"a":1}), verify.canonical_digest({"a":1.0}))

    def test_report_cannot_contaminate_checked_roots(self):
        snapshot = Path("/private/tmp/snapshot")
        packages = Path("/private/tmp/packages")
        lean = Path("/private/tmp/toolchain/bin/lean")
        for root in (snapshot, packages, lean.parent.parent, verify.ROOT):
            for destination in (root, root/"new-report"):
                with self.subTest(destination=destination):
                    with self.assertRaises(verify.VerificationError):
                        verify.check_report_location(destination, snapshot, packages, lean)

    def test_separate_report_location(self):
        verify.check_report_location(Path("/private/tmp/snapshot-review"),
                                     Path("/private/tmp/snapshot"), Path("/private/tmp/packages"),
                                     Path("/private/tmp/toolchain/bin/lean"))


if __name__ == "__main__":
    unittest.main(verbosity=2)
