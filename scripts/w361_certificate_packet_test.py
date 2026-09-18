#!/usr/bin/env python3
"""Durable structural/mutation regression tests, NOT a substitute for Lean replay.

Uses the checked staged exports as grammar fixtures. No expected mathematical
statement is inferred from these samples; all-rank bridges live in Lean.
"""
from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest
from contextlib import redirect_stdout
from io import StringIO

import w361_certificate_packet as packet


class PacketTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        paths = sorted((packet.ROOT / "generated/general-certificate-staged").glob("*.packet.json"))
        if not paths:
            raise RuntimeError("generate the staged packet fixtures first")
        cls.fixtures = []
        for path in paths:
            old = json.loads(path.read_text())["payload"]
            cls.fixtures.append(packet.make_packet(old["word"], old["fox"], old["phase"], old["cover"]))

    def reject_mutation(self, mutate, *, rehash=True):
        for fixture in self.fixtures:
            obj = deepcopy(fixture)
            mutate(obj)
            if rehash:
                obj["packet_hash"] = packet.digest(obj["payload"])
            with self.subTest(family=obj["payload"]["word"]["payload"]["family"]):
                with self.assertRaises(packet.word.TemplateError):
                    packet.validate(obj)

    def test_identity(self):
        for fixture in self.fixtures:
            self.assertEqual(packet.validate(fixture), fixture["payload"])
            self.assertEqual(packet.digest(fixture["payload"]), fixture["packet_hash"])

    def test_roundtrip(self):
        for fixture in self.fixtures:
            self.assertEqual(json.loads(packet.word.canonical_json(fixture)), fixture)

    def test_wrong_hash(self):
        self.reject_mutation(lambda o: o.update(packet_hash="0"*64), rehash=False)

    def test_wrong_status(self):
        self.reject_mutation(lambda o: o.update(status="ACCEPTED"))

    def test_wrong_schema(self):
        self.reject_mutation(lambda o: o["payload"].update(schema="approved"))

    def test_extra_payload(self):
        self.reject_mutation(lambda o: o["payload"].update(extra=True))

    def test_missing_cover(self):
        self.reject_mutation(lambda o: o["payload"].pop("cover"))

    def test_section_bool_is_not_one(self):
        self.reject_mutation(lambda o: o["payload"]["sections"][0].update(number=True))

    def test_section_float_is_not_one(self):
        self.reject_mutation(lambda o: o["payload"]["sections"][0].update(number=1.0))

    def test_section_order(self):
        self.reject_mutation(lambda o: o["payload"]["sections"].reverse())

    def test_changed_prose(self):
        self.reject_mutation(lambda o: o["payload"]["sections"][0]["paragraphs"].append("unproved"))

    def test_changed_reference(self):
        self.reject_mutation(lambda o: o["payload"]["sections"][0]["references"].append("GQ2.false"))

    def test_source_drift(self):
        self.reject_mutation(lambda o: o["payload"]["source_provenance"]["sha256"].update({
            "scripts/w361_certificate_packet.py": "0"*64}))

    def test_word_hash(self):
        self.reject_mutation(lambda o: o["payload"]["word"].update(template_hash="0"*64))

    def test_fox_hash(self):
        self.reject_mutation(lambda o: o["payload"]["fox"].update(template_hash="0"*64))

    def test_phase_hash(self):
        self.reject_mutation(lambda o: o["payload"]["phase"].update(template_hash="0"*64))

    def test_cover_hash(self):
        self.reject_mutation(lambda o: o["payload"]["cover"].update(template_hash="0"*64))

    def test_cover_link(self):
        def mutate(o):
            c = o["payload"]["cover"]
            c["payload"]["phase_template_hash"] = "0"*64
            c["template_hash"] = packet.cover.digest(c["payload"])
        self.reject_mutation(mutate)

    def test_alpha_requires_certificate_scope(self):
        def mutate(o):
            w = o["payload"]["word"]
            w["payload"]["structural"]["alpha"] = 1
            w["template_hash"] = packet.word.template_hash(w["payload"])
        self.reject_mutation(mutate)

    def test_rank_binding(self):
        other = next(f for f in self.fixtures if f["payload"]["phase"]["payload"]["structural"]["h"] == 0)
        for fixture in self.fixtures:
            if fixture["payload"]["word"]["payload"]["structural"]["h"] == 0:
                continue
            obj = deepcopy(fixture)
            obj["payload"]["phase"] = deepcopy(other["payload"]["phase"])
            obj["packet_hash"] = packet.digest(obj["payload"])
            with self.assertRaises(packet.word.TemplateError):
                packet.validate(obj)

    def test_all_sections_and_math_delimiters(self):
        for fixture in self.fixtures:
            tex = packet.render_tex(fixture)
            for n in range(1, 11):
                self.assertIn(r"\subsection*{"+str(n)+". ", tex)
            self.assertIn(r"\[\begin{pmatrix}", tex)
            self.assertIn(r"\[\begin{aligned}", tex)
            self.assertIn("STAGED", tex)
            self.assertNotIn("dyadicAppendixTODO", tex)

    def test_probe_is_deterministic_and_retains_type_checks(self):
        for family in ("pair", "mobile"):
            probe = packet.proof_probe(family)
            self.assertEqual(probe, packet.proof_probe(family))
            for ref in packet.references(family):
                self.assertIn("#check " + ref, probe)
            self.assertIn("collectAxioms", probe)
            self.assertNotIn("set_option", probe)

    def emitted(self, directory):
        out = Path(directory)/"general-certificate-staged"
        fixture = deepcopy(self.fixtures[0])
        base = packet.emit(fixture, out, "synthetic transcript: structure tests only\n")
        return out, base

    def test_artifact_only_is_explicit(self):
        with tempfile.TemporaryDirectory() as directory:
            out, _ = self.emitted(directory)
            capture = StringIO()
            with redirect_stdout(capture):
                self.assertEqual(packet.check(out), 1)
            self.assertIn("NOT Lean-synchronized", capture.getvalue())

    def test_output_scope(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(packet.word.TemplateError):
                packet.emit(self.fixtures[0], Path(directory)/"frozen", "")

    def test_manifest_hash_container(self):
        with tempfile.TemporaryDirectory() as directory:
            out, base = self.emitted(directory)
            path = out/(base+".files.json")
            manifest = json.loads(path.read_text())
            manifest["sha256"] = list(manifest["sha256"])
            path.write_text(packet.word.canonical_json(manifest))
            with self.assertRaises(packet.word.TemplateError):
                packet.check(out)

    def test_manifest_traversal(self):
        with tempfile.TemporaryDirectory() as directory:
            out, base = self.emitted(directory)
            path = out/(base+".files.json")
            manifest = json.loads(path.read_text())
            manifest["sha256"]["../escape"] = "0"*64
            path.write_text(packet.word.canonical_json(manifest))
            with self.assertRaises(packet.word.TemplateError):
                packet.check(out)

    def test_tex_drift(self):
        with tempfile.TemporaryDirectory() as directory:
            out, base = self.emitted(directory)
            (out/(base+".appendix.tex")).write_text("forged")
            with self.assertRaises(packet.word.TemplateError):
                packet.check(out)

    def test_probe_drift(self):
        with tempfile.TemporaryDirectory() as directory:
            out, base = self.emitted(directory)
            (out/(base+".proofs.lean")).write_text("forged")
            with self.assertRaises(packet.word.TemplateError):
                packet.check(out)

    def test_transcript_hash_drift(self):
        with tempfile.TemporaryDirectory() as directory:
            out, base = self.emitted(directory)
            (out/(base+".proofs.txt")).write_text("forged")
            with self.assertRaises(packet.word.TemplateError):
                packet.check(out)


if __name__ == "__main__":
    unittest.main(verbosity=2)
