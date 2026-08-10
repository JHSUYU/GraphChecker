#!/usr/bin/env python3

import hashlib
import importlib.util
import json
import os
import shutil
import tempfile
import unittest
from unittest import mock


HERE = os.path.dirname(os.path.abspath(__file__))
SPEC = importlib.util.spec_from_file_location(
    "solver_binding_audit",
    os.path.join(HERE, "solver_binding_audit.py"))
AUDIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUDIT)


class SolverBindingAuditTest(unittest.TestCase):
    def test_bound_operand_without_load_bearing_edge_is_a_finding(self):
        status, finding, inconclusive = AUDIT.edge_evidence_summary({
            "bindingStatus": "BOUND_TO_RECORDED_PRODUCER_VERSIONS",
            "edgeAblations": [{
                "classification": "REDUNDANT_OR_NOT_LOAD_BEARING",
            }],
        })
        self.assertEqual("NO_LOAD_BEARING_EDGE", status)
        self.assertTrue(finding)
        self.assertFalse(inconclusive)

    def test_exact_named_assertion_removal_preserves_similar_name(self):
        query = """(set-logic ALL)
(declare-const x Int)
(assert (! (= x 1) :named edge_value))
(assert (! (= x 2) :named edge_value_suffix))
(check-sat)
"""
        derived = AUDIT.build_query(query, removed=["edge_value"])
        self.assertNotIn(":named edge_value)", derived)
        self.assertIn(":named edge_value_suffix", derived)
        self.assertEqual(1, derived.count("(check-sat)"))

    def test_solver_error_cannot_be_misread_as_sat(self):
        with tempfile.TemporaryDirectory() as directory:
            solver = os.path.join(directory, "fake-z3")
            query = os.path.join(directory, "query.smt2")
            with open(solver, "w", encoding="utf-8", newline="\n") as handle:
                handle.write("#!/bin/sh\n"
                             "echo '(error \"malformed\")'\n"
                             "echo sat\n"
                             "exit 1\n")
            os.chmod(solver, 0o755)
            with open(query, "w", encoding="utf-8", newline="\n") as handle:
                handle.write("(check-sat)\n")
            result = AUDIT.run_solver(solver, query, 5000)
            self.assertEqual("solver_error", result["status"])
            self.assertEqual(1, result["answerCount"])

    def test_manifest_requires_exact_smt_hash(self):
        smt = """(set-logic ALL)
(declare-const operand Int)
(declare-const producer Int)
(assert (! (= operand producer) :named edge_value))
(assert (! true :named fatal_path_prefix))
(assert (! true :named fatal_path))
(check-sat)
"""
        with tempfile.TemporaryDirectory() as directory:
            smt_path, manifest_path = self._write_inputs(directory, smt)
            with open(manifest_path, encoding="utf-8") as handle:
                manifest = json.load(handle)
            manifest["composedSmtArtifact"]["sha256"] = ""
            with self.assertRaisesRegex(ValueError, "sha256"):
                AUDIT.validate_manifest(
                    manifest, smt_path, AUDIT.named_assertions(smt))

    @unittest.skipUnless(shutil.which("z3"), "z3 is unavailable")
    def test_report_publication_failure_is_inconclusive(self):
        smt = """(set-logic ALL)
(declare-const operand Int)
(declare-const producer Int)
(assert (! (= operand producer) :named edge_value))
(assert (! true :named fatal_path_prefix))
(assert (! true :named fatal_path))
(check-sat)
"""
        with tempfile.TemporaryDirectory() as directory:
            smt_path, manifest_path = self._write_inputs(directory, smt)
            output = os.path.join(directory, "audit")
            with mock.patch.object(AUDIT, "write_json",
                                   side_effect=OSError("publish failed")):
                status = AUDIT.main([
                    "--smt", smt_path,
                    "--manifest", manifest_path,
                    "--output-dir", output,
                    "--solver-timeout-ms", "5000",
                ])
            self.assertEqual(2, status)
            self.assertFalse(os.path.exists(os.path.join(
                output, "solver-binding-audit.json")))

    @unittest.skipUnless(shutil.which("z3"), "z3 is unavailable")
    def test_operand_audit_selects_its_own_path_prefix(self):
        smt = """(set-logic ALL)
(declare-const path0 Bool)
(declare-const path1 Bool)
(declare-const operand Int)
(declare-const producer Int)
(assert (! (= producer 1) :named producer_value))
(assert (! (=> path0 (= operand producer)) :named edge_value))
(assert (! (or path0 path1) :named fatal_path_prefix))
(assert (! (and path0 (= operand 2)) :named fatal_path))
(check-sat)
"""
        with tempfile.TemporaryDirectory() as directory:
            smt_path, manifest_path = self._write_inputs(directory, smt,
                                                         "path0")
            output = os.path.join(directory, "audit")
            status = AUDIT.main([
                "--smt", smt_path,
                "--manifest", manifest_path,
                "--output-dir", output,
                "--solver-timeout-ms", "5000",
            ])
            self.assertEqual(0, status)
            with open(os.path.join(output, "solver-binding-audit.json"),
                      encoding="utf-8") as handle:
                report = json.load(handle)
            self.assertEqual("AUDITED", report["state"])
            self.assertEqual("BOUND_TO_RECORDED_PRODUCER_VERSIONS",
                             report["operands"][0]["bindingStatus"])

    @unittest.skipUnless(shutil.which("z3"), "z3 is unavailable")
    def test_local_temporary_cannot_bind_to_unrelated_same_sort_version(self):
        smt = """(set-logic ALL)
(declare-const operand Int)
(declare-const producer Int)
(declare-const unrelated_port Int)
(assert (! (= producer 5) :named producer_value))
(assert (! (= unrelated_port producer) :named edge_value))
(assert (! (= operand 5) :named fatal_path_prefix))
(assert (! (= operand 5) :named fatal_path))
(check-sat)
"""
        with tempfile.TemporaryDirectory() as directory:
            smt_path, manifest_path = self._write_inputs(
                directory, smt, "(= operand 5)")
            with open(manifest_path, encoding="utf-8") as handle:
                manifest = json.load(handle)
            operand = manifest["operandBindingLedger"]["operands"][0]
            operand.pop("portId")
            operand.pop("regionInstanceId")
            operand["producerLineageStatus"] = \
                "UNAUDITABLE_NO_EXACT_PRODUCER_LINEAGE"
            operand["producerVersions"] = []
            with open(manifest_path, "w", encoding="utf-8",
                      newline="\n") as handle:
                json.dump(manifest, handle)
                handle.write("\n")

            output = os.path.join(directory, "audit")
            status = AUDIT.main([
                "--smt", smt_path,
                "--manifest", manifest_path,
                "--output-dir", output,
                "--solver-timeout-ms", "5000",
            ])

            self.assertEqual(2, status)
            with open(os.path.join(output, "solver-binding-audit.json"),
                      encoding="utf-8") as handle:
                report = json.load(handle)
            self.assertEqual("INCONCLUSIVE", report["state"])
            audited = report["operands"][0]
            self.assertEqual("UNAUDITABLE_NO_EXACT_PRODUCER_LINEAGE",
                             audited["bindingStatus"])
            self.assertEqual("INCONCLUSIVE",
                             audited["edgeEvidenceStatus"])
            self.assertEqual([], audited["producerVersions"])
            self.assertEqual([], audited["edgeAblations"])

    def test_manifest_rejects_producer_version_for_another_target_occurrence(
            self):
        smt = """(set-logic ALL)
(declare-const operand Int)
(declare-const producer Int)
(assert (! (= operand producer) :named edge_value))
(assert (! true :named fatal_path_prefix))
(assert (! true :named fatal_path))
(check-sat)
"""
        with tempfile.TemporaryDirectory() as directory:
            smt_path, manifest_path = self._write_inputs(directory, smt)
            with open(manifest_path, encoding="utf-8") as handle:
                manifest = json.load(handle)
            version = manifest["operandBindingLedger"]["operands"][0][
                "producerVersions"][0]
            version["targetRegionInstanceId"] = "REGION.OTHER@test#call9"

            with self.assertRaisesRegex(ValueError, "another operand"):
                AUDIT.validate_manifest(
                    manifest, smt_path, AUDIT.named_assertions(smt))

    def test_manifest_rejects_boxed_value_pin_for_exact_int_operand(self):
        smt = """(set-logic ALL)
(declare-datatypes () ((Value (VInt (vint Int)))))
(declare-const operand Int)
(declare-const producer Int)
(assert (! (= operand producer) :named edge_value))
(assert (! true :named fatal_path_prefix))
(assert (! true :named fatal_path))
(check-sat)
"""
        with tempfile.TemporaryDirectory() as directory:
            smt_path, manifest_path = self._write_inputs(directory, smt)
            with open(manifest_path, encoding="utf-8") as handle:
                manifest = json.load(handle)
            operand = manifest["operandBindingLedger"]["operands"][0]
            operand["pinTerm"] = "(VInt operand)"
            operand["pinSort"] = "Value"

            with self.assertRaisesRegex(ValueError, "not solver-native"):
                AUDIT.validate_manifest(
                    manifest, smt_path, AUDIT.named_assertions(smt))

    @unittest.skipUnless(shutil.which("z3"), "z3 is unavailable")
    def test_unsat_operand_path_baseline_is_inconclusive(self):
        smt = """(set-logic ALL)
(declare-const operand Int)
(declare-const producer Int)
(assert (! (= operand producer) :named edge_value))
(assert (! true :named fatal_path_prefix))
(assert (! true :named fatal_path))
(check-sat)
"""
        with tempfile.TemporaryDirectory() as directory:
            smt_path, manifest_path = self._write_inputs(directory, smt,
                                                         "false")
            output = os.path.join(directory, "audit")
            status = AUDIT.main([
                "--smt", smt_path,
                "--manifest", manifest_path,
                "--output-dir", output,
                "--solver-timeout-ms", "5000",
            ])
            self.assertEqual(2, status)
            with open(os.path.join(output, "solver-binding-audit.json"),
                      encoding="utf-8") as handle:
                report = json.load(handle)
            self.assertEqual("INCONCLUSIVE", report["state"])
            self.assertEqual("unsat", report["operands"][0]
                             ["pathRelationBaseline"]["status"])
            self.assertEqual("INCONCLUSIVE_PATH_BASELINE",
                             report["operands"][0]["bindingStatus"])

    @unittest.skipUnless(shutil.which("z3"), "z3 is unavailable")
    def test_empty_operand_ledger_is_a_failing_finding(self):
        smt = """(set-logic ALL)
(assert (! true :named fatal_path_prefix))
(assert (! true :named fatal_path))
(check-sat)
"""
        with tempfile.TemporaryDirectory() as directory:
            smt_path, manifest_path = self._write_inputs(directory, smt)
            with open(manifest_path, encoding="utf-8") as handle:
                manifest = json.load(handle)
            manifest["operandBindingLedger"]["operands"] = []
            manifest["operandBindingLedger"]["paths"][0][
                "operandCount"] = 0
            with open(manifest_path, "w", encoding="utf-8",
                      newline="\n") as handle:
                json.dump(manifest, handle)
                handle.write("\n")
            output = os.path.join(directory, "audit")
            status = AUDIT.main([
                "--smt", smt_path,
                "--manifest", manifest_path,
                "--output-dir", output,
                "--solver-timeout-ms", "5000",
            ])
            self.assertEqual(1, status)
            with open(os.path.join(output, "solver-binding-audit.json"),
                      encoding="utf-8") as handle:
                report = json.load(handle)
            self.assertEqual("AUDITED_WITH_FINDINGS", report["state"])
            self.assertIn("NO_FATAL_OPERANDS_CAPTURED",
                          report["findings"])

    @unittest.skipUnless(shutil.which("z3"), "z3 is unavailable")
    def test_one_empty_path_cannot_hide_behind_an_audited_path(self):
        smt = """(set-logic ALL)
(declare-const operand Int)
(declare-const producer Int)
(assert (! (= producer 1) :named producer_value))
(assert (! (= operand producer) :named edge_value))
(assert (! true :named fatal_path_prefix))
(assert (! (= operand 2) :named fatal_path))
(check-sat)
"""
        with tempfile.TemporaryDirectory() as directory:
            smt_path, manifest_path = self._write_inputs(directory, smt)
            with open(manifest_path, encoding="utf-8") as handle:
                manifest = json.load(handle)
            manifest["operandBindingLedger"]["paths"].append({
                "pathOrdinal": 1,
                "pathPrefixTerm": "true",
                "operandCount": 0,
            })
            with open(manifest_path, "w", encoding="utf-8",
                      newline="\n") as handle:
                json.dump(manifest, handle)
                handle.write("\n")
            output = os.path.join(directory, "audit")
            status = AUDIT.main([
                "--smt", smt_path,
                "--manifest", manifest_path,
                "--output-dir", output,
                "--solver-timeout-ms", "5000",
            ])
            self.assertEqual(1, status)
            with open(os.path.join(output, "solver-binding-audit.json"),
                      encoding="utf-8") as handle:
                report = json.load(handle)
            self.assertEqual("AUDITED_WITH_FINDINGS", report["state"])
            self.assertIn("NO_FATAL_OPERANDS_FOR_PATH:1",
                          report["findings"])

    @unittest.skipUnless(shutil.which("z3"), "z3 is unavailable")
    def test_unsat_final_query_cannot_make_pin_pass_vacuously(self):
        smt = """(set-logic ALL)
(declare-const operand Int)
(declare-const producer Int)
(assert (! (= producer 1) :named producer_value))
(assert (! (= operand producer) :named edge_value))
(assert (! true :named fatal_path_prefix))
(assert (! (= operand 2) :named fatal_path))
(check-sat)
"""
        with tempfile.TemporaryDirectory() as directory:
            smt_path, manifest_path = self._write_inputs(directory, smt)
            output = os.path.join(directory, "audit")
            status = AUDIT.main([
                "--smt", smt_path,
                "--manifest", manifest_path,
                "--output-dir", output,
                "--solver-timeout-ms", "5000",
            ])
            self.assertEqual(0, status)
            with open(os.path.join(output, "solver-binding-audit.json"),
                      encoding="utf-8") as handle:
                report = json.load(handle)
            self.assertEqual("unsat", report["finalQuery"]["status"])
            self.assertEqual("sat",
                             report["relationOnlyBaseline"]["status"])
            self.assertEqual("PASSED", report["vacuityGuard"]["status"])
            operand = report["operands"][0]
            self.assertEqual("BOUND_TO_RECORDED_PRODUCER_VERSIONS",
                             operand["bindingStatus"])
            self.assertEqual("LOAD_BEARING",
                             operand["edgeAblations"][0]["classification"])
            self.assertEqual("LOAD_BEARING_EDGE_FOUND",
                             operand["edgeEvidenceStatus"])

    @unittest.skipUnless(shutil.which("z3"), "z3 is unavailable")
    def test_relation_baseline_removes_every_fatal_dependent_assertion(self):
        smt = """(set-logic ALL)
(declare-const operand Int)
(declare-const producer Int)
(assert (! (= producer 1) :named producer_value))
(assert (! (= operand producer) :named edge_value))
(assert (! true :named fatal_path_prefix))
(assert (! (= operand 2) :named fatal_path))
(assert (! (= operand 2) :named fatal_absence_mutation_witness))
(check-sat)
"""
        with tempfile.TemporaryDirectory() as directory:
            smt_path, manifest_path = self._write_inputs(directory, smt)
            with open(manifest_path, encoding="utf-8") as handle:
                manifest = json.load(handle)
            manifest["operandBindingLedger"][
                "fatalDependentAssertionNames"].append(
                    "fatal_absence_mutation_witness")
            with open(manifest_path, "w", encoding="utf-8",
                      newline="\n") as handle:
                json.dump(manifest, handle)
                handle.write("\n")
            output = os.path.join(directory, "audit")
            status = AUDIT.main([
                "--smt", smt_path,
                "--manifest", manifest_path,
                "--output-dir", output,
                "--solver-timeout-ms", "5000",
            ])
            self.assertEqual(0, status)
            with open(os.path.join(output, "solver-binding-audit.json"),
                      encoding="utf-8") as handle:
                report = json.load(handle)
            self.assertEqual("sat",
                             report["relationOnlyBaseline"]["status"])
            self.assertEqual(2, len(report["vacuityGuard"]
                                    ["removedFatalDependentAssertions"]))

    @unittest.skipUnless(shutil.which("z3"), "z3 is unavailable")
    def test_unsat_relation_baseline_is_non_auditable(self):
        smt = """(set-logic ALL)
(declare-const operand Int)
(declare-const producer Int)
(assert (! false :named relation_false))
(assert (! (= operand producer) :named edge_value))
(assert (! true :named fatal_path_prefix))
(assert (! (= operand 2) :named fatal_path))
(check-sat)
"""
        with tempfile.TemporaryDirectory() as directory:
            smt_path, manifest_path = self._write_inputs(directory, smt)
            output = os.path.join(directory, "audit")
            status = AUDIT.main([
                "--smt", smt_path,
                "--manifest", manifest_path,
                "--output-dir", output,
                "--solver-timeout-ms", "5000",
            ])
            self.assertEqual(2, status)
            with open(os.path.join(output, "solver-binding-audit.json"),
                      encoding="utf-8") as handle:
                report = json.load(handle)
            self.assertEqual("NON_AUDITABLE_RELATION_BASELINE",
                             report["state"])
            self.assertEqual([], report["operands"])

    def _write_inputs(self, directory, smt, path_prefix="true"):
        smt_path = os.path.join(directory, "candidate.smt2")
        manifest_path = os.path.join(directory, "composition.json")
        with open(smt_path, "w", encoding="utf-8", newline="\n") as handle:
            handle.write(smt)
        digest = hashlib.sha256(smt.encode("utf-8")).hexdigest()
        manifest = {
            "schemaVersion": 2,
            "kind": "CONCOLIC_COMPOSED_SMT",
            "state": "CANDIDATE_READY",
            "composedSmtArtifact": {"sha256": digest},
            "operandBindingLedger": {
                "schemaVersion": 2,
                "kind": "FATAL_OPERAND_BINDING_LEDGER",
                "fatalPathAssertion": {
                    "name": "fatal_path",
                    "solverTerm": "(= operand 2)",
                },
                "fatalDependentAssertionNames": ["fatal_path"],
                "retainedPathPrefixAssertion": {
                    "name": "fatal_path_prefix",
                    "solverTerm": "true",
                },
                "paths": [{
                    "pathOrdinal": 0,
                    "pathPrefixTerm": path_prefix,
                    "operandCount": 1,
                }],
                "operands": [{
                    "operandId": "fatal_operand_0_0",
                    "pathOrdinal": 0,
                    "originKind": "SymbolExpression",
                    "solverTerm": "operand",
                    "solverSort": "Int",
                    "pinTerm": "operand",
                    "pinSort": "Int",
                    "portId": "REGION.T.in.operand",
                    "regionInstanceId": "REGION.T@test#call1",
                    "producerLineageStatus":
                        "EXACT_TARGET_PORT_OCCURRENCE",
                    "pathPrefixTerm": path_prefix,
                    "producerVersions": [{
                        "edgeId": "EDGE.1",
                        "solverTerm": "producer",
                        "solverSort": "Int",
                        "assertionName": "edge_value",
                        "guardTerm": "true",
                        "targetPortId": "REGION.T.in.operand",
                        "targetRegionInstanceId":
                            "REGION.T@test#call1",
                    }],
                }],
                "edgeAssertions": [{
                    "edgeId": "EDGE.1",
                    "assertionNames": ["edge_value"],
                }],
            },
        }
        with open(manifest_path, "w", encoding="utf-8",
                  newline="\n") as handle:
            json.dump(manifest, handle)
            handle.write("\n")
        return smt_path, manifest_path


if __name__ == "__main__":
    unittest.main()
