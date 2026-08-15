#!/usr/bin/env python3

import importlib.util
import os
import shutil
import tempfile
import unittest


HERE = os.path.dirname(os.path.abspath(__file__))
SPEC = importlib.util.spec_from_file_location(
    "branch_relation_report", os.path.join(HERE, "branch_relation_report.py"))
REPORT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(REPORT)


def query(final_assertion=""):
    clock = "environment__currentTimeMills_5__abc"
    compare0 = "(ite (< expiry0 {0}) (- 1) " \
               "(ite (> expiry0 {0}) 1 0))".format(clock)
    compare1 = "(ite (< expiry1 {0}) (- 1) " \
               "(ite (> expiry1 {0}) 1 0))".format(clock)
    return """(set-option :produce-models true)
(set-logic ALL)
(declare-const expiry0 Int)
(declare-const expiry1 Int)
(declare-const {clock} Int)
(assert (! (>= {compare0} 0) :named pc_1))
(assert (! (< {compare1} 0) :named pc_2))
{final_assertion}
(check-sat)
(get-value (expiry0))
""".format(clock=clock, compare0=compare0, compare1=compare1,
           final_assertion=final_assertion)


class BranchRelationReportTest(unittest.TestCase):
    def test_decodes_prefix_and_flipped_expiry_relation(self):
        relations = REPORT.discover_relations(query())
        self.assertEqual(2, len(relations))
        self.assertEqual(">=", relations[0]["operator"])
        self.assertEqual("prefix", relations[0]["role"])
        self.assertEqual("<", relations[1]["operator"])
        self.assertEqual("flipped_target", relations[1]["role"])

    @unittest.skipUnless(shutil.which("z3"), "z3 is unavailable")
    def test_sat_report_contains_concrete_flipped_relation(self):
        with tempfile.TemporaryDirectory() as directory:
            path = os.path.join(directory, "path_flip_query.smt2")
            with open(path, "w", encoding="utf-8", newline="\n") as handle:
                handle.write(query())
            report = REPORT.analyze(path, shutil.which("z3"), 5000)
        self.assertEqual("sat", report["status"])
        target = report["branchRelations"][-1]
        self.assertEqual("expiry < T_recv", target["relation"])
        self.assertTrue(target["evaluatesTo"])
        self.assertIn("expiry < T_recv", REPORT.render_text(report))

    @unittest.skipUnless(shutil.which("z3"), "z3 is unavailable")
    def test_unsat_is_reported_without_model_values(self):
        with tempfile.TemporaryDirectory() as directory:
            path = os.path.join(directory, "path_flip_query.smt2")
            with open(path, "w", encoding="utf-8", newline="\n") as handle:
                handle.write(query("(assert false)"))
            report = REPORT.analyze(path, shutil.which("z3"), 5000)
        self.assertEqual("unsat", report["status"])
        self.assertNotIn("expiryValue", report["branchRelations"][-1])

    def test_unrelated_clock_domain_is_not_a_branch(self):
        smt = """(set-logic ALL)
(declare-const environment__dn__currentTimeMills_1__x Int)
(assert (<= environment__dn__currentTimeMills_1__x 10))
(check-sat)
"""
        self.assertEqual([], REPORT.discover_relations(smt))


if __name__ == "__main__":
    unittest.main()
