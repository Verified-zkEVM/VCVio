#!/usr/bin/env python3
"""Regression checks for the audit's security and compatibility disclosures."""

import hashlib
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parent.parent


class SecurityDisclosureTests(unittest.TestCase):
    def test_mldsa_query_bounds_are_disclosed_without_statement_changes(self):
        source = (ROOT / "LatticeCrypto/MLDSA/Security.lean").read_text()
        start = source.index("theorem euf_cma_security\n")
        warning = source[source.rfind("/--", 0, start):start]
        self.assertIn("No hypothesis ties the adversary to `qS` or `qH`", warning)
        self.assertIn("placeholder, not the", warning)
        self.assertIn("cited theorem", warning)
        end = source.index("\nend MainTheorem", start)
        self.assertEqual(hashlib.sha256(source[start:end].encode()).hexdigest(),
                         "5728684c0691682d0d0d1b02e1280d22392808e841f19abf216e3d86b2b0f528")


class CompatibilityDisclosureTests(unittest.TestCase):
    def test_removed_runtime_method_is_not_a_live_reference(self):
        spec = importlib.util.spec_from_file_location("docnames", ROOT / "scripts/check-doc-names.py")
        checker = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(checker)
        guide = (ROOT / "docs/agents/probability-migration.md").read_text()
        spans = {span for _, span, _ in checker.guide_spans(guide)}
        self.assertIn("`ProbCompRuntime.prFail`", guide)
        self.assertNotIn("ProbCompRuntime.prFail", spans)
        self.assertIn("runtime.toSemanticsVia.prFail mx", spans)

    def test_lawfulness_ledger_and_responder_restrictions(self):
        guide = (ROOT / "docs/agents/probability-migration.md").read_text()
        section = guide.split("## Generic lawfulness and executable responders\n", 1)[1]
        section = section.split("\n## ", 1)[0]
        for name in (
            "LawfulMonad", "LawfulEvalDistSemantics", "EvalDistEq", "EvalDistEq.prEvent_eq",
            "EvalDistEq.of_forall_prEvent_eq", "EvalDistEq.refl", "EvalDistEq.rfl",
            "EvalDistEq.symm", "EvalDistEq.trans", "EvalDistEq.map", "EvalDistEq.map_congr",
            "prEvent_eq_evalDist_map", "evalDist_singleton_true", "prEvent_le_one",
            "prEvent_ne_top", "prEvent_lt_top", "prEvent_const_of_lossless",
            "prEvent_true_attach", "prEvent_true_add_prFail", "prFail_add_prEvent_true",
            "prFail_eq_zero_iff", "prFail_eq_one_iff", "SymmEncAlg.Complete",
            "SymmEncAlg.ciphertextRowsEqualAt", "OracleComp.expectedSimulatedQueryCount",
            "OracleComp.expectedSimulatedQueryCount_pure",
            "OracleComp.expectedSimulatedQueryCount_query_bind", "AddWriterT.prEvent_costs",
            "FiatShamirWithAbort.signAttemptAbortProbability_eq_prEvent",
            "instMeasurableSingletonClassState", "instMeasurableSingletonClassRange",
            "ProbResponder.pullback.measurableSingletonClass_range_of_injective",
            "ProbResponder.pullback.measurableSingletonClass_range_of_forall_injective",
            "runtime.toSemanticsVia.prFail mx", "prEvent_coord_eq_mul_of_forall",
            "MeasurableSingletonClass",
        ):
            self.assertIn(f"`{name}`", section)
        self.assertNotIn("`MeasureDistEquiv.of_step`", guide)
        roadmap = (ROOT / "docs/design/measure-conversion-roadmap.md").read_text()
        self.assertNotIn("MeasureDistEquiv", roadmap)
        self.assertIn("`DistEquiv`: equal event probabilities", roadmap)


if __name__ == "__main__":
    unittest.main()
