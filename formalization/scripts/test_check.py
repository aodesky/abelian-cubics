"""Prevent statement scaffolding from being promoted to proof coverage."""

import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from check import (cited_black_box_checks, proof_file_checks, supporting_declaration_checks,
                   target_checks)


class TargetAuditTests(unittest.TestCase):
    def schema(self):
        return {"status": "planned", "declarations": [], "target": {
            "kind": "schema", "declaration": "CubicTargets.Claim",
            "context": "CubicTargets.Data", "proof": None}}

    def test_unproved_schema_is_type_checked(self):
        errors, checks = target_checks("lemma:a", self.schema())
        self.assertEqual(errors, [])
        self.assertEqual(checks, ["example : CubicTargets.Data → Prop := CubicTargets.Claim"])

    def test_schema_cannot_be_marked_proved(self):
        entry = self.schema()
        entry.update(status="proved", declarations=["Cubic.helper"])
        errors, _ = target_checks("lemma:a", entry)
        self.assertTrue(any("cannot certify" in e for e in errors))

    def test_schema_proof_cannot_bypass_the_rule(self):
        entry = self.schema()
        entry["target"]["proof"] = "Cubic.helper"
        errors, _ = target_checks("lemma:a", entry)
        self.assertTrue(any("cannot certify" in e for e in errors))

    def test_conditional_proof_keeps_prerequisite_in_checked_type(self):
        entry = self.schema()
        entry.update(status="supporting", declarations=["Cubic.conditional"])
        entry["target"].update(prerequisite="CubicTargets.LocalCalculation",
                               conditional_proof="Cubic.conditional")
        errors, checks = target_checks("lemma:a", entry)
        self.assertEqual(errors, [])
        self.assertIn("example : ∀ D : CubicTargets.Data, CubicTargets.LocalCalculation D → "
                      "CubicTargets.Claim D := @Cubic.conditional", checks)
        entry["status"] = "proved"
        errors, _ = target_checks("lemma:a", entry)
        self.assertTrue(any("cannot certify" in e for e in errors))

    def test_conditional_proof_requires_named_prerequisite(self):
        entry = self.schema()
        entry["target"]["conditional_proof"] = "Cubic.conditional"
        errors, _ = target_checks("lemma:a", entry)
        self.assertTrue(any("must name their prerequisite" in e for e in errors))

    def test_proved_result_requires_a_target(self):
        errors, _ = target_checks("lemma:a", {"status": "proved", "declarations": ["Cubic.x"]})
        self.assertTrue(any("must have a concrete target" in e for e in errors))

    def test_concrete_target_requires_a_proof_when_marked_proved(self):
        entry = {"status": "proved", "declarations": ["Cubic.helper"],
                 "target": {"kind": "concrete", "declaration": "CubicTargets.Statement"}}
        errors, _ = target_checks("lemma:a", entry)
        self.assertTrue(any("Missing proof" in e for e in errors))

    def black_box(self):
        return {"status": "planned", "declarations": [], "target": {
            "kind": "black_box", "declaration": "CubicTargets.BlackBox", "proof": None}}

    def test_black_box_is_type_checked_without_becoming_a_proof(self):
        errors, checks = target_checks("eqn:poissonae", self.black_box())
        self.assertEqual(errors, [])
        self.assertEqual(checks, ["example : Prop := CubicTargets.BlackBox"])

    def test_black_box_cannot_be_marked_proved_or_have_a_proof(self):
        for update in ({"status": "proved"}, {"proof": "Cubic.helper"}):
            with self.subTest(update=update):
                entry = self.black_box()
                if "status" in update:
                    entry.update(update)
                else:
                    entry["target"].update(update)
                errors, _ = target_checks("eqn:poissonae", entry)
                self.assertTrue(any("cannot certify" in e for e in errors))

    def test_black_box_cannot_hide_setup_or_a_conditional_proof(self):
        for field in ("context", "prerequisite", "conditional_proof"):
            with self.subTest(field=field):
                entry = self.black_box()
                entry["target"][field] = "CubicTargets.Hidden"
                errors, _ = target_checks("eqn:poissonae", entry)
                self.assertTrue(any("bind their full setup" in e for e in errors))

    def test_concrete_proof_is_checked_against_the_target(self):
        entry = {"status": "proved", "declarations": ["Cubic.proof"], "target": {
            "kind": "concrete", "declaration": "CubicTargets.Statement", "proof": "Cubic.proof"}}
        errors, checks = target_checks("lemma:a", entry)
        self.assertEqual(errors, [])
        self.assertIn("example : CubicTargets.Statement := Cubic.proof", checks)

    def relative_proof(self):
        return {"status": "proved", "declarations": ["Cubic.proof"], "target": {
            "kind": "concrete", "declaration": "CubicTargets.Statement", "proof": "Cubic.proof",
            "black_box_assumptions": ["eqn:poissonae"]}}

    def authorized_inputs(self):
        entry = self.black_box()
        entry["target"]["authorized_by_user"] = "User explicitly permitted the general input."
        return {"eqn:poissonae": entry}

    def test_authorized_black_box_remains_in_exact_checked_proof_type(self):
        errors, checks = target_checks("lemma:a", self.relative_proof(), self.authorized_inputs())
        self.assertEqual(errors, [])
        self.assertIn("example : CubicTargets.BlackBox → CubicTargets.Statement := Cubic.proof", checks)

    def test_arbitrary_unproved_statement_cannot_be_an_authorized_input(self):
        for sources in ({}, {"eqn:poissonae": self.schema()},
                        {"eqn:poissonae": self.black_box()},
                        {"eqn:poissonae": self.relative_proof()}):
            with self.subTest(sources=sources):
                errors, _ = target_checks("lemma:a", self.relative_proof(), sources)
                self.assertTrue(any("unauthorized" in e for e in errors))

    def test_relative_proof_still_requires_a_completed_proof(self):
        entry = self.relative_proof()
        entry["target"]["proof"] = None
        errors, _ = target_checks("lemma:a", entry, self.authorized_inputs())
        self.assertTrue(any("Missing proof" in e for e in errors))

    def test_malformed_or_duplicate_assumptions_are_rejected(self):
        for assumptions in ("eqn:poissonae", [None], ["eqn:poissonae", "eqn:poissonae"]):
            with self.subTest(assumptions=assumptions):
                entry = self.relative_proof()
                entry["target"]["black_box_assumptions"] = assumptions
                errors, _ = target_checks("lemma:a", entry, self.authorized_inputs())
                self.assertTrue(errors)

    def test_schemas_and_black_boxes_cannot_use_relative_proof_metadata(self):
        for entry in (self.schema(), self.black_box()):
            entry["target"]["black_box_assumptions"] = ["eqn:poissonae"]
            errors, _ = target_checks("lemma:a", entry, self.authorized_inputs())
            self.assertTrue(any("Only concrete" in e for e in errors))


class ProofFileAuditTests(unittest.TestCase):
    def entry(self, filename="Cubic/Proof.lean"):
        return {"status": "proved", "declarations": ["Cubic.proof"], "proof_file": filename}

    def test_completed_result_requires_a_proof_file(self):
        errors, _ = proof_file_checks({"lemma:a": self.entry(None)}, Path("."))
        self.assertTrue(any("Missing or invalid" in e for e in errors))

    def test_missing_file_is_rejected(self):
        with TemporaryDirectory() as tmp:
            errors, _ = proof_file_checks({"lemma:a": self.entry()}, Path(tmp))
        self.assertTrue(any("does not exist" in e for e in errors))

    def test_proof_files_must_be_project_modules(self):
        for filename in ("../Proof.lean", "/tmp/Proof.lean", "Mathlib/Proof.lean", "Cubic/Proof.md"):
            with self.subTest(filename=filename):
                errors, _ = proof_file_checks({"lemma:a": self.entry(filename)}, Path("."))
                self.assertTrue(any("Missing or invalid" in e for e in errors))

    def test_two_completed_results_cannot_share_a_file(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "Cubic").mkdir()
            (root / "Cubic/Proof.lean").touch()
            errors, _ = proof_file_checks(
                {"lemma:a": self.entry(), "lemma:b": self.entry()}, root)
        self.assertTrue(any("share a proof file" in e for e in errors))

    def test_mapping_checks_defining_module_not_just_an_import(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "Cubic").mkdir()
            (root / "Cubic/Proof.lean").touch()
            errors, checks = proof_file_checks({"lemma:a": self.entry()}, root)
        self.assertEqual(errors, [])
        self.assertIn("env.getModuleIdxFor? ``Cubic.proof", checks[0])
        self.assertIn("env.getModuleIdx? `Cubic.Proof", checks[0])

    def test_supporting_result_does_not_require_a_dedicated_file(self):
        entry = {"status": "supporting", "declarations": ["Cubic.helper"]}
        self.assertEqual(proof_file_checks({"lemma:a": entry}, Path(".")), ([], []))




class CitedBlackBoxTests(unittest.TestCase):
    def cited(self):
        return {"cite:source-thm": {
            "source": "Author, Journal (2021), Theorem 1.5",
            "statement": "Quoted statement.",
            "target": {"kind": "black_box", "declaration": "CubicTargets.Cited.BlackBox",
                       "authorized_by_user": "User authorized this exact statement."}}}

    def relative_proof(self):
        return {"status": "proved", "declarations": ["Cubic.proof"], "target": {
            "kind": "concrete", "declaration": "CubicTargets.Statement",
            "proof": "Cubic.proof", "black_box_assumptions": ["cite:source-thm"]}}

    def test_authorized_cited_black_box_is_type_checked(self):
        errors, checks = cited_black_box_checks(self.cited())
        self.assertEqual(errors, [])
        self.assertIn("example : Prop := CubicTargets.Cited.BlackBox", checks)

    def test_cited_black_box_stays_in_the_checked_proof_type(self):
        errors, checks = target_checks("lemma:a", self.relative_proof(), self.cited())
        self.assertEqual(errors, [])
        self.assertIn(
            "example : CubicTargets.Cited.BlackBox → CubicTargets.Statement := Cubic.proof", checks)

    def test_unauthorized_or_unquoted_cited_black_box_is_rejected(self):
        for field in ("authorized_by_user", "statement", "source"):
            with self.subTest(field=field):
                cited = self.cited()
                entry = cited["cite:source-thm"]
                (entry["target"] if field == "authorized_by_user" else entry).pop(field)
                errors, _ = cited_black_box_checks(cited)
                self.assertTrue(errors)

    def test_cited_black_box_cannot_be_a_proof_or_misnamed(self):
        for change in ("proof", "status", "key"):
            with self.subTest(change=change):
                cited = self.cited()
                entry = cited["cite:source-thm"]
                if change == "proof":
                    entry["target"]["proof"] = "Cubic.proof"
                elif change == "status":
                    entry["status"] = "proved"
                else:
                    cited = {"lemma:source": entry}
                errors, _ = cited_black_box_checks(cited)
                self.assertTrue(errors)


class SupportingDeclarationTests(unittest.TestCase):
    def entry(self, names):
        return {"status": "proved", "declarations": ["Cubic.proof"],
                "supporting_declarations": names}

    def test_valid_supporting_list_passes(self):
        self.assertEqual(supporting_declaration_checks("lemma:a", self.entry(["Cubic.Other.lemma"])), [])

    def test_absent_list_passes(self):
        self.assertEqual(supporting_declaration_checks("lemma:a", {"declarations": []}), [])

    def test_malformed_duplicate_or_overlapping_lists_are_rejected(self):
        for names in ("Cubic.x", ["Mathlib.x"], [None], ["Cubic.x", "Cubic.x"], ["Cubic.proof"]):
            with self.subTest(names=names):
                self.assertTrue(supporting_declaration_checks("lemma:a", self.entry(names)))

    def test_supporting_names_are_not_proof_file_mappings(self):
        with TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Cubic").mkdir()
            (root / "Cubic" / "Proof.lean").write_text("")
            entry = {"status": "proved", "declarations": ["Cubic.proof"],
                     "proof_file": "Cubic/Proof.lean",
                     "supporting_declarations": ["Cubic.Elsewhere.lemma"]}
            _, checks = proof_file_checks({"lemma:a": entry}, root)
            self.assertFalse(any("Cubic.Elsewhere.lemma" in c for c in checks))


if __name__ == "__main__":
    unittest.main()
