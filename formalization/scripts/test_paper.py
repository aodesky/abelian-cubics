"""Regression checks for manuscript synchronization, not mathematical proofs."""

import unittest

from paper import statements, strip_comments


class PaperTests(unittest.TestCase):
    def test_comment_labels_are_ignored(self):
        text = r"% \label{lemma:old}" + "\n" + r"\begin{lemma}\label{lemma:a} A.\end{lemma}"
        self.assertEqual(list(statements(text)), ["lemma:a"])

    def test_escaped_percent_and_even_backslashes(self):
        self.assertEqual(strip_comments("a\\%b%hidden\n"), "a\\%b\n")
        self.assertEqual(strip_comments("a\\\\%hidden\n"), "a\\\\\n")

    def test_duplicate_active_labels_fail(self):
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            statements(r"\begin{lemma}\label{x}\label{x}\end{lemma}")

    def test_nested_equation_uses_its_own_statement(self):
        text = (r"\begin{lemma}[Title]\label{lemma:a} A. "
                r"\begin{equation}\label{eqn:a} x=1\end{equation}\end{lemma}")
        result = statements(text)
        self.assertEqual(result["lemma:a"].kind, "lemma")
        self.assertEqual(result["eqn:a"].kind, "equation")
        self.assertNotIn("Title", result["eqn:a"].text)

    def test_whitespace_and_comments_do_not_cause_drift(self):
        a = r"\begin{lemma}\label{lemma:a} A = B.\end{lemma}"
        b = a.replace(" A = B.", "\n A % note\n = B.")
        self.assertEqual(statements(a)["lemma:a"].text, statements(b)["lemma:a"].text)

    def test_statement_changes_are_detectable(self):
        a = r"\begin{lemma}\label{lemma:a} A = B.\end{lemma}"
        b = a.replace("A = B", "A = C")
        self.assertNotEqual(statements(a)["lemma:a"].text, statements(b)["lemma:a"].text)

    def test_unknown_mathematical_environment_fails(self):
        with self.assertRaisesRegex(ValueError, "Unrecognized"):
            statements(r"\begin{newtheorem}\label{lemma:a}\end{newtheorem}")

    def test_appendix_section_labels_are_structural(self):
        text = (r"\section{Geometry}\label{app:geometry}" "\n"
                r"\subsection{Boundary}" "\n" r"\label{app:boundary}" "\n"
                r"\begin{proposition}\label{prop:a} A.\end{proposition}")
        self.assertEqual(list(statements(text)), ["prop:a"])

    def test_appendix_prefix_does_not_hide_unknown_mathematics(self):
        with self.assertRaisesRegex(ValueError, "Unrecognized"):
            statements(r"\begin{newtheorem}\label{app:claim}\end{newtheorem}")

    def test_labelled_remark_and_nested_equation_are_inventoried(self):
        text = (r"\begin{rem}\label{rem:a} A. "
                r"\begin{equation}\label{eqn:a} x=1\end{equation}\end{rem}")
        result = statements(text)
        self.assertEqual(result["rem:a"].kind, "rem")
        self.assertEqual(result["eqn:a"].kind, "equation")

    def test_unlabelled_remark_is_allowed(self):
        self.assertEqual(statements(r"\begin{rem} A.\end{rem}"), {})

    def test_unlabelled_theorem_is_not_hidden_by_equation_label(self):
        with self.assertRaisesRegex(ValueError, "Unlabelled theorem"):
            statements(r"\begin{theorem}\begin{equation}\label{eqn:a}"
                       r"x=1\end{equation}\end{theorem}")


if __name__ == "__main__":
    unittest.main()
