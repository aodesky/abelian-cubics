"""Regression checks for shared helpers and hidden dependency paths."""

import unittest
from blueprint_dependencies import project_graph, validate_graph


class DependencyGraphTests(unittest.TestCase):
    def test_shared_helper_does_not_create_theorem_to_theorem_edge(self):
        records = {n: {'deps': ds} for n, ds in
                   {'A': ['hidden'], 'B': ['H'], 'hidden': ['H'], 'H': []}.items()}
        graph, _ = project_graph(records, {'a': 'A', 'b': 'B'})
        self.assertEqual(graph, {'a': [], 'b': []})
        graph, paths = project_graph(records, {'a': 'A', 'b': 'B', 'h': 'H'})
        self.assertEqual(graph, {'a': ['h'], 'b': ['h'], 'h': []})
        self.assertEqual(paths['a']['h'], ['A', 'hidden', 'H'])

    def test_traversal_stops_at_displayed_result(self):
        records = {n: {'deps': ds} for n, ds in
                   {'A': ['hidden'], 'hidden': ['B'], 'B': ['C'], 'C': []}.items()}
        graph, _ = project_graph(records, {'a': 'A', 'b': 'B', 'c': 'C'})
        self.assertEqual(graph, {'a': ['b'], 'b': ['c'], 'c': []})

    def test_missing_declaration_and_cycle_fail(self):
        with self.assertRaisesRegex(ValueError, 'Missing declaration'):
            project_graph({'A': {'deps': ['missing']}}, {'a': 'A'})
        with self.assertRaisesRegex(ValueError, 'Cycle'):
            validate_graph({'a': ['b'], 'b': ['a']})


if __name__ == '__main__':
    unittest.main()
