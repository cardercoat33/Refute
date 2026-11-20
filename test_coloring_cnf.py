#!/usr/bin/env python3
"""Tests for the k-edge-coloring CNF encoder and toy DPLL solver."""

from __future__ import annotations

import io
import itertools
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from coloring_cnf import (
    CNF,
    brute_force_edge_coloring,
    coloring_from_model,
    encode_edge_coloring,
    is_valid_edge_coloring,
    parse_edges,
    petersen_graph,
    run,
    solve_sat,
    to_dimacs,
    triangle_graph,
    Graph,
)

ROOT = Path(__file__).resolve().parent
SCRIPT = ROOT / "coloring_cnf.py"


def all_simple_graphs(n: int):
    possible = list(itertools.combinations(range(n), 2))
    for bits in range(1 << len(possible)):
        edges = [possible[i] for i in range(len(possible)) if bits & (1 << i)]
        yield Graph.from_undirected(range(n), edges)


class TestKnownInstances(unittest.TestCase):
    def test_triangle_two_colors_unsat(self):
        graph = triangle_graph()
        cnf = encode_edge_coloring(graph, 2)
        self.assertIsNone(solve_sat(cnf))
        self.assertIsNone(brute_force_edge_coloring(graph, 2))

    def test_triangle_three_colors_sat_assignment_valid(self):
        graph = triangle_graph()
        cnf = encode_edge_coloring(graph, 3)
        model = solve_sat(cnf)
        self.assertIsNotNone(model)
        coloring = coloring_from_model(graph, 3, model)
        self.assertTrue(is_valid_edge_coloring(graph, coloring))
        self.assertEqual(set(coloring.values()), {0, 1, 2})
        brute = brute_force_edge_coloring(graph, 3)
        self.assertIsNotNone(brute)
        self.assertTrue(is_valid_edge_coloring(graph, brute))

    def test_petersen_three_colors_unsat(self):
        graph = petersen_graph()
        self.assertEqual(len(graph.vertices), 10)
        self.assertEqual(len(graph.edges), 15)
        # Cubic: every vertex has degree 3.
        deg = {v: 0 for v in graph.vertices}
        for u, v in graph.edges:
            deg[u] += 1
            deg[v] += 1
        self.assertEqual(set(deg.values()), {3})
        cnf = encode_edge_coloring(graph, 3)
        self.assertIsNone(solve_sat(cnf))
        self.assertIsNone(brute_force_edge_coloring(graph, 3))

    def test_petersen_four_colors_sat_assignment_valid(self):
        graph = petersen_graph()
        cnf = encode_edge_coloring(graph, 4)
        model = solve_sat(cnf)
        self.assertIsNotNone(model)
        coloring = coloring_from_model(graph, 4, model)
        self.assertTrue(is_valid_edge_coloring(graph, coloring))
        self.assertLessEqual(max(coloring.values()), 3)
        self.assertGreaterEqual(min(coloring.values()), 0)
        brute = brute_force_edge_coloring(graph, 4)
        self.assertIsNotNone(brute)
        self.assertTrue(is_valid_edge_coloring(graph, brute))


class TestEncodingVsBruteForce(unittest.TestCase):
    def test_all_graphs_on_at_most_five_vertices(self):
        checked = 0
        for n in range(1, 6):
            for graph in all_simple_graphs(n):
                for k in (1, 2, 3):
                    brute = brute_force_edge_coloring(graph, k)
                    model = solve_sat(encode_edge_coloring(graph, k))
                    if brute is None:
                        self.assertIsNone(
                            model,
                            f"DPLL SAT but brute UNSAT: n={n} k={k} edges={graph.edges}",
                        )
                    else:
                        self.assertIsNotNone(
                            model,
                            f"DPLL UNSAT but brute SAT: n={n} k={k} edges={graph.edges}",
                        )
                        self.assertTrue(is_valid_edge_coloring(graph, brute))
                        coloring = coloring_from_model(graph, k, model)
                        self.assertTrue(is_valid_edge_coloring(graph, coloring))
                    checked += 1
        # 2^0+2^1+2^3+2^6+2^10 = 1+2+8+64+1024 = 1099 graphs, times 3 values of k.
        self.assertEqual(checked, 1099 * 3)


class TestDimacsAndValidation(unittest.TestCase):
    def test_dimacs_header_matches_formula(self):
        cnf = encode_edge_coloring(triangle_graph(), 3)
        text = to_dimacs(cnf)
        header = [line for line in text.splitlines() if line.startswith("p cnf ")]
        self.assertEqual(len(header), 1)
        _, _, nvars, nclauses = header[0].split()
        self.assertEqual(int(nvars), cnf.nvars)
        self.assertEqual(int(nclauses), len(cnf.clauses))
        body = [line for line in text.splitlines() if line and not line.startswith(("c", "p"))]
        self.assertEqual(len(body), len(cnf.clauses))
        for line in body:
            self.assertTrue(line.endswith(" 0"))

    def test_empty_graph_is_sat_for_any_k(self):
        graph = Graph.from_undirected(range(3), [])
        for k in (1, 2, 3):
            model = solve_sat(encode_edge_coloring(graph, k))
            self.assertIsNotNone(model)
            coloring = coloring_from_model(graph, k, model)
            self.assertEqual(coloring, {})
            self.assertTrue(is_valid_edge_coloring(graph, coloring))

    def test_single_edge_one_color_sat(self):
        graph = Graph.from_undirected(range(2), [(0, 1)])
        model = solve_sat(encode_edge_coloring(graph, 1))
        self.assertIsNotNone(model)
        coloring = coloring_from_model(graph, 1, model)
        self.assertTrue(is_valid_edge_coloring(graph, coloring))
        self.assertEqual(coloring[(0, 1)], 0)

    def test_parse_edges_and_reject_loops(self):
        graph = parse_edges("0-1,1-2,2-0")
        self.assertEqual(graph, triangle_graph())
        with self.assertRaises(ValueError):
            parse_edges("0-0")
        with self.assertRaises(ValueError):
            parse_edges("0-1,")
        with self.assertRaises(ValueError):
            parse_edges("")
        with self.assertRaises(ValueError):
            Graph.from_undirected(range(1), [(0, 0)])

    def test_colors_must_be_positive(self):
        with self.assertRaises(ValueError):
            encode_edge_coloring(triangle_graph(), 0)
        with self.assertRaises(ValueError):
            encode_edge_coloring(triangle_graph(), -1)
        with self.assertRaises(ValueError):
            brute_force_edge_coloring(triangle_graph(), 0)

    def test_cnf_rejects_out_of_range_literals(self):
        with self.assertRaises(ValueError):
            CNF(nvars=1, clauses=((2,),))
        with self.assertRaises(ValueError):
            CNF(nvars=1, clauses=((0,),))

    def test_invalid_coloring_is_rejected(self):
        graph = triangle_graph()
        self.assertFalse(is_valid_edge_coloring(graph, {}))
        monochrome = {e: 0 for e in graph.edges}
        self.assertFalse(is_valid_edge_coloring(graph, monochrome))


class TestCLI(unittest.TestCase):
    def _run(self, *args: str):
        return subprocess.run(
            [sys.executable, str(SCRIPT), *args],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

    def test_help(self):
        result = self._run("--help")
        self.assertEqual(result.returncode, 0)
        self.assertIn("edge-coloring", result.stdout)
        self.assertIn("not CaDiCaL", result.stdout)
        self.assertIn("--example", result.stdout)
        self.assertIn("petersen", result.stdout)

    def test_cli_triangle_unsat_and_sat(self):
        unsat = self._run("--example", "triangle", "--colors", "2")
        self.assertEqual(unsat.returncode, 0)
        self.assertIn("result=UNSAT", unsat.stdout)
        sat = self._run("--example", "triangle", "--colors", "3")
        self.assertEqual(sat.returncode, 0)
        self.assertIn("result=SAT", sat.stdout)
        self.assertIn("coloring:", sat.stdout)

    def test_cli_petersen_unsat_and_sat(self):
        unsat = self._run("--example", "petersen", "--colors", "3")
        self.assertEqual(unsat.returncode, 0)
        self.assertIn("result=UNSAT", unsat.stdout)
        sat = self._run("--example", "petersen", "--colors", "4")
        self.assertEqual(sat.returncode, 0)
        self.assertIn("result=SAT", sat.stdout)

    def test_cli_encode_only_and_custom_edges(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "triangle-2.cnf"
            result = self._run(
                "--edges",
                "0-1,1-2,2-0",
                "--colors",
                "2",
                "--encode-only",
                "--out",
                str(path),
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            text = path.read_text(encoding="utf-8")
            self.assertTrue(text.startswith("c "))
            self.assertIn("p cnf ", text)

        dumped = self._run("--example", "triangle", "--colors", "2", "--dump-cnf")
        self.assertEqual(dumped.returncode, 0)
        self.assertIn("p cnf ", dumped.stdout)
        self.assertNotIn("result=", dumped.stdout)

    def test_cli_rejects_bad_input(self):
        missing = self._run("--colors", "3")
        self.assertNotEqual(missing.returncode, 0)
        zero = self._run("--example", "triangle", "--colors", "0")
        self.assertNotEqual(zero.returncode, 0)
        loop = self._run("--edges", "1-1", "--colors", "2")
        self.assertNotEqual(loop.returncode, 0)
        encode_only = self._run("--example", "triangle", "--colors", "3", "--encode-only")
        self.assertNotEqual(encode_only.returncode, 0)

    def test_run_helper_is_deterministic(self):
        first = io.StringIO()
        second = io.StringIO()
        self.assertEqual(run(["--example", "triangle", "--colors", "3"], out=first), 0)
        self.assertEqual(run(["--example", "triangle", "--colors", "3"], out=second), 0)
        self.assertEqual(first.getvalue(), second.getvalue())
        self.assertIn("result=SAT", first.getvalue())


if __name__ == "__main__":
    unittest.main()
