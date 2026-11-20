#!/usr/bin/env python3
"""Encode k-edge-coloring of a simple undirected graph as DIMACS CNF.

This is a small, real encoder plus a toy DPLL SAT solver for tiny instances.
It is not a proof-producing pipeline, not CaDiCaL, and not the proposed Refute DSL.

Edge-coloring (chromatic index) is not the same as vertex-coloring (chromatic
number). The Petersen graph is 3-vertex-colorable but not 3-edge-colorable.
"""

from __future__ import annotations

import argparse
import itertools
import sys
from dataclasses import dataclass
from typing import Iterable, Mapping, Optional, Sequence, TextIO

Lit = int
Clause = tuple[Lit, ...]
Coloring = dict[tuple[int, int], int]


@dataclass(frozen=True)
class Graph:
    """Simple undirected graph with integer vertices and no loops or parallels."""

    vertices: tuple[int, ...]
    edges: tuple[tuple[int, int], ...]  # each edge is (u, v) with u < v

    @staticmethod
    def from_undirected(
        vertices: Iterable[int], edges: Iterable[Iterable[int]]
    ) -> "Graph":
        seen: set[int] = set()
        verts: list[int] = []
        for v in vertices:
            _require_int_vertex(v)
            if v not in seen:
                seen.add(v)
                verts.append(v)
        edge_set: set[tuple[int, int]] = set()
        for raw in edges:
            e = tuple(raw)
            if len(e) != 2:
                raise ValueError(f"each edge must have two endpoints, got {e!r}")
            u, v = e
            _require_int_vertex(u)
            _require_int_vertex(v)
            if u == v:
                raise ValueError(f"loops are not allowed: {u}")
            a, b = (u, v) if u < v else (v, u)
            edge_set.add((a, b))
        for a, b in edge_set:
            for x in (a, b):
                if x not in seen:
                    seen.add(x)
                    verts.append(x)
        return Graph(tuple(sorted(verts)), tuple(sorted(edge_set)))

    def adjacent_edge_pairs(self) -> tuple[tuple[int, int], ...]:
        """Pairs of edge indices that share a vertex, each pair i < j."""
        incident: dict[int, list[int]] = {v: [] for v in self.vertices}
        for i, (u, v) in enumerate(self.edges):
            incident[u].append(i)
            incident[v].append(i)
        pairs: set[tuple[int, int]] = set()
        for idxs in incident.values():
            for a, b in itertools.combinations(idxs, 2):
                pairs.add((a, b) if a < b else (b, a))
        return tuple(sorted(pairs))


@dataclass(frozen=True)
class CNF:
    nvars: int
    clauses: tuple[Clause, ...]
    comments: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if self.nvars < 0:
            raise ValueError("nvars must be >= 0")
        for clause in self.clauses:
            for lit in clause:
                if lit == 0 or abs(lit) > self.nvars:
                    raise ValueError(f"literal {lit} is outside 1..{self.nvars}")


def _require_int_vertex(v: object) -> None:
    if isinstance(v, bool) or not isinstance(v, int):
        raise ValueError(f"vertices must be integers, got {v!r}")


def _require_colors(k: int) -> int:
    if isinstance(k, bool) or not isinstance(k, int) or k < 1:
        raise ValueError(f"colors must be an integer >= 1, got {k!r}")
    return k


def triangle_graph() -> Graph:
    return Graph.from_undirected(range(3), [(0, 1), (1, 2), (2, 0)])


def petersen_graph() -> Graph:
    """The Petersen graph, via 2-subsets of {0,1,2,3,4} adjacent when disjoint."""
    subsets = list(itertools.combinations(range(5), 2))
    index = {s: i for i, s in enumerate(subsets)}
    edges = [
        (index[a], index[b])
        for a, b in itertools.combinations(subsets, 2)
        if set(a).isdisjoint(b)
    ]
    return Graph.from_undirected(range(len(subsets)), edges)


def _var(edge_index: int, color: int, k: int) -> int:
    return edge_index * k + color + 1


def encode_edge_coloring(graph: Graph, k: int) -> CNF:
    """CNF that is SAT iff the graph is k-edge-colorable.

    Variable _var(i, c, k) is true iff edge i receives color c in 0..k-1.
    Each edge gets exactly one color; edges that share a vertex get different
    colors.
    """
    k = _require_colors(k)
    nvars = len(graph.edges) * k
    comments = [
        "k-edge-coloring CNF (not vertex-coloring)",
        f"vertices={len(graph.vertices)} edges={len(graph.edges)} colors={k}",
        "variable e*k+c+1 means edge index e (0-based, sorted) has color c",
    ]
    for i, (u, v) in enumerate(graph.edges):
        comments.append(f"edge {i}: {u}-{v}")

    clauses: list[Clause] = []

    def add(lits: Iterable[int]) -> None:
        clause = tuple(sorted(set(lits)))
        if any(-x in clause for x in clause if x > 0):
            return  # tautology
        if not clause:
            clauses.append(())
            return
        clauses.append(clause)

    for i, _ in enumerate(graph.edges):
        add(_var(i, c, k) for c in range(k))
        for c1, c2 in itertools.combinations(range(k), 2):
            add((-_var(i, c1, k), -_var(i, c2, k)))

    for i, j in graph.adjacent_edge_pairs():
        for c in range(k):
            add((-_var(i, c, k), -_var(j, c, k)))

    return CNF(nvars=nvars, clauses=tuple(clauses), comments=tuple(comments))


def to_dimacs(cnf: CNF) -> str:
    lines = [f"c {line}" for line in cnf.comments]
    lines.append(f"p cnf {cnf.nvars} {len(cnf.clauses)}")
    for clause in cnf.clauses:
        lines.append(" ".join(str(x) for x in clause) + " 0")
    return "\n".join(lines) + "\n"


def _lit_value(lit: int, assignment: Mapping[int, bool]) -> Optional[bool]:
    val = assignment.get(abs(lit))
    if val is None:
        return None
    return val if lit > 0 else (not val)


def _unit_propagate(
    assignment: dict[int, bool], clauses: Sequence[Sequence[int]]
) -> Optional[list[list[int]]]:
    remaining = [list(c) for c in clauses]
    changed = True
    while changed:
        changed = False
        nxt: list[list[int]] = []
        for clause in remaining:
            unassigned: list[int] = []
            satisfied = False
            for lit in clause:
                v = _lit_value(lit, assignment)
                if v is True:
                    satisfied = True
                    break
                if v is None:
                    unassigned.append(lit)
            if satisfied:
                continue
            if not unassigned:
                return None
            if len(unassigned) == 1:
                lit = unassigned[0]
                assignment[abs(lit)] = lit > 0
                changed = True
                continue
            nxt.append(unassigned)
        remaining = nxt
    return remaining


def solve_sat(cnf: CNF) -> Optional[dict[int, bool]]:
    """Toy DPLL with unit propagation. Not proof-producing. Not CaDiCaL.

    Returns a total assignment of variables 1..nvars if SAT, or None if UNSAT.
    Unassigned don't-care variables in a satisfying assignment are set False.
    The decision order is deterministic: smallest remaining variable, True first.
    """
    assignment: dict[int, bool] = {}

    def search(clauses: list[list[int]]) -> bool:
        reduced = _unit_propagate(assignment, clauses)
        if reduced is None:
            return False
        if not reduced:
            for v in range(1, cnf.nvars + 1):
                assignment.setdefault(v, False)
            return True
        var = min(abs(lit) for clause in reduced for lit in clause)
        saved = dict(assignment)
        saved_clauses = [list(c) for c in reduced]
        for value in (True, False):
            assignment.clear()
            assignment.update(saved)
            assignment[var] = value
            if search([list(c) for c in saved_clauses]):
                return True
        assignment.clear()
        assignment.update(saved)
        return False

    if any(len(clause) == 0 for clause in cnf.clauses):
        return None
    if search([list(c) for c in cnf.clauses]):
        return {v: assignment[v] for v in range(1, cnf.nvars + 1)}
    return None


def coloring_from_model(
    graph: Graph, k: int, assignment: Mapping[int, bool]
) -> Coloring:
    k = _require_colors(k)
    coloring: Coloring = {}
    for i, edge in enumerate(graph.edges):
        colors = [c for c in range(k) if assignment.get(_var(i, c, k), False)]
        if len(colors) != 1:
            raise ValueError(
                f"assignment does not give edge {edge} exactly one color: {colors}"
            )
        coloring[edge] = colors[0]
    return coloring


def is_valid_edge_coloring(graph: Graph, coloring: Mapping[tuple[int, int], int]) -> bool:
    if set(coloring.keys()) != set(graph.edges):
        return False
    for edge, color in coloring.items():
        if isinstance(color, bool) or not isinstance(color, int):
            return False
    for i, j in graph.adjacent_edge_pairs():
        e1, e2 = graph.edges[i], graph.edges[j]
        if coloring[e1] == coloring[e2]:
            return False
    return True


def brute_force_edge_coloring(graph: Graph, k: int) -> Optional[Coloring]:
    """Independent backtracking search; used to check the CNF encoding."""
    k = _require_colors(k)
    edges = graph.edges
    if not edges:
        return {}
    conflict = [set() for _ in edges]
    for i, j in graph.adjacent_edge_pairs():
        conflict[i].add(j)
        conflict[j].add(i)
    colors = [None] * len(edges)

    def rec(idx: int) -> bool:
        if idx == len(edges):
            return True
        for c in range(k):
            if any(colors[j] == c for j in conflict[idx]):
                continue
            colors[idx] = c
            if rec(idx + 1):
                return True
            colors[idx] = None
        return False

    if rec(0):
        return {edges[i]: colors[i] for i in range(len(edges))}  # type: ignore[misc]
    return None


def parse_edges(spec: str) -> Graph:
    text = spec.strip()
    if not text:
        raise ValueError("edge list is empty")
    edges: list[tuple[int, int]] = []
    for part in text.split(","):
        item = part.strip()
        if not item:
            raise ValueError(f"empty edge in list: {spec!r}")
        sep = "-" if "-" in item else ("/" if "/" in item else None)
        if sep is None:
            raise ValueError(f"expected u-v, got {item!r}")
        left, right, *rest = item.split(sep)
        if rest or not left.strip() or not right.strip():
            raise ValueError(f"expected u-v, got {item!r}")
        try:
            u = int(left.strip(), 10)
            v = int(right.strip(), 10)
        except ValueError as exc:
            raise ValueError(f"expected integer endpoints in {item!r}") from exc
        edges.append((u, v))
    return Graph.from_undirected((), edges)


EXAMPLES = {
    "triangle": triangle_graph,
    "petersen": petersen_graph,
}


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="coloring_cnf.py",
        description=(
            "Encode k-edge-coloring of a simple undirected graph as DIMACS CNF, "
            "and optionally decide small instances with a toy DPLL solver. "
            "The solver is not proof-producing and is not CaDiCaL."
        ),
    )
    src = parser.add_mutually_exclusive_group(required=True)
    src.add_argument(
        "--example",
        choices=sorted(EXAMPLES),
        help="built-in graph: triangle (K3) or petersen",
    )
    src.add_argument(
        "--edges",
        metavar="LIST",
        help="comma-separated undirected edges, e.g. 0-1,1-2,2-0",
    )
    parser.add_argument(
        "--colors",
        type=int,
        required=True,
        help="number of colors k (>= 1)",
    )
    parser.add_argument(
        "--encode-only",
        action="store_true",
        help="write or dump the CNF without running the toy solver",
    )
    parser.add_argument(
        "--out",
        metavar="FILE",
        help="write DIMACS CNF to FILE",
    )
    parser.add_argument(
        "--dump-cnf",
        action="store_true",
        help="print DIMACS CNF to stdout (implies --encode-only)",
    )
    return parser


def resolve_graph(example: Optional[str], edges: Optional[str]) -> tuple[str, Graph]:
    if example is not None:
        return example, EXAMPLES[example]()
    assert edges is not None
    return "custom", parse_edges(edges)


def format_coloring(coloring: Coloring) -> str:
    lines = ["coloring:"]
    for edge in sorted(coloring):
        u, v = edge
        lines.append(f"  {u}-{v}: {coloring[edge]}")
    return "\n".join(lines)


def run(argv: Optional[Sequence[str]] = None, out: Optional[TextIO] = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    stream = out if out is not None else sys.stdout
    try:
        if args.colors < 1:
            raise ValueError(f"colors must be an integer >= 1, got {args.colors!r}")
        name, graph = resolve_graph(args.example, args.edges)
        cnf = encode_edge_coloring(graph, args.colors)
    except ValueError as exc:
        parser.error(str(exc))

    encode_only = args.encode_only or args.dump_cnf
    if encode_only and not args.out and not args.dump_cnf:
        parser.error("--encode-only requires --out or --dump-cnf")

    dimacs = to_dimacs(cnf)
    if args.out is not None:
        with open(args.out, "w", encoding="utf-8") as fh:
            fh.write(dimacs)
    if args.dump_cnf:
        stream.write(dimacs)
        return 0
    if encode_only:
        stream.write(
            f"wrote {len(cnf.clauses)} clauses, {cnf.nvars} variables to {args.out}\n"
        )
        return 0

    model = solve_sat(cnf)
    header = (
        f"example={name} vertices={len(graph.vertices)} edges={len(graph.edges)} "
        f"colors={args.colors}\n"
        f"variables={cnf.nvars} clauses={len(cnf.clauses)}\n"
        "solver=toy DPLL (not proof-producing; not CaDiCaL)\n"
    )
    stream.write(header)
    if model is None:
        stream.write("result=UNSAT\n")
        return 0
    coloring = coloring_from_model(graph, args.colors, model)
    if not is_valid_edge_coloring(graph, coloring):
        raise RuntimeError("solver returned SAT but the coloring is invalid")
    stream.write("result=SAT\n")
    stream.write(format_coloring(coloring) + "\n")
    return 0


def main(argv: Optional[Sequence[str]] = None) -> int:
    return run(argv)


if __name__ == "__main__":
    sys.exit(main())
