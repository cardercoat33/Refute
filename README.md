# Refute

A design proposal for a SAT-based conjecture engine for finite graph theory.

**This repository is a design sketch, not an implementation.** There is no working library, solver pipeline, or public API yet. The Python fragment below is proposed syntax only; `import refute` will not work.

## Proposed user syntax

A conjecture is a predicate over finite graphs, compiled and checked at a bounded order `n`. The following example is intentionally false:

```python
from refute import Graph, conjecture, cubic, bridgeless, edge_colorable

@conjecture(n=range(4, 13, 2))
def cubic_bridgeless_is_class_one(G: Graph):
    return (cubic(G) & bridgeless(G)).implies(edge_colorable(G, 3))
```

It asserts that every cubic bridgeless graph of even order between 4 and 12 is 3-edge-colorable (class one). That fails at `n = 10`: the Petersen graph is cubic and bridgeless, but not 3-edge-colorable. A correct engine should therefore report a counterexample at that order, not a proof of the claim.

## Planned pipeline

1. Compile a restricted DSL fragment to CNF.
2. Solve with CaDiCaL.
3. Convert a DRAT proof through `dpr-trim` to LRAT.
4. Check the LRAT certificate with `cake_lpr`.

A checked UNSAT certificate is a bounded result *relative to a correct encoding*. It does not prove the conjecture for all `n`, and it does not verify the DSL compiler. Encodings must be benchmarked independently. Any counterexample must be checked by an independent procedure (for example, against a known graph or a second generator), not trusted merely because the solver returned SAT.

## What a result means

Each bounded check should end in one of three outcomes:

- **Counterexample**, independently checked.
- **Bounded verified UNSAT**: the encoding is unsatisfiable, and `cake_lpr` accepted the LRAT proof.
- **Unknown**: the solver or proof checker failed, timed out, or the claim left the fragment of the DSL for which encodings are believed sound.

Do not treat “the search for a counterexample is UNSAT” as a standard SAT proof that a graph is not edge-colorable, or that every graph in a class is. Edge-colorability has a nested-quantifier shape: a counterexample to “every cubic bridgeless graph is 3-edge-colorable” is a graph *G* such that *every* 3-edge-coloring of *G* fails. A single SAT instance that merely searches for a graph together with a coloring answers a different question. The staged plan is therefore:

1. Enumerate or SAT-search candidate graphs (CEGAR-style refinement is in scope later).
2. For a fixed candidate, search for a coloring; if that instance is unsatisfiable, produce a *separate* checked proof of non-colorability of that graph.
3. Restrict the initial proof-supported DSL fragment to encodings that can be kept sound under this discipline.

If a check cannot be discharged inside that fragment, the result is **Unknown**, not a proof.

## Symmetry

Isomorphic copies would otherwise blow up the CNF. The planned symmetry breaking uses lex-leader constraints in the spirit of Codish et al. Completeness of the breaking will be checked incrementally against nauty’s `geng`, without claiming that the encoding eliminates all isomorphism at the outset.

## Initial milestones

These are targets, not achieved benchmarks:

- Recover the Petersen graph as a checked counterexample to the toy conjecture at `n = 10`.
- Recover the classical fact `R(3,3) = 6` inside the same pipeline, with a checked bounded certificate.

## Implementation plan

The intended first coding tasks, if a coding agent such as Devin is used later, are:

- a parser and CNF encodings for a small, sound DSL fragment;
- exhaustive checks on small graphs;
- proof plumbing with pinned versions of CaDiCaL, `dpr-trim`, and `cake_lpr`.

Triage should stop after **3 attempts or 45 minutes**. A failure remains **Unknown**; it is not a disproof and not a license to weaken the checker.

## Status

Design only. No solver integration, no tests, and no published results live in this repository.
