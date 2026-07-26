# Lean Atlas and Lean Compass

[Lean Atlas](https://github.com/NyxFoundation/lean-atlas) exports a Lean project's declaration
dependency graph. Its Lean Compass algorithm removes value dependencies originating in theorem
proofs: Lean's type checker has already verified those proof terms, so human semantic review can
focus on the statements and definitions that determine what the selected theorem means.

This repository uses Atlas to generate [`../atlas-audit.md`](../atlas-audit.md) for
`GQ2.SectionTen.main_surjection_count'`, the count-form capstone.

## Current result

The graph as regenerated on 2026-07-26, after the L-campaign, contains 5,571 project nodes and
49,304 edges. The target's 1,789-node Atlas closure reduces to a **30-declaration Lean Compass
review cone** (98.3% reduction). Those 30 declarations are the project statements and definitions
that, under Compass's dependency model, should receive human semantic review. The generated report
links every declaration to the source location it had when the report was generated.

This number is not an axiom count. The capstone separately depends on all **nine** documented
literature axioms.

The review cone is unchanged at 30 declarations across the last three reports (2026-07-15, the
post-R-campaign one, and this one), and so is the nine-axiom trust base — with B9 appearing under
its restated name `GQ2.relativeStiefelWhitney_dyadic` since the R-campaign, `GQ2.evensKahn_dyadic`
having become a derived theorem. The full closure has likewise not moved from 1,789 nodes since the
R-campaign: everything the L-campaign added lives in `GQ2/Roe/`, which `main_surjection_count'`
does not reach. (The earlier growth from 638 nodes had two proof-level causes:
`GQ2/Phase140/GammaA/Hsep.lean` and `GQ2/AnabelianBridge/Construction.lean` landed in the very
commit that generated the 2026-07-15 report, so the 638 figure never reflected them, and the B9
restatement rerouted part of `thm_4_2`'s proof. Both travel along theorem-proof value edges, which
Compass prunes — which is why the closure moved and the review cone did not.)

The whole-graph `sorry` count is **0**: the `GQ2/Roe/Labute/` files that held the last 11 landed
sorry-free on 2026-07-26, and `scripts/check_axioms.sh`'s allowlist is empty. None of them was ever
reachable from `main_surjection_count'`, whose closure has been sorry-free throughout and contains
no `GQ2/Roe/` declaration.

The whole-graph totals moved by +220 nodes and +1,812 edges against the post-R-campaign report —
the net of the L-campaign's `GQ2/Roe/Labute/` work landing (`TwoCentralTower.lean`,
`Levelwise.lean`, `SpanFoundation.lean`, `Assembly.lean`, the five `GradedLie/` modules and the six
`StageLemma/` modules of the CU-B split are all present in the regenerated graph, 407 visible nodes
between them) against the cleanup passes, which privatized declarations during the split and
deleted local restatements, and so remove nodes from the user-visible graph.

A Compass report for the `Γ_R` capstone now exists: **`atlas-audit-roe.md`** (generated
2026-07-26 from the same graph export, targeting
`GQ2.main_presentation_literal_roe_unconditional`; `GQ2.main_presentation_literal_roe` is the
same theorem with the discharged `BLabHypothesis` binder). Its full closure is 2,342 nodes,
reducing to a **32-declaration review cone** — two nodes more than the paper capstone's cone,
with the same 9-axiom trust base. Regenerate both reports together after source edits.

## Why the report uses two data sources

Lean Atlas intentionally filters compiler-internal names, including Lean's mangled names for
`private` declarations. This is appropriate for the visible semantic-review graph: private
theorems used only inside a checked proof do not create additional public statements to align.
It does mean that the full Atlas graph is not an authoritative way to reconstruct a theorem's
kernel axiom dependencies. An axiom can be reached through a private proof helper and therefore be
absent from the user-visible graph closure.

Accordingly, [`../scripts/atlas_audit.py`](../scripts/atlas_audit.py) combines:

1. the Atlas graph and the official Compass edge-pruning rule for the semantic review cone; and
2. Lean's own `#print axioms` result for the complete kernel trust base.

The generator fails if a kernel-reported project axiom is absent from the exported project's axiom
census, preventing the post-privatization undercount that a graph-only report would produce.

## Regenerating the report

From the repository root:

```sh
lake exe atlas graph-data -o atlas-graph.json
python3 scripts/atlas_audit.py atlas-graph.json
```

The first command rebuilds the project as needed and exports the graph. The second computes the
Compass cone, queries Lean for the target's axioms, and rewrites `atlas-audit.md`. The generated
`atlas-graph.json` and its cache are ignored; `atlas-audit.md` is committed.

To inspect another declaration without overwriting the capstone report, pass the target and output
path explicitly:

```sh
python3 scripts/atlas_audit.py atlas-graph.json GQ2.thm_4_2 /tmp/thm-4-2-audit.md
```

The target must be available after `import GQ2`.

## Relationship to `lake exe atlas compass`

The upstream `atlas compass` command requires target declarations to carry Lean Atlas's
`mainTheorem` metadata. Importing `LeanAtlas` into a mathematical `GQ2` module merely to attach that
attribute would couple the library to a review-only tool. The local generator instead applies the
same rule directly to the exported edge kinds:

- keep type dependencies and definition-value dependencies;
- remove `theorem_value_to_definition` and `theorem_value_to_theorem` edges.

This produces the same Compass cone without changing the mathematical import graph. Lean Atlas is
pinned as a Lake development dependency, but no `GQ2` source module imports it.

## Interactive viewer

`lake exe atlas serve` starts the Atlas viewer at `http://localhost:5326`. It requires Node 18 or
newer and `pnpm`; the first run installs web dependencies under `.lake/packages/lean-atlas/web`.
For reproducible review, the headless graph export and committed Markdown report are the primary
interface.
