# Lean Atlas and Lean Compass

[Lean Atlas](https://github.com/NyxFoundation/lean-atlas) exports a Lean project's declaration
dependency graph. Its Lean Compass algorithm removes value dependencies originating in theorem
proofs: Lean's type checker has already verified those proof terms, so human semantic review can
focus on the statements and definitions that determine what the selected theorem means.

This repository uses Atlas to generate [`../atlas-audit.md`](../atlas-audit.md) for
`GQ2.SectionTen.main_surjection_count'`, the count-form capstone.

## Current result

The graph as regenerated on 2026-07-26, after the R-campaign, contains 5,351 project nodes and
47,492 edges. The target's 1,789-node Atlas closure reduces to a **30-declaration Lean Compass
review cone** (98.3% reduction). Those 30 declarations are the project statements and definitions
that, under Compass's dependency model, should receive human semantic review. The generated report
links every declaration to the source location it had when the report was generated.

This number is not an axiom count. The capstone separately depends on all **nine** documented
literature axioms.

The review cone is unchanged at 30 declarations from the previous (2026-07-15) report, and so is
the nine-axiom trust base — with B9 now appearing under its restated name
`GQ2.relativeStiefelWhitney_dyadic`, `GQ2.evensKahn_dyadic` having become a derived theorem. The
full closure grew from 638 nodes for two reasons, both proof-level: `GQ2/Phase140/GammaA/Hsep.lean`
and `GQ2/AnabelianBridge/Construction.lean` landed in the very commit that last generated the
report, so the 638 figure never reflected them; and the B9 restatement rerouted part of `thm_4_2`'s
proof. Both changes travel along theorem-proof value edges, which Compass prunes — which is why the
closure moved and the review cone did not.

The whole-graph `sorry` count in the committed snapshot is **11**, all in the then-in-flight
`GQ2/Roe/Labute/` files (`StageLemma.lean`, `Assembly.lean`). **Stale as of 2026-07-26**: those
files landed sorry-free that day, so the true library-wide count is now **0** and
`scripts/check_axioms.sh`'s allowlist is empty; the snapshot figure updates at the next Atlas
regeneration (the graph itself must be re-exported — see below). None of them was ever reachable
from `main_surjection_count'`, whose closure remains sorry-free and contains no `GQ2/Roe/`
declaration.

No Compass report has yet been generated for the `Γ_R` capstone — now unconditional, and best
targeted as `GQ2.main_presentation_literal_roe_unconditional` (`GQ2.main_presentation_literal_roe`
is the same theorem with the discharged `BLabHypothesis` binder) — though the declaration is
present in the exported graph.
The generator takes a target argument (see below), so producing one is a single command; until
then, the review cone described here covers the paper's capstone only.

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
