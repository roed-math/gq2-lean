# Lean Atlas — dependency-graph tooling

[Lean Atlas](https://github.com/NyxFoundation/lean-atlas) is a Lean 4 dependency-graph tool. We
use it to produce [`atlas-audit.md`](../atlas-audit.md) — the trust-base audit of the
formalization capstone `GQ2.SectionTen.main_surjection_count'`:

- **the axioms the proof rests on** (its `#print axioms`, minus the `propext`/`Classical.choice`/
  `Quot.sound` core), and
- **the Lean Compass review cone** — the statement-level nodes whose *semantic* correctness can
  affect the capstone (the full closure minus the theorem-proof value edges the type checker
  already guarantees). For the capstone that is 30 nodes out of a 3185-node closure (≈ 99 %).

It is wired in as a Lake dependency (`lakefile.toml`) pinned to a commit that builds under this
repo's toolchain. **`GQ2` never imports it**, so normal builds are unaffected.

## Regenerating `atlas-audit.md`

Two commands from the repo root — no source edits:

```bash
lake exe atlas graph-data -o atlas-graph.json      # export the graph (~8 MB; do NOT commit it)
python3 scripts/atlas_audit.py atlas-graph.json    # render atlas-audit.md
```

`scripts/atlas_audit.py` computes the cone directly from the graph and the target name, so it
needs neither the web viewer nor a `mainTheorem` marker.

**Different target:** pass its fully-qualified name, e.g.

```bash
python3 scripts/atlas_audit.py atlas-graph.json GQ2.thm_4_2
```

(`thm_4_2` additionally pulls in the B9/B11/B12/B13 Kummer axioms.) Line numbers in the audit
are a snapshot from graph-export time — regenerate after source edits.

## Optional: the official `lake exe atlas compass`

`scripts/atlas_audit.py` already replicates Compass's reduction and prints the actual cone. If
you want the tool's own reduction-rate output, Compass reads a `mainTheorem` flag from the
environment. Mark the target temporarily (do **not** commit — importing `LeanAtlas` from a `GQ2`
module would couple every build to the dev tool):

```bash
cat > GQ2/AtlasMarks.lean <<'EOF'
import LeanAtlas
import GQ2.SectionTenSources
attribute [formalMeta "main_surjection_count'"
  "Formalization capstone: #(continuous surjections G_Q2 ↠ G) = admissibleCount G" mainTheorem]
  GQ2.SectionTen.main_surjection_count'
EOF
echo 'import GQ2.AtlasMarks' >> GQ2.lean
lake build GQ2 && lake exe atlas compass
# back out:
sed -i '' -e '/^import GQ2\.AtlasMarks$/d' GQ2.lean   # macOS; drop the '' on Linux
rm GQ2/AtlasMarks.lean
```

## Optional: the interactive web viewer

`lake exe atlas serve` starts a viewer at `http://localhost:5326` (needs Node ≥ 18 + pnpm; the
first `serve` runs `pnpm install` in `.lake/packages/lean-atlas/web`). **Caveat:** the full GQ2
graph (~4.4k nodes / 39k edges) overwhelms the browser renderer and hangs — the headless
`graph-data` / `compass` + `scripts/atlas_audit.py` path above is the practical interface for a
project this size.

## Backing out entirely

```bash
# remove the dependency, then:
lake update      # rewrites lake-manifest.json without lean-atlas
rm -rf .lake/packages/lean-atlas atlas-graph.json
```
and delete the `[[require]] name = "lean-atlas"` block from `lakefile.toml`.
