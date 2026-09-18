# W361 STAGED all-parameter L/N word export and replay

Status: additive, unapproved publication tooling. This closes the gap between
the existing **rank-uniform** L/N denotation theorems and executable one-tree
export/replay. It introduces **no new word grammar or Python word factory**.
The old `RawWord` constructors, S1.1 serializer, renderer, manifest, fixture pins,
and generated appendix skeletons are unchanged.

## Uniform formal connection

`Word/GeneralTemplateLNCanonical.lean` adds eight default-limit, standard-three-
or-less declarations in `GQ2.Dyadic.GeneralTemplateLN`:

- `canon_rawLsq`, `canon_rawNCompact`, and `canon_rawNpc` describe the exact
  existing constructor-level canonicalization;
- `npcW_canonicalEtaHat` proves literal semantic word equality after rational
  sign/gcd normalization, assuming the original denominator is odd;
- `denote_canon_rawLsq`, `denote_canon_rawNCompact`, and
  `denote_canon_rawNpc` connect the **actually serialized canonical tree** to
  the original semantic word for every structural parameter and handle rank;
- `denote_canon_rawNpc_display` identifies that tree with `npcWUnit … eta` when
  supplied an **exact** `NpcDisplayFor eta`.

The last point matters. `Export.canonicalJson` canonicalizes `EtaHat` before
serializing it. Merely citing `GeneralTemplateLN.denote_rawNpc` for an arbitrary
unreduced input pair would skip this step. The new bridge uses the existing
`EtaData.canonicalEtaHat_toZhat` theorem, so `3/9`, `-3/-9`, and `1/3` really
denote the same profinite exponent, not just the same residue modulo a power
of two. Numerator and denominator are both required odd by the executable
well-formedness contract. No claim is made that an arbitrary externally given
two-adic unit has a finite rational display.

`Word/GeneralTemplateLNExport.lean` is a separate executable, not an umbrella
import. It calls the existing raw factories and `canonicalJson`/`astHash`
directly, without retyping their formulas. Its nine audit pins use at most the
standard three axioms. The original all-rank `GeneralTemplateLN` bridges and
the existing `wf_rawLsq`, `wf_rawNCompact`, and `wf_rawNpc` are retained.

## Scope: syntax is not a complete word certificate

| Export request | Exact semantic target | Separate certificate conditions |
|---|---|---|
| `L H` | `Words.LSq.lSqW H`, degree `2H+1` | The existing final L certificate uses `q=2^f` with `Odd f`. No `q` occurs in this word export. |
| `N0 ALPHA H` | `Words.nCompactW ALPHA H`, degree `2+2H` | Complete certificate: `2≤ALPHA`, nonzero even `q`. |
| `Npc ALPHA R H NUM DEN` | `Words.Npc.npcW ALPHA R H ⟨NUM,DEN⟩`, degree `2+2H` | Both integers odd; exact `NpcDisplayFor` for the semantic-unit target; complete certificate also has `2≤ALPHA` and nonzero even `q`. Selected procyclic branches have `1≤R`. |

Syntax and denotation identities allow every natural `ALPHA,R,H`, even where a
particular final certificate has stronger hypotheses. The output states those
conditions rather than silently treating export success as certificate success.
The handles remain the **unexpanded** `HyperbolicHandles` node; the generic
Lean bridge proves its ordered expansion at every rank. L omits that node at
rank zero; N0/Npc retain the zero-count node, interpreted as the empty product.

## Schema, identity and provenance

The wrapper schema is `gq2.w361.ln-word.v1.staged`. Its `tree` is the unchanged
S1.1 canonical AST (version 1), not the separate symbolic pair/mobile grammar.
The envelope is `{payload, status: STAGED, template_hash}`. Exact payload fields:

```text
alphabet_degree, ast_schema_version, binding, bridge, factory, family,
schema, semantic_target, structural, tree, unit_bridge, word_hash
```

`unit_bridge` is null for L/N0 and names the exact-display theorem for Npc.
`structural` keeps the **requested** integers, including a negative or
nonreduced odd rational spelling. There are two different hashes:

1. `word_hash` is the old S1.1 SHA-256 of the canonical unexpanded AST bytes.
   All existing frozen hashes remain identical. Equivalent rational spellings
   intentionally share this hash.
2. `template_hash` is SHA-256 of `GQ2-W361-LN-WORD`, NUL, then canonical payload
   JSON. It additionally binds the exact request, alphabet, semantic context,
   factory and bridge names. Thus the three spellings above have distinct
   envelope hashes even though their word hashes coincide.

A `.provenance.json` sidecar binds the envelope hash and direct bytes of the
factory/semantic bridge/serializer/renderer source files. This is expressly
**not** a transitive build attestation or a hash of a chosen coefficient module,
finite resolver, field, full certificate, or future approved release.

## Executable interface and checking

New helper: `scripts/w361_general_ln_word_tex.py`. It imports
`dyadic_word_tex.py` **read-only** for canonical S1.1 validation and rendering.
It exports `validate(envelope)`, `loads(text)`,
`from_lean(runner,family,parameter_dictionary)`, `render_tex(envelope)`, and
`provenance(envelope)`.

```text
python3 scripts/w361_general_ln_word_tex.py self-test
python3 scripts/w361_general_ln_word_tex.py generate L 4 --lean-runner RUNNER --out DIR
python3 scripts/w361_general_ln_word_tex.py generate N0 5 3 --lean-runner RUNNER --out DIR
python3 scripts/w361_general_ln_word_tex.py generate Npc 3 2 3 -3 -9 --lean-runner RUNNER --out DIR
python3 scripts/w361_general_ln_word_tex.py check DIR --lean-runner RUNNER
```

`DIR` must contain the path component `general-ln-template-staged`; its default
is `generated/general-ln-template-staged`. The runner may be the durable
`scripts/w361_lean_runner.sh`, configured with its matching package/artifact
paths. Each request emits `.ln.json`, `.tex`, and `.provenance.json` under a
canonical parameter-derived basename. Export stdout has the marker
`W361_LN_WORD_JSON=`; the library and export executable remain separate.

Validation enforces strict field sets and literal integer types, family-bound
semantic metadata, exact degree/rank, generator/handle bounds, actual concrete
exponents, exact canonical odd `EtaHat` display, expected handle-block count,
and consistent auxiliary definitions. Unknown/unresolved `Shadow` and unused
`OrbitNorm` syntax are rejected. Duplicate JSON keys and nonfinite constants
are rejected. Check mode re-renders TeX, verifies direct-source provenance and
canonical filenames, and, when supplied a runner, **re-emits Lean's factory**.

Artifact-only mode is labelled `NOT Lean-synchronized`. A rehashed, well-typed
but altered formula can pass structural checking and is not thereby proved to
be the factory output; actual Lean replay rejects it. The renderer uses the
same AST and unchanged auxiliary definitions, and prints Npc's exact original
and reduced fraction explicitly rather than leaving the value of eta hidden
behind a symbol.

## Verification and remaining publication boundary

Both new Lean modules compile at default limits, warning-free, with eight plus
nine audit pins at most `[propext, Classical.choice, Quot.sound]`. The helper's
built-in malformed-input tests pass 39 checks. An independent temporary
regression harness passes 52 checks, including eight fresh Lean replays,
rehashed wrong-factory rejection, and filename/TeX/provenance mutations.
Runtime generation and strong replay exercise all three families beyond the old fixture ranks, the three
canonicalization-equivalent Npc spellings, and the existing L/N0/Npc frozen
hashes. These tests check executable synchronization; the quantified Lean
bridges, not the finite test selection, prove the general case.

Six durable examples and a replay README are staged under
`generated/general-ln-template-staged`: L at ranks zero and four, N0 at
`alpha=5,h=3`, and Npc at its frozen display plus the nonreduced displays `3/9`
and the genuinely negative ratio `-3/9` at `alpha=3,r=2,h=3`. All six passed fresh Lean replay. These are
regressions of the generic mechanism, not additional fixture-specific proofs.

This addition supplies exact word synchronization for ledger items 1 and 10.
It does not claim to finish the full L/N ten-item appendix: Fox profiles,
ordered operations, resolvers, actual-boundary Hessian coordinates and affine
phase fields must still be assembled under their exact family-specific
hypotheses. In particular Npc's completed full-offset quadratic diagonal and
L's odd-degree Wall endpoint must not be replaced by the common compact
pair/mobile phase just to reuse a renderer. Existing theorem-level records
already supply those facts; their synchronized publication packet and the
owner-approved treatment of the old skeletons remain separate tasks.
