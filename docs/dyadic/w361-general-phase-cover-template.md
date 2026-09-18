# W361 STAGED typed phase-cover export

This additive format exports the actual compact phase-cover data uniformly in
the handle rank. It does not change the original `PhaseCoverCertificate`, any
frozen word/appendix, or the existing phase-template schema. It has no owner
approval or migration status beyond **STAGED**.

## Formal source and scope

Library: `GQ2/Dyadic/Word/GeneralPhaseCoverTemplate.lean`.
Namespace: `GQ2.Dyadic.GeneralPhaseCoverTemplate`.
Separate executable: `GQ2/Dyadic/Word/GeneralPhaseCoverTemplateExport.lean`.
Do not import the executable into an umbrella: it declares global `main`.

`compactTemplate h` contains:

- the existing `GeneralPhaseTemplate.compactPhase h` tree;
- two typed coordinate tables with values `InputTerm.zero` or `InputTerm.input`;
- a quadratic diagonal term `baseQuad input`;
- a typed dimension expression `(literal h + literal 1) * dimension`;
- the integer sign `1`.

`Embedding.denote` interprets the two tables in the actual
`CompactCoordinates V h`. `diagonalEmbedding_denote` and
`crossEmbedding_denote` identify them with the existing additive inclusions
`headDiagonal h` and `headCross h`, hence with `((v,0),0)` and `((0,v),0)`.
`compactTemplate_phase` identifies the exported phase with the exact existing
`wPhCompactWallHandlePhase q h` for every additive coefficient group and every
function `q`; no quadraticity hypothesis is needed just for this equality.

The principal bridge is **`compactTemplate_agrees`**. For the original inputs
`dat`, `hdat : IsEquivariantFactorSet q dat`, quadraticity and nonsingularity of
`q`, finite `V`, and `hcard : #V = 2^d`, it proves all of the following:

1. the phase tree denotes the actual full compact quadratic phase;
2. its two embeddings are exactly the original head inclusions;
3. its diagonal evaluates to the actual `dat.f v v` (not a value inferred from
   the polar form alone);
4. its dimension term at `d` equals the original `compactPhaseCover … h`.baseDim;
5. its integer sign equals that record's `baseSign`.

The original cover still supplies `card_eq`, `gauss_eq`, `polar_id`, and
`kappa_id`. No new hypothesis is used to replace any of those proofs. The
coefficient dimension `d` is left symbolic in the export: the record assumes
`#V=2^d` and its half-dimension is `(h+1)d`. This template is the common compact
phase of the changed pair/mobile sources after their checked coordinate maps;
it is not the general arbitrary-diagonal Npc phase template or the odd L phase.

For exact source binding, retain the actual source comparison or
`SourceCompactHessian` record. The existing
`GeneralPhaseTemplate.sourcePhase_eq_denote` and
`sourceHessian_cov_eq_denote` identify that record's full phase using its
unchanged coordinate map. The typed cover export does not by itself identify a
source word, field, boundary lift, or coefficient module.

## Payload and hashing

Schema: `gq2.w361.phase-cover.v1.staged`.
Envelope: `{"payload":…, "status":"STAGED", "template_hash":…}`.
The hash is SHA-256 of `GQ2-W361-PHASE-COVER`, NUL, then the canonical payload JSON.

The payload has exactly these fields:

| Field | Computable source |
|---|---|
| `base_dim` | `DimensionTerm.toJson` on the template's dimension AST |
| `base_sign` | the template's actual integer sign |
| `bridge` | `GQ2.Dyadic.GeneralPhaseCoverTemplate.compactTemplate_agrees` |
| `diagonal` | `DiagonalTerm.toJson`, retaining the base quadratic value |
| `factory` | `GQ2.Dyadic.GeneralPhaseCoverTemplate.compactTemplate` |
| `j0`, `j1` | `Embedding.toJson`: ordered `{at: coordinate, value: inputTerm}` tables |
| `kind` | `compact-wall-handle` |
| `phase_template_hash` | the exact existing phase-and-matrix payload hash at this rank |
| `phase_tree` | the template's actual `Tree.toJson` |
| `schema` | the new schema above |
| `structural` | `{h: H}` |

Dimension terms are `literal` with a natural `value`, `dimension` with variable
`d`, or binary `add`/`mul`. Input terms are exactly `zero`/`input`. Coordinates
reuse the rank-indexed phase coordinate syntax. All JSON comes directly from
these typed data; the renderer does not maintain another formula for the cover.

The linked phase hash is **not** a source-word hash. A combined packet must
check the linked hash, exact phase-tree equality, and common rank against its
actual phase artifact, as well as its separate source-word/profile binding.

## Renderer and replay

`scripts/w361_general_cover_tex.py` exports `validate(envelope)`, `loads(text)`,
`from_lean(runner,h)`, and `render_tex(envelope)`. Its CLI has `self-test`,
`generate H --lean-runner RUNNER --out DIR`, and `check DIR [--lean-runner RUNNER]`.
Generation is restricted to a path containing the `general-certificate-staged`
component. Filenames are `compact-cover-hH.cover.json` and `.cover.tex`.

The renderer traverses the typed embedding tables, dimension term, diagonal,
and phase tree. It prints the coefficient quadratic form as `q_0`, to distinguish
it from the residue-cardinality parameter `q`. Embedding vectors are explicitly
in the flattened head/handle coordinate order. The symbolic `d` is not assigned
by the renderer.

Validation enforces exact fields, strict integer types, positive-one sign,
coordinate count/order/bounds, typed terms, lowercase SHA-256 linkage, canonical
payload hash, and rejection of duplicate keys/nonfinite JSON constants. The
embedding length is checked before allocating an expected rank table. Strong
checking reruns the Lean exporter and compares the whole envelope; artifact-only
checking is labelled `NOT Lean-synchronized` and does not pretend to prove an
arbitrary well-typed, rehashed template is this factory output.

The library and executable compile under default Lean options, warning-free;
all twenty library and two executable audit pins use at most
`[propext, Classical.choice, Quot.sound]`. Runtime exports at `h=0,1,2` were
independently parsed and checked against Python canonical JSON/SHA-256 and the
separately exported phase hashes/trees. Four malformed exporter invocations
(missing rank, negative rank, nonnumeric rank, extra argument) fail. The renderer
self-test passes 51 tests. CLI generation and strong durable-runner replay pass
at all three ranks. A separate nineteen-check harness verifies embedding/diagonal
TeX fidelity, filenames, output restriction, negative ranks, and intentional
artifact-only versus strong-check behavior: rehashed altered embeddings,
dimensions, and linked phase hashes pass structural-only checking but are all
rejected by actual Lean replay.

| h | Cover template hash |
|---|---|
| 0 | `49acd1e6bdf6fe5b988bd1c26b135fb614d686f5e0c95bc534fe63ca6820031b` |
| 1 | `d21b7952f6b4eeccbf62573e6bd1b5f258e999854fe27041ccd02dbc5b2597f9` |
| 2 | `89e5086b67f609720cb357dbf29aed23fd7034eca445affa0930ecaf6a971999` |

These finite executable tests check synchronization, not the rank-uniform
mathematical result; the latter is the quantified Lean bridge.
