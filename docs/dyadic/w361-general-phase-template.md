# W361 staged typed quadratic-phase export

Status: checked additive format, 2026-09-17. Not an approved replacement for
the frozen appendix or export format. No existing word, Hessian record,
renderer, manifest or generated artifact was edited.

## Mathematical object and checked bindings

[Word/GeneralPhaseTemplate.lean](../../GQ2/Dyadic/Word/GeneralPhaseTemplate.lean)
defines a finite computable syntax in namespace
`GQ2.Dyadic.GeneralPhaseTemplate`:

* `Coordinate h`: `head0`, `head1`, `handleU (j : Fin h)`,
  `handleV (j : Fin h)`;
* `Tree h`: `zero`, `baseQuad coordinate`, `polar coordinate coordinate`,
  `add tree tree`;
* `compactPhase h`: the actual head tree plus the increasing-handle list
  `List.ofFn`, folded by `Tree.sumList` with a trailing zero.

For **every** h, additive coefficient group V, function `q : V → ZMod 2`, and
coordinate vector p, `denote_compactPhase` proves

```
(compactPhase h).denote q p = WordPhase.wPhCompactWallHandlePhase q h p.
```

Thus the literal tree denotes
`q(head0)+polar q head0 head1+sum_j polar q (handleU j) (handleV j)`.
This identity does not assume q quadratic and is not established by finite
rank tests. Here q is the **quadratic-function parameter**, not the residue
cardinality parameter of a source presentation.

The ties to existing proofs are also checked:

* `sourcePhase_eq_denote` rewrites a supplied actual
  `SourceWordPhaseComparison` through this equality while retaining its
  exact `phaseEquiv` map and source `QZeroBar`.
* `sourceHessian_cov_eq_denote` does the same with the actual `cov` of
  `sourceCompactHessianOfComparison`, using the existing additivity witness.
* `compactPhaseCover_tree` supplies the original complete
  `PhaseCoverCertificate` with the tree denotation as endpoint. Its
  diagonal, cross-polar identity, cardinality and Gauss data are transported
  from the original compact record, not entered separately in a renderer.

The source-comparison input is essential: the payload does not independently
assert that an arbitrary presentation has this phase. The pair/mobile
records supply exactly that comparison in the previously checked profiles.
For the ramified branch the comparison includes the existing head swap;
the raw pre-swap `q(head1)+B(head0,head1)` is not asserted equal to the
exported post-swap compact phase. This compact tree does not replace the
different actual Npc diagonal or the L Wall form.

## Matrix data is read from existing certified definitions

`Coordinate.blockIndex` sends the typed coordinates to the existing
`Fin 2 ⊕ (Fin h × Fin 2)` polar-matrix indices.
`Coordinate.denote_eq_blockCoordinates` proves the coordinate agreement.
`coordinateList` orders the two heads, then U/V of each increasing handle;
membership and length `2+2*h` are proved.

`matrixJson` traverses this order and reads the actual entries of
`WordPhasePolarNormal.reducedCoefficientMatrix` and
`reducedInverseMatrix`. There is no second manually entered matrix formula.
`polar_denote_compactPhase` transports the existing full matrix formula to
the tree, and the existing `reducedCoefficientMatrix_mul_inverse` and
`reducedInverseMatrix_mul_coefficient` prove both inverse products for every
h. These are coefficients **relative to `polar(q)`**. They do not assume
that the underlying bilinear pairing has an identity matrix in a chosen
basis.

## Schema and executable

The library has no global `main`. The separate executable is
[Word/GeneralPhaseTemplateExport.lean](../../GQ2/Dyadic/Word/GeneralPhaseTemplateExport.lean).
Invoke it as:

```
bash /private/tmp/gq2-w360-lean.sh --run \
  GQ2/Dyadic/Word/GeneralPhaseTemplateExport.lean H
```

It prints one line prefixed `W361_PHASE_TEMPLATE_JSON=`. The envelope has
`payload`, `status: "STAGED"`, and `template_hash`. The payload contains:

| Field | Meaning |
| --- | --- |
| `schema` | `gq2.w361.quadratic-phase.v1.staged` |
| `kind` | `compact-wall-handle` |
| `structural` | `{ "h": H }` |
| `factory`, `bridge` | Exact `compactPhase` and `denote_compactPhase` declaration names |
| `tree` | Direct `Tree.toJson` traversal of that factory's tree |
| `coordinates` | Typed coordinate ordering, including bounded handle indices |
| `matrix`, `inverse_matrix` | Integer 0/1 entries from the existing certified ZMod-2 matrices |
| `pairing` | `polar(q)` |

Coordinates serialize as `{"coordinate":"head0"}` or `head1`, and as
`{"coordinate":"handleU","index":j}` or `handleV`. Tree shapes are:

```
{"op":"zero"}
{"at":COORDINATE,"op":"baseQuad"}
{"left":COORDINATE,"op":"polar","right":COORDINATE}
{"left":TREE,"op":"add","right":TREE}
```

The deterministic library serializer preserves every addition and trailing
zero. Its SHA-256 hash domain is the bytes
`GQ2-W361-QUADRATIC-PHASE` followed by NUL. The hash binds the canonical
payload bytes: the symbolic phase template, rank, coordinate ordering and
matrix data. It does **not** hash a concrete V, q-function, source word,
factor set, source comparison or transitive Lean build. The synchronized
packet must retain those theorem-level bindings and provenance separately.
An external renderer/checker should re-emit the Lean factory when verifying
the payload; no claim of a formally verified JSON parser is made here.

## Verification

The library and executable compile under default Lean options without
warnings. The library's 23 printed pins and executable's two pins are all
subsets of the standard three. The tree factory and its list constructor
are axiom-free. Both `.olean` files were generated in the shared build cache.

Runtime emission was checked at h=0 and h=2; `jq` parsed the output. The
zero-handle tree keeps its explicit zero tail; h=2 emits six coordinates,
the certified 6×6 matrix and its inverse, and both ordered handle summands.
A nonnumeric argument is rejected. These are executable-format checks;
the arbitrary-rank denotation and matrix claims are the Lean theorems above,
not extrapolations from these examples.

This supplies a theorem-bound expression artifact for compact-phase items
7–9. It does not by itself complete or approve the combined ten-item packet,
and it should not be imported together with other executable modules that
also declare a global `main`.
