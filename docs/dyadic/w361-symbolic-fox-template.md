# W361 staged symbolic Fox-operation template

This is an additive, **STAGED** export. It does not change the frozen S1.1 word
grammar, old fixtures, old manifests, or approval status of the proposed appendix.

## One typed tree and uniform denotation

`Word/GeneralFoxTemplate.lean` introduces typed input rows, operation lists,
carried inverse coefficients, and identity-pivot target rows. Its coefficient
constructors are the original constants, atoms, addition, negation, and ordered
composition, plus two finite-sum **templates**. At natural values `q,k`, the latter
expand into literal original `FoxCoeff (TameSym n)` trees; no inverse atom or
unproved inverse operator is added to the original grammar.

The three denotation theorems identify the scalar, unramified, and ramified
operation lists and targets for **every** alphabet rank and `q,k`. The three
input-evaluation theorems identify the input-row expressions as full-cochain
operators. `Instances/TameSpliceFoxTemplateBinding.lean` then supplies six literal
equalities to the operation/target fields of the actual pair/mobile original
`FoxCertificate` producers. Their original source, action, resolver, and death
hypotheses remain in the types. These are uniform theorems, not proofs for the
export examples. The three modules, including the executable export, have 42
public axiom pins, each within the standard three axioms; default compilation is
warning-free.

The parameters have different roles:

- `q` is the source residue size. Certified uses require it to be nonzero and
  even; the norm sum has `q` terms.
- `k` is derived from the **actual coefficient action**: its odd action order is
  `2*k+1`. It is the sigma-action half-period in the unramified sector and the
  tau-action half-period in the ramified sector. It is not the handle rank or
  ambient group order. The scalar bridge chooses the unused value zero.
- `h` determines only the alphabet: `n=2+2*h`, with `n+1` wild letters and pivot
  index two. A pair certificate additionally requires a selected handle, so an
  exported rank-zero template does not assert existence of a pair instance.

Composition is ordered: `comp(outer,inner)` applies `inner` first. In particular,
the ramified inverse is the odd tau-action polynomial composed with sigma, not
the reverse product. Row lists apply their head first. Column lists denote the
head composed with the tail, so the rightmost input substitution acts first.
Every formal inverse carried by a scale operation is serialized and rendered.

## Export and checker boundary

`Word/GeneralFoxTemplateExport.lean` directly traverses the same profile value,
including its input rows, row and column operations, and target rows. Only `h`
is instantiated. The source word, `q,k`, coefficient space, marking, resolver,
and source exponent values are **not** selected or hashed.

The hash is SHA-256 of `GQ2-W361-FOX-TEMPLATE\0` followed by canonical sorted-key
JSON of the payload. This is a **symbolic template identity**, not a hash of an
instantiated certificate or of the Lean dependency closure. Declaration-name
metadata is not itself content-addressed proof provenance.

`scripts/w361_general_fox_tex.py` validates strict object keys and constructors,
literal integer types (rejecting Python booleans and floats), generator bounds,
alphabet/handle concordance, parameter roles, expected bridge metadata, and the
canonical hash. It renders the input/target full-cochain vectors and ordered
operations directly from the tree. All unlisted matrix columns are zero; no
handwritten sector formula supplies the rendered rows.

The importable API is `validate(envelope) -> payload`, `loads(text)`,
`from_lean(runner,h)`, `render_tex(envelope)`, `coeff_tex`, `row_tex`, and the
three packet fragments `input_rows_tex(profile)`, `operations_tex(profile)`,
`target_rows_tex(profile)`. A fragment receives a full, already-validated profile
dictionary, not merely its `tree` field.

An artifact-only check establishes syntax/hash/render agreement, **not** Lean
synchronization: a legal modified tree can be rehashed. The acceptance path is
`check --lean-runner`, which reruns Lean and compares the entire exported
envelope. This distinction is printed in checker results and artifact headers.
The 81 self-tests include malformed constructors, parameter-role corruption,
out-of-range wild indices, missing carried inverses, duplicate JSON keys,
Boolean/float integer substitutions, and an explicitly rehashed legal reversal
of noncommutative composition demonstrating this weak/strong boundary.

```sh
python3 scripts/w361_general_fox_tex.py self-test
python3 scripts/w361_general_fox_tex.py generate 4 --lean-runner /private/tmp/gq2-w360-lean.sh
python3 scripts/w361_general_fox_tex.py check generated/general-certificate-staged --lean-runner /private/tmp/gq2-w360-lean.sh
```

Generation is restricted to a separate `general-certificate-staged` directory.
Examples demonstrate executable synchronization only; rank-uniform coverage
comes from the Lean denotation and concrete certificate-binding theorems.

Verification recorded for this addition: the 81 self-tests and Python bytecode
check pass; `h=0` and `h=4` generation and subsequent independent Lean replay
match the complete exported envelopes. Their hashes are respectively
`ba0946aa20af5c0824507adb1de9e1f90ff5298676c4123df8ed58ed2b77e7b3` and
`2d37d38f6aa9e5f3c9febe98547f04b1cd22269645ca6a6d0754941268ca454f`.
The generated rank-four TeX also passes a standalone LaTeX syntax compilation;
final publication layout remains the surrounding packet renderer's task.
