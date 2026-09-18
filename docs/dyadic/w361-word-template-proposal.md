# W361 staged symbolic word templates

Status: **STAGED tooling and proof interface, not an approved S1.1 migration.**

## Why an additive format is needed

The frozen S1.1 exponent grammar represents integers, omega-two, and rational
EtaHat displays. The new certified pair/mobile sources contain arbitrary
two-adic wild-shear coefficients, an arbitrary two-adic unit in the mobile
source, and a classically chosen prime-to-two profinite tame-correction
exponent. No finite rational display represents every such value. Rounding
them to a finite quotient would change the statement and cannot certify the
actual source word.

The frozen `RawWord.shadow` is also not the new `tameShadow`: the former has no
general Lean denotation and belongs to the old S4.2 contract; the latter is an
explicit, proved generator substitution. They must not be identified by a
printer convention.

## Proposed bounded implementation

New `GeneralTemplate*` modules provide a separate syntax with typed named
two-adic/profinite parameters, an exact environment-valued denotation into
`PWord`, and uniform bridges to the actual pair/mobile splice constructors.
The tree is the source of both JSON and TeX. Parameter values are mathematical
Lean environment values, never numerical approximations in JSON.

Discrete structural parameters (alpha, rank, mobile levels, selected handle)
are inputs to computable Lean tree factories. Their bridge theorems quantify
over all values. An emitted artifact instantiates these discrete parameters,
but retains the continuous exponent parameters symbolically. Thus a sample
artifact is a structural template instance, not a proof by checking a finite
class and not a single finite JSON tree encoding an unbounded handle rank.

The correction parameter is bound, in the Lean bridge, to the exact
`tamePrimeToTwoCorrectionExponent` used in the certified source. Its displayed
name is not evidence that an arbitrary assignment satisfies tame
specialization. The source certificate applies only after the stated binding.

New `w361_general_word*` tooling reads only this separate versioned envelope.
Its hash is domain-separated from S1.1 and binds the staged schema, actual
tree, alphabet rank, source family, and structural parameters. It never
updates the old hash manifest or fixtures. It must validate the complete tree,
including exact field sets and typed parameters, and refuse a supplied hash
that differs from the bytes it renders.

**This is a symbolic-template hash, not the hash of an instantiated profinite
word.** The mathematical environment values `q`, `nuP`, the actual unit `eta`,
wild coefficients, and correction exponent are not serialized or hashed.
Equal template hashes do not assert equal instantiated words at different
bindings. The stored binding/bridge declaration names are references, not
content addresses. Separate `.provenance.json` sidecars snapshot the SHA-256
of the five direct staged Lean modules and the renderer; this is not complete
transitive-build provenance.

## Implemented interface and verification

- `Word/GeneralTemplate.lean`: typed symbolic syntax, exact `PWord` denotation,
  substitution, semantic tame shadow/splice, and JSON traversal.
- `Word/GeneralTemplateM.lean`: computable uniform compact-M, pair, and
  arbitrary-unit mobile tree factories, with exact source syntax bridges.
- `Word/GeneralTemplateSplice.lean`: exact environments and the literal
  `denote_pairSplice` / `denote_mobileSplice` certified-source word equalities.
- `Word/GeneralTemplateEval.lean`: direct integer evaluator and its uniform
  equality with profinite evaluation at valid pinned finite levels. Correct
  finite resolution is proved, not replaced by a finite-precision assumption.
- `Word/GeneralTemplateExport.lean`: executable staged JSON emission from
  those trees. This is a tooling driver with `main`, not an umbrella import.
- `scripts/w361_general_word_tex.py`: strict parser, same-tree TeX/hash,
  source provenance, regression tests, and optional fresh Lean replay.

All five Lean modules compile at default limits with standard-three-or-less
axioms. The four generated structural examples live only in
`generated/general-template-staged/`; each retains symbolic continuous
parameters. Rank-zero mobile, both positive/zero `p`, and selected handles at
different ranks are tooling regressions, not the mathematical proof.

The **strong staged acceptance command** is:

```
export GQ2_W361_PACKAGES=/Users/roed/claude/gq2-paper/formalizations/gq2-claude/.lake/packages
python3 scripts/w361_general_word_tex.py check generated/general-template-staged \
  --lean-runner scripts/w361_lean_runner.sh
```

The runner path is local verification configuration, not an artifact premise.
The durable runner checks the pinned Lean version and exact package manifest and uses only
declared dependency artifact roots. Set `GQ2_W361_ARTIFACTS` to a completed fresh output root
to replay without any shared GQ2 cache. The workstation package path above is replaceable
by a manifest-matched package directory on another machine.
Without `--lean-runner`, `check` verifies artifact consistency and direct source
provenance only and explicitly reports `NOT Lean-synchronized`: a rehashed
arbitrary tree with the expected theorem-name string is not evidence that the
tree is produced by that theorem's factory. Strong mode compares the complete
envelope against fresh Lean emission and closes that tooling gap.

The CLI accepts natural structural arguments to quote the constructors. Such
arguments alone are not a source certificate. The exact bridge has its stated
`alpha >= 1`, nonzero even `q`, and environment-binding premises; the complete
analytic source theorems require `alpha >= 2` and the appropriate selected
structural hypotheses. Selected mobile use also supplies its actual D-unit
and `p = p epsilon r`; arbitrary CLI values do not assert those field facts.

## Non-claims and remaining acceptance work

This does not modify `Word/Export.lean`, `dyadic_word_tex.py`, the old fixtures,
the old manifest, or the frozen selection. It is not migration authorization
and does not activate a new merge gate. The existing D4 check says nothing
about the new splice artifacts.

The ledger's ten-item acceptance appendix remains a separate deliverable:
syntax, both specializations, evaluated Fox Jacobian, invertible operations,
normal matrix, Stokes identity, Hessian, quadratic change of variables, affine
phase cover, and the tree/TeX hash link. A compositional presentation of those
proofs may be appropriate for splicing, but an equivalent appendix format
requires owner acceptance; a hash alone does not discharge it.

Authority: `docs/dyadic/plan.md` A1 and merge gate 7;
`docs/dyadic/tickets.md` WW5 wave-2 mismatches (arbitrary `z2pow` requires a
migration note); `refs/dyadic-presentations-formalization-ledger.md` section 7.
