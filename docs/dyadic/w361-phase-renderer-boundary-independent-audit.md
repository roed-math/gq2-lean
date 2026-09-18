# W361 independent audit: phase renderer and actual-boundary Hessian records

Status: **STAGED audit, 2026-09-17; passed after two parser fixes.** This is not
owner approval, migration of the frozen appendix, or a certificate for arbitrary
hand-authored JSON. No frozen artifact, old source word, or Lean proof was edited.

## 1. Renderer findings and fixes

Reviewed `scripts/w361_general_phase_tex.py` against the actual computable
`GeneralPhaseTemplate.compactPayload`, `Tree.toJson`, `Coordinate.toJson`,
`matrixJson`, and `envelope` in `GQ2/Dyadic/Word/GeneralPhaseTemplate.lean`.

Two validation defects were fixed in the renderer, with **no schema, CLI, hash,
filename, or valid-output change**:

1. Python's equality identifies `False` and `0`, and identifies `0.0` and `0`.
   Comparing the coordinate table to the canonical table therefore did not by
   itself enforce literal integer handle indices. Each coordinate is now checked
   by the strict coordinate validator before table equality.
2. A huge declared `h` could allocate its expected coordinate table before the
   input length was rejected. The supplied list length is now checked against
   `2+2*h` first. This adds no artificial rank restriction to the formal family.

The expanded built-in self-test passes **44 checks**. A separate bounded test
harness in a temporary directory passes **69 checks**, covering valid rank-zero,
one, and two exports; strict integer types; negative/out-of-range coordinates;
missing and additional fields; matrix dimensions and bit types; malformed trees;
nested duplicate keys; nonfinite JSON constants; hashes; filenames; TeX drift;
output-directory restriction; and the distinction between artifact-only and
Lean-replayed checking. Huge-rank testing used a tiny payload and `10^100`, not
large matrix allocation.

### Exact semantics checked

- The schema is `gq2.w361.quadratic-phase.v1.staged`. Envelope and nested object
  fields are exact, status remains `STAGED`, and duplicate JSON keys are rejected.
- Handle indices are actual natural numbers strictly below `h`; head coordinates
  carry no index. Coordinate order is exactly
  `head0,head1,handleU(0),handleV(0),…`.
- Both matrices are square of size `2+2*h`, with literal integer bits. The checker
  explicitly multiplies in **both orders** modulo two and compares to identity.
  Independent tests recomputed both products. The head blocks are respectively
  `[[1,1],[1,0]]` and `[[0,1],[1,1]]`, followed by handle swap blocks.
- These are coefficient matrices **relative to `B = polar(q)`**, not a choice of
  identity Gram matrix for the coefficient pairing or a reconstruction of `q`
  from its polarization.
- The TeX renderer traverses the exported tree. Its coordinate labels and ordered
  handle terms match the exact tree, including the explicit terminal zero. The
  rendered full phase contains the base quadratic value, not merely its polar
  form. A subsequent presentation-only update labels it `q_0(c_0)` to distinguish
  the coefficient quadratic form from residue cardinality `q`; hashes and schema
  are unchanged.
- The hash is SHA-256 of the exact canonical payload prefixed by the bytes
  `GQ2-W361-QUADRATIC-PHASE` followed by NUL. Python hashes and canonical JSON agree
  with the actual Lean envelope at all three tested ranks.
- Canonical files are `compact-phase-hH.phase.json` and
  `compact-phase-hH.phase.tex`. Check mode re-renders the TeX and rejects a
  noncanonical filename, including a leading-zero rank spelling.

The artifact-only validator deliberately does **not** prove that an arbitrary
well-typed tree or mutually inverse matrix pair is the advertised factory output.
For example, after recomputing its hash and TeX, replacing the phase by zero or
both matrices by identity passes structural checking. Both mutations are rejected
by `check --lean-runner …` as differing from the actual Lean tree. The artifact-only
success message explicitly says `NOT Lean-synchronized`. This distinction must
remain visible in any combined packet checker.

### Executed replay

All outputs were confined to
`/private/tmp/w361-phase-audit.CkdZ1V/general-certificate-staged` or sibling temporary
test directories. The durable runner was `scripts/w361_lean_runner.sh`, with
`GQ2_W361_PACKAGES` pointing to the matching paper dependency tree and
`GQ2_W361_ARTIFACTS` to the campaign artifact cache. Commands were:

```text
python3 scripts/w361_general_phase_tex.py self-test
python3 scripts/w361_general_phase_tex.py generate H \
  --lean-runner scripts/w361_lean_runner.sh --out TEMP/general-certificate-staged
python3 scripts/w361_general_phase_tex.py check TEMP/general-certificate-staged \
  --lean-runner scripts/w361_lean_runner.sh
```

`H=0,1,2` each generated and strongly replayed successfully:

| h | Exact template hash |
|---|---|
| 0 | `fc9c8a3ee507a372098e78739637ce8b27c809ab12bb296a4ab73936cd6d314f` |
| 1 | `e48eecf746e3bb42d6f28431b8d8ecfe5839d018b4afdd063e222254e28090cc` |
| 2 | `39744d51b2c2818f0c9bda2e72a04a36d870fae2279d9b5b97c2d1deb466f1a4` |

These are regression tests of executable synchronization, **not** the proof of
the arbitrary-rank family. That proof is `denote_compactPhase`, together with
`polar_denote_compactPhase` and the existing inverse-matrix theorems. Rank zero
is valid for this phase template even though the promoted-pair source itself
requires a supplied `j : Fin h`.

## 2. Actual-boundary Hessian wrapper

Independently read and freshly compiled
`GQ2/Dyadic/Instances/TameSpliceBoundaryHessianCertificates.lean` under default
campaign Lean options. Exit status zero, no warning; both public declarations
print exactly `[propext, Classical.choice, Quot.sound]`:

- `pairBoundaryHessian`;
- `mobileBoundaryHessian`.

Compared their complete inputs and boundary constructions with
`EvenMHeadHandlePairSpliceBoundary.headHandlePairSplice_boundaryComparison` and
`MpcMobileSpliceBoundary.mpcMobileTameSplice_boundary_comparison`, respectively.
No stronger premise was added. In particular:

- The source groups are still the **literal changed pair/mobile splice words**,
  with their actual source parameters and arbitrary handle rank. The pair keeps
  `j : Fin h`; mobile keeps the actual two-adic unit and `r,p` parameters.
- The input lift is still
  `BoundaryLiftsK (sourceBoundaryMapK tame pro2 compat) F …`, and the conclusion
  uses the **same** `rhoPrimeK` at the same descended radical data, not a new
  abstractly isomorphic source or newly chosen lift.
- The standing finite target/block, exponent-two elementary quotient, compatible
  tame/pro-two maps, canonical tame generator equations, nonzero coefficient
  module, nontrivial coefficient action, and nonzero radical character are
  retained exactly. Thus this theorem concerns the same nontrivial simple
  boundary branch, not the scalar branch without those hypotheses.
- `projectedHead_marking` derives actual projected wild base values equal to one.
  This is not the invalid inference from trivial coefficient action alone.
  `rhoPrimeK_surjective` derives the required `IsWildTwo`; quotient surjectivity
  and the factor-set descent equalities are proved inside the wrapper.
- The unramified branch derives actual projected tau equal to one, fixed-point-
  free sigma, and actual projected `powOmega2 sigma = 1` from the existing head
  profile theorems. The ramified branch derives odd actual tau order and its
  fixed-point-free action. No off-branch sigma restriction is smuggled into the
  ramified conclusion.
- The ramified call supplies the actual word's uniform Stokes theorem,
  specialization, and pinned-resolver endpoint internally. The unramified calls
  use `pairUnramifiedHessian` and `nonempty_mobileUnramifiedHessian`.
- `Fintype.ofFinite` is local instance bookkeeping, not a new finiteness
  assumption or a replacement of the coordinate equivalence.

The strengthened conclusion is `Nonempty (SourceCompactHessian … h)`, an
abbreviation for the **original `HessianCertificate`**, including a genuine
linear change of variables, its equality with the actual full descended
`QZeroBar`, quadraticity/nonsingularity, and the original affine phase-cover
record. It is not merely a polar congruence or equality of Gauss sums. The full
diagonal remains `DD.dat.f v v`, justified by the factor-set diagonal identity.

## 3. Remaining scope boundaries

No mathematical defect was found in the new boundary wrapper. Neither audit
changes the field theorem's `RamifiedIData` qualification, certifies a frozen
table word, approves the staged output format, or certifies a source-word hash
from the symbolic phase hash alone. A combined packet must still bind its exact
word/profile, phase comparison, operation records, and chosen export templates,
and must run strong Lean replay when claiming synchronization. The phase codec
currently exports the full phase and polar matrices; symbolic phase-cover fields
are a separate potential additive export, not silently present in this schema.
