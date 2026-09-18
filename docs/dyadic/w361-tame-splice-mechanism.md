# W361: one source construction for the general even-M problem

This note explains the rank-uniform construction. The shared field packet has since been
derived from the existing field bundles, and the assembled field equivalence preserves tame
and the full unramified character. The live verification and stronger-marking status is in
`w361-overnight-progress.md`; inherited local-field axioms have not been eliminated.

## Why a new word is necessary

The earlier frozen compact-M source has a genuine marking obstruction: its distinguished
C-coordinate cannot realize every selected field's actual unramified character. Changing a
marking on that same source does not remove the no-go theorems. W361 changes the source word.

Promoting a unit handle supplies the correct pro-2 core at strict M0 level. At positive Mpc
level the actual D-coordinate is a unit, for either epsilon sign and every handle rank. Both
cores can be normalized by a simultaneous wild shear. But the naive normalized hyperbolic
word can lose the ramified Stokes pairing. The finite diagnostic in
`scripts/w361_hyperbolic_action_diagnostic.py` demonstrates that defect for abstract row data;
it does not assert that those rows have been realized by a selected field.

The repair separates structural and analytic roles without separating nilpotency classes.

## The tame averaging splice

Let omega2 be the profinite exponent that is one at the 2-primary component and zero at every
odd-primary component. On the common generator alphabet define a substitution P by

```
P(sigma) = sigma
P(tau) = 1
P(wild_i) = (wild_i * tau)^omega2 * (tau^omega2)^(-1).
```

For a structural word R and a ramified template H put

```
Shadow(R) = substitute P into R
Splice(R,H) = Shadow(R) * H * Shadow(H)^(-1).
```

Here H is the established compact-M word on the same alphabet. The structural R is already
wild-normalized and prime-to-two tame-corrected. All statements quantify over the complete
handle rank; the construction is not a list of small-class corrections.

Three separate facts explain the splice.

1. On every pro-2 evaluation with tau=1, P is the identity. Hence Splice(R,H) evaluates exactly
   as R. The complete pro-2 presentation, not just an abelianized row, is preserved.
2. In a ramified simple elementary module, pass to the actual faithful head quotient. Wild
   base entries are one, and tau has odd order and no fixed vectors. Averaging kills the
   vector coordinates of each shadow wild lift. Its remaining central coordinate cancels
   because the relator has even wild exponents. Tame specialization kills the residual
   pure-sigma word. Consequently the splice evaluates exactly as H in the relevant lifted
   extension, on arbitrary cochains.
3. In the unramified branch, tau-normal cochains have zero tau coordinate. The pinned omega
   exponent is one modulo four. Shadow therefore preserves first and second coordinates,
   and H cancels its own shadow. The splice agrees with R on this normal subspace.

The structural statements live in `TameShadowWord`; the Heisenberg statements in
`TameShadowUnramified` and `Instances/TameShadowRamified`. Tame specialization and endpoint
parity are proved for the splice, rather than silently carried as new analytic assumptions.

## Why the finite resolver matters

One finite level N=4*exponent(C) works for every finite elementary coefficient over a finite
base group C. `OmegaPinnedLevelResolver` resolves every profinite word at the required lift
groups, pins omega2 to the nonnegative integer omega2Exp(N), and derives the 2-adic resolver
from the same profinite resolver. Thus coincident exponent nodes remain consistent.

The congruence omega2Exp(N)=1 modulo four controls central quadratic terms, not just parity.
The prime-to-two tame correction resolves to a multiple of four at this level. No global
integer display of an arbitrary 2-adic unit is assumed: `MpcSemanticUnramifiedStokes` supplies
an exact literal display at each particular finite resolver.

## Stokes is not yet the quadratic determinant

The Heisenberg comparison supplies the full finite-coefficient Stokes ladder. Action-image
devissage then handles arbitrary finite elementary coefficients, including the scalar case.
`UniformStokesSupply` packages this result independently of a presentation family.

Its common consumers provide finite generation, scalar H2 of order two, the scalar character
count, all four Stokes-certificate clauses, and corrected exact lifting. Together these give
`SourceAnalyticCoreRN`. No separate class-by-class proof enters these consumers.

The affine determinant additionally sees the quadratic factor set, including its diagonal.
Ordinary bilinear-pairing equality is insufficient. `TameShadowHessian` and its ramified
counterpart therefore repeat the comparison in the full extraspecial central extension.
The actual boundary datum descends through `blockProjF` with explicit identities for BOTH
factor-set components. Trivial action is never substituted for an unproved base-group
identity or an unproved factor-set descent.

`GammaRUniformWordTrace` and the two phase-seam modules identify the actual scalar obstruction
QZero with the resolved word trace, before and after this genuine descent.

## Normal coordinates on the changed source

The unramified phase has coordinates

```
(v0,v1) and h pairs (a_j,b_j),
```

with sigma, tau and the third core coordinate zero. Its quadratic form is

```
plusFormD(qbar,qbar)(v0,v1) + sum_j polar(qbar)(a_j,b_j).
```

For |V|=2^(2m), its Gauss sum is 2^((2+2h)m). The ramified phase reaches the same endpoint by
exchanging the two head coordinates. Both comparisons are uniform in h.

There are two important proof safeguards.

- Equality of the first differential is not asserted off the normal subspace. The tame row
  first kills tau; a coboundary kills sigma because sigma is fixed-point-free. Comparing on
  sigma=tau=0 then identifies the complete cocycle kernels. `SigmaNormalKernelTransport`
  makes this argument explicit.
- The raw structural word need not die in the original nonfaithful coefficient group. Only
  its chain-square identity is required, and that follows from its computed Fox row.
  `WordPhaseRawUnramifiedNormal` has no unnecessary raw-relator-death hypothesis.

The wild shear and tame correction disappear on normalized cochains. The semantic Mpc unit
and the promoted pair word have the same displayed compact phase there. Thus the checked
normal-form and QZero results apply to the ACTUAL new source, not to an unidentified old
source group.

## What this does and does not settle

The source-side pipeline is now word-generic: a normalized core, uniform Stokes supply and
actual branch-free phase supply produce complete flexible certificate leaves through
`GammaRUniformDeterminant`. Concrete boundary assembly is tracked in the progress note.

At selected M0 level zero the strict handle row gives exactly nu(U)=1. At positive selected
Mpc level, nu(D)=eta+2^r*w is a unit; its actual value is used, rather than pretending the
displayed eta is already exact. Zero-handle M0 has no strict-handle alternative and retains
the canonical C branch.

The output is a changed-word flexible certificate/residual. It is not a certificate at the
old frozen obstructed word. `FieldFamilySpliceFinal` discharges the compatible field packet
from the standing field bundles, and `FieldFamilySpliceTameCanonical` gives the bare
ramified-i field endpoint with literal tame and full-nu equations. Stronger prescribed
core/orientation compatibility is tracked separately in the progress note. Existing no-go
theorems and the established axiom census remain unchanged.
