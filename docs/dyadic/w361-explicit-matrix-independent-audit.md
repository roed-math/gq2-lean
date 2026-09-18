# W361 independent audit: explicit unramified Fox and polar matrices

2026-09-17. Read-only audit of the five Lean modules below, including their
actual-word and selected-source connections. No Lean source, frozen appendix,
owner decision, or ramified Fox artifact was changed.

**Verdict:** the advertised all-cochain unramified Fox identities and the
common-phase polar matrix identities are genuine. They do not infer equality of
full differentials from equality of kernels. The essential restrictions are the
finite, exponent-two, fixed-point-free unramified action profile and death of
the **actual changed** relator family. The polar artifact is a matrix for the
explicit normal-coordinate phase, relative to its coefficient-space pairing;
it is not by itself a congruence certificate for every source cochain or a
replacement for the full quadratic phase/Gauss calculation.

## 1. Independent verification

Each file was freshly checked with
`bash /private/tmp/gq2-w360-lean.sh <file>` against the campaign's dependency
cache, using the runner's ordinary Lean limits and strict implicit settings.
All five checks exited zero, with no diagnostics other than the requested axiom
prints:

| Module | Result |
| --- | --- |
| [SigmaNormalFoxElimination](../../GQ2/Dyadic/SigmaNormalFoxElimination.lean) | Three public pins, standard three axioms |
| [SigmaNormalFoxRows](../../GQ2/Dyadic/SigmaNormalFoxRows.lean) | Four pins, at most standard three |
| [SigmaNormalSpliceFox](../../GQ2/Dyadic/SigmaNormalSpliceFox.lean) | One pin, standard three |
| [TameSpliceFoxNormal](../../GQ2/Dyadic/Instances/TameSpliceFoxNormal.lean) | Both actual-word pins, standard three |
| [WordPhasePolarNormal](../../GQ2/Dyadic/Instances/WordPhasePolarNormal.lean) | Fourteen pins, at most standard three |

Here the standard three are `propext`, `Classical.choice`, and `Quot.sound`.
Inspection found no new axiom, placeholder, option override, or `native_decide`
in these files. Small finite coefficient identities use kernel-checked
`decide`. These checks re-elaborate the five sources, not the entire dependency
tree; the parent build is the separate integration check.

## 2. What the Fox matrix actually says

Write `d = heisD1 t w`, `S(a) = t.sigma • a`, and

```
U = S⁻¹,     D = 1 - S⁻¹,
L(a) = (d (Pi.single tau a)) 1.
```

The explicit row equivalence and its inverse are

```
E(z0,z1)    = (U⁻¹ z0, D⁻¹ (z1 - L(U⁻¹ z0))),
E⁻¹(a,b)    = (U a, L a + D b).
```

`rowElimination` checks both inverse identities and additivity.
`full_rows_of_normal` proves, for **every** cochain x,

```
d x = (U(x_tau), L(x_tau) + D(x_wild_j)).
```

Consequently `reduced_rows_of_normal` proves

```
E(d x) = (x_tau, x_wild_j).
```

In column order sigma, tau, wild_0, ..., wild_n, the original evaluated
operator matrix therefore has zero sigma column, first-row entry U at tau,
second-row entry L at tau and D at the selected wild column, and zero remaining
entries. The reduced matrix has identity entries precisely at tau and that wild
column. No input-column change is needed for this identity.

The proof uses an actual additive decomposition
`x = x_sigma + x_tau + x_normal`, not a statement about cocycles alone. Its
three inputs are the first-row formula, a zero sigma column, and the second-row
formula on sigma=tau=0. The latter restriction is sufficient **because** the
other two columns are separately established.

`sigma_column_zero` supplies the essential missing column honestly: when tau
and all wild letters act trivially, `d0(a)` is supported only at sigma and has
entry `S(a)-a`. Finite fixed-point-freeness makes this map onto. Thus
`d d0 = 0` implies that the entire sigma column is zero. Merely knowing that two
differentials have the same kernel would not justify this calculation, and is
not used here.

### The meaning of “explicit”

This is an exact operator-valued row reduction, not a displayed numerical
matrix after choosing a basis of A. `L` is the actual changed word's evaluated
tau derivative, a defined additive homomorphism; it is not assumed to equal the
raw word's coefficient 1. The modules do not expand L into a closed symbolic
group-ring expression.

Likewise, `oneSubInvAction` defines D exactly and constructs its inverse by
`AddEquiv.ofBijective`, using finiteness and fixed-point-freeness. This is a
checked inverse operator, but not a closed polynomial formula in S or a
printed inverse matrix in a selected basis. If an appendix requires the latter
format, that remains a display/computation requirement. It is not an unproved
invertibility premise.

Only `d1` is row-reduced here. The proof also identifies the image of `d0`, but
these files do not package a simultaneous basis change for the complete
cochain complex.

## 3. Exact hypotheses and actual-word specialization

`heisD1_reduced_of_normal` requires finite C and A, an additive C-action on A,
`a+a=0`, even q, trivial tau and wild **actions**, fixed-point-free sigma,
a resolver lifting to `WordLift A C`, the chain-square identity for the
supplied family, and its stated normal first-jet formula.

`normalizedCorrectedSplice_reduced_rows` supplies the normal comparison for

```
W = tameSplice
      ((subst (wildShearNielsen k).backward R) * (tau^z)⁻¹) H.
```

Its additional hypotheses are trivial action of every resolved sigma power
`sigma ^ E(padicOmega2(k_i))`, `E(omega2)=e` with `e % 4 = 1`, and actual
death in C of both resolved relators of `gammaFam n q W`. This death supplies
the chain-square identity via `heisD1_comp_heisD0`. **There is no raw R-death
hypothesis.** Nor does this theorem require actual tau/wild elements or those
sigma powers to equal one in the possibly nonfaithful group C. Action equality
is enough for the Heisenberg first-jet comparison.

The raw first-jet premise is not left assumed in the two public source
specializations:

* `pairSplice_reducedFox` applies to the literal
  `headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP` and discharges it by
  `foxD_headHandlePairCompactW_unram`.
* `mobileSplice_reducedFox` applies to the literal
  `tameSplice (mpcMobileTameCorrectedW ... eta ... nuP) (mCompactW alpha h)`.
  It first replaces the semantic unit display by its **exact finite resolved
  integer**, then uses `foxD_mpcW_unram_of_eq`. `pinned_eta_smul_eq_sigma`
  proves the resulting unit-head action is S; no rational approximation or
  unjustified replacement of eta by 1 is made.

Both use `omegaPinnedLevelZhatResolver` and its coherent Z2 companion at
`4 * exponent(C)`. The resolver is independent of A; its lifting property for
`WordLift A C` is proved from A's exponent-two condition. Both reduce at
`wild (x2Idx h)`, not at the promoted handle.

Their remaining representation hypotheses are exactly:

1. finite exponent-two A, trivial tau/wild actions;
2. fixed-point-free sigma and trivial action of `powOmega2 sigma`;
3. death of the **actual pinned family** at the supplied marking.

They are uniform in rank and continuous normalization parameters. The pair
requires a genuine `j : Fin h`; it says nothing about a nonexistent handle at
h=0. The mobile theorem allows every h and every semantic unit, with no rank,
class, or rational-unit cutoff. Its Fox statement needs only `1 ≤ alpha` and
does not additionally require positive r or a selected head-charge relation.
The stronger field-selection constraints are supplied elsewhere.

### Restrictions that must not disappear in prose

“Unramified nontrivial” must not be interpreted as an arbitrary unramified
module: a reducible module can have sigma-fixed vectors, and even a
fixed-point-free finite action need not have trivial two-primary sigma action.
The two-pivot reduction does not cover the nonzero scalar/trivial-action
branch, where D is zero. Nor does it give a universal invertible row operation
over the abstract group ring, independent of the coefficient representation.

At the actual nontrivial minimal-block boundary these are discharged, rather
than new arithmetic assumptions. In
[WordPhaseHeadProfiles](../../GQ2/Dyadic/Instances/WordPhaseHeadProfiles.lean),
`head_cyclic_of_unramified`, `head_sigma_fixedPointFree`, and
`head_sigma_omega_eq_one` prove the profile in the faithful head. The existing
pair/mobile unramified comparisons pull it back to the possibly nonfaithful
lower group. Actual family death there follows from `lower_rel` and the pinned
resolver applied to the representation of `GammaR`; raw death is unnecessary.

## 4. Connection to the selected words

The source wrappers are not calculations at abandoned raw ancestors. Their
word expressions are the constructors retained by
[SelectedWordProfile](../../GQ2/Dyadic/Instances/FieldFamilySpliceSelectedWord.lean).
For M0's changed-word alternative the profile retains the same h, alpha, q,
j, nuP and literal word, together with the unit-U condition. For Mpc it retains
the same mobile constructor at the actual unit etaD and actual nuP, with
`nuP(D)=etaD` after the stated coercion and
`etaD = selectedEta + 2^r*w`. The matrix theorem already quantifies over
arbitrary eta, so this congruence introduces no analytic specialization gap.

The selected-word final record preserves this profile through realization
calibration. A matrix assertion for an arbitrary instance of that record can
therefore be transported using its degree equality and word `HEq`. The five
audited files do not themselves provide that final dependent-transport wrapper
or a boundary-frame wrapper invoking the new row theorem. This is a small
interface/appendix integration task, not an unproved raw-to-actual comparison.
The pre-existing complete source certificates do not depend on these new
presentation artifacts; their analytic and determinant proofs are separate.

## 5. The polar matrix is literal, with the right interpretation

For `B = polar q`, the phase being certified is exactly

```
Q(c0,c1,(uj,vj)) = q(c0) + B(c0,c1) + sum_j B(uj,vj).
```

`polar_compactPhase_reducedMatrix` proves the full finite double-sum formula
for its polar form with index `Fin 2 ⊕ (Fin h × Fin 2)`. The head coefficient
matrix is `[[1,1],[1,0]]`, each handle coefficient matrix is
`[[0,1],[1,0]]`, and every off-block entry is zero. Both products with the
displayed full inverse are proved for every h, including zero.

Each coefficient multiplies B. No basis of V, identification of B with the
identity, or invertibility of a chosen Gram matrix is silently assumed.
`polarBlockEquiv` is the explicit additive coordinate operator

```
J(c0,c1,(uj,vj)) = (c0+c1,c0,(vj,uj)),
J⁻¹(d0,d1,(aj,bj)) = (d1,d0-d1,(bj,aj)).
```

The factorization through the coordinatewise B-pairing is proved exactly.
Nonsingularity additionally and explicitly requires `Nonsingular q`; inversion
of the scalar coefficient matrix alone would not suffice if B were singular.
The identities require `IsQuadraticFp2 q` and an additive commutative V, with
no finiteness or positivity-of-h requirement.

This is not the assertion that Q is a sum of purely hyperbolic quadratic
functions: the term `q(c0)` is retained. In characteristic two, a polar matrix
does not determine a quadratic function or its Gauss sign. The full phase
equalities and the cardinality-dependent Gauss calculation remain necessary.

Those connections exist in
[EvenMHeadHandlePairUnramifiedComparison](../../GQ2/Dyadic/Instances/EvenMHeadHandlePairUnramifiedComparison.lean),
[MpcMobileUnramifiedComparison](../../GQ2/Dyadic/Instances/MpcMobileUnramifiedComparison.lean),
their boundary comparison modules, and the two
`wPh_compactWallHandlePhase_gaussSum_standard*` theorems in
[WordPhase](../../GQ2/Dyadic/Instances/WordPhase.lean). They establish the actual
source's full normal-coordinate phase and Gauss value, not merely its polar
form. The mobile extra factor-set term is removed using actual projected
sigma-two-part equality, not just equality of coefficient actions.

One interface distinction matters for publication: `SourceWordPhaseComparison`
in [GammaLDeterminantBridge](../../GQ2/Dyadic/Instances/GammaLDeterminantBridge.lean)
stores an ordinary `Equiv` and pointwise phase equality, explicitly not an
`AddEquiv`. This is enough for Gauss reindexing. On its own it does **not**
assert a linear congruence of the original source quotient's polar form. The
actual pair/mobile constructions use the explicit coordinatewise normal map
`wPmCompactPhaseNormal`; its formulas support an additive normal-coordinate
bridge. If the appendix claims such a source-H1 matrix congruence, that
additivity/transport should be packaged and cited rather than inferred from
an arbitrary phase-preserving bijection. This qualification does not affect
the already proved determinant statements.

## 6. Remaining scope and acceptance work

**Subsequent checked strengthening (same session):** the additive-coordinate
interface noted above has now been closed in two additive modules, without
editing any of the five audited modules.
[WordPhaseAdditiveNormal](../../GQ2/Dyadic/Instances/WordPhaseAdditiveNormal.lean)
upgrades the exact original quotient and normal-form equivalences to
`AddEquiv`, proves additivity of `wPmCompactPhaseNormal`, and supplies
`phaseComparison_polar_reducedMatrix` as a literal source-polar congruence.
[WordPhaseSpliceAdditiveNormal](../../GQ2/Dyadic/Instances/WordPhaseSpliceAdditiveNormal.lean)
proves additivity of the existing named pair and common ramified comparisons
and constructs a stronger additive mobile comparison. It preserves every
original boundary/factor-set hypothesis. The generic module's eighteen pins
and the actual-word module's three pins are at most standard three, checked
under the same ordinary Lean settings. The warning about arbitrary phase
bijections remains logically necessary, but is no longer an outstanding
interface gap for these actual constructions.

No mathematical defect was found in the five audited declarations. The
remaining distinctions to preserve are:

* The new Fox artifact covers the indicated nontrivial unramified branch;
  scalar and ramified matrices are separate work. This audit does not approve
  or review the concurrent ramified Fox lane.
* L and D-inverse are exact evaluated operators, not expanded symbolic entries
  and inverse polynomials. A changed appendix format must say which kind of
  matrix certificate it accepts.
* The polar artifact concerns the actual reduced coordinate phase. The new
  additive bridge supplies its source polar-congruence; publications should
  cite that bridge, not infer linearity from the weaker stored phase equivalence.
* Connecting the new display leaves directly to the selected record and
  generated word tree is release plumbing still to be integrated. It is not
  evidence for the old frozen M word or automatic approval of a replacement
  appendix. The existing owner/editorial gate remains unchanged.

## 7. Independent follow-up: original-format Fox records

The later module
`GQ2/Dyadic/Instances/TameSpliceFoxCertificates.lean` was independently read in full and
recompiled under the default runner. It exits 0; all nine public axiom pins are exactly
standard three. No code was edited. This follow-up supersedes the historical missing-record
qualification above for the six concrete pair/mobile Fox producers, not for every other
appendix item or family.

**Carrier and resolver.** `foxJacobian_pinned_apply` identifies the original reflected
`foxJacobian` with the two coordinates of the actual resolved `heisD1`, on every cochain.
It uses `omegaPinnedLevelZhatResolver (4 * Monoid.exponent C)` and the linked two-adic
resolver on both sides. Crucially, its bridge invokes
`omegaPinnedLevelZhatResolver_fourMulExponent_wordLift`, not merely resolution in the
base group: the order bound for `WordLift A C` uses exponent-two coefficients. Thus the
old `evalFin` convention at omega2 is genuinely reconciled with the integer-resolved word
on the lift, including the semantic mobile exponent and normalization powers. A different
unrelated resolver is not admitted implicitly.

**Actual source binding.** The three `pairSplice_FoxCertificate_*` return
`FoxCertificate` whose matrix contains exactly
`headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP`. The three
`mobileSplice_FoxCertificate_*` contain exactly
`tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
  (mCompactW alpha h)`.
They do not substitute the old frozen M source. The mobile parameter is an arbitrary
`eta : Z₂ˣ`, with all `r,p,h`; the pair parameter `j : Fin h` excludes `h=0` automatically.
The common structural bounds are `1 ≤ alpha`, nonzero even `q`. These are first-order
certificate bounds, not an assertion that every stronger source theorem has the same bounds.

**What is replayed.** All three sectors carry genuine finite formal operation lists and
the original `FoxCertificate.verifies` equality, with two-sided inverses wherever required:

* Scalar: under exponent-two coefficients and **trivial action of every generator**, both
  input rows are literally the tau coordinate. The list is
  `[FoxRowOp.addSnd (FoxCoeff.neg FoxCoeff.one)]`, with no column operation. Its literal
  target is `(tau,0)`. It does not assert two independent pivots, and does not require
  actual relation death or actual trivial base elements. The proof is the direct endpoint
  exponent-sum calculation, not a chain-square inference without its hypotheses.
* Nontrivial unramified: finite coefficients, wild/tau actions trivial, sigma
  fixed-point-free, sigma's omega2 part acting trivially, and death of **both actual
  changed resolved relators** are explicit. Complete row equality transports
  `mCompactJacobianCertUnram`: one operation `wild += S*tame`, no column operations,
  target `nCompactUnramNormalForm h`, namely tau block `S^-1` and x2 block `1-S^-1`.
  This record is not itself the later identity-pivot scaling. The inverse of the second
  block follows from the explicit fixed-point-free premise; the polynomial inverse theorem
  is a separate strengthened display. No raw pair/mobile relator-death assumption appears.
* Ramified: finite projected head `D`, surjective `pi : C →* D`, action compatibility,
  **actual** `pi(t.x i)=1`, actual tame relation in `C`, tau fixed-point-freeness, and
  trivial action of tau's omega2 part are explicit. The shadow/splice transport gives
  complete differential equality with the compact template. The replayed record has no
  row operations and scales x2 by `S`, with inverse `S^-1`. Its target is the universal
  tame row together with the x2 unit pivot, **not** yet the separate sigma/x2 identity
  target of `TameSpliceRamifiedFoxNormal`. No relation-death premise is added here;
  the structural tame-specialization and endpoint premises of the common helper are
  discharged for each concrete source.

The projected-head condition in the last bullet is substantial and correctly retained:
trivial wild action alone was not substituted for actual projected wild base one. Likewise
the unramified proof retains actual changed-word death where it uses the chain relation.
No hidden stronger premise, detached word, scalar rank error, or matrix-carrier mismatch
was found. The original-format **Fox** packaging gap is closed for these profiles. Hessian
records, all-family coverage, synchronized generated displays, and owner acceptance remain
separate work; this result is not a claim that every appendix criterion is now satisfied.
