# W361 parametric pair/mobile certificate appendix

**STAGED compositional appendix, 2026-09-17. Not an approved replacement
format and not generated TeX.** This gives all ten ledger items uniformly for
the new pair and mobile source constructors. It does not fill or approve the
old frozen appendices or assert equality to the old M words. The cited Lean
producers now instantiate the **original** `FoxCertificate`,
`HessianCertificate`, and `PhaseCoverCertificate` structures, including full
identity-pivot Fox records with literal inverse coefficients. This document
explains those checked records; it is not itself their generated export.
The final section identifies the current synchronization boundaries.

**15:44 UTC refresh:** the separate staged packet generator now supplies four
ten-item specimens, checked by strong Lean replay and adversarial mutation tests.
The 29-page review PDF has passed complete visual QA. This hand-authored appendix
remains explanatory prose; the generated packets do not independently prove that
prose, prescribe expected theorem types, or serialize the whole source quotient
map. **Final 17:30 UTC update:** the fixed 1,541-module clean build and complete
source-bound replay passed, with an independent post-replay recheck. See
`w361-final-verification.md`, `w361-staged-pdf-qa.md` and
`w361-certificate-packet-independent-audit.md`.

## Parameters, source identity, and conventions

Fix `alpha ≥ 2`, `h : Nat`, nonzero even q, and
`nuP : DM alpha h →ₜ* Ztwo`. Set `n=2+2*h` and
`H=Words.MCompact.mCompactW alpha h`. Coefficient modules and finite target
groups are universally quantified **after** these source data are fixed.

The pair family additionally has `j : Fin h`. Its complete core certificate
requires `nuP(U_j)=ztwoOne`. The mobile family has `r,p : Nat` and an arbitrary
unit `etaD : Z₂ˣ`; its complete normalized core certificate requires
`ztwoIota(nuP(D))=ofAdd etaD`. In the selected positive branch, selection
supplies `r≥1`, `p=epsilon*2^(r−1)`, and
`etaD=selectedEta+2^r*w`. It does not supply equality to selectedEta.

Let `Rraw` be `headHandlePairCompactW alpha j` for the pair and
`mpcWUnit alpha r p etaD h` for the mobile family. Let C denote the respective
`headHandlePairCorePresentation` or `mpcCorePresentationUnit`, and put

```
k_i = toAdd (ztwoIota (nuP (C.mark (wild i)))),
Rnorm = subst (wildShearNielsen k).backward Rraw,
Rcorr = Rnorm * (tau^kappa)^(-1),
W = tameSplice Rcorr H.
```

The backward shear is `wild_i ↦ wild_i * sigma^(padicOmega2 k_i)`; sigma and
tau are fixed. `kappa` is exactly the constructor's
`tamePrimeToTwoCorrectionExponent`, bound using that normalized word's tame
defect. It is not a free formal parameter when claiming a certificate.

The shadow substitution is

```
sigma ↦ sigma,  tau ↦ 1,
wild_i ↦ (wild_i*tau)^omega2 * (tau^omega2)^(-1),
Splice(R,H) = Shadow(R) * H * Shadow(H)^(-1).
```

These define the literal sources `headHandlePairSpliceW ... j nuP` and
`tameSplice (mpcMobileTameCorrectedW ... etaD ... nuP) H`. Pair h=0 has no j;
mobile h=0 is allowed. The selected M0 h=0 alternative is the separate
canonical source. All assertions below concern `GammaR n q W`, including its
pro-2 wild-normal-closure condition, not the bare two-relator group.

## 1. Exact syntax tree

The typed AST factories are `GeneralTemplate.pairSplice alpha j` and
`GeneralTemplate.mobileSplice alpha r p h`. `pairEnvironment` and
`mobileEnvironment` bind k, etaD and kappa exactly as above.
`denote_pairSplice` and `denote_mobileSplice` prove literal `PWord` equality
with the certified constructors for every permitted structural parameter,
not merely equality on a finite collection of target groups.

Source: [GeneralTemplateSplice](../../GQ2/Dyadic/Word/GeneralTemplateSplice.lean),
with raw factories in [GeneralTemplateM](../../GQ2/Dyadic/Word/GeneralTemplateM.lean).
Two-adic and profinite leaves are separately typed. The tree is finite for
each structural input and retains exact symbolic continuous parameters; it
does not encode them by decimal digits or bounded residues.

The family theorem, rather than the four emitted sample trees, supplies
rank-uniformity. `SelectedWordProfile` pins this same word, core and nuP in
the field endpoint; realization calibration leaves them unchanged.

## 2. Both specialization reductions

On a pro-2 target with tau=1, shadow fixes each generator, so
`eval_pro2_tameSplice` gives `eval W = eval Rcorr`. The prime-to-two
correction evaluates to one, and backward Nielsen normalization transports
the full core presentation. The complete results are
`flexibleCore_headHandlePairSplice` and the mobile normalized/core splice
construction, not only a check that a single relation dies.

On the canonical tame marking, `Rcorr` has its full tame defect removed;
`tameSpecializes_tameSplice` combines its specialization with H's.
The actual family results are `headHandlePairSpliceW_specializes` and
`mpcMobileTameCorrectedW_specializes` followed by the generic splice theorem.
The normalized head-unit equations are still required for the complete core
certificate; syntax equality or tame specialization alone does not discharge
them.

Anchors: [TameShadowWord](../../GQ2/Dyadic/TameShadowWord.lean),
[EvenMHeadHandlePairSpliceSupply](../../GQ2/Dyadic/Instances/EvenMHeadHandlePairSpliceSupply.lean),
[MpcMobileNuSource](../../GQ2/Dyadic/Instances/MpcMobileNuSource.lean), and
[MpcMobileSpliceBoundary](../../GQ2/Dyadic/Instances/MpcMobileSpliceBoundary.lean).

## 3. Evaluated Fox Jacobian, with exact profiles

At a finite marking t in C use the coefficient-independent pinned resolver
at `N=4*exponent(C)` and coherent Zhat/Z2 exponents. Let A be an exponent-two
additive C-module, S and T its sigma/tau actions, and `x₂` the cochain at
`wild (x2Idx h)`. The two-relator first differential is on **all cochains**.

| Profile | Row zero | Row one |
| --- | --- | --- |
| All generator actions trivial | `x_tau` | `x_tau` |
| Finite A; wild/tau actions trivial; S fixed-point-free; sigma's two-primary action trivial | `S⁻¹ x_tau` | `x_tau + (1−S⁻¹)x₂` |
| Finite ramified projected profile below | `S⁻¹(T−1)x_sigma + (S⁻¹−N_q(T))x_tau` | `−S⁻¹ x₂` |

Every omitted column is zero. Here `N_q(T)=sum(i<q) T^i`, with composition
order as written. The second profile additionally requires actual death of
the pinned changed-word family. No raw-word death is assumed. Scalar rows
need neither relator death nor fixed-point-freeness.

The ramified profile consists of finite C,A and a finite surjective projected
head `pi:C→D` with compatible action, wild generators mapping to one in D,
the actual tame relation at q, tau fixed-point-free, and its two-primary
action trivial. It does not restrict sigma to be trivial or odd. The actual
structural words supply the generic theorem's tame-specialization and pinned
endpoint premises. The quotient projection is explicit; action-trivial
elements are not silently set equal to one in C.

Actual-word row anchors:
[TameSpliceScalarFoxNormal](../../GQ2/Dyadic/Instances/TameSpliceScalarFoxNormal.lean),
`pairSplice_scalar_rows`, `mobileSplice_scalar_rows`;
[TameSpliceUnramifiedFoxRows](../../GQ2/Dyadic/Instances/TameSpliceUnramifiedFoxRows.lean),
`pairSplice_unramified_rows`, `mobileSplice_unramified_rows`;
[TameSpliceRamifiedFoxNormal](../../GQ2/Dyadic/Instances/TameSpliceRamifiedFoxNormal.lean),
`tameSplice_ramified_rows` and its pair/mobile specializations.
The unramified tau entry is proved to be identity by
`compactSplice_tauColumn`, not left as an unknown entry or inferred from
kernel equality.

These are the relevant simple-action profiles used by the analytic assembly,
not a claim that every nonsplit coefficient module has the same reduced
matrix. Item 6 supplies the general-module extension argument.

The original carrier is now explicitly linked to these equations:
`TameSpliceFoxCertificates.foxJacobian_pinned_apply` identifies the original
`foxJacobian` with both coordinates of this `heisD1`, using resolution at the
**WordLift** level at `4*exponent(C)`. Thus the original records below verify
the actual evaluated Fox matrix, not a separately postulated matrix with the
same kernel. Their result types contain the actual W and both pinned resolvers.

## 4. Invertible row/column operations

All operations below are now lists in the unchanged original
`FoxRowOp`/`FoxColOp` grammar, with invertibility witnesses and complete replay
in a `FoxCertificate`. Their evaluated additive-equivalence identities also
remain available. No CAS equality is trusted.

**Scalar.** Replace row two by row two minus row one. The inverse adds row
one back. No column operation is used.

**Nontrivial unramified.** Put `U=S⁻¹`, `D0=1−S⁻¹`.
First apply U⁻¹ to row one, then subtract that new row from row two, then
apply D0⁻¹ to row two. Equivalently

```
E(z0,z1) = (S z0, D0⁻¹(z1 - S z0)),
E⁻¹(a,b) = (S⁻¹ a, a + D0 b).
```

There is no column operation. Write `m=2k+1` for the order of the actual sigma
action permutation. The inverse pivot is the finite polynomial
`P_S=sum(j<k) S^(-(2*j+1))`. Trivial two-primary action implies m odd, even
if sigma has even order in C. Both `P_S D0=1` and `D0 P_S=1` are proved.
`unramIdentityOps` is the literal three-operation list, with the last scale
carrying `unramPivotCoeff = 1-S⁻¹` as its formal inverse.

Precisely, `oddPowerCoeff g sign 0 = .zero` and
`oddPowerCoeff g sign (k+1) = .add (oddPowerCoeff g sign k)
(.atom (.gen g (sign*(2*k+1))))`. Here `sign` is an integer exponent.
Only the old coefficient constructors and integer-power generator atoms are
used; there is no opaque inverse atom or new coefficient constructor. The
length is `sigmaActionHalfPeriod = orderOf(sigma action)/2`, not an externally
assumed odd ambient order. `oneSubInvAction_symm_eq_actionPolynomial` connects
this same polynomial to the inverse in the earlier row equivalence.

**Ramified.** Put `U=S⁻¹(T−1)`, `L=S⁻¹−N_q(T)`, `D0=−S⁻¹`.
Precompose by the column shear
`x_sigma ↦ x_sigma−U⁻¹ L x_tau`, leaving all other coordinates unchanged;
its inverse uses plus. Scale the two resulting rows by U⁻¹ and D0⁻¹.
Here `U⁻¹=(T−1)⁻¹ S` and `D0⁻¹=−S`; finite fixed-point-freeness supplies
the checked inverse of T−1. More explicitly, write the actual tau action order
as `2k+1` and put `P_T=sum(j<k) T^(2*j+1)`. Then `U⁻¹=P_T ∘ S`:
**S is applied first. No S/T commutation is assumed or used.** Both inverse
products are checked, retaining this order.

`ramifiedIdentityColOps` contains exactly the transvection
`.transvect .sigma .tau (.neg (.comp Uinv Lcoeff))`;
`ramifiedIdentityRowOps` contains the two scales by `Uinv` and `D0inv`,
carrying U and D0 as their inverse expressions. `normPowerCoeff` recursively
encodes `N_q(T)` using powers `0,...,q−1`; `oddPowerCoeff .tau 1 k` encodes
P_T. Addition, negation and composition are the existing grammar operations.
The distinct-generator witness sigma≠tau makes the shear invertible without
an additional premise. The polynomial length is
`tauActionHalfPeriod = orderOf(tau action)/2`.

The zero coefficient module is allowed: its action order is one and the
empty polynomial is the identity endomorphism of the zero group. These are
finite formulas derived uniformly from the coefficient action, not a list of
rank- or field-class computations.

Anchors: `scalarRowElimination`,
[SigmaNormalFoxElimination.rowElimination](../../GQ2/Dyadic/SigmaNormalFoxElimination.lean),
[SigmaNormalFoxPolynomialInverse](../../GQ2/Dyadic/SigmaNormalFoxPolynomialInverse.lean),
and [SigmaRamifiedFoxElimination](../../GQ2/Dyadic/SigmaRamifiedFoxElimination.lean),
`columnShear`, `rowScaling`. The original record/list implementations are
[TameSpliceFoxCertificates](../../GQ2/Dyadic/Instances/TameSpliceFoxCertificates.lean),
[TameSplicePolynomialFoxCertificates](../../GQ2/Dyadic/Instances/TameSplicePolynomialFoxCertificates.lean),
and [TameSpliceRamifiedPolynomialFoxCertificates](../../GQ2/Dyadic/Instances/TameSpliceRamifiedPolynomialFoxCertificates.lean).

## 5. Reduced matrices

Scalar: `[x_tau,0]`; nontrivial unramified: `[x_tau,x₂]`; ramified after the
displayed column shear: `[x_sigma,x₂]`. Thus each indicated pivot is identity
and all remaining columns vanish. The actual pair/mobile `*_reducedFox`
theorems prove these equations on all cochains. The following original
record producers now package the formal replay and literal target as well:

| Sector | Pair record | Mobile record |
| --- | --- | --- |
| Scalar | `pairSplice_FoxCertificate_scalar` | `mobileSplice_FoxCertificate_scalar` |
| Nontrivial unramified | `pairSplice_FoxCertificate_unramified_identity` | `mobileSplice_FoxCertificate_unramified_identity` |
| Ramified | `pairSplice_FoxCertificate_ramified_identity` | `mobileSplice_FoxCertificate_ramified_identity` |

Their targets use `FoxRowNormalForm.single` at the displayed generators (and
the literal zero second row in the scalar case). They retain exactly the
profiles in item 3: actual changed-word death in the unramified sector;
explicit projected head, tame relation and tau hypotheses in the ramified
sector; no death premise in the scalar sector. Ramified records do not add
raw or changed wild-relator death. The older non-`_identity` unramified and
ramified records remain valid, but stop at their earlier operator-block
targets; they should not be confused with the fully reduced records here.

## 6. Stokes chain identity and extension to all coefficients

`uniformStokesSupply_headHandlePairSplice` and
`mpcMobileTameSplice_uniformStokesSupply` supply the fixed finite resolver,
endpoint, and full `StokesDuality` for every finite elementary coefficient
module pushed from a representation of the actual `GammaR`.
The natural chain identity and induced cohomology maps are part of that
interface. The action-image/simple-branch arguments feed the proved
composition-series exact-diagram extension; equality of dimensions on simple
modules is not substituted for this step.

Sources: [EvenMHeadHandlePairSpliceSupply](../../GQ2/Dyadic/Instances/EvenMHeadHandlePairSpliceSupply.lean),
[MpcMobileSpliceSupply](../../GQ2/Dyadic/Instances/MpcMobileSpliceSupply.lean),
[TameSpliceActionImage](../../GQ2/Dyadic/Instances/TameSpliceActionImage.lean),
and [GammaRUniformStokesSupply](../../GQ2/Dyadic/Instances/GammaRUniformStokesSupply.lean).
The lower-group relator death used in item 3 is discharged by the actual
representation and resolver, not an extra field hypothesis.

## 7. Full extraspecial Hessian, not just polarization

Let `dat` be the actual equivariant factor set, `q0` its quadratic form and
`B=polar q0`. Normal offsets have sigma=tau=x₂=0, core coordinates c₀,c₁,
and arbitrary handle pairs `(u_j,v_j)`.

In the unramified faithful projected head, the pair's **full central
extension evaluation** is the central inclusion of

```
Qplus = q0(c0) + B(c0,c1) + sum_j B(uj,vj).
```

This is `hessEvalZ_headHandlePairSplice_normal`, with scalar-coordinate
corollary `hessRelZ_headHandlePairSplice_normal` in
[EvenMHeadHandlePairSplicePhase](../../GQ2/Dyadic/Instances/EvenMHeadHandlePairSplicePhase.lean).
The hypotheses about resolved sigma powers here are actual equalities in the
projected group, stronger than trivial coefficient action. The boundary
profile and exact pinned transport prove them where consumed.

For mobile, the raw semantic formula initially contains the extra charge
`dat.m ((s^E(omega2))^p) c0`. It is kept until actual `s^E(omega2)=1` and
factor-set normalization remove it.
`hessRelZ_mpcMobileTameSplice_unramified_compactPhase` in
[MpcMobileUnramifiedPhase](../../GQ2/Dyadic/Instances/MpcMobileUnramifiedPhase.lean)
then gives Qplus for the actual normalized, corrected and spliced word.
There is no argument that a vanishing polar contribution alone kills this
quadratic/linear charge.

On the ramified projected head, the shadow terms are identity in the full
extraspecial extension; `hessEvalZ_tameSplice_ramified` in
[TameShadowHessianRamified](../../GQ2/Dyadic/TameShadowHessianRamified.lean)
reduces W to H. Its honest normal phase is
`Qram=q0(c1)+B(c0,c1)+sum B(uj,vj)`. The factor set descends by explicit
`hf` and `hm` equalities. Faithfulness of the module alone is not used to
descend an arbitrary central extension.

The continuous source obstruction is connected to this computation by
`UniformStokesSupply.QZero_eq_pinned_projectedHessian_of_tameNormal` in
[GammaRUniformProjectedPhaseSeam](../../GQ2/Dyadic/Instances/GammaRUniformProjectedPhaseSeam.lean),
with resolution at four times the exponent of the **original graph group**.
It is not silently replaced by a smaller projected-group resolver.

## 8. Actual quadratic coordinates and polar matrix

`wPmCompactPhaseNormal` is the coordinatewise additive normal cochain map.
Actual pair/mobile comparisons prove its cocycle condition and unique
representative property modulo coboundaries. In the ramified case the final
head swap `(c0,c1)↦(c1,c0)` carries Qram to Qplus; handles are unchanged.

[WordPhaseAdditiveNormal](../../GQ2/Dyadic/Instances/WordPhaseAdditiveNormal.lean)
upgrades the original quotient/H1 and normal-coordinate maps to additive
equivalences without changing their underlying functions.
[WordPhaseSpliceAdditiveNormal](../../GQ2/Dyadic/Instances/WordPhaseSpliceAdditiveNormal.lean)
proves this for the actual named pair/common ramified comparisons and
constructs an additive mobile comparison witness. Its formulas imply
linearity over F₂ on these exponent-two spaces; an arbitrary phase-preserving
bijection is not used as evidence of linearity.

This is now packaged in the original Hessian record.
`WordPhaseCompactCertificates.fp2LinearEquiv` gives the same additive map a
linear interpretation. `sourceCompactHessianOfComparison` derives the local
F₂ module structures and finite dimension, preserves the actual phase map as
`cov`, and takes its full quadratic identity as `cov_eq`. The concrete
adapters in
[TameSpliceHessianCertificates](../../GQ2/Dyadic/Instances/TameSpliceHessianCertificates.lean)
are `pairUnramifiedHessian`, `pairRamifiedHessian`,
`mobileRamifiedHessian`, and `nonempty_mobileUnramifiedHessian`.
The mobile unramified result is explicitly `Nonempty` of the original record,
using its proved additive comparison witness; it does not assert that every
arbitrary phase-preserving equivalence is additive.

These adapters retain the projected-boundary hypotheses: the actual finite
quotient rho, compatible source action and wild-two condition, an equivariant
factor set `base`, action-compatible pi, the **separate** `hf` and `hm`
factor-set descent equalities, and surjectivity of the semidirect-product
projection. In the unramified branch they also require projected tau/wild
equal to one, sigma fixed-point-free, and actual projected
`powOmega2(sigma)=1`. In the ramified branch they require projected wild=1,
odd projected tau order and tau fixed-point-freeness. The named pair/mobile
ramified adapters discharge the common adapter's uniform Stokes,
tame-specialization and pinned-endpoint arguments from those actual words.
There is no new assumed normal form, matrix, Gauss sum or cardinality premise.
These phase profiles are stronger than merely matching coefficient actions;
the existing boundary producers derive them where the records are used.

Relative to B, the full polar coefficient matrix is block diagonal:

```
head = [[1,1],[1,0]], inverse head = [[0,1],[1,1]],
each handle = [[0,1],[1,0]] = its own inverse.
```

The index is `Fin 2 ⊕ (Fin h × Fin 2)`. `polar_compactPhase_reducedMatrix`
proves the full double-sum identity, and both inverse products are checked.
`phaseComparison_polar_reducedMatrix` transports it to the source quotient
using the additive coordinates. B itself is not assumed to be the identity
matrix. Nonsingularity uses `Nonsingular q0`; quadraticity and the full value
formula are separately proved. Sources:
[WordPhasePolarNormal](../../GQ2/Dyadic/Instances/WordPhasePolarNormal.lean)
and the additive modules above.

For `|V|=2^(2m)`, the full Qplus Gauss sum is `2^((2+2h)m)` by the separate
`wPh_compactWallHandlePhase_gaussSum_standardRam`/`standardUnram` theorems.
The sign agreement follows from even degree, not merely nonsingularity.

For comparison with an arbitrary quadratic diagonal, the additional
[WordPhaseWallHandlePolarInverse](../../GQ2/Dyadic/Instances/WordPhaseWallHandlePolarInverse.lean)
constructs the unique operator L satisfying `B_d0(v,w)=B_q0(Lv,w)` from
finite nonsingular polar duality. The actual head is then
`[[L,1],[1,0]]`, with inverse `[[0,1],[1,−L]]`, and handles swap; both literal
endomorphism-matrix products and the full pairing factorization are proved.
No supplied-adjoint premise remains in `canonicalWallPolarEquiv`. For the
present pair/mobile Qplus, `d0=q0`, L=1, and this recovers the block above.
This general polar inverse does **not** authorize replacing a different
diagonal by q0 or discarding a linear/affine phase term.

## 9. Affine phase-cover interface

The actual boundary producers quantify over the recursion frame, minimal
block, nonzero radical-cover character and compatible boundary lift. They
derive the projected-head/factor-set data and branch-specific phase
comparison internally. The public endpoints are

* `headHandlePairSplice_boundaryComparison`,
  `headHandlePairSplice_branchFreeSupply`,
  `headHandlePairSplice_determinant`, and
  `headHandlePairSplice_flexibleCertificateLeaves` in
  [EvenMHeadHandlePairSpliceBoundary](../../GQ2/Dyadic/Instances/EvenMHeadHandlePairSpliceBoundary.lean);
* `mpcMobileTameSplice_boundary_comparison`,
  `mpcMobileTameSplice_branchFreeSupply`,
  `mpcMobileTameSplice_determinant`, and
  `mpcMobileTameSplice_flexibleCertificateLeaves` in
  [MpcMobileSpliceBoundary](../../GQ2/Dyadic/Instances/MpcMobileSpliceBoundary.lean).

`UniformStokesSupply.determinant_of_branchFree` in
[GammaRUniformDeterminant](../../GQ2/Dyadic/Instances/GammaRUniformDeterminant.lean)
connects these to the actual RN affine determinant obligation. No determinant
premise or assumption of boundary-compatible equivalence with a frozen word
remains. This is more than equality of an unshifted Gauss sum.

The original affine-phase record is also now instantiated, independently of
that downstream packaging. In
[WordPhaseCompactCertificates](../../GQ2/Dyadic/Instances/WordPhaseCompactCertificates.lean),
`compactPhaseCover` has

```
j0(v)=((v,0),0),  j1(v)=((0,v),0),  diag(v)=dat.f(v,v),
baseDim=(h+1)*d,  baseSign=1,  where |V|=2^d.
```

It proves the endpoint cardinality and Gauss sum, the cross-polar identity
against `dat.f(v,w)+dat.f(w,v)`, and the **full** kappa-diagonal identity
`Qplus(j0(v))=dat.f(v,v)`. This exact `PhaseCoverCertificate` is the
`affinePhase` field of the source-QZeroBar Hessian records in item 8. The
dimension d is derived internally from the finite exponent-two coefficient
module in `sourceCompactHessianOfComparison`; it is not an extra word-source
premise. The original affine translation interface then applies to all polar
representatives, retaining their actual Q-values. Thus neither the original
Hessian-record interface nor its phase-cover field remains a record gap.

## 10. Same-tree TeX/hash and remaining synchronization

`GeneralTemplate.Tree.toJson` traverses the same typed tree used by denotation.
The strict staged renderer consumes this tree and produces TeX plus a
domain-separated hash. Strong validation re-emits the Lean factory and checks
the full envelope:

```
python3 scripts/w361_general_word_tex.py check generated/general-template-staged \
  --lean-runner /private/tmp/gq2-w360-lean.sh
```

The hash binds the **symbolic template**, structural arguments and named
bindings; it does not hash actual q, nuP, etaD, k or kappa values. Their exact
binding is a theorem-level obligation supplied in item 1. The sidecar records
direct staged-source bytes, not the full transitive build. Neither the four
structural fixture hashes nor their passing tests prove the general family;
the uniform Lean theorems do.

This document provides the parametric mathematical appendix content. The separate
`w361_certificate_packet.py` now combines exact word, Fox, phase and phase-cover
ASTs into ten synchronized sections for four structural specimens, with checked
input/signature/cover bridges and declaration transcripts. The original certificate
records exist as described above. This is stronger than the earlier word-only
export, but it is not an independent kernel proof of the generated exposition.
Approval is still needed for how the exposition and record displays meet the
amended appendix contract and for activating it for these changed sources.

### Remaining evidence and owner decisions

1. **Decide the accepted synchronization contract.** Four staged ten-item packets
   now bind the same word/Fox/phase/cover factories, with strong replay of all
   trees and cited declaration transcripts. Their editorial reductions and prose
   are not independently proved serialized objects. Item 8 does not encode the
   whole quotient coordinate map, and cited types have no separate expected-type
   specification. These limits must be accepted explicitly or the export enlarged;
   do not describe the old word-only limitation as the current state.
2. **Bind the verification envelope to a final tree.** Replay the record
   producers and theorem references together with that export, retain the
   actual finite-action/profile parameters (whose polynomial lists are not
   fixed source-word parameters), and run the full build, axiom and unchanged
   degree-one regression gates on the chosen integration tree. A symbolic
   template hash and direct-source sidecar are not a transitive-build hash.
3. **Owner/editorial decisions remain.** Approve the changed pair/mobile
   selection and theorem/appendix amendments; decide the accepted symbolic
   parameter and certificate-display format; authorize migration/gate
   activation and the final census/release steps. This appendix grants none
   of those approvals and does not supersede the frozen M appendices.

Within the stated pair/mobile profiles, no remaining Fox inverse, original
Hessian/phase-cover record, or full quadratic identity is identified as a
mathematical premise. The remaining generated artifact content is genuine
work, not merely an approval checkbox. Scalar Fox records should not be
misread as a separate scalar Hessian claim: the Hessian adapters address the
projected radical-cover branches, whose boundary coverage is supplied by the
existing branch-free proof.

### Dependency map and non-claims

```
selected exact profile → typed AST + exact environment → actual W
actual W → tame/core reductions + pinned universal Stokes supply
actual W + action profile → full Fox rows → invertible operations → normal cocycles
actual W + descended factor set → full Hessian → source QZero
normal cocycles + full phase → original linear Hessian + PhaseCover records
full Fox rows → original finite-polynomial Fox records → identity-pivot targets
all boundary frames/covers → branch-free supply → affine determinant → RN word certificate
```

No new arithmetic axiom, fixed-rank test, chosen nilpotency cutoff or changed
source word is introduced by this appendix. The underlying source proofs and
matrix/additive leaves have standard-three-or-less footprints; the complete
field theorem retains its separately documented foundational inputs.
Owner approval of the changed word selection, amended theorem quantifiers,
certificate format and migration remains outstanding. See
[acceptance readiness](w361-acceptance-readiness.md).
