# W361: compositional certificate map for the changed M sources

This is a staged acceptance companion, not an amendment of the frozen word table or a
claim that the old ten-item generated appendices are complete. Its purpose is to connect
the actual word constructors, checked structural transformations, and full affine phase
to the publication requirements in the ledger's §7. Exact unramified operator-matrix
artifacts, polar block matrices, and symbolic tree exports are checked alongside this map.
Scalar, nontrivial unramified, and ramified Fox specializations are now all checked, including
six concrete producers of the original `FoxCertificate` record for the actual pair/mobile words.
The additional identity-pivot reductions are now original records too: their finite action
polynomials are literal terms in the unchanged coefficient grammar. Original Hessian and
phase-cover records also retain each actual source's full quadratic phase.

## Scope and source identity

Both new families have degree `n = 2 + 2h`, with `alpha >= 2` and nonzero even residue
cardinality q. The pair family additionally has a genuine selected handle `j : Fin h`
whose normalized U-coordinate has nu-value one. The mobile family uses an arbitrary unit
`eta : Z2^x` at the actual D-coordinate. Field selection provides positive r and the
appropriate integer head charge `p(epsilon,r)`; the source analysis itself is uniform
in those discrete parameters. The zero-handle compact case is handled by the separately
proved canonical alternative, not by inventing a handle.

The actual constructors are:

```
pair:   headHandlePairSpliceW alpha h q halpha hq0 hqe j nuP
mobile: tameSplice (mpcMobileTameCorrectedW hq0 hqe alpha r p h eta halpha nuP)
                   (MCompact.mCompactW alpha h)
```

For either family the last operation is
`Splice(R,H) = Shadow(R) * H * Shadow(H)^(-1)`, where Shadow substitutes

```
sigma  -> sigma
tau    -> 1
wild_i -> (wild_i * tau)^omega2 * (tau^omega2)^(-1).
```

This is the semantic substitution in `TameShadowWord.lean`, not the unresolved `shadow`
constructor in the frozen S1.1 interchange grammar. The new `SelectedWordProfile` retains
literal equality to these constructors, their exact core and nu, and the selected branch
parameters. `SelectedWordMarkedFieldData` retains that profile, the complete certificate,
and every marking equation on the calibrated branch. The stronger public
`HasSelectedOriginalMarkedWordPresentationRN` additionally retains the ORIGINAL selected
branch and its cyclotomic character together with the profile and aligned equivalence.
Its bare-field producer is `hasSelectedOriginalMarkedWordPresentationRN_ramifiedI`.

## Ten-item acceptance map

| Ledger item | Checked mathematical producer | Publication status |
| --- | --- | --- |
| 1. Exact syntax tree | Concrete constructors above; `SelectedWordProfile`; new `GeneralTemplate.denote_pairSplice` and `.denote_mobileSplice` | Separate symbolic template format is staged. It does not silently migrate frozen S1.1. |
| 2. Tame/pro-two reductions | `tameSpecializes_tameSplice`, `eval_pro2_tameSplice`, `CorePresentation.ofTameSplice`; pair/mobile flexible core constructors | Uniform semantic reductions proved; generated display must cite the same tree. |
| 3. Evaluated Fox Jacobian | `TameSpliceScalarFoxNormal`, `TameSpliceUnramifiedFoxRows`, `TameSpliceRamifiedFoxNormal` | All three sector matrices are literal all-cochain identities for actual changed words. In particular the unramified tau column is proved to be the identity, not left opaque or copied from the raw word. |
| 4. Invertible row/column operations | `SigmaNormalFoxElimination`, `SigmaRamifiedFoxElimination`, both `FoxPolynomialInverse` modules; `TameSpliceFoxCertificates`, `TameSplicePolynomialFoxCertificates`, `TameSpliceRamifiedPolynomialFoxCertificates` | Explicit triangular row operations and inverse, ramified column shear, and finite action-polynomial inverses are checked. Original-format records now cover both the old normal targets and the full identity-pivot lists, using literal finite sums in the unchanged grammar. No commutation of sigma and tau is assumed. |
| 5. Reduced normal matrix | Actual scalar, unramified, and ramified wrappers in the modules above | Scalar target `(x_tau,0)`; unramified identity pivots on tau and x2; ramified pivots on sigma and x2 after the explicit shear. All are identities on ALL cochains, not merely cocycles. |
| 6. Stokes chain identity | `uniformStokesSupply_headHandlePairSplice`, `mpcMobileTameSplice_uniformStokesSupply` | Complete coefficient-independent supply, including finite resolvers and devissage; no simple-module-only gap. |
| 7. Extraspecial Hessian | `hessEvalZ_tameSplice_ramified`; pair full-extension normal evaluation; mobile semantic full-extension Hessian | Full central extension is retained. Bilinear Stokes alone is not substituted for the quadratic phase. |
| 8. Quadratic normal coordinates | Pair `headHandlePairSplice_compactNormal` and unramified comparison; mobile unramified comparison; common ramified comparison; `WordPhasePolarNormal`, `WordPhaseAdditiveNormal`, `WordPhaseSpliceAdditiveNormal` | Actual cocycle/coboundary normal forms and exact phase comparison are proved. Actual source comparisons are proved additive, so the common polar matrix and its explicit inverse are genuine additive-coordinate congruences, uniformly in rank. |
| 9. Affine phase-cover certificate | Pair/mobile `*_boundaryComparison`, `*_branchFreeSupply`, `*_determinant`; `UniformStokesSupply.determinant_of_branchFree`; `TameSpliceHessianCertificates` | Complete actual-boundary affine determinant, for every relevant cover/character; no determinant premise left. Original Hessian/phase-cover records use the same now-F2-linear source coordinate maps and derive cardinality internally. |
| 10. TeX/tree hash | New staged template serializer/checker with formal constructor-denotation bridges and pinned finite-evaluation theorem | Four structural examples pass strong Lean replay, TeX/hash, and direct-source provenance; 37 tooling tests pass. These are symbolic-template hashes, NOT instantiated-word hashes. Separate from the old five-fixture manifest; migration and acceptance are not owner-approved. |

## What the common endpoint actually is

Let V be the finite quadratic coefficient space, let `q0 : V -> F2` be its nonsingular
quadratic form, and write B for its polar form. In the normal coordinates supplied by the
source comparisons, BOTH changed M families have the same phase

\[
Q(c_0,c_1,(u_j,v_j)_j)
=q_0(c_0)+B(c_0,c_1)+\sum_{j<h}B(u_j,v_j).
\]

This is literally `WordPhase.wPhCompactWallHandlePhase q0 h`. For `|V| = 2^(2m)` its
Gauss sum is `2^((2+2h)m)`. The ramified and unramified numerical targets coincide because
the field degree is even, not because the two arithmetic branches have been conflated.

On the unramified mobile source the raw full-extension expression initially contains
the additional factor-set charge `dat.m ((sigma^E(omega2))^p) c0`. It is not discarded
by looking only at its polar form. The actual faithful-head projection proves the
two-primary sigma element is ONE; `hessRelZ_mpcUnit_unramified_compactPhase_of_sigma2_one`
then removes this charge using the normalized factor set. The pair proof likewise uses
the full central-extension evaluation, not just the first jet.

On ramified heads, the odd fixed-point-free tau action makes the entire tame-shadow
contribution trivial in the relevant Heisenberg AND extraspecial evaluations. Consequently
the splice inherits the compact template's full phase. This is the uniform mechanism
replacing the failed raw sheared-source argument; no nilpotency-class cutoff enters it.

## The precise finite-to-profinite check

The finite resolver is pinned at `4 * exponent(C)`, with coherent resolutions of the full
Zhat and Z2 exponents. This handles the relevant word lifts and central extensions, whose
orders need not equal the base group's orders. A resolver chosen only at exponent(C), or
one that depends on the coefficient module, would not establish the required uniform
word certificate. The actual `UniformStokesSupply` contains a single coefficient-independent
level family and a theorem for EVERY finite exponent-two coefficient module; the use of
finite modules is universal cohomological reduction, not testing a handful of finite targets.

## Assembly and trust

`FlexibleCertificateLeavesRN` contains tame specialization, normalized presented core,
exact lifting, full Stokes duality, scalar Hilbert data and the affine determinant.
`wordCertificateRN_of_flexibleLeaves` supplies the remaining routine source fields.
The pair and mobile constructors of these leaves use only the standard Lean axioms.
The general field endpoint additionally inherits the established arithmetic/foundation
inputs, as recorded in the exact-footprint audit and the current trust-boundary document.

This compositional presentation is not automatically an approved replacement for the
ledger's requested generated row-operation lists and appendices. The checked artifacts
make the mathematical content reviewable; any revised publication acceptance format must
be stated explicitly and approved through the existing campaign process.

The companion `w361-pair-mobile-certificate-appendix.md` is a hand-authored parametric
ten-item appendix, not itself a generated synchronized artifact. **14:25 UTC update:**
the separate `w361_certificate_packet.py` now emits four STAGED ten-item specimens,
using exact Lean-exported word, Fox, phase and phase-cover ASTs. Typed input/signature
and original-cover bridges are checked; strong replay re-emits all four trees and
compares the cited declaration type/axiom transcript. It does not prove the prose,
independently prescribe expected declaration types, or give transitive artifact
provenance. **Final update, 17:30 UTC:** all 29 PDF pages have passed visual QA;
the complete 1,541-module clean build and source-bound staged replay passed,
followed by an independent post-replay content recheck. The exact record is
`w361-final-verification.md`. This is
substantive synchronization progress, not adoption of the release format.

All five old generated appendices
still have placeholders for items 2–9 (40 invocations total); their passing old word hash
does not attest complete appendices. Original-format Hessian/phase-cover record packaging
is now proved separately in `WordPhaseCompactCertificates` and `TameSpliceHessianCertificates`,
including the full phase identity, not inferred merely from equality of polar matrices.
