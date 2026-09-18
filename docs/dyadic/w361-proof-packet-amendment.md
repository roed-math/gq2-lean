# W361 proposed amendment to the dyadic proof packet

**Draft for owner/editorial adoption, 2026-09-17. Not approved.** This additive
note proposes replacement statements for the July 28 packet's main theorem,
marked-matching requirement, source-data interface, and reconstruction proof.
It does not edit the vendored packet, the selection freeze, or an owner memo.
The standing scope remains finite `K/Q₂` with **K(i)/K ramified**.

## 1. Proposed main theorem

Use `GammaR n q W`, including its mandatory pro-2 wild-normal-closure condition:

\[
 \Gamma_W=\langle\sigma,\tau,x_0,\ldots,x_n\mid
 \sigma^{-1}\tau\sigma=\tau^q,\ W=1,
 \overline{\langle\!\langle x_0,\ldots,x_n\rangle\!\rangle}
 \text{ is pro-}2\rangle_{\mathrm{prof}}.
\]

The bare two-relator profinite group is not substituted for this group.

**Proposed theorem (selected, certified, fully marked presentation).** Assume
the standing local/foundational inputs listed in Section 7 below. Fix, in this
order:

1. A finite intermediate field `K ⊆ Q̄₂` and `RI : RamifiedIData K`.
2. `Rec : LocalReciprocity`, `B : MarkedRecip Rec K`, a unit filtration `FF`,
   `T : OrientedTameQuotientK B FF`, and `D : FiniteDyadicParameters K FF`.
3. `WM : FamilyFieldBranchWitness D.params (B.fieldMarkedPair FF)`,
   `hmatch : WM.MatchesCyclotomicRange`, and
   `S : FamilyFieldBranchSelection K D.params (B.fieldMarkedPair FF) WM`.

Put `n = [K:Q₂]` and `q = qOf K FF`. There exist a pro-2 core `P`, a continuous
surjective character `nuP : P → Ztwo`, a word `W : PWord (Generator n)` with
the exact selected profile of Section 2, an initial marked realization
`j₀ : P ≃ G_K(2)`, and a certificate

```
WordCertificateRN n q W P hP nuP (standardNumerics n).
```

Write `p_W : Γ_W → P` and `t_W : Γ_W → T_q` for its actual pro-2 and tame
maps. **Before choosing a field isomorphism**, fix
`chiP = chiCycKTwo ∘ j₀`. There then exist a continuous group isomorphism
`e : Γ_W ≃ G_K` and a marked realization `j : P ≃ G_K(2)` such that, for all g,

\[
\begin{aligned}
 T.\mathrm{tameFK}(e(g)) &= t_W(g),\\
 \pi_{K,2}(e(g)) &= j(p_W(g)),\\
 \chi_K(e(g)) &= \chi_P(p_W(g)),\\
 B.\nu_{\mathrm{ur}}(\mathrm{ab}(e(g)))
   &= \mathrm{ztwoIota}(\nu_P(p_W(g))).
\end{aligned}
\]

Moreover `chiCycKTwo ∘ j = chiP`. Equivalently the carried projection
`j⁻¹ ∘ π_K,2` identifies `e(g)` with `p_W(g)` on the nose. The new realization
may replace `j₀`, but the word, core, `nuP`, degree, and certificate are
unchanged. **There is no assertion that an arbitrarily prescribed `j₀` is
preserved pointwise by e.**

The range selector discharges item 3. Choosing `B = markedRecipAt K`, the
canonical filtration and finite parameters, and
`T = orientedTameQuotientAt K FF`, gives a public corollary with only finite K
and `RI` as explicit mathematical inputs. `RI` means a root `deltaI² = -1`
together with `¬HasEqualNormValueGroups K deltaI`; it is not available for
every finite K. Odd degree supplies it by a proved corollary, not a new axiom.

The exact combined public endpoint is now
`HasSelectedOriginalMarkedWordPresentationRN B FF T S`, not a proposed
combination of two unrelated existential witnesses. Its literal content is

```
∃ G, G.degree = S.semantic.degree ∧ SelectedWordProfile FF S G ∧
  ∃ cert : GenAsmFlexibleRowResidualRN FF G,
    Nonempty (AlignedMarkedFieldEquiv G cert.cand T).
```

Here G is the **pre-calibration** source: its selected profile, entire actual
certificate, and original core character are retained together. The
`AlignedMarkedFieldEquiv` carries e and the induced realization in its
`branch`. The theorem is still existential in G, j₀ and the selected handle;
it does not preserve an arbitrarily prescribed external realization or
handle. The supplied-bundle, range-selector, canonical-parameter, bare-RI,
and odd-degree variants are in
[FieldFamilySpliceOriginalMarked.lean](../../GQ2/Dyadic/Instances/FieldFamilySpliceOriginalMarked.lean),
exported by `GeneralMain`. In particular,
`hasSelectedOriginalMarkedWordPresentationRN_of_matchesRange` and
`hasSelectedOriginalMarkedWordPresentationRN_ramifiedI` realize precisely
the quantifier order above.

Additional checked anchors:
[FieldFamilySpliceSelectedWordFinal.lean](../../GQ2/Dyadic/Instances/FieldFamilySpliceSelectedWordFinal.lean),
`nonempty_selectedWordMarkedFieldData_of_matchesRange`,
`nonempty_selectedWordMarkedFieldData_ramifiedI`, and
`SelectedWordMarkedFieldData.degree_eq_field`;
[FieldFamilySpliceMarkedFinal.lean](../../GQ2/Dyadic/Instances/FieldFamilySpliceMarkedFinal.lean),
`nonempty_alignedMarkedFieldEquiv`, which retains the **initial** character;
public exports in [GeneralMain.lean](../../GQ2/Dyadic/GeneralMain.lean).

## 2. Exact replacement word profile

All even branches have `n = 2 + 2h`, `alpha ≥ 2`; positive-level branches have
`r ≥ 1`. The L branch has `n = 2h + 1`. Here h is the selected
`handleCount D.params S.branch`, not a new freely chosen rank.

Let `H = Words.MCompact.mCompactW alpha h`. Define the *new tame shadow*
substitution and splice by

\[
 \mathcal S(\sigma)=\sigma,\qquad \mathcal S(\tau)=1,\qquad
 \mathcal S(x_i)=(x_i\tau)^{\omega_2}(\tau^{\omega_2})^{-1},
 \qquad \operatorname{Sp}(R,H)=\mathcal S(R)H\mathcal S(H)^{-1}.
\]

This is `tameShadow`/`tameSplice`, not the old exporter token `RawWord.shadow`.
Under pro-2 specialization the splice equals R; its tame specialization is
also proved. See [TameShadowWord.lean](../../GQ2/Dyadic/TameShadowWord.lean),
`eval_pro2_tameSplice` and `tameSpecializes_tameSplice`.

| Selected branch | Exact admitted word and core |
| --- | --- |
| L | `Words.LSq.lSqW h`, with the exact `selectedPresentation S` core. |
| N0 alpha | `Words.nCompactW alpha h`, with the selected canonical core. |
| Npc alpha r eta | `Words.Npc.npcW alpha r h d.data`, where d is the compatible display carried by S; the exact selected canonical word/core are retained. |
| M0 alpha | Either the exact canonical selected word H/core, **or** `headHandlePairSpliceW alpha h q ... j nuP` with core `DM alpha h`, `j : Fin h`, and `nuP(U_j) = ztwoOne`. |
| Mpc alpha r epsilon eta | `tameSplice (mpcMobileTameCorrectedW ... alpha r (p epsilon r) h etaD ... nuP) H`, with core `DM alpha h` and the actual unit `etaD` specified below. |

The ellipses above suppress **proof arguments only** (`1 ≤ alpha`, `q ≠ 0`,
`Even q`); no exponent or marking parameter is suppressed. The pair word is
exactly the splice of `headHandlePairPrimeCorrectedW` with H. On Mpc,

\[
 p(\epsilon,r)=\epsilon\,2^{r-1},\qquad
 \operatorname{ztwoIota}(\nu_P(D))=\operatorname{ofAdd}(\eta_D),\qquad
 \eta_D=\eta+2^r w\quad\text{for some }w\in\mathbf Z_2.
\]

Here epsilon is read as 0 or 1. Both eta and etaD are units. **Do not replace the last congruence by
`etaD = eta`.** The raw semantic mobile core uses the head `D^(etaD⁻¹)`;
its wild shear uses the actual character values, and its prime-to-two tame
correction is the constructor's specified correction. Consequently the new
word may depend on `nuP` and actual continuous exponent parameters, not just
the finite/discrete branch label. Neither the word nor its parameters are
chosen anew for each finite target or coefficient module.

The precise code predicate is `SelectedWordProfile` in
[FieldFamilySpliceSelectedWord.lean](../../GQ2/Dyadic/Instances/FieldFamilySpliceSelectedWord.lean).
It records literal `HEq` word equality with explicit degree/core equalities;
on splice branches it also records `HEq` of the actual `nuP`. The canonical
branches retain `selectedPresentation S`, not merely a family name.
`selectedWordProfile_alignedBranch` proves that this profile survives
calibration definitionally. When `h=0`, no pair index exists, so M0 uses its
canonical alternative; the mobile Mpc construction itself includes `h=0`.

This profile replaces the **universal frozen-M-word** claim. It does not prove
that the old frozen M word is the actual field presentation in the obstructed
markings, nor that the new splice is boundary-compatibly equivalent to it.

## 3. Corrected source interface and R-stage equation

Replace the general-degree `SourceDataN`/`WordCertificate` references by their
additive RN companions. Keep the frozen APIs for degree-one regression.
The standard values are

\[
\begin{array}{c|c}
\texttt{homScalar}&2^{n+2}\\
\texttt{mMult}(M),\ \texttt{tMult}(M)&M^{n+1}\\
\texttt{h1Mult}(V)&V^n\\
\texttt{gaussUnram}(m)&(-1)^n2^{nm}\\
\texttt{gaussRam}(m)&2^{nm}.
\end{array}
\]

The H² scalar cardinality and the half-torsor factor remain 2. The outer
`|V|` in the V-cocycle cardinality remains separate, giving
`|Z¹(V)| = |V| · h1Mult(|V|) = |V|^(n+1)` in the applicable nontrivial-simple
case. These formulas are `standardNumerics` in
[Recursion/Numerics.lean](../../GQ2/Dyadic/Recursion/Numerics.lean).

For a recursion frame RF, let `R = Blk.frattiniK` be the finite radical group
(not the presentation word), and use the existing `D_R = RF.DR`. The corrected
coefficient is

\[
 z_{R,n}:=\texttt{SN.tMult}(|R|)\,|D_R|,
 \qquad z_{R,n}=|R|^{n+1}|D_R|\quad\text{for standard numerics}.
\]

Thus equation (136), with the existing exact-image and mB conventions, is

\[
 |D_R|\,N_\Gamma(T)
 =z_{R,n}\sum_{\lambda\in D_R}
       \bigl(2m_{\Gamma,\lambda}(B)-N_\Gamma(T_B)\bigr),
\]

an equality in the integers. Equations (137)-(140) keep their existing forms.
The two compared sources must share the same `n,q,P,nuP,SN`. No general-degree
equality `zRN RF SN = RF.zR` is assumed. The RN comparison equates the two
right-hand sums and then the common left-hand multiples; it does not need to
cancel `zRN` or assume its nonvanishing.

At `n=1`, `zRN RF (standardNumerics 1) = RF.zR` is **rfl**, since the frozen
factor is `|R|²|D_R|`. Explicit mutually inverse degree-one source and closed
recursion conversions recover the old interfaces. The remaining degree-one
numeric simplifications have their own checked lemmas; not all are rfl.

Checked anchors: `zRN`/`zRN_standard_one` in
[Recursion/Recursion.lean](../../GQ2/Dyadic/Recursion/Recursion.lean);
`blockStageR136NK` in
[Recursion/BlockRStage.lean](../../GQ2/Dyadic/Recursion/BlockRStage.lean);
`SourceDataRN`, `WordCertificateRN`, and degree-one conversions in
[SourceDataRN.lean](../../GQ2/Dyadic/SourceDataRN.lean);
`count_eq_of_closedRecursionRN` in
[Recursion/ClosedRN.lean](../../GQ2/Dyadic/Recursion/ClosedRN.lean);
`thm_4_2_of_sourcesRN` in [ThmFourTwoRN.lean](../../GQ2/Dyadic/ThmFourTwoRN.lean).
The field leaf is `exactLiftingSemanticsRN_galK` in
[KExactLiftingGalK.lean](../../GQ2/Dyadic/Instances/KExactLiftingGalK.lean).

Accordingly, replace “the induction is unchanged” by “the induction strategy
is retained in a corrected degree-indexed implementation; the R-fibre
coefficient and every dependent source/recursion interface are parameterized.”

## 4. Full MC-N lifting is now proved; proof-method reconciliation remains

**18:55 UTC update:** there is no longer a need to weaken the mathematical
MC-N criterion. `nFullStabilizer_lift` and `nFullStabilizer_lift_iff` prove the
full orientation/cup stabilizer assertion on the actual canonical N frame,
including arbitrary handle mixing, torsion and an all-element commuting
square, for every alpha >= 2 and h. The proof has only standard-three axioms.
The old packet's finite Nielsen-generator-list method is a separate artifact
not supplied by this filtered correction/compactness proof. The proposed
editorial change is now acceptance of that alternative proof method, not
weakening of the mathematical lifting target. See
`w361-n-full-stabilizer-scope.md` and the current Claude Code handoff.

For comparison, the earlier narrower proposed criterion was the correction
theorem actually needed by the field consumer (still proved):

> For every continuous marking `nu' : DN alpha h → Z₂` for which the pair
> `(nu'(sigma), nu'(x₂))` is unimodular, there exists a continuous automorphism
> u preserving `chiN` and satisfying `nu' ∘ u = nuN`.

Here unimodular means that at least one of the two entries is a two-adic unit.
The field-facing applications must discharge their marked-data conditions;
the theorem does not silently replace them by surjectivity of nu' alone.

The proof uses the exactly realized determinant-one plane action to normalize
one primitive row, followed by the proved handle/core-mixing corrections.
It requires no `NScalingHypothesis` or `NPlaneScalingHypothesis`. Anchors:
`nCorePlane_sl2_lift`, `nSL2_normalize_pivot`, and
`nMarkedCorrection_of_pair` in [MarkedCore/N.lean](../../GQ2/Dyadic/MarkedCore/N.lean);
`nMarkedMatching` in
[MarkedCore/Certificate.lean](../../GQ2/Dyadic/MarkedCore/Certificate.lean).
The selected N0/Npc certificate producers are `hasSelectedRowResidualRN_n0`
and `hasSelectedRowResidualRN_npc` in
[FieldFamilyCampaignBoundary.lean](../../GQ2/Dyadic/Instances/FieldFamilyCampaignBoundary.lean).

**16:47 UTC update:** arbitrary-determinant integral plane lifting is now
unconditional by `nPlaneScalingHypothesis_general` and
`nCorePlane_gl2_lift_general`. The further theorem
`nStabParam_fullFrame_lift_general` realizes every admissible core parameter
on the entire canonical abelianization, including its torsion entries, with
identity handle columns. All are uniform for alpha >= 2 and arbitrary h,
with only standard-three logical axioms. See the independent strong-scaling
and full-row audits for the actual composed proofs and verification scope.

The formerly missing assertion covering **every** invariant-triple automorphism,
including arbitrary handle mixing, is supplied by the new full theorem above.
It follows from the actual arbitrary-basis/initial-cup/exact-row/compact-limit
chain, not merely from the old marking correction or core-parameter theorem.
The same editorial principle applies on M:
the source construction uses the proved canonical-or-strict-handle alternative,
not unrestricted transitivity to a canonical C pivot.

## 5. Replacement reconstruction and marking proof

The old implication “equal unframed counts, hence an isomorphism identifying
all prescribed maps” is insufficient. Use these additional steps.

1. **Keep the tame constraint in finite quotients.** For a finite quotient
   `f₂ : S₂ → Y`, divide Y by the image of `ker(t₂)`. That image is a 2-group;
   the residual head is a finite quotient of `T_q`. Apply the fixed-frame RN
   exact-image equality to obtain a surjection `f₁ : S₁ → Y` such that, for
   every x, some y satisfies `f₂(y)=f₁(x)` and `t₂(y)=t₁(x)`.
   Anchor: `exists_tameCompatible_finiteSurj_of_sourcesRN` in
   [TameMarkedFiniteLifts.lean](../../GQ2/Dyadic/TameMarkedFiniteLifts.lean).
2. **Take a constrained inverse limit.** At every open normal quotient, the
   allowable maps form a nonempty finite set stable under projection. The
   finite cofiltered-system argument produces a continuous surjection
   preserving the tame map. Repeat in the other direction; Hopfianity gives
   injectivity without replacing the boundary-preserving map. Anchors:
   `exists_contSurj_of_allowed_levels` and
   `nonempty_markedEquiv_of_quotient_lifts` in
   [MarkedReconstruction.lean](../../GQ2/MarkedReconstruction.lean).
3. **Recover full nu, not only mod 2.** Source compatibility is
   `nuTq ∘ tame = nuP ∘ pro2`. Exact tame equality therefore gives equality of
   the full `Ztwo` characters. Anchor:
   `exists_tameNuCompatible_equiv_of_sourcesRN` in
   [TameMarkedReconstruction.lean](../../GQ2/Dyadic/TameMarkedReconstruction.lean).
4. **Calibrate only the existential realization.** For the resulting e,
   `p_W ∘ e⁻¹ : G_K → P` has kernel `proPKernel 2 G_K`. Let
   `j : P ≃ G_K(2)` be the inverse of its induced quotient equivalence.
   Then `π_K,2 ∘ e = j ∘ p_W` literally. Full nu makes j a marked
   realization. `alignedBranch` replaces only this field, so W, P, nuP and
   the certificate do not change. Anchors: `alignedRealization_maxPro2` and
   `alignedBranch_certificate` in
   [FieldFamilySpliceAlignedFinal.lean](../../GQ2/Dyadic/Instances/FieldFamilySpliceAlignedFinal.lean).
5. **Preserve the already fixed cyclotomic character.** The full crossed-
   derivation basis/master-matrix argument proves characteristic canonical
   orientation for all M, N, and L-square ranks. One oriented field/core
   identification transfers this to `chiCycKTwo`. Apply characteristicness to
   `j ∘ j₀⁻¹` to get `chiCycKTwo ∘ j = chiCycKTwo ∘ j₀`, and then the
   cyclotomic equation in Section 1. Anchors: `mCoreOrientationCharacteristic_all`,
   `nCoreOrientationCharacteristic_all`, `sqCoreOrientationCharacteristic_all`,
   [OrientationMasterTransport.lean](../../GQ2/Dyadic/OrientationMasterTransport.lean),
   `chiCycKTwo_characteristic_ramifiedI` in
   [FieldCyclotomicCharacteristic.lean](../../GQ2/Dyadic/Instances/FieldCyclotomicCharacteristic.lean),
   and `cyclotomic_eq_original_of_aligned` in the marked-final module.

This proves the marked **existence** theorem. It does not require a count
theorem over every finite quotient of a previously fixed full pro-2 core map;
the elementary-2 frame slot is not silently promoted to that stronger slot.

### 5A. Proposed explicit certificate appendix for the changed words

The replacement appendix should use the actual constructors of Section 2,
not the frozen M matrices. The following all-cochain identities now supply
literal evaluated matrices. Write S,T for the generator actions and
`N_q(T)=sum(i<q) T^i`.

| Coefficient profile | Actual differential `(d₀(x),d₁(x))` | Reduced pivots |
| --- | --- | --- |
| All generator actions trivial, exponent two | `(x_tau, x_tau)` | Subtract row one from row two: `(x_tau,0)` |
| Finite exponent-two, tau/wild trivial, sigma fixed-point-free and its two-primary action trivial | `(S⁻¹x_tau, x_tau+(1−S⁻¹)x₂)` | Invert first pivot, subtract its value, invert second pivot: `(x_tau,x₂)` |
| Ramified projected boundary, tau fixed-point-free of odd action order | `(S⁻¹((T−1)x_sigma+x_tau)−N_q(T)x_tau, −S⁻¹x₂)` | Explicit sigma/tau column shear and row scaling: `(x_sigma,x₂)` |

These identities have their stated finite-action/boundary hypotheses; they
are not one common two-pivot matrix for every reducible coefficient module.
The full Stokes supply handles general finite elementary coefficients by its
proved exact-sequence argument. Nontrivial unramified rows require actual
changed-relator death; scalar rows do not. No raw-word death is assumed.

In the unramified row the formerly abstract tau coefficient is now proved
to be **identity** by `compactSplice_tauColumn`. The inverse of
`1−S⁻¹` is the explicit polynomial

```
sum (j < m/2) S^(-(2*j+1)),
m = order of the actual sigma action (odd).
```

Anchors: [TameSpliceUnramifiedFoxRows](../../GQ2/Dyadic/Instances/TameSpliceUnramifiedFoxRows.lean),
[TameShadowTauColumn](../../GQ2/Dyadic/TameShadowTauColumn.lean),
[TameSpliceScalarFoxNormal](../../GQ2/Dyadic/Instances/TameSpliceScalarFoxNormal.lean),
[TameSpliceRamifiedFoxNormal](../../GQ2/Dyadic/Instances/TameSpliceRamifiedFoxNormal.lean),
and [SigmaNormalFoxPolynomialInverse](../../GQ2/Dyadic/SigmaNormalFoxPolynomialInverse.lean).
The period is the action order, not an assumed odd order of sigma in a
possibly nonfaithful ambient quotient.

For the common reduced quadratic phase
`Q=q(c₀)+B(c₀,c₁)+sum B(u_j,v_j)`, the full coefficient matrix has head
`[[1,1],[1,0]]`, handle blocks `[[0,1],[1,0]]`, and zero off-block entries,
each coefficient multiplying B. Its explicit inverse and exact polarization
are in [WordPhasePolarNormal](../../GQ2/Dyadic/Instances/WordPhasePolarNormal.lean).
The source-coordinate comparison is now an actual **additive** equivalence:
[WordPhaseAdditiveNormal](../../GQ2/Dyadic/Instances/WordPhaseAdditiveNormal.lean)
and [WordPhaseSpliceAdditiveNormal](../../GQ2/Dyadic/Instances/WordPhaseSpliceAdditiveNormal.lean)
prove source polar congruence for the existing pair and common ramified maps
and an explicitly additive mobile witness. This is stronger than reindexing
Gauss sums by an arbitrary bijection.

The polar matrix still does not determine Q in characteristic two. The full
extraspecial evaluation, including the mobile factor-set charge and its
justified vanishing in the faithful projected head, and the actual affine
determinant interface remain separate required entries. The proposed
[parametric pair/mobile appendix](w361-pair-mobile-certificate-appendix.md)
maps all ten ledger items to those proofs. It is staged mathematical content,
not itself a generated, owner-approved appendix. The original `FoxCertificate`
records now exist, including literal finite-polynomial full-pivot lists;
the original `HessianCertificate` and attached `PhaseCoverCertificate` values
also exist for actual pair/mobile sources and their boundary lifts. These
record producers do not by themselves approve the changed word selection or
finish synchronized publication generation.

## 6. Correct the historical unit-norm/inertia sentence

Replace the general assertion `1+8Z₂ ⊆ I` in the old AX3 proposal's explanatory
prose by

\[
 (\mathbf Z_2^\times)^n\subseteq I,
 \qquad n=[K:\mathbf Q_2].
\]

Indeed, for a base unit w, `N_K/Q₂(w)=w^n`, its reciprocity image over K has
nu-value zero, and its cyclotomic value is `w^(-n)`. Inversion does not change
the power subgroup. More explicitly, the lower bound is all `Z₂ˣ` if n is
odd, and `1+2^(v₂(n)+2)Z₂` if n is even. It becomes `1+8Z₂` when
`v₂(n)=1`, including the old degree-two examples, not for all degrees.
For instance, K containing `μ₁₆` has cyclotomic image contained in `1+16Z₂`.

This is a correction to historical prose, not to a field of `MarkedRecip`.
See [the clause-level source audit](w361-axiom-source-verification.md) for
checked primary citations and the distinction between direct statements and
composite finite-r/K(i) arguments.

## 7. Adoption decisions and release contract

The mathematical proposal requires explicit owner/editorial decisions on:

1. Replacing the universal frozen-M table by Section 2's exact flexible
   selected profile, including marking-dependent continuous parameters and
   the etaD congruence. Leave the historical frozen Main theorem separate.
2. Adopting the existential realization quantifiers and original-character
   preservation in Section 1; do not promise an arbitrary fixed realization.
3. Replacing the general-degree R-stage/interface by RN and accepting the
   exact degree-one regression, without changing the frozen degree-one APIs.
4. Accepting the new proved full MC-N stabilizer theorem's uniform filtered
   proof in place of the prescribed finite Nielsen-generator-list method,
   or separately constructing that literal presentation artifact. The full
   mathematical stabilizer theorem itself no longer needs commissioning.
5. Adopting a symbolic exponent/tree export and compositional certificate
   appendix for the actual splice words. The appendix must connect exact
   constructor equality, both specializations, evaluated Fox rows and
   invertible operations, Stokes, polar and quadratic normal forms, and the
   affine phase-cover interface. A finite sample hash or unshifted Gauss sign
   does not replace any of these. The staged template proposal is not an
   activated S1.1 migration or an approved replacement acceptance format.
6. Reviewing the clause-level AX3/AX4 citation annotations and correcting the
   historical sentence in Section 6, without treating source verification
   as elimination of formal axioms.

The canonical theorem's measured trust boundary is standard three plus the
existing nine declarations: `hilbertSymbol_normCriterion_finiteDyadic`,
`localReciprocity`, `markedRecipAt`, `orientedTameQuotientAt`,
`peripheralCyclotomicAction`, `relativeStiefelWhitney_dyadic`, `tateDualityAt`,
`Foundations.absGalQ2_isTopologicallyFinitelyGenerated`, and
`Foundations.absGalQ2_localEulerCharacteristic`. The supplied-bundle endpoint
omits the three reciprocity/tame constructors from this print. No new axiom
or field-specific presentation assumption is proposed.

After adoption, release still requires one final-tree build/gate record,
the approved actual-word appendix and tree/TeX/hash artifacts, and the owner
release sign-off. These are acceptance steps, not claims that the old freeze
or its manifest already certifies the changed words.
The remaining work is not approval alone: the synchronized ten-item generated
appendix and its activated verification gate still need content/integration.
See [the acceptance-readiness checklist](w361-acceptance-readiness.md) for the
distinction between mathematical proofs, artifact assembly, and owner decisions.
