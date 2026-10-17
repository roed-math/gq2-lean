# W361: clause-level source verification for AX3 and AX4

Date: 2026-09-17. Scope: the already approved citation targets for B5-K
(`markedRecipAt`) and B10-K (`orientedTameQuotientAt`). This is a source audit,
not an axiom change, a new owner approval, or a census revision. No source PDF
is vendored by this audit.

> *Superseded status (2026-10-17):* B5-K and B10-K are no longer axioms. Ticket C1' of
> [`tauceti-discharge-plan.md`](tauceti-discharge-plan.md) proved both from Tau Ceti revision
> `706344c35` (`GQ2/TauCeti/{GaloisDictK,B5K,B10K}.lean`; census 0). The statements are
> byte-identical, so this audit now records which published statements those proofs establish,
> not a trust assumption. The "inherited-axiom status of the current general endpoint" in §1,
> item 6 is superseded: see [`literature-axioms-dyadic.md`](literature-axioms-dyadic.md)
> §W361.0. The audit text below is unchanged.

## 1. Result and limits

The principal cited results were found and inspected in primary sources.
In particular, the general-local-field and general-residue-cardinality scope
of NSW (7.5.2)/(7.5.3), Serre's norm/inclusion diagram, and Serre's
unit/uniformizer formulas are supported by the actual pages, not just their
bibliographic entries.

The **bundles are composite interfaces**. Their precise Lean types, topology,
sign convention, spectral-norm formulation, finite `r`, and `K(i)` clause are
not verbatim statements of a single cited theorem. The table below separates
direct source support from the required mathematical translations. Those
translations do not become Lean proofs merely because they are explained
here. Both declarations remain axioms in the current formal trust boundary.

One historical proposal overclaim was found, described in Section 6. It is
not an axiom field or a premise of the W361 endpoint.

## 2. Sources and inspection record

References in this note use **printed page numbers**. The PDF page numbers
are one-based and are supplied separately because the Serre scan has missing
blank pages and does not have a constant offset.

### N: Neukirch, Schmidt, Wingberg

*Cohomology of Number Fields*, second edition, electronic corrected version
2.3 (May 2020). Local provided copy: `/Users/roed/Downloads/NSW2.3.pdf`.
The [author's institutional page](https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/)
links the [electronic text](https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/NSW2.3.pdf).

- VII Section 1, p. 371, (7.1.1): local-field scope and class-field axiom.
- p. 375, (7.1.4)/(7.1.5): invariant maps and local class formation.
- VII Section 5, pp. 409-411, (7.5.1)-(7.5.3): wild inertia, tame quotient,
  Frobenius action, presentation and proof.
- III Section 1, pp. 152-153, 157: reciprocity and inverse-limit construction
  were also checked in extracted text; the direct norm diagram was verified
  visually in Serre instead of relying on this cross-reference alone.

The complete pages 371, 375, 409, 410, 411 were rendered and visually inspected
(PDF 385, 389, 423, 424, 425). SHA-256:
`abbb7cdefc9ecb3350286c3cba36fe36a90c103257ff8f64173e09a50afdcb91`.

### S: Serre

*Local Fields*, translated by M. J. Greenberg, GTM 67, 1979. The edition and
DOI were checked against the [publisher record](https://link.springer.com/book/10.1007/978-1-4757-5673-9).
The full text was obtained from the [University of Rochester faculty-hosted scan](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Serre-Local.pdf).
The browser text tool rejected its size; a normal download of the public PDF
succeeded. No paywall or access control was bypassed.

Complete relevant pages were rendered and visually inspected:

- I Section 4, p. 14: ramification index and unramifiedness (PDF 22).
- IV Section 1, p. 63: inertia fixed field (PDF 70).
- IV Section 2, pp. 67-68: Proposition 7 and Corollary 3 (PDF 74-75).
- XI Section 3, pp. 170-171: reciprocity functoriality diagrams and passage to
  the limit (PDF 176-177).
- XIII Section 4, pp. 197-198: Propositions 10-13 and the corollary to
  Proposition 13 (PDF 202-203).

The checked download has 249 PDF pages. SHA-256:
`cfda5836dfddf3c74b0ccb6e28c390e2559227b2a2160bafcd6946f101b869d4`.

### M: Milne (corroborating source)

*Class Field Theory*, v4.03, 2020-08-06,
[author's text](https://www.jmilne.org/math/CourseNotes/CFT.pdf).
The local provided copy is
`/Users/roed/claude/TauCetiRoadmap/references/Milne -- Class Field Theory (course notes).pdf`.
Complete pages 20, 23-24, 44, and 107 were visually inspected
(PDF 29, 32-33, 53, 116): I Theorem 1.1; I 1.8-1.11; I Example 3.13;
III Theorem 3.1 and Lemma 3.2. SHA-256:
`50d79af78250a9f1117ad9d337e0b231704a533fc707966ed1bfa52e13d498f5`.

Important limitation: the proof of III Lemma 3.2 is marked as still to be
added. It corroborates the diagram's *statement*, not its proof. Serre XI
Section 3 and XIII Proposition 10(a) give the directly checked primary
support used here.

## 3. Actual interfaces audited

The source of truth is the current code, not the earlier proposal sketch:

- [MarkedRecipBundle.lean](../../GQ2/Dyadic/MarkedRecipBundle.lean):
  `MarkedRecip`, twelve fields.
- [OrientedTameBundle.lean](../../GQ2/Dyadic/OrientedTameBundle.lean):
  `OrientedTameQuotientK`, seven fields, counting the subgroup and normality
  instance separately.
- [Foundations/Axioms.lean](../../GQ2/Foundations/Axioms.lean):
  `markedRecipAt K : MarkedRecip localReciprocity K` and
  `orientedTameQuotientAt K FF : OrientedTameQuotientK (markedRecipAt K) FF`.

In particular, the second axiom does **not** quantify over every arbitrary
`MarkedRecip R K`. The two named axioms assert coherently chosen data over the
named base reciprocity constant. Literature support supplies a simultaneous
classical choice. It is not a uniqueness theorem for every structure
inhabiting the abstract B5 interface. The W361
[normalization audit](../../GQ2/Dyadic/Instances/LocalReciprocityNormalizationAudit.lean)
already warns against that stronger inference.

## 4. AX3 clause map

Status **D** means the mathematical content is directly present in the
specified source. **T** means a standard translation or derivation is needed;
it is explained below, not represented as a verbatim source theorem.

| Current bundle field(s) | Status | Evidence and exact qualification |
| --- | --- | --- |
| `recip` | D/T | M I Theorem 1.1, p. 20; N (7.1.5) plus class-formation reciprocity. Identify the classical abelianized Galois group with `GalKab K`. |
| `continuous_recip`, `denseRange_recip` | D/T | M I 1.10, p. 23: completion and topology. Ordinary-topology continuity and density follow; surjectivity of `Kˣ` onto the infinite profinite group is not asserted. |
| `nu_ur`, `continuous_nu_ur` | T | Unramified quotient followed by negative projection `Zhat → Ztwo`; N p. 409, S p. 198, M I 1.8. |
| `norm_compat` | D/T | S XI Section 3, diagrams (1)/(1)*, pp. 170-171; XIII Proposition 10(a), p. 197. This is norm versus induced inclusion on abelianizations, **not** transfer versus field inclusion. Finite-layer identities pass to the inverse limit. |
| `nu_ur_recip_unit` | D/T | S XIII Proposition 13 and corollary, pp. 197-198; apply the coordinate above. |
| `nu_ur_recip_uniformizer` | D/T | S XIII Proposition 13, p. 197, rather than its corollary alone. A maximal nonzero norm below 1 means normalized valuation 1; negative projection gives `-1`. |
| `r`, `nu_ker_chi_le`, `nu_ker_chi_ge` | T | A nonzero closed subgroup of `Ztwo` is `2^r Ztwo`; nonzeroness follows from `rec_K(2)` as detailed below. No single theorem with these three Lean fields was found. |
| `ki_unramified` | T | Inertia fixes `μ₄`, then the inertia fixed-field criterion and `e=1`; details below. S IV p. 63 and I p. 14 support the underlying criteria, not this bundled formula. |

### 4.1 The finite-r datum has a short general derivation

Write `n = [K:Q₂]`, `e = v_K(2) > 0`, and use additive notation for `nu_ur`.
Let `g = rec_K(2)`. Norm compatibility and the base normalization give

```
chi_K(g) = chi_Q2(rec_Q2(N_K/Q2(2)))
         = chi_Q2(rec_Q2(2^n)) = 1.
```

The last equality is B5's `chiCyc_recip_uniformizer`; its classical convention is also
consistent with M I Example 3.13, p. 44. Write `2 = u * pi^e` with `u` a unit.
The unit and uniformizer clauses then give `nu_ur(g) = -e`, which is nonzero
in `Ztwo`.

The image `A = nu_ur(ker chi_K)` is a closed additive subgroup: the kernel is
closed in a compact profinite group, and its continuous image is compact in
the Hausdorff target. Every nonzero closed additive subgroup of `Ztwo` is
`2^r Ztwo`. For completeness, take the least two-adic valuation of a nonzero
element `a` of the subgroup. Closure contains the closure of the integer
multiples of `a`, namely `a Ztwo = 2^r Ztwo`; minimality gives the reverse
inclusion. This supplies both quantified directions in the bundle.

Thus an explanatory derivation is available without treating the proposal's
broad reference to cyclotomic-tower ramification as an exact theorem number.
This paragraph is a mathematical audit argument, **not** a newly formalized
replacement for those three fields.

### 4.2 The K(i) implication and the inertia distinction

Use the canonical coordinate constructed from the unramified quotient.
Actual inertia maps into `ker nu_ur`; equality is neither needed nor true in
general, because `nu_ur` remembers only the two-primary unramified coordinate.
The bundle's hypothesis therefore makes actual inertia act trivially on
`μ₄`. For either root `delta_i^2 = -1`, Galois correspondence puts
`K(delta_i)` in the maximal unramified extension. Its relative ramification
index is 1. A base uniformizer is consequently still a uniformizer, so every
nonzero element in the extension has the same norm as an integral power of
that base uniformizer. This is precisely the equal-value-group condition
encoded by `HasEqualNormValueGroups`; the trivial extension is included.

This argument requires the ordinary identification of the mod-4 cyclotomic
character with the action on `μ₄` and the identification of the spectral norm
with the extended local-field norm. Neither is a new reciprocity axiom.
Neither should be concealed by the false equation `ker nu_ur = inertia`.

## 5. AX4 clause map and convention check

N Chapter VII begins with an arbitrary complete discretely valued field with
finite residue field. Its scope explicitly includes every finite extension
of `Q_p`, not just `Q_p` itself. In (7.5.2)/(7.5.3), `q` is the actual residue
cardinality. The proof chooses a lift of residue Frobenius, so it supplies
the oriented quotient, not merely an abstract isomorphism type.

| Current bundle field(s) | Status | Evidence and translation |
| --- | --- | --- |
| `W`, `normal`, `isClosed` | D/T | Take actual wild inertia. N p. 409 constructs it as the inverse limit of finite ramification groups. Closedness is the usual profinite kernel/inverse-limit fact. |
| `isProP` | D/T | N (7.5.1), p. 409; S IV Section 2 Proposition 7 Corollary 3, pp. 67-68, at finite level, followed by inverse limits. Set residue characteristic to 2. |
| `equiv` | D/T | N (7.5.2)/(7.5.3), pp. 410-411. Translate its profinite presentation to the repository's `Tq`, with geometric generator as below. |
| `nuT_recip_unit` | D/T | S XIII Proposition 13 and its corollary. The coordinate factors through abelianization, so the formula holds for every lift `g` used in the field. |
| `nuT_recip_uniformizer` | D/T | S XIII Proposition 13, with the same geometric-coordinate conversion. The filtration's chosen uniformizer satisfies the required valuation condition. |

NSW writes `phi * tau * phi^-1 = tau^q`, with `phi` arithmetic Frobenius.
The repository writes `sigma^-1 * tau * sigma = tau^q`. Set
`sigma = phi^-1`. The reciprocity map remains **arithmetic**; only the
chosen tame generator and unramified coordinate are geometric. Consequently
the reciprocity image of a uniformizer has coordinate `-1`, exactly as both
bundles require. Inverting the reciprocity map instead would be the wrong
translation for the specified norm and cyclotomic conventions.

There is one additional repository bridge: `qOf K FF = 2^FF.f` must equal the
actual residue cardinality for the supplied filtration. This is established
by `residueField_card_eq_pow_f` in
[UnitFiltrationCounts.lean](../../GQ2/UnitFiltrationCounts.lean), and by
`normInteger_residueField_card_eq_pow_f` in
[ResidueLocalFieldBridge.lean](../../GQ2/Dyadic/ResidueLocalFieldBridge.lean).
It is not permission to replace the residue cardinality by an arbitrary
even integer. Likewise, `W = O₂(G_K)` and `compatF_K` are derived repository
results, not additional literature clauses hidden inside AX4.

## 6. Corrections, unresolved citation work, and non-claims

1. **Historical AX3 proposal overclaim.** Section 1.5 of
   [ax3-proposal.md](ax3-proposal.md) says `1+8Ztwo` is always contained in
   `I`, citing `N(w)=w^n` and the square subgroup of `Ztwoˣ`. For arbitrary
   `n`, this only supplies the **nth-power** subgroup, not necessarily every
   square. For example, if K contains `μ₁₆`, its cyclotomic image, and hence
   `I`, is contained in `1+16Ztwo`, whereas `9` belongs to `1+8Ztwo` and not
   `1+16Ztwo`. The quoted inference is valid in the displayed degree-two
   examples, not uniformly for all finite K. No corresponding axiom field
   occurs in `MarkedRecip`; the owner memo was not edited.
2. **NSW reference precision.** (7.1.1)/(7.1.5) provide the local
   class-formation input, not a single printed theorem spelling all of AX3.
   For norm functoriality, Serre XI Section 3 diagrams (1)/(1)* and XIII
   Proposition 10(a) are now exact checked locators. A vague reference to
   NSW I Section 5 alone should not be described as the full bundle theorem.
3. **No exact standalone cyclotomic-tower locator verified.** The proposals'
   broad Serre IV / NSW VII Section 5 citation was not verified as a theorem
   stating the finite-r formula. Section 4.1 gives the explicit short
   derivation instead. Do not stamp that broad citation as directly verified.
4. **Sources versus encoding.** This audit checks the relevant statements,
   diagrams, conventions, and mathematical implications. It does not audit
   every upstream proof in the books, replace the two axioms by terms, or
   certify their Lean encodings by source quotation alone.
5. **Access status.** No essential target remained inaccessible: the
   university-hosted Serre scan resolved the initial browser size failure.
   The publisher landing page was used for bibliographic metadata only.
6. **Governance.** The owner approvals, source declarations, old proposal
   annotations, and axiom census were left untouched. A future documentation
   revision can replace the blanket PDF-pending wording with this clause-level
   account; it must retain the composite-interface qualifications and the
   inherited-axiom status of the current general endpoint.

No inference in this audit depends on one of the historical small-field
example tables or on the frozen compact-M word. The arguments and the
verified source scope are uniform in finite K.
