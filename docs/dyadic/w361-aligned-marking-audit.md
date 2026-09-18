# W361 independent audit: aligned realization and characteristic orientation

Date: 2026-09-17. Auditor lane: `raw_pairing`.

## Verdict and scope

No circularity, dropped source data, or unproved marking equation was found in the new
aligned endpoint. The calibration replaces only an existentially carried core realization.
The actual presentation word, core, full two-adic unramified marking, and **exact same word
certificate** remain definitionally unchanged. The new realization satisfies both literal
maximal-pro-two compatibility equations.

The new orientation modules prove full characteristicness uniformly in the handle rank.
This additionally implies that calibration preserves the cyclotomic character pulled back
along the original realization; it is not a redefinition of that character to force the
answer.

This audit covers the banked modules:

- `Instances/FieldFamilySpliceTameFinal.lean`;
- `Instances/FieldFamilySpliceAlignedFinal.lean`;
- `OrientationMasterTransport.lean`;
- `Instances/MOrientationCharacteristic.lean` (existing input to the new transport layer);
- `Instances/NOrientationCharacteristic.lean`;
- `Instances/SqOrientationCharacteristic.lean`;
- `Instances/FieldCyclotomicCharacteristic.lean`;
- the relevant marked-reconstruction and characteristic-character transport interfaces.

The independent probe `/private/tmp/W361AlignedFinalAudit.lean` compiled successfully with
default limits. This audit made no proof-module edits.

## No circularity in the construction

The actual dependency order is:

1. An existing branch `G` carries a core realization compatible with `nuP`. It is used to
   construct the arithmetic source over the same abstract pro-two slot as the certificate.
2. Relative reconstruction gives a field equivalence `e` preserving the actual tame map.
   Its full two-adic unramified equation follows from tame reciprocity and the certificate's
   boundary compatibility.
3. Define the new field-to-core projection as `W.pro2 ∘ e⁻¹`.
4. This projection is surjective and has exactly the actual maximal-pro-two kernel, because
   the certificate projection has that kernel and continuous equivalences transport it.
5. The universal property of the maximal pro-two quotient therefore gives a genuine core
   equivalence. The already-proved full unramified equation proves its `nu_equiv` field.
6. Replace `G.realization` by this induced equivalence. Reuse the original `W` and `e`.

No count theorem is re-run using the newly chosen realization. No field equivalence is
assumed in order to produce itself. In particular, the word certificate is established
before calibration and does not depend on the replacement realization.

## Data-retention probes

The independent file verified each of the following by `rfl`:

```
(alignedBranch G W e hnu).degree = G.degree
(alignedBranch G W e hnu).word   = G.word
(alignedBranch G W e hnu).core   = G.core
(alignedBranch G W e hnu).nuP    = G.nuP
(alignedBranch_certificate G W e hnu).cand = W
```

The final line is stronger than the existence of some replacement certificate: the exact
original certificate, with its actual `GammaR` carrier and quotient map, remains the witness.
The branch update also retains `coreIsProP`, `hdeg`, and surjectivity of `nuP` by construction.
There is no hidden equality cast between a canonical frozen word and a changed splice word.

## Exact marking equations

For the newly aligned branch, the endpoint retains the actual tame equation and proves

```
newRealization.pro2 (e g) = W.pro2 g
maxProPMk 2 (GalK K) (e g) = newRealization.equiv (W.pro2 g)
B.nu_ur (toAbK K (e g)) = ztwoIota (G.nuP (W.pro2 g)).
```

These are literal equations, not merely agreement modulo two, conjugacy, or equality of
kernels. The `nu_equiv` obligation also holds before precomposition with the maximal-pro-two
projection, at every element of the core.

The unramified equation here is the complete **two-adic** character exposed by `MarkedRecip`
and `MarkedCoreRealization`. The audit does not reinterpret it as a newly proved signed
full-Zhat reciprocity normalization. The actual tame-map equation is separately retained.

The selected endpoint still assumes the genuine `RamifiedIData K` standing condition and
the existing field bundles. It ranges over all valid selected families and degrees; there
is no new odd-degree, positive-handle-rank, `r`, or epsilon restriction.

## Existential calibration is not fixed-input preservation

`HasSelectedAlignedFlexibleAssemblyRN` existentially quantifies a branch `G`. Its selected
degree agrees with the semantic selection, and its actual word/certificate are retained.
The theorem is allowed to replace the realization carried by that existential witness.

It does **not** prove that the reconstructed equivalence preserves an arbitrary previously
specified realization. That stronger fixed-input claim remains the refined-induction task
described in `w361-full-core-marking-audit.md`. The aligned module's docstrings explicitly
state this distinction.

## Orientation: genuine rigidity rather than calibration by definition

`OrientationMasterTransport.DerivationBasis` bundles actual crossed homomorphisms realizing
all integral generator-coordinate vectors, together with continuity of their additive
coordinates. The transport proof shows:

- their reductions modulo two are ordinary homomorphisms, since every two-adic unit
  reduces to one;
- an automorphic generating tuple still spans all mod-two coordinates;
- the corresponding square evaluation matrix is invertible modulo two and hence over
  `Z₂`;
- linear combinations of the basis masters realize every coordinate vector for the
  pulled-back character.

This is a uniform matrix argument. It does not assume an automorphism classification or
orientation invariance. The N and square-core modules then evaluate their complete defining
relations: the core coordinate identities identify the canonical orientation, and the
independent handle rows force both characters on every handle to be one. No handle is
dropped and no finite rank/class check is substituted for the general proof.

The final core statements cover:

- `DM alpha h`, every `alpha >= 1` and every `h`;
- `DN alpha h`, every `alpha >= 1` and every `h`;
- `DSq h`, every `h`.

`FieldCyclotomicCharacteristic.chiCycKTwo_characteristic_ramifiedI` uses the already-proved
oriented equivalence in the actual range-selected family, then transports characteristicness
to the actual field character. Its family case split selects those existing producers; it
is not a new class-by-class proof of orientation rigidity. No arbitrary-realization
orientation hypothesis is hidden in the final statement.

The independent probe also verified, from characteristicness alone, that

```
chiCycKTwo (newRealization.equiv p)
  = chiCycKTwo (oldRealization.equiv p),

chiCycK K (e g)
  = chiCycKTwo (oldRealization.equiv (W.pro2 g)).
```

Thus alignment retains the original pulled-back cyclotomic character. To name that
pullback as a displayed canonical `chiM`, `chiN`, or `chiSq`, use the established oriented
core equivalence; `GenAsmFlexibleBranch` itself has no separate arbitrary character field.
No conclusion about an independently supplied unmatched character is being smuggled in.

## Independently checked axiom boundaries

The probe printed the exact following baselines:

| Result | Axioms beyond the standard three |
|---|---|
| Alignment construction, both pro-two squares, certificate retention, alignment from a tame witness | None |
| N and square-core characteristic orientation | None |
| Actual field cyclotomic characteristicness in ramified-i scope | `hilbertSymbol_normCriterion_finiteDyadic`, `tateDualityAt`, `Foundations.absGalQ2_isTopologicallyFinitelyGenerated`, `Foundations.absGalQ2_localEulerCharacteristic` |
| Selected aligned endpoint with supplied field bundles | The preceding four, plus `peripheralCyclotomicAction` and `relativeStiefelWhitney_dyadic` |

Here the standard three are `propext`, `Classical.choice`, and `Quot.sound`. Thus the selected
aligned endpoint retains the same nine-total-axiom baseline as the existing selected source
endpoint. It adds no axiom for reconstruction, alignment, or orientation rigidity. Supplying
canonical literature bundles rather than explicit ones has its separately recorded baseline
and is not silently included in this table.

## Final packaging addendum: MarkedFinal and MarkedCanonical

The following additional modules have now been inspected independently after being banked:

- `Instances/FieldFamilySpliceMarkedFinal.lean`;
- `Instances/FieldFamilySpliceMarkedCanonical.lean`.

The extended `/private/tmp/W361AlignedFinalAudit.lean` and the new
`/private/tmp/W361MarkedCanonicalAudit.lean` both compiled successfully at default limits.

### The record keeps the original cyclotomic character

`AlignedMarkedFieldEquiv G W T` contains the reconstructed equivalence and all marking
equations. Its `cyclotomic` field literally states

```
chiCycK K (equiv g)
  = chiCycKTwo (G.realization.equiv (W.pro2 g)).
```

Here `G.realization` is the **original input realization**, not the one constructed from
`equiv`. Thus this field is not a vacuous post-reconstruction definition of the character.
Its proof uses actual field characteristicness as audited above.

The `.pro2` and `.maxPro2` fields explicitly use the aligned realization, and `.branch`
exposes exactly that calibrated branch. The additional independent probes verified:

```
(M.branch G W).word = G.word                         -- rfl
(M.branch G W).core = G.core                         -- rfl
(M.certificate G W).cand = W                         -- rfl
(M.branch G W).realization.pro2 (M.equiv g) = W.pro2 g
maxProPMk 2 (GalK K) (M.equiv g)
  = (M.branch G W).realization.equiv (W.pro2 g).
```

The selected record-valued endpoint retains both the original branch and this aligned
equivalence. Its type constrains the selected degree, not an equality with an old frozen
canonical word. The concrete source producer supplies the appropriate changed word and
certificate; calibration never substitutes a different word afterward.

### Bare field endpoint

`exists_certifiedFullyMarkedFlexiblePresentation_ramifiedI K RI` requires only a finite
intermediate dyadic field `K` and `RI : RamifiedIData K`. Its public signature has no hidden
topology, filtration, degree-parameter, source certificate, or marking hypothesis. The module
constructs the standard topology instances and canonical parameter packet internally.

It returns an existential **new aligned** branch at the exact field degree, its actual
certificate, the actual source-to-field equivalence, and literal tame, pro-two, maximal
pro-two, cyclotomic, and full two-adic unramified equations. In this repackaged statement the
cyclotomic equation is expressed using the returned branch's realization. The proof first
uses `M.cyclotomic` against the original realization and then the characteristic equality
between the old and new realizations. The stronger original-character assertion remains
available in the record-valued selected endpoint.

The odd-degree corollary discharges `RI` via the established odd-degree norm obstruction.
The all-degree theorem does not drop `RI` and does not include fields where `K(i)/K` is
unramified or trivial.

### Final independently printed baseline

- `nonempty_alignedMarkedFieldEquiv`, with the word certificate and compatible field
  packet supplied: standard three plus the Hilbert norm criterion, relative
  Stiefel--Whitney, Tate duality, and absolute-Galois TFG/Euler inputs (eight total).
- `hasSelectedFullyMarkedFlexibleAssemblyRN_fieldSelectionFromRange` and the canonical
  parameter wrapper with reciprocity/tame bundles supplied: the established nine total.
- Both bare ramified-i endpoints, the odd-degree endpoint, and the expanded existential
  theorem: the established twelve total. Compared with the supplied-bundle baseline,
  these add exactly `localReciprocity`, `markedRecipAt`, and `orientedTameQuotientAt`.

No additional axiom, circular assumption, or fixed-input-preservation claim was found in
this final packaging.
