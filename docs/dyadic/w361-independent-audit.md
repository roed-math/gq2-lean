# W361 independent interface and claim audit

Date: 2026-09-17. Auditor: `raw_pairing`, acting independently of the final
boundary/assembler authors. This was a read-only proof audit; the only new files
were this note and the local compile-only probe `/private/tmp/W361IndependentAudit.lean`.

## Verdict

The checked source-closure claim is justified: the pair-splice and mobile-Mpc
splice have complete `FlexibleCertificateLeavesRN`, including the affine
determinant, for the actual changed `GammaR` word. Their constructors do not take
a Stokes, phase, determinant, field-ramified-data, or raw-relator-death hypothesis.
Their new dependency footprints are the standard three axioms only.

The selected even-M bridge is also genuine, but conditional in precisely the
advertised field-side ways. It keeps ordinary pro-2 orientation and the existing
M0 canonical-or-strict boundary explicit. Its canonical M0 alternative takes the
existing canonical residual producer explicitly. It produces a **flexible
changed-word residual**, not a residual at the frozen selected word.

This is not yet an unconditional presentation theorem for every finite dyadic
field. The separate compatible field packet and the inherited arithmetic
theorems used by final assembly remain outside source closure.

## Exact concrete source endpoints

| Constructor | Remaining input beyond ordinary types | Coverage |
| --- | --- | --- |
| `EvenMHeadHandlePairSpliceBoundary.headHandlePairSplice_flexibleCertificateLeaves` | `2 ≤ alpha`, nonzero even `q`, `j : Fin h`, actual `nuDM`, and `nuDM(dmGen ... (handleIdxU j)) = ztwoOne` | Every valid alpha and every rank admitting the specified promoted handle |
| `MpcMobileSpliceBoundary.mpcMobileTameSplice_flexibleCertificateLeaves` | `2 ≤ alpha`, nonzero even `q`, semantic unit `eta`, actual `nuM`, and `ztwoIota(nuM(dmD ...)) = ofAdd eta` | Arbitrary `r`, `p`, and `h`, including `h = 0` |

Both signatures also expose `1 ≤ alpha`; this is redundant with `2 ≤ alpha`,
not an additional mathematical restriction. The latter bound is supplied by
validity of the selected M0/Mpc branch. Nonzero even `q` is supplied by
`two_le_qOf` and `even_qOf` at the field interface.

The full words are respectively:

- `headHandlePairSpliceW alpha h q ... j nuDM`;
- `tameSplice (mpcMobileTameCorrectedW ... alpha r p h eta ... nuM)
  (Words.MCompact.mCompactW alpha h)`.

All analytic clauses are attached to `GammaR (2 + 2*h) q` of these words.
No old canonical `GammaR` carrier is substituted at the final certificate.

The probe explicitly instantiated the Mpc certificate at `h = 0` with arbitrary
`r` and `p`. It compiled at default limits. Thus zero handles are not merely
suggested by a comment or hidden behind an impossible handle index.

## No residual analytic or boundary hypothesis is hidden

`UniformStokesSupply` quantifies over every finite target group and every finite
elementary-two coefficient module. The two concrete supplies discharge the
simple action-image branches and then invoke the general finite-module ladder;
they do not stop at simple modules or a finite list of nilpotency classes.

The abstract `UniformStokesSupply.determinant_of_branchFree` does require a phase
supply. This is not left as an input to either concrete certificate constructor:
both `...Splice_branchFreeSupply` theorems construct it. The boundary comparison
splits on the actual tau action and supplies:

- in the unramified branch, actual projected tau identity, actual projected
  `powOmega2 sigma = 1`, and sigma fixed-point-freeness from the faithful head;
- in the ramified branch, actual odd order and fixed-point-freeness of projected
  tau, then the generic compact-M shadow-splice comparison.

The nonzero/simple/nontrivial module and radical-index premises occur where the
existing determinant specification demands them. They are not new global field
or source assumptions. The two Gauss branches are identified using the proved
even-degree equality at `n = 2 + 2*h`, rather than by assuming a sign.

The quadratic statements evaluate the full `kappa0` central extension, retaining
the factor-set `m` charge. In particular, the raw pair computation proves a full
central-extension equality before taking its scalar fibre. There is no silent
replacement of the Hessian by only the bilinear Heisenberg pairing.

## Core marking and unramified compatibility survive

`TameShadowWord.CorePresentation.ofTameSplice` retains the original normalized
core marking, not only the abstract isomorphism type of the pro-2 quotient.
`FlexibleCoreLeavesRN.ofTameSplice` retains both normalized rows:
`nu_sigma = ztwoOne` and every `nu_wild = 1`.

The final leaves use the canonical `tameOfSpec`, the core map from that same
`CorePresentation`, and `C.compat`. The latter proves equality of their
unramified characters. `wordCertificateRN_of_flexibleLeaves` carries through
the core-map surjectivity, exact maximal-pro-2 kernel, and compatibility.
No nu-compatibility obligation disappears in the determinant assembler.

At the field bridge, `nuP` is `mFieldTransportZ B e.1`, with its proved
surjectivity and the exact `ztwoIota_mFieldTransportZ` realization equation.
The selected Mpc proof does **not** replace this map by the displayed eta:
it proves its actual D-coordinate is a unit and chooses that unit as `etaD`.

## Resolver consistency

The source word and resolved family are coefficient-independent:
`pinnedResolvedFamily n q R N` depends on `N` and the actual word, not on a
chosen coefficient module. Its Z2 resolver is defined through the same pinned
Zhat resolver, preventing inconsistent values at coincident power nodes.

`OmegaPinnedLevelResolver` resolves every genuine profinite/2-adic exponent in
every finite target killed by `N`. At `4 * exponent C`, the complete Heisenberg
extension is covered. The omega representative is the positive natural
`omega2Exp N`, with the required residue one modulo four.

For quadratic traces the level is instead taken at the full graph group
`SemiProd C V`. This is legitimate use of the same universal level family, not
a change of source word. `GammaRUniformWordPhaseSeam` resolves every word in
the full central extension at that level. `HessianPinnedResolverTransport`
uses a **surjective lower-group projection** to bound the projected full central
extension; it does not infer central resolution merely from action-image
resolution. The actual boundary comparisons construct that surjection.

I found no resolver-level mismatch between the normal-form, projected phase,
scalar trace, and final determinant consumers.

## Selected coverage and deliberate exclusions

`EvenMSelectedSpliceComplete` supplies:

- strict M0 level zero: the old normalized strict U row is `2^0 = 1`, exactly
  the input to the pair source;
- every selected positive Mpc level: `D = eta + 2^r*w`, with `r > 0`, implies
  the actual D-coordinate is a unit. This works for both epsilon values and
  every handle count; no canonical C-placement is used;
- the M0 canonical alternative through an explicit old canonical residual
  producer. At zero handles the strict alternative is impossible, so the
  existing C-pivot alternative remains the appropriate path.

`SelectedEvenMCompleteInputs` is not an unconditional proof that these field
inputs exist. The ordinary orientation is known to have existing producers
from a selection carrying `MatchesCyclotomicRange`; the M0 strict dichotomy
also has an existing range-matching producer. They are deliberately not called
inside the new standard-three bridge.

`HasSelectedFlexibleRowResidualRN` records selected degree, field-tied flexible
branch, and complete residual. It deliberately forgets equality with the frozen
word. The concrete witnesses still carry `DM alpha h` and the actual transported
nu. No theorem converts the new source into `HasSelectedRowResidualRN` for the
old frozen word, and no proof of the false distinguished-C assertion is used.

## Checked axiom boundary and remaining field premises

The local audit probe rechecked the concrete pair/Mpc flexible leaves, both
finite pushed-Stokes producers, selected complete-data constructors/dispatcher,
and generic scalar, exact-lifting, Stokes-certificate and determinant consumers.
All printed exactly `[propext, Classical.choice, Quot.sound]`.

For contrast, the existing producers outside the new closure print:

- ordinary selected M orientation and M0 strict-boundary producer: standard
  three plus `hilbertSymbol_normCriterion_finiteDyadic`, `tateDualityAt`,
  `Foundations.absGalQ2_isTopologicallyFinitelyGenerated`, and
  `Foundations.absGalQ2_localEulerCharacteristic`;
- canonical M0 residual producer: standard three plus
  `peripheralCyclotomicAction`;
- `genAsmFlexible_candidate_equiv_galKRN_compatible`: standard three plus
  `hilbertSymbol_normCriterion_finiteDyadic`, `relativeStiefelWhitney_dyadic`,
  `tateDualityAt`, and the two named absolute-Galois foundations above.

The final assembler's explicit `GenAsmCompatibleFieldInputs` consists of an
oriented tame quotient, field parameters with degree/q identifications, and
`CompatibleRamifiedDataAt` for that actual tame quotient. The latter quantifies
over compatible head-inflated field representations and supplies genuine field
ramified certificates. It is not supplied by the new candidate-source
determinant, and the two must not be conflated.

The W300 route to this field arithmetic still has its base absolute-residue,
abstract tame reciprocity, and relative finite-abelian norm-reciprocity laws.
This audit does not claim that any of those laws follows from the current
`MarkedRecip` bundle. Parallel lanes are investigating anchored norms
(`source_audit`), actual tame/absolute inertia (`odd_front_audit`), and base
reciprocity normalization (root).

## Next bounded theorem task

The agreed next task is the **relative odd-cyclotomic unramifiedness theorem**:
for arbitrary finite `K/Q₂` and an odd-order primitive root `ζ`, prove that
`K(ζ)/K` has relative ramification index one and therefore equal norm-value
groups. The proof uses faithful action on the relative residue field, not a
relative norm-reciprocity assumption. In particular `K/Q₂` is not required to
be Galois.

This lane owns the relative degree argument and the concrete norm-value
witnesses. `source_audit` separately owns the absolute odd-root-field theorem
and the fixed-field/finite-containment bridge; `odd_front_audit` owns the
actual-inertia/reciprocity bridge. Their intended composition is containment
of the anchored field in odd-cyclotomic composita, followed by equal norm-value
groups. These are general field arguments, without a presentation class or
handle-count restriction.

Follow-up outcome: `RamifiedCertificateRelativeOddCyclotomic.lean` is now
checked and cached. Its 13 public declarations have standard-three axiom
footprints. In particular, `relativeOddCyclotomic_relE_eq_one` proves the
relative ramification statement, and
`exists_same_norm_mem_base_of_mem_odd_cyclotomic` constructs the promised
nonzero base-field norm witness, without a filtration premise on the upper
field. This does not itself discharge the independent actual-inertia/tame
compatibility premise needed by the anchored-field composition.

Verification command used for the independent probes:

```sh
bash /private/tmp/gq2-w360-lean.sh /private/tmp/W361IndependentAudit.lean
```

Result: exit 0, including the explicit zero-handle Mpc specialization. The
parent-owned full rebuild and repository gates are separate checks; this note
does not claim to have rerun them.
