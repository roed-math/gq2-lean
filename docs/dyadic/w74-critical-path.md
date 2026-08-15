# The critical path of `ramifiedI_candidate_equiv_galK`

Lane W74-HOUSE, ticket 1.  Produced against tree `4fff1592`, shared cache at `608d3ded`.
Verification of record: `scripts/mirror.sh` (sweep, check).  **No `lake` command was run.**

This memo answers three questions about the final theorem
`GQ2.Dyadic.ramifiedI_candidate_equiv_galK` (`GQ2/Dyadic/Main.lean:670`):

* **(a)** what each per-row residual record actually asks for, and which workstream owes it;
* **(b)** whether anything on the path consumes the even route's `alpha = 1` stratum;
* **(c)** the smallest set of open statements that closes every record.

Everything numeric below was recounted at this tree and is stated as-of `4fff1592`.

---

## 0.  The shape of the path

The final theorem takes two arguments and does one `cases`:

```
theorem ramifiedI_candidate_equiv_galK (r : FrozenQuadRow) (F : FieldInputs K B FF)
    (S : RowResidual K B FF F.T r) : Nonempty (ContinuousMulEquiv (candidateGroup ...) (GalK K))
```

`RowResidual` (`Main.lean:569`) is a five-way match onto the five records, and each branch is
discharged by one `rowEquiv_*` theorem (`Main.lean:592`-`641`), each of which is one instance
headline re-read off the record.  So the path is **exactly** the union of the five records plus
`FieldInputs`, with no derivation in between.  Field counts, recounted:

| record | fields | expands to |
| --- | --- | --- |
| `FieldInputs` (`:320`) | 6 | 6 |
| `ResidualSqrtNegTwo` (`:352`) | 13 | 13 |
| `ResidualSqrtTwo` (`:391`) | 9 | 8 + `KSupply`'s 9 = 17 |
| `ResidualSqrtFive` (`:435`) | 9 | 17 |
| `ResidualSqrtTen` (`:480`) | 9 | 17 |
| `ResidualSqrtNegTen` (`:524`) | 9 | 17 |

The four `M` rows are field-for-field identical up to the core parameters, so there are really
**three** distinct shapes on the path: `FieldInputs`, the pilot, and the `M` row.

The row cores are `DN 2 0`, `DM 3 0`, `DM 2 0`, `DMpc 2 1 0`, `DMpc 2 1 1`.  **Every row sits at
`alpha >= 2` and at handle count `h = 0`**, and `FieldInputs.params_n` pins the degree slot to
`n = 2 = 2 + 2*0`.  This one observation drives most of §2 and §3.

---

## 1.  (a) The records, field by field, with the owing workstream

Four workstreams appear.  **CLASS** = the classification workstream (the even route at even
degree, the sq/odd graded route at odd degree) which produces the identification of `G_K(2)`
with the row's core.  **ASK** = the K-supply/arithmetic layer (`GQ2/Dyadic/Instances/KSupply.lean`).
**CAND** = the candidate-side clause layer (AS1/AS2/AS3's analytic clauses at `GammaR`).
**DONE** = already proved, or a pin that is definitional at the quadratic slot.

### 1.1  `FieldInputs`: row-independent, 6 fields

| field | owes | note |
| --- | --- | --- |
| `T : OrientedTameQuotientK B FF` | DONE (bundle) | AX4 enters as a *bundle*, never as the axiom `orientedTameQuotientAt`; the docstring at `:314` says so and the tree bears it out |
| `params`, `params_n`, `params_qK` | DONE | F1's package pinned to the quadratic slot; `params_qK` is `rfl` against `qOf K FF` |
| `ramified` | **not to be discharged** | this is the standing hypothesis that *selects* `K`; see §2 |
| `ramifiedData` | DONE (constructible) | LG5's ramified-marking input, constructor `ramifiedCertificateOfSubtype` |

### 1.2  `ResidualSqrtNegTwo`: the pilot, 13 fields

| field | owes | note |
| --- | --- | --- |
| `hdeg : finrank ℚ₂ K = 2` | DONE per field | proved at every committed quadratic model (`finrank_KSqrtNegTwo` and siblings) |
| `fLab`, `horient`, `hpair` | **CLASS** | the Labute/Demushkin identification `DN 2 0 ≅ G_K(2)`, oriented, with a unimodular marked pair |
| `piAb`, `hpiAb`, `hpiNu` | **CLASS**, but see §1.5 | AS2's abelianization slot: `toAbK` does not factor through `G_K(2)`, so this is genuinely extra data *on this producer* |
| `hexact`, `hstokes` | **ASK** | `ExactLiftingSemantics` / `StokesDualityCertificate` at the carrier `galKProfinite K` |
| `hsimp` | **CAND** | `PilotHsimp`, per-simple-module Stokes duality; owner ruling: binder, never axiom.  The module derives every duality payload the count lane consumes from this one binder (`SqrtNeg2.lean:35`-`41`) |
| `hsplit`, `hZcount` | **CAND** | `stageR136`'s two recursion-side residues; `ℚ₂` ancestors are the `RStage` per-carrier computations |
| `hdet` | **CAND**, ⚠⚠ **no supplier lane** | `PilotDet`, the candidate-side `AffineDeterminantCertificate` whole; the count lane closed 9 of the 11 `SourceDataN` clauses on the candidate side and these are the two it did not |

### 1.3  `ResidualSqrt{Two,Five,Ten,NegTen}`: the `M` rows, 9 fields each

| field | owes | note |
| --- | --- | --- |
| `nuP`, `hnuSigma`, `hnuWild`, `hnuP` | **CAND** (construction) | F3's `prop_3_4_three` conditions through AS3's core dictionary.  Main.lean:387 records "satisfiability hand-verified, Lean witness = ticket AS3-b", so this is an *unbuilt construction*, not an open mathematical question |
| `exactLifting`, `stokes`, `scalar`, `determinant` | **CAND** | the four analytic clauses at the candidate carrier `GammaR n q word`.  AS1 divergence 4: the certificate ⇒ count bridges have no owner.  Main.lean §6 prices the row certificate at **13 of 17 fields proved**, these four carried |
| `KS : KSupply` | **ASK** + **CLASS**, see 1.4 | |

### 1.4  `KSupply`: 9 fields, nested in each `M` row

`KSupply.lean`'s own table prices `SourceDataN` at **21 fields, 10 discharged, 11 carried**.
The record's nine:

| field | owes | note |
| --- | --- | --- |
| `hdeg`, `hhom` | DONE | degree and numerics pins; `hhom` is `rfl` at the slot |
| `pro2`, `hpro2`, `ker_pro2`, `nu_compat` | **CLASS** | the pro-`2` coordinate of eq. (27): the marked-core certificate's output.  This is the *same* classification datum as the pilot's `fLab`, in a different spelling (§1.5) |
| `exactLifting`, `stokes`, `determinant` | **ASK** | the K-clones of the `ℚ₂` counting pack.  `KSupply.lean` names precisely what is owed: `GQ2/Phase140/Local.lean`, `GQ2/RStage/Local.lean`, `liftsOver_card_local`, `lemma_8_6_local`, and the LG5 ⇒ `GaussZResidueK` bridge, whose `ℚ₂` ancestor is `GQ2/GaussZ/FinalD.lean` and **which has no `K` clone** |

**[W82-HOUSE, as of `a45bc557`: THAT ROW IS SUPERSEDED IN FULL.  All three named `ℚ₂` objects
have `K`-side successors, and none of the three is a clone.**  Replacement row:

| field | owes | supplier at `G_K` |
| --- | --- | --- |
| `stokes` | **nothing** | `stokesDualityCertificate_galK` (`Instances/KAnalytic.lean:82`) from `hdeg` alone, over the `Γ`-generic `Count/LocalDuality.lean` layer (`:152`, `:178`, `:210`, `:252`) rather than a clone of `Phase140/Local.lean` |
| `determinant` | **the wiring only** | `affineDeterminant_galK` (`GQ2/Dyadic/GaussZ/FinalDK.lean`); flagged already by W79-HOUSE, which corrected item 5 of §3 below but not this row |
| `exactLifting` | **one `Prop`**, `askCStageVanishing` | `liftsOver_card_galK` and `lem86_galK_of_noDescent` (`Instances/KExactLiftingGalK.lean:86`, `:106`) plus `correctedRStageSemantics_galK` give `ExactLiftingSemanticsRN` at every degree; the *frozen* bundle these records ask for differs by the equation-(136) coefficient (`zR = #R²·#D_R` versus `#R^{n+1}·#D_R`) and is equivalent to `askCStageVanishing` at `2 ≤ n`, which is every row's degree |

So the ASK block of this memo's residual surface is **one** `Prop`, not three counting theorems,
and the `Prop` is a coefficient condition.  W81-ASK also showed it is not clearly the right
thing to want: carrying the frozen field at `2 ≤ n` forces `#BoundaryLiftsK = 0` on every frame
with nontrivial Frattini block, i.e. asserts `G_K` has no boundary-framed surjection onto any
such marked target.  The recommended statement change, restating the row records against
`ExactLiftingSemanticsRN`, is an owner item.  See `docs/dyadic/w81-ask-note.md` for the
per-clause tables and `Instances/AskCounting.lean` for the checked restatements.]**

Note `ScalarHilbertCertificate` is *not* a `KSupply` field: `KSupply.lean` §3 proves it
(`scalarHilbert_galK`).  It is the only `SourceDataN` clause discharged at `G_K` by arithmetic.

### 1.5  Finding: the pilot row is one producer-generation behind the `M` rows

The two row shapes ask for the classification datum in **two different and non-interchangeable
spellings**, and neither is the spelling the even route produces.

* The pilot goes through `marked_matching_certificate_KN` (`SqrtNeg2.lean:971`), the
  *abelianization* producer.  Its orientation clause is
  `horient : ∀ x, chiCycKAb K (piAb (fLab x)) = chiN 2 0 x`, which is why `piAb`/`hpiAb`/`hpiNu`
  are record fields at all.
* `GQ2/Dyadic/LabuteInterface.lean:67` carries `marked_matching_certificate_KTwoN`, the direct
  `G_K(2)` producer, whose own docstring says: *"In contrast with the older
  `marked_matching_certificate_KN`, this needs no homomorphism to the full abelianization."*
  Its orientation clause is `∀ x, chiCycKTwo (K := K) (f x) = chiN alpha h x`.
* The even route delivers `OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))`,
  which unpacks to exactly the `KTwoN` clause and **not** to the pilot's.

So restating `ResidualSqrtNegTwo` against `marked_matching_certificate_KTwoN` would remove three
record fields and put the fourth in the spelling the classification workstream actually produces.
That is a **statement change** and is therefore reported here, not made.  It is the single largest
avoidable item on the residual surface: three of the pilot's thirteen fields.

---

## 2.  (b) The `alpha = 1` stratum is OFF the critical path: verified, with a corrected reason

**Verdict: the orchestrator's conclusion is correct.  Its stated reason is not the tree's, and
the reason it gives is weaker than the one available.**

### 2.1  The mechanical half

The transitive import closure of `GQ2.Dyadic.Main` is **427 of the tree's 930 `GQ2` modules**.
Not in it:

* `GQ2.Dyadic.Instances.EvenStratumPoint`, `...EvenStratumFrame`, `...EvenStratumShift`, all
  three `alpha = 1` stratum modules;
* the whole `SqCore/Graded*` family (66 modules), including `SqLamMarkTransitivity` and
  `SqClassClearingSupply`;
* `MarkedCore/NFrameAlphaOne.lean` and `Instances/EvenAlphaOne.lean`.

**[W76-HOUSE, sweep items 10 and 14, two count repairs to this subsection.**  (i) The
`SqCore/Graded*` figure was **68** and is corrected above to **66**.  This memo's preamble
says every number is as-of `4fff1592`; at that commit the family is 66, and the two that make
the difference are wave 74's own `GradedUniformTower.lean` and `GradedDeltaFunctionals.lean`,
which landed on `dyadic` after this memo's tree.  The conclusion strengthens rather than
weakens: 66 then, 68 at the wave-74 close, 69 now, and **zero** of them in the closure at any
of those trees.  Second site of the same figure, `w74-house-note.md:79`, corrected there.
(ii) "930 `GQ2` modules" is right only with the convention stated: `GQ2/` holds **929** `.lean`
files at `4fff1592`, and 930 counts the root `GQ2.lean` as well.  `w74-house-note.md:246`'s
"929 physical" is the same tree under the other convention.  The numerator 427 is exact under
both, since `GQ2.lean` is not in `GQ2.Dyadic.Main`'s closure.]**

**[W77-HOUSE, ticket 1: a rival figure of 325 is refuted; the denominator is dated, the
numerator is not.**  A redundant count-audit reported this closure as **325**, not 427.
Recomputed with the regex of record (`w72-house-note.md` §1.0, which admits `public import`):
**427** at `4fff1592` and **427** at `1d3d5a84`, and the two closures are the *same set*.
**325 is exactly what a plain `^import ` grep returns**, because that grep drops the 586
`public import` lines the aggregators use; the rival number is the wave-72 method trap
reproduced verbatim.  Only the denominator has moved: **936** `.lean` files under `GQ2/` at
`1d3d5a84`, **937** counting the root.  Read line 130 as **427 of 930 as of `4fff1592`**.  The
seven modules added since that tree are reached from `GQ2.lean` alone and never from
`GQ2.Dyadic.Main`, which is why the numerator did not move and why the bullet list above still
holds verbatim.  The `SqCore/Graded*` family is **70** at `1d3d5a84` (annotation (i) above says
"69 now", as of the wave-76 lane's base), and **zero** of the 70 are in the closure.]**

Only four `SqCore` modules are in the closure (`Certificate`, `Cores`, `PivotLemma`, `Rank3`) and
no `Instances/Even*` module at all.  A module outside the closure cannot be consumed by the
theorem, so this settles "consume" in the literal sense.  It does **not** by itself settle the
interesting question, because the residual records are *hypotheses*, and the classification
workstreams exist to discharge them from outside.  §2.2 settles that.

### 2.2  The mathematical half, machine-checked

The `alpha = 1` point is not merely unused; it is **provably outside the standing hypothesis**.
The chain is three committed statements and needs no reciprocity input:

1. `EvenUnram.evenUnram_imChiN_eq_prin_iff` (`EvenUnramified.lean:236`): for `alpha >= 2`,
   `imChiN a = evenRangePrin alpha ↔ a <= 1 ∧ alpha = 2`.  Taking `a = 1`, `alpha = 2`:
   `imChiN 1 = evenRangePrin 2`.
2. `EvenUnram.evenUnram_range_eq_of_oriented` (`:117`) + `OrientationCorrection.range_chiN`
   (`:209`): an oriented equivalence with `chiN 1 h` forces
   `range chiCycKTwo = imChiN 1 = evenRangePrin 2`.
3. `EvenRangeModel.evenRangeF_hasEqualNormValueGroups_of_range_eq_prin`
   (`EvenRangeModelFields.lean:890`), whose docstring is *"The third stratum is exactly the
   unramified one"*: from `range = evenRangePrin beta` with `2 <= beta`, `K(i)/K` is unramified
   for **every** choice of `i`, that is, `HasEqualNormValueGroups K deltaI` holds.

Step 3's conclusion is the literal negation of `FieldInputs.ramified`.  I composed the three into
a standalone check and ran `scripts/mirror.sh check` on it; both statements elaborate and print
**std-3** (`[propext, Classical.choice, Quot.sound]`):

```lean
theorem w74_orientedN_one_forces_unramified (B : MarkedRecip R K) {h : ℕ}
    (e : OrientedContinuousMulEquiv (chiN 1 h) (chiCycKTwo (K := K)))
    (deltaI : ℚ̄₂) (hdeltaI : deltaI ^ 2 = -1) : HasEqualNormValueGroups K deltaI

theorem w74_ramified_excludes_alphaOne (B : MarkedRecip R K)
    (hram : ∀ deltaI : ℚ̄₂, deltaI ^ 2 = -1 → ¬ HasEqualNormValueGroups K deltaI) (h : ℕ) :
    IsEmpty (OrientedContinuousMulEquiv (chiN 1 h) (chiCycKTwo (K := K)))
```

The check file is a lane artefact and is **not** added to the tree (plan A6 freeze, and the three
sibling lanes own the new modules this wave).  Anyone re-running it needs
`import GQ2.Dyadic.Instances.{EvenUnramified, EvenParityModel}` and the four `open`s for
`EvenUnram`, `EvenRangeModel`, `EvenParity`, `EvenCyclotomicRange`.

### 2.3  Three corrections to the briefing

**(i) The `demushkinQ = 2` route is conditional; the stratum route is not.**  The orchestrator's
reason runs through `demushkinQ (D_N 1 h) = 4` against `demushkinQ (G_K(2)) = 2`.  The first
half is unconditional (`NFrameAlphaOne.lean:614`, `nFrame4_demushkinQ_DN_one`).  The second is
**not**: `EvenDemushkinQ.demushkinQ_maxProTwoGalK_eq_two_of_ramifiedI` (`:149`) carries
`hrecip : Function.Injective (proTwoReciprocityToTopAb B)`, completed-reciprocity injectivity,
which is itself unproved in the tree.  So the demushkinQ argument buys the conclusion only on
credit.  §2.2's route buys it outright.

**(ii) "forcing `i ∈ K`" is not a tree implication.**  `EvenUnramified.lean:429`-`432` records
explicitly that the implication in that direction *is not available and is not true*: a `K` with
`K(i)/K` unramified quadratic has `i ∉ K`.  What the tree has is `i ∈ K ⟹ third stratum`
(`evenUnram_range_le_prin_two_of_sqrt_neg_one`, `:478`) and `third stratum ⟹ unramified`
(step 3 above).  The composite that matters runs through the stratum, never through `i ∈ K`.

**(iii) `alpha = 1` is an `N`-only phenomenon, and the `M` row is excluded for a different
reason.**  `EvenForwardRouteSkeleton.lean:85`-`87` records that at `alpha = 1` the `M` row has
`demushkinQ = 2`, the same as a ramified-`i` field, so the `q`-invariant argument does **not**
exclude the `M` row there.  What excludes it is `evenUnram_isEmpty_orientedM` (`:544` for the
model field): `imChiM a` contains `-1` for every `a` and `evenRangePrin alpha` omits it for
`alpha >= 2`, so the `M` row never meets the third stratum at all.  A briefing that says
"the `alpha = 1` point has `demushkinQ = 4`" is describing one of the two branches.

### 2.4  Consequence for the workstream

Confirmed: **the `alpha = 1` stratum work is classification-completeness, not load-bearing for
the final theorem.**  It decides what the even classification *says* at the one field family the
five frozen rows exclude by hypothesis.  `EvenUnramified.lean:517-519` states the same thing from
the other side, and is worth quoting because it is the tree's own sentence on this point:

> This is the tree's first named field on the third stratum; the five committed quadratic rows
> (`±2, 5, ±10`) all carry odd valuation and are ramified-`i` fields.

Two caveats before the workstream is deprioritised.  First, this argument is about the **path**,
not about the **paper**: `evenUnram_classification_conclusion_false` (`:361`) shows the
ramification binder on `parityFinal_evenClassification` is *necessary*, so a classification
statement that dropped it would be false, and the stratum work is what establishes where the
boundary sits.  Second, the same reasoning that takes `alpha = 1` off the path also takes it off
for the `alpha >= 3` third stratum, which is already known empty, so the stratum programme's
remaining value is entirely at the single surviving point.

---

## 3.  (c) The smallest closing set

A preliminary, and it is load-bearing for how this list should be read.

**"Close every record at every ramified-`i` `K`" is not achievable, and should not be a goal.**
The records are not all obligations; some of them *select* `K`.  `fLab`, `horient`, `hpair` and
`KSupply.pro2`/`hpro2`/`ker_pro2`/`nu_compat` assert that `G_K(2)` **is** the row's specific core
at the row's specific `(alpha, h)`.  No theorem can supply those at an arbitrary ramified-`i`
`K`, because a ramified-`i` `K` of the wrong degree or the wrong branch simply is not that row's
field.  The honest goal is: *close every record at every ramified-`i` `K` **that the row's branch
identification places on that row***.  The list below is written to that goal, and item C is the
item that makes the difference explicit.

### The list: eight items, in three groups

**A.  The classification input (group CLASS), for the row's own `(alpha, h)`.**

1. **The branch identification, per field**: `range chiCycKTwo = imChiN alpha` (resp. `imChiM`)
   at the row's depth.  This is pure arithmetic about `K` and is what turns the even route's
   *existential* output, `parityFinal_evenClassification` gives `∃ alpha >= 2, (M-branch ∨
   N-branch)`, into the row's specific core.  `parityFinal_orientedEquivN_sqrtNegTwo`
   (`EvenParityModel.lean:257`) already takes exactly this as `hrange`.  **This is the smallest
   genuinely-open item and it gates all five rows.**
2. **The `KTwoN`/`KTwoM` adapter into the two record spellings** (§1.5).  Not open mathematics,
   a restatement, but until it is done the even route's output does not typecheck into either
   record.

**B.  The `G_K`-side counting pack (group ASK), three clause bundles, one carrier.**

3. `ExactLiftingSemantics (galKProfinite K) ...`, the `K` clones of `liftsOver_card_local` and
   `lemma_8_6_local`.  `KSupply.lean:256`-`260` narrows the second to **one existential**: the
   `K` analogue of `RadicalEdgeLocal.exists_good_twist` (public entry `half_torsor_local`).
4. `StokesDualityCertificate (galKProfinite K) ...`, `tcocycle_card`, `hsep`, `hpartial`,
   `hZcard` at `G_K`.
5. `AffineDeterminantCertificate (galKProfinite K) ...`, the **LG5 ⇒ `GaussZResidueK` bridge**,
   i.e. the (83)-evaluation rung from an Arf/zero-count statement to `GaussZResidueK`.
   `KSupply.lean` is explicit that this has **no `K` clone** and that inlining a hypothesis named
   after LG5 would have hidden the gap.  ⚠⚠

**[W82-HOUSE, as of `a45bc557`: GROUP B IS DOWN TO ONE `Prop`, and it is not any of items 3-5
as stated.**  Item 4 is a theorem (`stokesDualityCertificate_galK`), item 5 is a theorem
(`affineDeterminant_galK`, W79-HOUSE), and item 3's named existential is a theorem
(`lem86_galK_of_noDescent`) as is its companion (`liftsOver_card_galK`), which together with
`correctedRStageSemantics_galK` give `ExactLiftingSemanticsRN` at every degree.  The residue is
the coefficient by which the **frozen** `ExactLiftingSemantics` differs from the corrected one,
and `askC_exactLifting_iff_stageVanishing` identifies it exactly, at `2 ≤ n`, with the single
`Prop` `askCStageVanishing`.  Two footnotes.  (i) Item 3 cites `KSupply.lean:256`-`260` for the
narrowing sentence; at those lines sits `scalarHilbert_galK`, and the sentence is in the
`lem86_galK` docstring further down (now annotated there).  (ii) The remaining `Prop` may be
the wrong thing to want: it is equivalent, at the campaign's degree, to `G_K` admitting no
boundary-framed surjection onto any marked target with nontrivial Frattini block.  The
recommended restatement against `ExactLiftingSemanticsRN` is an owner item.]**

**C.  The candidate-side clause layer (group CAND).**

6. The four analytic clauses at `GammaR n q word`, `exactLifting`, `stokes`, `scalar`,
   `determinant`, i.e. the **certificate ⇒ count bridges**, AS1 divergence 4.  One statement per
   clause, uniform in the row (all four `M` rows ask for the identical shape at different words),
   so this is four statements, not sixteen.
7. The pilot's four named candidate residuals: `hsimp` (`PilotHsimp`), `hsplit`/`hZcount`
   (`stageR136`), and `hdet` (`PilotDet`).  `hdet` is the ⚠⚠ item: no supplier lane was ever
   opened.  Note `hsimp` is *one* binder from which the module derives every duality payload the
   count lane consumes, so it is a single statement with unusually high leverage.
8. The `nuP` construction for the four `M` rows (`nuP`/`hnuSigma`/`hnuWild`/`hnuP`), ticket
   AS3-b.  Hand-verified satisfiable; this is a build, not a proof.

### What that adds up to

| group | statements | status |
| --- | --- | --- |
| A | 1 open (arithmetic, per field) + 1 restatement | the even route is otherwise **closed as mathematics** at even degree |
| B | 3 clause bundles at `G_K` | one of them (item 5) has no owner and no `ℚ₂`-to-`K` rung |
| C | 4 + 4 + 1 construction | two of the nine (`hdet`, and the `gaussZ` half of item 5) are the same mathematics on the two sides |

**The single sharpest statement on the list is item 5 / `hdet`**: the Gauss-`Z` determinant
residue is the only place where *both* sides of the two-sided architecture are carried and
neither has a supplier lane.  Everything else is either owned, or a restatement, or arithmetic
about a specific quadratic field.

**[W82-HOUSE, as of `a45bc557`: the scoreboard and the "sharpest statement" verdict have both
moved, in group A as well as group B.**  Replacement scoreboard:

| group | statements | status |
| --- | --- | --- |
| A | item 1 is **closed at four of the five rows** | `fieldUni_genAsmBranch_sqrtNegTwo` / `_sqrtTwo` and `mpcNorm_genAsmBranch_sqrtTen` / `_sqrtNegTen_of_pivot` are branch data over the bundles alone (rows 1, 2, 4) or over one clause (row 5, the `ε = true` pivot); row 3 (`ℚ₂(√5)`) carries `fieldUni_TwoIsUniformizer KSqrtFive`.  Item 2, the `KTwo*` adapter, is the standing "pilot spelling" owner item |
| B | **one `Prop`**, `askCStageVanishing` | items 4 and 5 are theorems; item 3 is one coefficient, see the annotation above |
| C | 4 + 4 + 1 construction | unchanged by waves 79-81; `hdet` / `SqrtNeg2.PilotDet` is still unowned |

The half of the verdict that survives is the half about `hdet`: the **candidate** side of the
Gauss-`Z` determinant residue is still the only clause with no supplier lane.  The half that
does not survive is "item 5": the arithmetic side has one.  The genuinely sharpest OPEN item on
the board is no longer on this list at all, it is the odd seam
(`LSquare.SqMarkedForwardSupply B h` at `h ≥ 1`, `docs/dyadic/w81-oddid-note.md`), which serves
the `L` row that §3's own closing bullets set aside as already unconditional.]**

### What is NOT on the list, and should be said out loud

* The `alpha = 1` even stratum (§2).
* `SqClassClearingSupply h k` at any class, and `SqLamMarkTransitivity h` at any `h >= 1`.  The
  frozen quadratic table is at `h = 0` on `M`/`N` cores; the `Sq` core and its graded route serve
  the **`L` row / odd degree** (`Main.lean` §7, `wordCertificateLSq`, which is already
  *unconditional*).  Waves 68-73's class-four and class-five work is therefore also
  classification-completeness with respect to *this* theorem.
* `demushkinQ (G_K(2)) = 2` as such.  It is a hypothesis of the older `abstractEquiv_KTwoN/M`
  adapters (`LabuteInterface.lean:200`), not of the even route, and the even route is the live
  producer.  A lane that spends effort on completed-reciprocity injectivity in order to get `hq`
  is working on the superseded path.
