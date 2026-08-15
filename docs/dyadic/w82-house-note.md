# W82-HOUSE: the stale-records sweep, watch round 19, and the endgame board

**Lane W82-HOUSE, branch `claude/w82-house`, base `a45bc557`.**  Standing verification lane.
Comment-only throughout: no statement anywhere in the tree was changed, no theorem added or
removed, no `sorry`, no axiom, no import, no `GQ2.lean` edit, no `GQ2/Roe/` edit.

Verification of record: `scripts/mirror.sh sweep` at lane start (5958 artifacts), then `check`
on every edited module, all green.  `scripts/mirror.sh check GQ2/AxiomLedger.lean` green, exit
`0`, **0 terminal violations**.  **No `lake` command was run.**

`dyadic` advanced past this lane's base mid-round, to `db50b7a4` (W82-CAND's `LRowCand.lean`
plus its registration).  Annotations written against the advanced tree say so explicitly; the
rest are as-of `a45bc557`.

## Headline

**The campaign's newest big claim survives the near-miss check exactly.**  `oddId_orientedEquiv`
is what it says it is: the oriented identification at explicit handle count from a marked bundle
and the degree pin alone, and its census is exactly {B1, B6, B7, B11a}.  So are all sixteen of
that module's pins, all thirteen of `AskCounting`'s, and every value theorem the norms lane
matched against the frozen rows.  I elaborated the pins rather than reading them: 16 + 13 + 72
`#print axioms` lines, and **every one of the three lane notes' axiom tables is exact**.

**What is wrong is prose, and the pattern is the wave-81 pattern one turn further in.**  The
worst finding is not that a remains-list has a theorem on it.  It is that the lane whose whole
purpose was to catch that produced a fresh instance of it, in an annotation, about a theorem ten
days older than its own base, while its own wave sibling was building on that theorem.

**And there is a root cause, which nobody has named.**  Ten of the eleven stale sites I found
point, directly or transitively, at `KSupply.lean` §6.  Item **AB-0** of
`docs/dyadic/followup/analytic-bridges-plan.md` §6, "correct the stale obligation
inventories in `CertificateMain.lean` and `KSupply.lean`", was queued six waves ago and
never done, while AB-2 through AB-7 all landed.
Every wave since has annotated the symptom.

---

# Findings, by severity

## S1.  The odd-degree equivalence: a wave-81 annotation is false at its own base

**`GQ2/Dyadic/GeneralAssembly.lean:546-548`** (the W81-HOUSE block), verbatim:

> What does NOT change with the closure: the `L`-row's other open binder
> `e : OrientedContinuousMulEquiv (SqCore.chiSq h) (chiCycKTwo)`, which IS the odd-degree
> classification statement and **which no theorem in this tree produces at an arbitrary
> ramified-`i` `K`**

and its twin at **`docs/dyadic/w81-house-note.md:362`**:

> This binder **is** the odd-degree classification statement; **no theorem in the tree produces
> it at an arbitrary ramified-`i` `K`**.  … what `genAsm_branch_of_oddSq_canonical` still binds
> is `hdeg`, `e`, `hsigma`, `hx0` - of which **only `e` is deep**.

**Correction.**  `LSquare.nonempty_orientedEquiv_oddDegree`
(`GQ2/Dyadic/Instances/GammaLSylowPreimageFieldLabuteCubicNeutral.lean:249`) is

```
theorem nonempty_orientedEquiv_oddDegree (B : MarkedRecip Rec K) (hodd : Odd (finrank ℚ₂ K)) :
    Nonempty (OrientedContinuousMulEquiv (SqCore.chiSq ((finrank ℚ₂ K - 1) / 2)) (chiCycKTwo))
```

with no further hypothesis.  It landed **2026-08-05** (`dde1ec3a`, `0e396715`), ten days before
the annotation, and is present at `git show 6f2916f3:` the annotation's own base.  Ramifiedness
at odd degree is itself free (`not_hasEqualNormValueGroups_sqrt_neg_one_of_odd_finrank`, which
the same section of that note states correctly), so `e` **is** produced at every odd-degree
ramified-`i` `K`.

The ranking in the last clause is therefore inverted.  What is deep is the **pair `hsigma`,
`hx0` at the equivalence**: the transported pivot row's parity is an invariant of the target
(`SqCore/PivotClimb.lean` §9) and the rows do not follow from orientation
(`Instances/GammaLSylowPreimagePivotNu.lean` §5, a refutation).  The honest seam is
`LSquare.SqMarkedForwardSupply B h`, and `oddId_supply_iff_certificate` shows it is
interchangeable with the `L`-row marked-core certificate with **no side binder at all**.
**The odd residual is the rows, not the equivalence.**

**Why this is S1 and not a footnote.**  Three things compound:

1. *Own-base blindness* - the theorem predates the base, which is the named pattern, now at its
   fourth recorded instance.
2. *Sibling blindness* - W81-ODDID, off the **same base**, in the **same wave**, built its entire
   §1 on that theorem (`oddId_orientedEquiv` is three lines of re-indexing over it).  So the
   wave contained both the claim and its refutation.
3. *It came from the auditing lane.*  W81-HOUSE's own headline is that "the wave-80 lanes ran
   blind to each other and to their own base", and its §3.4 congratulates the protocol for
   catching one instance at commit time.  The re-check caught the ASK sibling and missed the
   ODDID one.  A re-check that reads only the branches that merged before you is half a check.

Both sites annotated.  Verified by elaboration, not by reading: `oddId_orientedEquiv` prints
`[propext, Classical.choice, hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt, Quot.sound,
absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic]`.

## S2.  `ℚ₂(√5)` is not open, and the norms note contradicts itself about it

**`docs/dyadic/w81-norms-note.md:169`** (§6 table row 3) and **`:216`** (§8 item 2), verbatim:

> | 3 | `ℚ₂(√5)` | `.M0 2 0` | `fieldUni_genAsmBranch_sqrtFive_of_unramified` |
> `fieldUni_TwoIsUniformizer KSqrtFive` |

> 2. **`fieldUni_TwoIsUniformizer KSqrtFive`** (row 3), **still open** and unchanged by this lane.

**Correction.**  `fieldFive_twoIsUniformizer : fieldUni_TwoIsUniformizer KSqrtFive`
(`GQ2/Dyadic/Instances/FieldSqrtFiveUnramified.lean:209`, commit `b1bd2e64`, wave 79) proves it
with **no hypotheses**, and `fieldFive_genAsmBranch_sqrtFive` (`:235`) is the row-3 branch datum
with no clause at all.  Registered at `GQ2.lean:868`.  Present at the note's own base.

The note's §6 prose even reaches the right total by the wrong route: it says "**four of the five
rows' branch data now stand over the bundles alone**" and then "the **two** open items", which is
six of five.  Its own table lists three free rows.  The resolution is that four is right and the
table's row-3 cell is wrong.

**And the fact was known in-wave.**  `docs/dyadic/w81-house-note.md` §3.5 records exactly this,
and flags `w80-rowdata-note.md` §7 item 4 for the orchestrator.  So wave 81 contained a lane that
knew, a lane that did not, and a handover that nobody executed.  Three files annotated
(`w81-norms-note.md` §6 and §8, `w80-rowdata-note.md` §7, whose four "what is next" items are now
all settled).

## S3.  The ASK straggler field: eleven sites, and a root cause

The ASK lane listed two stale sentences for me (`KSupply.lean` §4/§6, `w74-critical-path.md`
§1.4).  A tree-wide sweep on the subjects found **eleven** unannotated sites, of which nine were
outside that list.  All annotated this round.  In tree:

| file:line | verbatim (abridged) | subject |
|---|---|---|
| `KSupply.lean:275` | "at `K` it is **unowned**, which is why it is carried whole" | half-torsor |
| `KSupply.lean:82-88` | "The K-clones of the `*Local` counting pack … **are still owed**" | both |
| `KSupply.lean` §6 items 2, 3 | "the natural first targets for a follow-on ticket" | both |
| `GeneralAssembly.lean:250-253` | "the `K` analogue of `half_torsor_local`" | both |
| `SqrtNeg2.lean:57-59` | "**still owed by the `Phase140/Local`-successor lane**" | both |
| `MpcRowData.lean:603` | "from the two **genuinely unowned** counting clauses" | both |
| `LiftingDualityG.lean:78-80` | "Those consume `prop_5_16` and **remain owed**" | stokes |
| `GaussZ/FinalDK.lean:167`, `:200` | "the **(unowned)** `K`-clone" | stokes |
| `CertificateMain.lean:168-170` | "at general `K` it **has no owner**" | exactLifting |

and in live documents: `w74-critical-path.md` §1.4 and §3 group B and its closing scoreboard;
`literature-axioms-dyadic.md:162-163` (the G3 trust boundary a reviewer reads);
`followup/analytic-bridges-plan.md:24-27`; `followup/glab-ksupply-plan.md:32-38`.

**What is actually true**, verified against the Lean and the pins:

* **`stokes` is free.**  `stokesDualityCertificate_galK` (`Instances/KAnalytic.lean:82`), all
  four clauses from `hdeg` alone, over the `Γ`-generic `Count/LocalDuality.lean` layer
  (`:152`, `:178`, `:210`, `:252`).  The `Phase140/Local.lean` residues were never cloned, which
  is exactly the shape `KSupply.lean` §6 item 3 predicted.  Pins: B6 + B7.
* **`determinant` is free** given the packet's `ramifiedData`.  W79-HOUSE said so; only the
  wiring is outstanding.
* **`exactLifting` is one coefficient.**  `liftsOver_card_galK` + `lem86_galK_of_noDescent` +
  `correctedRStageSemantics_galK` give `ExactLiftingSemanticsRN` at every degree.  The frozen
  bundle pins (136) at `zR = #R²·#D_R` where `G_K` counts `#R^{n+1}·#D_R`, and
  `askC_exactLifting_iff_stageVanishing` makes the two the same statement at `2 ≤ n` as
  `askCStageVanishing`.  Every live row is at `n = 2`.

**Root cause.**  `followup/analytic-bridges-plan.md` §6 item **AB-0** is "correct the stale
obligation inventories in `CertificateMain.lean` and `KSupply.lean`".  AB-2 through AB-7 landed;
AB-0 never did.  Every one of the eleven sites is either those two files or a pointer into
`KSupply.lean` §6 (`Main.lean:71`, `:75`, `:348`, `:368`, `:371`, `:390`, `:427`;
`Instances/Sqrt2.lean:184`).  Annotating the leaves does not stop the propagation; AB-0 does,
and it is a statement change.  Recorded as a new owner item.

## S4.  The CAND constructor table: one row stale since wave 76, one since this round

**`GQ2/Dyadic/GeneralAssembly.lean:297-306`**, verbatim rows:

> | `Npc α r η h` | none | none |
> | `L h` | none over `D_sq h` | see `genAsm_nonempty_equiv_L_core_piBd` |
>
> So the CAND field is not a placeholder for a solved problem: **on three of the five rows the
> campaign has no producer at free parameters at all.**

Both rows are wrong.  `genCertNpcWordCertificate` (`GeneralCertificates.lean:727`, wave 76)
covers `Npc` at free `(α, r, h, q)`; `Instances.LRowCand.lCand_wordCertificateCanonical`
(W82-CAND, `b465ffdc`) covers `L h` at free `(h, q)`.  The `Npc` correction was flagged in
`w76-house-note.md` and again in `w81-house-note.md` §3.1a and never marked at the site, which is
**five waves** of a known-stale in-tree table.

Corrected, the closing sentence inverts: **four of the five rows have a free-parameter producer**,
all carrying the same four analytic clauses, and the residue is uniform rather than per-row.  The
one row without is `N0 α h`, covered only at `(α, h) = (2, 0)`.  Annotated, plus the same
inventory in `Instances/OddIdentification.lean:232` ("which has no producer at free `h` in this
tree").

## S5.  The line-length owner item is understated

**`docs/dyadic/w81-house-note.md`** owner item 2, verbatim: "the corpus has lines over 100
*bytes* but **none over 100 *codepoints***".

Counting codepoints, `GQ2/` carries **707** such lines in **250** files.  The per-file half of the
claim is right (every file that lane touched is clean) and was over-generalized to the corpus.
Wave 81 also regressed the measure: `Instances/AskCounting.lean` lands **six** over-100-codepoint
lines (`:20` 121, `:21` 112, `:22` 109, `:23` 104, `:442` 101, `:450` 129), all markdown table
rows in docstrings.  `OddIdentification.lean` and `MpcNormValues.lean` are clean at 0.

Fixed in passing: `Instances/KSupply.lean:275` at **135** codepoints, the worst line in the ASK
chain, which happened to be the S3 sentence as well.  Every line this lane wrote is under 100.

## S6.  One citation miss in an otherwise line-exact note

`docs/dyadic/w81-ask-note.md` §1 and `w74-critical-path.md` §3 item 3 both cite
**`KSupply.lean:256-260`** for the "unowned" sentence.  At those lines sits `scalarHilbert_galK`;
the sentence is the `lem86_galK` docstring at `:270-276`.  Recorded because I checked the rest:
the other twelve citations in that note (`RadicalEdge/Local.lean:475`, `:523`;
`Phase140/Local.lean:258`, `:325`, `:537`, `:864`; `SectionEight/Partition.lean:307`;
`Count/LocalDuality.lean:152`, `:178`, `:210`, `:252`; `KExactLiftingVar.lean:109`;
`KExactLiftingGalK.lean:106`; `KAnalytic.lean:740`) are **exact**.

---

# Ticket 2: watch round 19, item by item

## (a) `oddId_orientedEquiv`: statement and pins verified exactly

Statement, at `Instances/OddIdentification.lean:90`, section binders `{Rec : LocalReciprocity}`,
`{K}`, `[FiniteDimensional ℚ_[2] K]`, `[CompactSpace (GalK K)]`, `[T2Space (GalK K)]`,
`[TotallyDisconnectedSpace (GalK K)]`:

```
theorem oddId_orientedEquiv (B : MarkedRecip Rec K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) :
    Nonempty (OrientedContinuousMulEquiv (chiSq h) (chiCycKTwo (K := K)))
```

`B` and `Rec` are binders; neither `localReciprocity` (B5) nor `markedRecipAt` (B5-K) occurs in
any of the module's sixteen pins.  Elaborated: census {B1, B6, B7, B11a}, exactly the note's
claim, and exactly what `nonempty_orientedEquiv_oddDegree` carries.

**All sixteen pins verified against the note's four-way split**: std-3 only on 5
(`oddId_certificate_of_supply`, `_orientedEquiv_withRows_of_supply`, `_supply_iff_certificate`,
`_genAsmBranch_L_of_supply`, `_demushkinQ_congr`); std-3 + {B1,B6,B7,B11a} on 8; std-3 + {B1,B6,B7}
on `oddId_candidate_equiv_galK_of_supply`; std-3 + {B1,B3c,B6,B7,B8,B11a} on the two degree-one
declarations.  5 + 8 + 1 + 2 = 16.  Declaration count 16, matching.

## (b) The near-miss check on "both bundles already closed": passes

`stokesDualityCertificate_galK` (`KAnalytic.lean:82`) concludes
`StokesDualityCertificate (galKProfinite K) n q P nuP (standardNumerics n) (smulZmod2GalK K)`
with binders `{n q : ℕ} {P} {nuP}` and hypothesis `hdeg` only.
`exactLiftingSemanticsRN_galK` (`KExactLiftingGalK.lean:130`) concludes
`ExactLiftingSemanticsRN (galKProfinite K) n q P nuP (standardNumerics n)`, same binder shape,
same single hypothesis.  Both consume `q` as a free binder, so `askC_*_galK`'s specialization to
`qOf K FF` is genuine and not a coincidence of unfolding.

**One precision item, not an error.**  Both suppliers are pinned at `standardNumerics n`, while
`KSupply`'s `stokes` and `exactLifting` fields are stated at a **general** `SN : SourceNumerics n`.
So the ASK note's "the spelling `KSupply.stokes` … is written at" is true at every live consumer
but not at the record's full generality.  Checked: all five `Main.lean` row records instantiate
`KSupply` at `standardNumerics (2 + 2 * 0)` (`:428`, `:472`, `:518`, `:563`), and
`GenAsmRowResidual.stokes` is *defined* at `standardNumerics G.degree`
(`GeneralAssembly.lean:288`).  So the claim holds wherever it is used, and the residual gap is
`KSupply` at non-standard numerics, which nothing in the tree instantiates.

## (c) The five norm values against the frozen rows' exact demands: 5 for 5

`mpcRow_rowData_sqrtTen` (`MpcRowData.lean:482`) demands `MpcNoUnitKerChi B`,
`MpcLambdaOne B (-1) 0`, `hpivot`.  `mpcRow_rowData_sqrtNegTen` (`:520`) demands
`MpcNoUnitKerChi B`, `MpcLambdaOne B (-1) 1`, `MpcLambdaOne B (mUnit 2) 1`, `hpivot`.
The norms lane supplies exactly those five non-pivot demands, name for name and argument for
argument, and `MpcNormValues.lean:809-848` is the consumption, elaborated green.  **No
disagreement, in either direction**, and the pins agree too: all five values print std-3 and
nothing else, `mpcNorm_level_sqrt{Ten,NegTen}` likewise, `mpcNorm_free_unique`,
`mpcNorm_pivot_of_even_dmB`, `mpcNorm_compSub` and `mpcNorm_exists_kerChiM` likewise.

The note's sharpest pin claim also checks: `mpcNorm_genAsmBranch_sqrtTen` sits at **exactly**
`mpcRow_genAsmBranch_sqrtTen`'s axiom set - both {B1, B6, B7, B11a, `peripheralCyclotomicAction`},
measured on both modules - so removing all three of its inputs costs no axiom.

## (d) Headline versus statement, three modules

`AskCounting.lean`: 13 declarations, headline "the two arithmetic counting bundles … are not
[unowned]" is borne out by §1's three restatements; the §4 census table is exact on all thirteen
rows, including the two footnoted readings (the coefficient lemmas print std-3 and nothing else;
`askC_halfTorsor_galK` prints B6 and B1 but **not** B7).  `askCKSupply_of_markedCore`'s extra
`hilbertSymbol_normCriterion_finiteDyadic` and `relativeStiefelWhitney_dyadic` are present and
do arrive through the determinant field, as claimed.

`OddIdentification.lean`: 16 declarations, all pinned, all verified (see (a)).  One docstring
inventory stale as of `db50b7a4` (S4).

`MpcNormValues.lean`: 72 pins printed, the three-set split as described, `hilbertSymbol_...`
absent from the four values, the two levels, the freeness and the abstract pivot criterion, as
the headline claims.  Zero lines over 100 codepoints.

## (e) The own-base pattern, per note against its own base tree

| note | base | own-base status claims |
|---|---|---|
| `w81-ask-note.md` | `6f2916f3` | **clean** (one citation miss, S6) |
| `w81-oddid-note.md` | `6f2916f3` | **clean** |
| `w81-norms-note.md` | `6f2916f3` | **one hit**, S2 |
| `w81-house-note.md` | `6f2916f3` | **one hit**, S1; plus S5 |

Two hits in four, and both are facts that another lane **of the same wave** had in hand.  The
pattern this round is not "the base moved under me"; it is "my sibling knew".

---

# Ticket 3: the endgame board

As of `db50b7a4` (`dyadic`), plus this lane's annotations.

## The odd seam

One `Prop` at `h ≥ 1`: `LSquare.SqMarkedForwardSupply B h` - some oriented equivalence carries
the two selected rows `ν(f σ) = 1`, `ν(f x₀) = 0`.  Equivalently, with **no** side binder,
`Nonempty (MarkedCoreCertificateKTwoSq B h)` (`oddId_supply_iff_certificate`, std-3).

* The **equivalence alone is free** at every odd-degree `K` (S1).
* The **rows are not**, and cannot be made so model-side: the pivot-row parity is a target
  invariant and reading rows off orientation is refuted.
* Free at `h = 0` (`oddId_markedSupply_degreeOne`).
* Producers at `h ≥ 1` all consume frame data; cheapest is `SqCupAdaptedFrameRelator K`.

W82-SEAM has a 698-line `Instances/OddSeam.lean` in flight on `claude/w82-seam`; **not merged**
at `db50b7a4`, so nothing on this board depends on it.

## The selector: four plus the pivot

| row | `pres` | branch datum | carried |
|---|---|---|---|
| `ℚ₂(√−2)` | `.N0 2 0` | `fieldUni_genAsmBranch_sqrtNegTwo` | **nothing** |
| `ℚ₂(√2)` | `.M0 3 0` | `fieldUni_genAsmBranch_sqrtTwo` | **nothing** |
| `ℚ₂(√5)` | `.M0 2 0` | `fieldFive_genAsmBranch_sqrtFive` | **nothing** (S2) |
| `ℚ₂(√10)` | `.Mpc 2 1 false .one 0` | `mpcNorm_genAsmBranch_sqrtTen` | **nothing** |
| `ℚ₂(√−10)` | `.Mpc 2 1 true .one 0` | `mpcNorm_genAsmBranch_sqrtNegTen_of_pivot` | the pivot |

**Four plus the pivot**, and the pivot is one clause on the whole frozen table.  W81-NORMS §5
shows the obstruction is real: wave 80's counterexample `(−8, 1, 4, 1)` makes it independent of
the level, both `λ`-values and surjectivity, so it must come from the certificate side or from a
classification of the markings `D_M 2 0` admits.  W82-PIVOT is 25 lines in flight; **not five
yet**.

## The record blocks per row, under both ASK spellings

| spelling | `exactLifting` | `stokes` | `determinant` | ASK blocks |
|---|---|---|---|---|
| frozen (the records say) | `askCStageVanishing` at `2 ≤ n` | free | free given data | **1** |
| corrected `RN` (what is proved) | free, every degree | free | free | **0** |

Plus `cand` per row, which after W82-CAND is the same **four analytic clauses** at `Γ_R` on `M0`,
`Npc` and `L`, and is covered only at `(α, h) = (2, 0)` on `N0`.

⚠ The surviving ASK `Prop` is not obviously wanted.
`askC_isEmpty_boundaryLifts_of_exactLifting` derives from the frozen field, at `2 ≤ n`, that
`G_K` admits **no** boundary-framed surjection onto any marked target with nontrivial Frattini
block - and the recursion exists to count those.  Deciding whether to prove it or to restate the
records is the sharpest open question on the arithmetic side, and it is a statement question, not
a mathematical one.

## The even route: unchanged since wave 74, confirmed

Every commit touching `Instances/Even*` or `MarkedCore/NFrameAlphaOne.lean` since the wave-74
close is a prose or comment pass (watch rounds 10 to 12, the em-dash scrub, the module-comment
sweep).  Last substantive touch: `EvenParityModel.lean` 2026-08-12, `EvenFamilyStatus.lean`
2026-08-11.  The surviving point remains `EvenFamParitySupply` / `Hfam`, proved *equivalent in
strength* to the even classification at the field's own depth
(`hfamFinal_parityN_iff_orientedEquiv`, `hfamFinal_parityM_iff_orientedEquiv`), so it can be
neither refuted nor discharged by soft means.  The `alpha = 1` stratum remains off the critical
path, twice re-verified (`w74-critical-path.md` §2, W76 and W77 annotations).

## The assembly wiring list

What turns the pieces into the general theorem's instances.  **All six are statement changes**,
which is the point: the residual surface is now mostly wiring, and wiring is what a worker lane
may not do.

1. `KSupply.determinant` → call `affineDeterminant_galK` instead of binding.  Arguments priced by
   W79-HOUSE; all six are already in scope at the record.
2. `KSupply.stokes` and `GenAsmRowResidual.stokes` → call `stokesDualityCertificate_galK`.
3. Restate `exactLifting` against `ExactLiftingSemanticsRN`, giving a **zero-block** ASK record
   (`sourceRN_of_markedCore` + `askC_stokes_galK` + `affineDeterminant_galK`).
4. Strengthen the existential branch producers to carry `G.nuP`.
   `genAsm_branch_of_oddSq_canonical`, `genAsm_branch_of_evenN`,
   `genAsm_branch_of_evenM` and the `fieldId_genAsmBranch_*` family all return
   `∃ G, G.pres = …` and forget the marking, while `cand` is stated at `G.nuP`; W82-CAND
   worked around it by rebuilding the datum as a definition.
5. Restate `ResidualSqrtNegTwo` against `marked_matching_certificate_KTwoN`, removing three of the
   pilot's thirteen fields and putting the fourth in the spelling the classification route
   produces (`w74-critical-path.md` §1.5).
6. AB-0: truth-sync the obligation inventories in `CertificateMain.lean` and `KSupply.lean`.

Registration is **current**: `AskCounting`, `OddIdentification`, `MpcNormValues` and `LRowCand`
are all in `GQ2.lean`.  Nothing owed there.

## Owner items

The four standing, plus three new.

1. **ASK restatement** (item 3 above).  New weight: it is no longer one field of three, it is the
   *whole* ASK block, and the alternative to taking it is proving a statement that empties the
   object the recursion counts.
2. **Pilot spelling** (item 5).  Unchanged since `w74-critical-path.md` §1.5.
3. **The A6 freeze** - `GQ2/Roe/*`, now **nine** review rounds without motion (eight at wave 81).
   Nothing in this lane touched `GQ2/Roe/` or `GQ2.lean`; `git diff a45bc557 HEAD` on both paths
   is empty.
4. **Line length** - corrected (S5): **707** lines over 100 codepoints in **250** files, not zero,
   and wave 81 added six.  The policy call is still owed.
5. **NEW: AB-0** (item 6).  The root cause of the whole straggler field, queued six waves ago
   while every other item in its own sequence landed.
6. **NEW: the forgotten marking** (item 4).
7. **NEW: is `askCStageVanishing` a fact about `G_K` or a wrong ask?**  Not a housekeeping
   question and not resolvable by a house lane, but it is now the single sharpest open item on
   the arithmetic side and nothing owns it.

---

# What this lane did not do

No statement was changed anywhere.  The six wiring items above are all statement changes and are
reported, not made, in line with W74-HOUSE §1.5.  I did not touch `Instances/OddSeam.lean`,
`Instances/MpcPivot.lean` or `Instances/LRowCand.lean` (sibling-owned), `GQ2.lean`, or
`GQ2/Roe/*`.  I did not attempt to prove or refute `askCStageVanishing`, the `ε = true` pivot, or
the odd seam.
