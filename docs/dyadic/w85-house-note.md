# W85-HOUSE lane note (round 22)

Standing verification lane. Base `76f21241`, which was `dyadic`'s tip at lane start and still is
at lane close (no sibling merged during the round). Mirror swept at start (6003 artifacts).
Scoreboard run before and after; both captured. Four commits, all comment-only in `GQ2/` plus one
tooling change in `scripts/scoreboard.sh`. Every edited Lean file re-elaborates green against the
mirror: `Instances/OddFrame.lean`, `Instances/CanonicalRecords.lean`, `CertificateMain.lean`,
`GeneralAssembly.lean`.

**The round's headline is a repeat offence.** The scoreboard's own documented blind spot fired a
second time, on the wave it was extended to watch, and this time it printed three wrong producer
counts rather than one. Second in severity: wave 84's sharpest reading, "the pilot spelling is
strictly dominated", is right as a comparison of spellings and wrong in the two things a reader
takes from it.

---

## 1 Ticket 1: the wave-84 findings, applied

### 1(a) The OddFrame prose audit, all eight findings

Every one verified against the current tree before acting. Items 1 to 7 fixed, comment-only, in
`GQ2/Dyadic/Instances/OddFrame.lean` (commit `7bbe2ed7`).

| # | audit's severity | verified? | disposition |
| --- | --- | --- | --- |
| 1 | HIGH | yes | fixed at three sites |
| 2 | MEDIUM | yes | fixed at two sites |
| 3 | MEDIUM-LOW | yes | fixed, plus one adjacent site the audit did not list |
| 4 | LOW | yes | fixed at two sites |
| 5 | LOW | yes | fixed by disclosing the binder in the T2 preamble |
| 6 | LOW | yes | disclosed in the docstring; binder NOT changed |
| 7 | LOW | yes | fixed |
| 8 | INFO | yes, exactly five warnings | recorded in the module doc, not fixed |

Item 1 is the one that mattered. `oddFrame_presenting_relator_rowSum` produces MOD-2 rows
(`frattiniFrameEval ... = 0`, a `ZMod 2` value) while the seam's target object, §4's
`oddFrame_cupAdaptedFrame_of_clear`, produces EXACT `ℤ₂` rows (`nuUrKTwo B (F.generators 0) =
ofAdd (1 : ℤ_[2])`). "Only the split of the row sum is missing" was therefore false by a whole
lift out of `2ℤ₂`, at each of two rows. The three prose sites now say MOD-2 explicitly and point
"the ticket's target object" at §4.

Item 2: `GQ2/Dyadic/Instances/GammaLOddDegreeBridge.lean` has sections §1 to §4 with primes and no
§9; the result cited is `SqCore/PivotClimb.lean` §9 ("The `K`-facing form: the parity of the
transported pivot row is not a choice"), which `GammaLOddDegreeBridge` itself cites correctly at
its own line 35. Both OddFrame sites now cite `PivotClimb` §9.

Item 3: "the whole seam costs exactly the MODEL-side clearing statement" contradicted the file's
own `oddFrame_supply_iff_clearInstance`, which says the clearing overshoots the seam by its
marking quantifier. Only `oddFrame_supply` is proved, one implication. Now "is BOUGHT BY", with
the overshoot named. The adjacent site the audit did not list is `oddFrame_supply`'s own docstring
("the clearing is now the seam's whole remaining cost"), corrected the same way.

Item 6 is a binder, not a comment: `oddFrame_candidate_equiv_galK_of_clear` has `{FF}` implicit
where its seven §4 siblings have it explicit. Changing it would change a signature, so the
docstring now discloses it instead and says the "exactly the two record blocks" is read on top of
the data.

Item 8, reported rather than fixed, because `omit`ting the instances changes three signatures. The
five `linter.unusedSectionVars` warnings are exactly:

* `oddFrame_card_H1`, `oddFrame_nu_notin_kappaTau_span`: `[T2Space (GalK K)]`;
* `oddFrame_presenting_relator_rowSum`, `oddFrame_isUnit_transported_sqPivot`: `[CompactSpace
  AbsGalQ2]`, `[TotallyDisconnectedSpace AbsGalQ2]`;
* `oddFrame_supply_iff_clearInstance`: all three.

So three theorems advertise a hypothesis on the absolute Galois group of `ℚ₂` they do not use.
Recorded in the module doc under a new "Known linter noise" heading, with the instruction to read
them as holding without any `AbsGalQ2` hypothesis. **Owner item, small:** `omit ... in` on five
declarations, five one-line signature changes.

### 1(b) `CertificateMain.lean`'s "genuinely unowned"

Confirmed stale, and corrected in place with an as-of-hash supersession block, keeping the
superseded phrase under a `⚠ SUPERSEDED` marker per the file's own annotation convention. The
supporting facts, checked by elaboration and not by grep:
`MCompact.exactLiftingRN_unconditional` (`Instances/EvenMRamifiedPairing.lean:175`) and
`NCompact.exactLiftingRN_unconditional` (`Instances/N0M0CompactBranches.lean:250`) both bind
`2 ≤ α`, `q ≠ 0`, `Even q` and nothing else, and the tree has exactly two declarations of that
name.

Two limits are written into the supersession, because a bare "it is owned now" would be the next
stale line: it covers the compact `M`/`N` carriers at `2 ≤ α`, not `Mpc`
(`MProcyclicExact.exactLiftingRN_of_uniformPushed`, `Instances/MpcExact.lean:1140`, still binds
`UniformHsimp`); and "owned" means the CORRECTED bundle, which is the same sense the `G_K` bullet
above it uses.

### 1(c) "The residue is uniform across the four rows"

Narrowed to three at four sites, with the fifth left alone deliberately.

1. `docs/dyadic/w83-records-note.md` reading 2, the origin.
2. `GQ2/Dyadic/Instances/CanonicalRecords.lean` reading 2, the in-tree copy. **This was the
   highest-value site**: it is the docstring a reader hits first, and it sat three lines under a
   W84-HOUSE annotation ending "Identical across all four rows, which is reading 2 confirmed",
   which is now qualified to "at the level of the binder LISTS".
3. `docs/dyadic/w84-house-note.md` §2.4, which certified reading 2 one section before W84-CLAUSES
   narrowed it inside the same wave, plus its record-block table heading.
4. `docs/dyadic/w83-house-note.md`'s handover bullet, which propagated the reading forward on the
   same axis that note's own S3 had just corrected.
5. NOT corrected, pointer only: `GQ2/Dyadic/GeneralAssembly.lean`'s "the residue is uniform rather
   than per-row". That is a DIFFERENT four (the rows with free-parameter producers), the claim is
   shape-level, and it is true. It got one bracketed sentence saying so, because the word
   "uniform" is the same word and this is how the reading spread the first time.

The underlying fact, re-verified: `exactLiftingRN_unconditional` exists in exactly two namespaces,
`MCompact` and `NCompact`. `MProcyclicExact` has no such theorem, and the file
`Instances/NpcUnramifiedScalar.lean` declares `namespace GQ2.Dyadic.NProcyclicUnram`, so W84's
`NpcUnramifiedScalar.uniformPushedHsimp` is `NProcyclicUnram.uniformPushedHsimp`. In-tree
corroboration at `GQ2/Dyadic/CertificateSupplyRN.lean:67`.

### 1(d) The wave-84 note's own housekeeping list

Disposition recorded as a block in `docs/dyadic/w84-clauses-note.md` §6.

1. **Already discharged before this lane.** `GQ2.lean:877` imports `Instances.RowClauses`
   (`1630ab1e`), `:785` `SqCore.GradedClearing` (`3e2a5a60`), `:878` `Instances.MpcWord`
   (`0a94a4bc`). The trap: none of the three appeared in the scoreboard's REGISTRATION section at
   lane start, which is the import-set horizon, not a verdict. See §2.1.
2. Done, see 1(b).
3. Done at four sites, see 1(c).
4. Done, **with one correction to the recommendation**, see §2.5.

---

## 2 Ticket 2: watching round 22, ranked by severity

### 2.1 HIGH: the scoreboard blind spot fired a second time, and undercounted three sets

The board's own list of what it cannot see says a producer in a module no row imports is
invisible, and records that this "HAS FIRED ONCE", at wave 84. It fired again immediately, on
wave 84's own three landings, and nothing named a declaration in them.

Measured by re-running the board's `sbProducers` scan over the full import set:

| target | board printed | true | missing producers |
| --- | --- | --- | --- |
| `MpcPivShift` | 1 | **4** | `mpcWord_shift_of_word`, `mpcWord_shift_of_forall_class`, `mpcWord_shift_of_forall_class_four` |
| `SqNuOrientedClearAtUnitPivot` | 3 | **6** | `gClear_clearing_of_model`, `gClear_clearing_of_families`, `gClear_clearing_zero` |
| `SqMarkedForwardSupply` | 14 | **16** | `gClear_supply_of_model`, `gClear_supply_of_ray` |

The `MpcPivShift` line is the one that would have misled a reader worst: the board said the
`√−10` residual move has ONE producer, on a tree where wave 84 had just given it the finite-class
route, which is the whole point of the wave.

Fixed at the documented extension point (`a817a9a8`): four `decl` rows naming
`mpcWord_shift_of_forall_class_four`, `gClear_clearing_of_model`, `rowCl_mCand_exactLifting_iff`
and `rowCl_nCand_exactLifting_iff`, plus one new `prod` row for `GClearModelMove`, the row-plane
Prop the odd route now stops at (4 producers). The REGISTRATION section now confirms all three
wave-84 modules registered. The blind-spot entry records the second firing and carries the lesson:
**add the row in the same wave that lands the module.**

This is the one non-comment change this lane made, and it is in a read-only tool wired into no
gate, at the extension point the tool documents, with W84-HOUSE's `f3ca3183` as precedent.

### 2.2 HIGH: "strictly dominated" is right, and both corollaries drawn from it are wrong

`Instances/RowClauses.lean` §5 concludes: "everything it buys, the `genCertN` spelling buys with
two fewer residues and no coefficient condition." Both halves fail.

**(i) "No coefficient condition" is false.** `genCertNWordCertificateCanonical`
(`GQ2/Dyadic/GeneralCertificates.lean:553`) binds `exactLifting : ExactLiftingSemantics (GammaR
(2 + 2h) q (nCompactW α h)) ...`, the FROZEN bundle. By the same module's own
`rowCl_nCand_exactLifting_iff`, that clause IS `askCStageVanishing` at that carrier, at `2 ≤ α`,
`q ≠ 0`, `Even q`. The coefficient condition is on BOTH routes: the pilot's three recursion
residues imply it (`rowCl_pilot_stageVanishing`), and the `genCertN` spelling's `exactLifting`
clause is equivalent to it. Only the RN restatement removes it, and that restatement is owner item
1, not this module.

**(ii) "Two fewer residues" is one.** Honest count at the `√−2` row:

* pilot `sqrtNegTwoWordCertificate`: `PilotHsimp`, `PilotStageSep`, `PilotStageZ`, `PilotDet` = 4;
* `genCertN`: `exactLifting` (= the coefficient), `stokes`, `determinant` = 3, the `scalar` clause
  being discharged by `rowCl_nCand_scalar`. No `rowCl_nCand_stokes` exists.

So 4 against 3. The comparison still favours `genCertN`, and the domination claim as a claim about
SPELLINGS stands. The arithmetic in the headline does not.

### 2.3 HIGH: nothing consumes `PilotHsimp` on the record path, and the assembly does

The claim to check was that nothing should still consume the pilot residues on the live path. On
the record path it holds: `canRec_analytic_sqrtNegTwo` routes through
`canRec_rowResidual_N0_of_analytic` and `canRec_candN` (= `genCertNWordCertificateCanonical`), and
`canRec_candPilot` has no consumer in `CanonicalRecords.lean` beyond its own `#print axioms`.

On the campaign assembly it does not, and this is a live path, not a leftover:

* `GQ2/Dyadic/Main.lean:352` `ResidualSqrtNegTwo` carries `hsimp : SqrtNeg2.PilotHsimp`,
  `hsplit`, `hZcount` and `hdet` as structure fields;
* `Main.lean:592` `rowEquiv_sqrtNegTwo` consumes all four;
* `Main.lean:672` `ramifiedI_candidate_equiv_galK`, the five-row endpoint, dispatches to it;
* `GQ2/Dyadic/GeneralAssembly.lean:557` `genAsm_rowEquiv_sqrtNegTwo` is `rowEquiv_sqrtNegTwo F S`;
* `GQ2/Dyadic/Instances/Fields.lean:706` `sqrtNegTwo_candidate_equiv_galK_literal`, a committed
  headline, carries them too.

Recorded at the `CanonicalRecords.lean` table so a reader of the record lane is not told the
pilot is retired. **Owner item, not housekeeping:** retiring it means dropping four fields from
`ResidualSqrtNegTwo` and re-proving `rowEquiv_sqrtNegTwo` off `genCertNWordCertificateCanonical`.
Deleting `PilotHsimp` alone changes nothing, because all four residues die into the same two
sinks.

### 2.4 MEDIUM: `gClear_transport` and "the marking quantifier is gone", verified exactly

`SqNuOrientedClearAtUnitPivot h` printed in full is `∀ nu', SqJointSurjective h nu' → IsUnit
(toAdd (nu' (sqPivot h))) → ∃ Ψ, ...`. `gClear_clearing_of_model` takes `(∀ a b : ℤ_[2], IsUnit
(a - sqPivotExp * b) → GClearModelMove h a b)`, and `GClearModelMove h a b` is a single-marking
statement about the explicit `nuSqOf h a b` with two row clauses and no handle or `x₁` clause. So
the module doc's phrasing is exact: the `∀ nu'` binder over a function space is replaced by a
two-parameter family over the row plane. It is not eliminated, and the module does not say it is.

Elaborated at one `h ≥ 1` instance, `h = 1`, both stopping points:

* `gClear_clearing_of_model H : SqNuOrientedClearAtUnitPivot 1` from `H : ∀ a b, IsUnit
  (a - sqPivotExp * b) → GClearModelMove 1 a b`;
* `gClear_supply_of_model B FF (h := 1) (by omega) H : SqMarkedForwardSupply B 1` at any `K` with
  `finrank ℚ_[2] K = 3`.

Both elaborate. One free strengthening, not stated anywhere: `gClear_transport` does not take the
joint-surjectivity hypothesis, and `gClear_clearing_of_model` discards the one it is handed
(`intro nu' _ hpiv`). So what the reduction actually proves is the joint-surjectivity-FREE
strengthening of the clearing. Worth saying at the site, in a later lane.

Axiom hygiene claims re-measured against the board and correct: the model-side chain is std-3, the
`h = 0` pins add `{dyadicOrientation, peripheralCyclotomicAction}` (B3c, B8, labels checked
against `docs/dyadic/literature-axioms-dyadic.md:94,98`), and the §5 seam composites add
`{hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated,
absGalQ2_localEulerCharacteristic}`.

### 2.5 MEDIUM: the finite-class principle against its binders

`mpcWord_shift_of_forall_class (H : ∀ k, (mpcWordSet k).Nonempty) : MpcPivShift 2`. One binder,
and the module doc's account of it is exact: nested (`mpcWordSet_antitone`), closed
(`mpcWord_isClosed_set`, all five clauses), compact (the correction space is a product of copies
of `DM 2 0`), directed (`max k k'`), and the tower separates points
(`mpcWord_iInf_twoCentralSeries`). `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`
is fed all four.

The near-miss check, which is where this kind of argument usually goes wrong, comes out clean:

* the family is genuinely nested the right way round, `k' ≤ k → mpcWordSet k ⊆ mpcWordSet k'`, so
  the directedness witness `max k k'` is correct and not accidentally inverted;
* the per-`k` witnesses may differ, and the whole content of the argument is producing a single
  common one; that is what `mpcWord_iInter_nonempty` does and it is not short-circuited anywhere;
* the sharpened form is exactly `∀ k, 4 ≤ k → ...` (`mpcWord_shift_of_forall_class_four`), and the
  `k ≤ 3` half is a theorem (`mpcWord_nonempty_of_le_three`), so no bounded range of `k` makes the
  hypothesis vacuous or the criterion trivial;
* the contrapositive as stated, "if `M6` is false it fails at a finite class, in a finite
  2-group", is sound in both readings of "M6" (the ansatz, or `MpcPivShift 2`), because the
  ansatz-to-shift implication `mpcWord_shift_of_word` runs the direction the contrapositive needs.

One INFO: the "in a finite 2-group" half is a reading, not a statement of this module. It is
backed by `finite_levelQuot G hfg hpro k` together with the two facts this module already uses
(`dm_topologicallyFinGen_zero 2`, `isProP_DM 2 0`), so the reading is correct; it is simply not
instantiated here. A one-line `haveI` would make it checkable at the site.

### 2.6 MEDIUM: "one statement twice", elaborated at both carriers

The claim is that the `√5` row record carries `askCStageVanishing` twice, at two groups. Checked
by elaboration, and it is exact in a stronger sense than the note claims: the two instances agree
in the `Prop`, in `q`, in the marking group `P` and in `nuP`, and differ ONLY in the carrier.

* candidate side: `rowCl_mCand_exactLifting_iff : ExactLiftingSemantics (GammaR (2+2h) q
  (mCompactW α h)) ... ↔ askCStageVanishing (GammaR (2+2h) q (mCompactW α h)) q P nuP`, binders
  `2 ≤ α`, `q ≠ 0`, `Even q`;
* arithmetic side: `askC_exactLifting_iff_stageVanishing : ExactLiftingSemantics (galKProfinite K)
  n q P nuP ... ↔ askCStageVanishing (galKProfinite K) q P nuP`, binders `finrank = n`, `2 ≤ n`.

At the row (`rowCl_rowResidual_sqrtFive`) the two are instantiated at `P := genAsmCore (.M0 2 0)`
and `P := DM 2 0` respectively, which look different and are not: `genAsmCore (.M0 2 0) = DM 2 0`
is `rfl`, checked. The `N` twin `rowCl_nCand_exactLifting_iff` is the same statement at
`nCompactW`.

### 2.7 LOW: headline against statement on the three new modules

`SqCore/GradedClearing.lean`: headlines check out. `gClear_transport`, `gClear_clearing_of_model`,
`gClear_modelMove_of_ray` and `gClear_clearing_of_families` all say what they prove, including the
"strictly fewer binders" claim (two against `sqNuOrientedClearAtUnitPivot_of_families`' three,
with `hfix` discharged by wave 80's `gOdd_pivotFix` and the two survivors literally the same two
Props, so the board's own STRENGTH caveat does not bite here). "What this does NOT do" is honest.
The only unstated thing is the free strengthening in §2.4.

`Instances/MpcWord.lean`: headlines check out; see §2.5. Two INFO items. The section numbering
skips §8 (§7 is followed by §9). And the module docstring cites an OFF-TREE exact `𝔽₂` computation
in the Magnus model climbing to class six; it is flagged as off-tree and recorded in the lane
note, which is the right handling, but it is worth noticing that a Lean module docstring now
carries an unreproducible computational claim.

`Instances/RowClauses.lean`: headlines check out except for §5, which is §2.2 and §2.3 above. Two
LOW items. The sections are physically out of order, `§1, §2, §4, §3, §5, §6`, while the module
doc's Contents lists them in numeric order, so "see §3" sends a reader backwards. And "Four of the
six close" (module doc, and again at §3) is loose: of the six, two are DISCHARGED (`cand scalar`,
`ASK stokes`) and two are TRADED for one shared `Prop` (`cand exactLifting`, `ASK exactLifting`),
which is not the same thing and is exactly what the module's next sentence says correctly.

---

## 3 Ticket 3: the endgame board, annotated

Read off the closing scoreboard, which is the corrected one.

**The odd route.** Down to the model move, and only that. `SqMarkedForwardSupply` has 16
producers; the live chain is `GClearModelMove → SqNuOrientedClearAtUnitPivot → SqMarkedForwardSupply
→ GenAsmBranch .L h → the general theorem`, and every link is a theorem. The open item is the
row-plane family `∀ (a b) on the unit locus, GClearModelMove h a b` at `h ≥ 1`. Its four producers
are `gClear_modelMove_one_zero` (the base point, free), `gClear_modelMove_zero` (`h = 0` only,
riding B3c + B8), and `gClear_modelMove_of_families` / `gClear_modelMove_of_ray`, which trade it
for the two one-parameter families that are themselves open at `h ≥ 1`. Nothing in the tree at
`h ≥ 1` moves rows. If the `w85-rowmove` sibling lands a row move the odd route closes; until then
this is the whole of it, and the board now shows the residual as its own row.

**The selector.** Four tied rows, unchanged: `N0 2 0` (`ℚ₂(√−2)`), `M0 3 0` (`ℚ₂(√2)`), `M0 2 0`
(`ℚ₂(√5)`), `Mpc 2 1 false 1 0` (`ℚ₂(√10)`). The fifth, `ℚ₂(√−10)`, needs BOTH `MpcPivShift 2`
(the M6 identity) and the tie (owner item 8, one line at `Instances/MpcPivot.lean`): the board
shows `mpcPiv_genAsmBranch_sqrtNegTen_of_shift` carrying `MpcPivShift` and `MarkedRecip`, and
`mpcPiv_genAsmBranch_sqrtNegTen` untied, and neither is admissible to `CanonicalRecords` as it
stands. What changed this round is the visibility of the M6 half: `MpcPivShift` now shows 4
producers, and the finite-class route is on the board. If the `w85-m6build` sibling lands the
class-`k` solvability the selector is five subject to the tie alone.

**The record blocks per row.** Both templates carry identical binder LISTS at all four rows, and
that is all that is identical. After wave 84:

| row | residue of the analytic template |
| --- | --- |
| `M0 3 0`, `M0 2 0` | `stokes` + `determinant` at `Γ_R`, plus `askCStageVanishing` at `Γ_R` and at `G_K` |
| `N0 2 0` | the same, at `nCompactW` |
| `Mpc 2 1 false 1 0` | the full four analytic clauses plus two `ASK` blocks, unreduced |

Success at one row is success at three. Bringing the fourth in is
`MProcyclicExact.exactLiftingRN_unconditional`, a small ticket with the pattern already in the
tree on the procyclic `N` side.

**The even route.** One surviving point, unchanged since wave 74 and untouched by wave 84 or this
round: `Hfam` (`EvenRouteFinalFamily{N,M} h K`), proved EQUIVALENT to the even classification at
that field by `hfamFinal_family{N,M}_iff_orientedEquiv`, so it can be neither refuted without
refuting the classification there nor discharged by soft means. Arithmetic form
`EvenFamParitySupply{N,M}`.

**Owner items: nine standing, none takeable by a comment-only lane.** Carried forward from
W84-HOUSE §4 unchanged in count. Two annotations from this round:

* item 3, **the A6 freeze, is at twelve review rounds** (eleven at wave 84). `GQ2/Roe/` and
  `GQ2.lean` are untouched by this lane, checked. The board's machine substitute now reads: last
  commit `4341a1a3`, 2026-08-10, comment-only; **13** house notes added since.
* item 2, the pilot spelling, gains the concrete consumer list in §2.3, which is what a lane
  taking it needs.

Two candidate additions this round, both small and both signature changes, so neither was taken:
the five `omit`s in `OddFrame.lean` (§1(a) item 8), and stating the joint-surjectivity-free
strengthening at `gClear_clearing_of_model` (§2.4).

---

## 4 What this lane did not do

No statement changed anywhere in `GQ2/`; every tree edit is a comment. `GQ2.lean` and `GQ2/Roe/*`
untouched. The sibling-owned files `SqCore/GradedRowMove.lean`, `Instances/MpcBuild.lean`,
`Instances/RecordBlocks.lean` and `Instances/MpcPivot.lean` untouched. No `lake` command was run;
verification is `scripts/mirror.sh check` and `scripts/scoreboard.sh` throughout. The four frozen
wave-83 and wave-84 lane notes were annotated with dated supersession blocks rather than rewritten.
`MpcPivShift 2`, `askCStageVanishing` and the model moves were not attempted. The one behaviour
change outside the tree is the scoreboard's row table and blind-spot entry, §2.1.
