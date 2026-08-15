# W84-HOUSE: the wave-83 corrections, watch round 21, and the endgame board

**Lane W84-HOUSE, branch `claude/w84-house`, base `45f9c42d`.**  Standing verification lane plus
the corrections the wave-83 lanes owed.  Comment-only in the tree throughout: no statement
anywhere was changed, no theorem added or removed, no `sorry`, no axiom, no import, no `GQ2.lean`
edit, no `GQ2/Roe/` edit.  One behaviour change outside the tree, `scripts/scoreboard.sh`, taken
at that script's own documented extension point and reported in §2.3.

Verification of record: `scripts/mirror.sh sweep` at lane start (5988 artifacts), `check` on
every edited module, all green.  `scripts/mirror.sh check GQ2/AxiomLedger.lean` green, exit `0`,
**0 terminal violations**.  Scoreboard run before and after.  **No `lake` command was run.**

**The base did not move under this lane.**  `45f9c42d` was `dyadic` and `origin/dyadic` at lane
start and at every commit; the own-base check that has caught six previous rounds is clean this
time, and is recorded here so the next round can tell the difference between "checked" and
"not checked".

---

## Headline

**The board built last round to stop the campaign trusting prose was itself printing a false
number, and it was the exact falsehood its own blind-spot list predicted.**
`scripts/scoreboard.sh` reported `v-10 residual move  producers: 0` for `MpcPivShift`, the
`ℚ₂(√−10)` row's whole residue.  There is one producer, `MpcOrb.mpcOrb_shift_of_marking`, landed
by W83-ORBIT in the same wave.  It was invisible because `Instances/MpcOrbit.lean` is a module no
scoreboard row imported, and a `prod` scan reads the environment.  The script's own list says
this is "the one way the board can be stale"; it went stale that way on its first round of use.
Fixed at the documented extension point, machine-confirmed, and the incident is now printed in
the blind-spot list rather than left as a prediction.

**The second finding is the one that matters mathematically.**
`mpcPiv_genAsmBranch_sqrtNegTen_of_shift` carries the headline **THE `√−10` BRANCH DATUM AT THE
ROW'S CANONICAL MARKING**, and its conclusion is
`∃ G : GenAsmBranch KSqrtNegTen B, G.pres = .Mpc 2 1 true .one 0` and nothing more.  The proof
routes through wave 83's strengthened site 5, which does name `mpcNu 2 1 (p true 1)`, and then
drops the conjunct with `Exists.imp`.  So **`ℚ₂(√−10)` has no tied statement at this tree**: the
two statements it has differ in hypothesis, not in tie.  Two other prose sites assert the
opposite, one of them in the Lean tree.  This is the wave-83 records ticket's own defect,
surviving in the one place that ticket did not reach, and it changes the reading of the selector:
the row is not "one abstract move away from tied", it is one abstract move away plus a one-line
statement change.

Everything else the wave-83 lanes claimed and this round could check is **true**.  The odd
route's newest reduction verifies exactly, including end to end at an odd field; the five
strengthened existentials are clean at all five sites with docstrings updated; the tied/untied
sweep found **zero** defects; the record blocks measure exactly as the per-row table says under
both templates.

---

## 1  Ticket 1: the corrections the wave-83 lanes owed

### 1(a) and 1(b): the `M6` ruling, superseded at both quote sites

W83-ORBIT proved `CoreMixM.lean` §7's ruling on `⟨M4, M6, M7⟩` unsound **as an argument**: the
premise it rests on, a `ℤ₂`-symplectic invariant of `D_M` to violate, does not exist, because the
relator `P_M = Ā²[Ā,B̄]C̄₀^{2^α}[C̄₀,D̄]` carries the square `Ā²` and so is not a product of
commutators.  Demushkin duality here pairs into `H²(G, ℤ/q)` with `q = 2`, i.e. only mod 2, and
mod 2 `M6` is the identity, hence an isometry of the only bilinear invariant there is.

Corrected, comment-only, at three sites:

* `GQ2/Dyadic/Instances/MpcPivot.lean`, the module doc's "What does not land", which quoted the
  ruling and drew a conditional from it ("If that ruling is right then `MpcPivShift` is false").
  The quote is left in place with a `⚠⚠ [W84-HOUSE, as of 45f9c42d: ...]` block saying the
  conditional must not be read as evidence either way, citing `mpcOrb_frame_shift` and
  `mpcOrb_chi_shift` for the frame level and `mpcOrb_shift_iff_marking` for what replaces it.
* `GQ2/Dyadic/MarkedCore/CoreMixM.lean` §7 itself, superseded in place.  **The binder stands and
  the ruling's conclusion may still be true**; what does not stand is the reason, and the words
  "structurally obstructed rather than merely unbuilt" go with it.  The entry names
  `mpcOrb_frame_shift` and `mpcOrb_chi_shift` as the citations to prefer, records the lane note's
  unformalized `F/γ₃` computation as unformalized, and is explicit that `M4` and `M7` were not
  examined and inherit only the loss of the reason, not a new status.
* `GQ2/Dyadic/MarkedCore/CoreMixM.lean` §5, where the epithet "the **non-symplectic** M4/M6/M7
  directions" reproduced the superseded reason.  The claim §5 actually makes, that those
  directions are unnecessary for a particular marking, is `mMixHypothesis_of_scaling`, a theorem,
  and depends on the epithet nowhere; the entry says so.

Both files typecheck green.  Neither has a statement, import or pin changed.

### 1(c): the tied/untied sweep

**Zero defects.**  No site in the Lean tree and none in `docs/dyadic/` claims five clause-free
quadratic rows without the tied/untied or canonical-marking qualifier.  Swept over `GQ2/**/*.lean`
and `docs/dyadic/**/*.md` on the claim vocabulary (`unconditional`, `clause-free`, `no clause`,
`carries nothing`, `closed`, `discharged`), the scope vocabulary (`all five`, `five rows`, `every
row`, `whole frozen table`, ...) and the qualifier vocabulary, single-line and paragraph-spanning,
plus every occurrence of `mpcPiv_genAsmBranch_sqrtNegTen{,_of_shift}` and `MpcPivShift`.

Sites checked and found already correct include `MpcPivot.lean:48` (the canonical statement of the
distinction), `CanonicalRecords.lean:23/35/140` ("the four clause-free quadratic rows"),
`GeneralAssembly.lean:686` (`FOUR-OF-FIVE-FREE`), `FieldUnimodularity.lean:650`,
`w82-pivot-note.md:200/212`, `w83-orbit-note.md:181`, `owner-items-2026-08-05.md:19/66`.
True "all five" claims about a *different* obligation (the α-pin, the Stokes endpoints, the
presentation instances, `r ≤ 1`) are correct and were left alone.

**One adjacent staleness found and corrected**, in the conservative direction:
`GQ2/Dyadic/Instances/FieldBranchIdentification.lean:102`, whose contents list said "the five
rows' branch data, **one clause each**".  Four rows now carry nothing.  Annotated; the file's own
contribution at that item is unchanged.

**Note for the record.**  The tied/untied distinction is swept correctly through the tree, but
§2.2 below shows the distinction is being *applied* to a statement that does not satisfy it.  The
vocabulary is right; one of the facts it is attached to is not.

---

## 2  Ticket 2: watch round 21

Scope: the wave-83 landings (`Instances/OddFrame.lean`, `Instances/MpcOrbit.lean`,
`Instances/CanonicalRecords.lean`, the five strengthened files, `scripts/scoreboard.sh`, the four
w83 notes).  Staleness first, own base included (clean, above), scoreboard run at the start.

### 2.1 (a) `oddFrame_supply` and the "K-side complete" claim: VERIFIED EXACTLY

Elaborated type, from the mirror:

```
@oddFrame_supply : ∀ {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂}
  [FiniteDimensional ℚ_[2] ↥K] [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  (B : MarkedRecip Rec K) (FF : DyadicUnitFiltration K) {h : ℕ},
  Module.finrank ℚ_[2] ↥K = 2 * h + 1 → SqNuOrientedClearAtUnitPivot h → SqMarkedForwardSupply B h
```

Four explicit binders, matching the board's `carries 4 : MarkedRecip, DyadicUnitFiltration, Eq,
SqNuOrientedClearAtUnitPivot`.  `Rec` and `h` are implicit; the six instance binders are the
standing ones.

The **"K-side complete"** claim (`w83-frame-note.md:77`, "The K-side arithmetic is complete:
rows-up-to-a-bit and the unit pivot are theorems") **verifies**, in the precise sense that the
only non-bundle input is `SqCore.SqNuOrientedClearAtUnitPivot h`, and that is
`SqNuOrientedClearAtUnitPivot : ℕ → Prop`, elaborated: a statement whose entire signature is a
natural number, with no field, no bundle, no frame and no cup form in it, exactly as the module
doc says.  Its definition (`SqCore/PivotClimb.lean:787`) quantifies only over
`ContinuousMonoidHom (DSq h) (Multiplicative ℤ_[2])`, `SqJointSurjective`, `IsUnit`, and
χ-preserving `ContinuousMulEquiv`s of `DSq h`.  Everything K-side is discharged inside the proof:
the oriented equivalence by `orientedEquiv_of_oddDegree`, the level by
`B.level_eq_zero_of_odd_finrank`, joint surjectivity by `jointSurjective_transportedNuUr`, and
the unit pivot by `oddFrame_isUnit_transported_sqPivot`.

"Complete" here means **no binder**, not axiom-free: `oddFrame_supply` is std-3 plus
`{hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt,
absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic}`.  The module's own
axiom-hygiene claim that neither `B5 localReciprocity` nor `B5-K markedRecipAt` occurs in any pin
holds on the board's measured census.

**Elaborated end to end at one odd field.**  At degree 1 (`h = 0`, the cheapest genuinely odd
field) the whole chain runs with **no clearing binder**: the composite through
`oddFrame_candidate_equiv_galK_of_clear` fed by `oddFrame_clearAtUnitPivot_zero` elaborates, as
do `oddFrame_supply_degreeOne` and `oddFrame_cupAdaptedFrame_of_clear` at the same degree.  The
`h = 0` clearing is unconditional as a binder count but costs two further axioms,
`dyadicOrientation` and `peripheralCyclotomicAction`, which the board shows and which is why
`oddFrame_supply_degreeOne` prints a larger set than `oddFrame_supply`.

### 2.2 (b) the five strengthened existentials: CLEAN, and a sixth site that was missed

All five verified at source, line numbers undrifted, **statement and docstring agreeing at every
one**:

| # | declaration | file:line | marking in the conjunct |
| --- | --- | --- | --- |
| 1 | `genAsm_branch_of_oddSq` | `GeneralAssembly.lean:770` | the argument `nuP` |
| 2 | `genAsm_branch_of_oddSq_canonical` | `GeneralAssembly.lean:803` | `lNu h` |
| 3 | `fieldUni_genAsmBranch_of_orientedM_level_zero` | `FieldUnimodularity.lean:267` | `fieldId_mNuZtwo alpha 0` |
| 4 | `fieldUni_genAsmBranch_of_orientedN_level_zero` | `FieldUnimodularity.lean:286` | `nNuZtwo alpha 0` |
| 5 | `mpcCert_genAsmBranch_of_orientedMpc` | `MpcCertificate.lean:421` | `mpcNu α r pp` |

Each carries a `[W83-RECORDS: ...]` docstring block naming the marking and the reason for `HEq`;
none lags its statement.  `grep "HEq G.nuP"` confirms exactly these five pre-existing statements
changed, so no sixth site was silently strengthened.  Every consumer is accounted for: seven
downstream re-exports strip the conjunct with `.1` (proof-only), four sites in
`CanonicalRecords.lean` keep it, and the single place that uses it is `canRec_rowResidual_of_tied`.
Compile spot-check on the four highest-risk importers (`CanonicalRecords`, `FieldUnimodularity`,
`MpcCertificate`, `OddIdentification`): **4/4 green, exit 0**.  `OddIdentification` passing
doubles as a mirror-staleness self-check, since its `.1` would not elaborate against a pre-edit
`GeneralAssembly` olean.

**THE FINDING: a sixth site drops the marking, and two prose sites say it does not.**
`mpcPiv_genAsmBranch_sqrtNegTen_of_shift` (`Instances/MpcPivot.lean:478`) is headlined **THE
`√−10` BRANCH DATUM AT THE ROW'S CANONICAL MARKING, OVER `MpcPivShift` ALONE** and concludes

```
∃ G : GenAsmBranch KSqrtNegTen B, G.pres = .Mpc 2 1 true .one 0
```

with no conjunct: the proof obtains the strengthened site 5's output and applies
`Exists.imp (fun _ hG => hG.1)`.  A proof-level comment there is honest about it; the docstring
headline is not, and the headline is what readers cite.  Consequences:

* **`ℚ₂(√−10)` has no tied statement at this tree.**  Both its statements are untied; they differ
  in hypothesis (`MpcPivShift 2` versus nothing), not in tie.
* `Instances/CanonicalRecords.lean`'s per-row table reading 3 ("The tied statement at that row is
  `mpcPiv_genAsmBranch_sqrtNegTen_of_shift`") is **false at the statement level**, and that is in
  the Lean tree.  Corrected comment-only.
* `docs/dyadic/w83-records-note.md` §0 says it "routes through site 5 and therefore does carry
  `mpcNu`".  The **"therefore" is the error**: routing through a producer that names the marking
  does not make your conclusion name it, when you explicitly drop the conjunct.
  `docs/dyadic/w83-orbit-note.md`'s five-row table has the same reading ("tied form needs
  `MpcPivShift 2`").  Both are frozen lane notes and are reported, not edited.
* The board cannot see this, and says so: "whether a producer's conclusion is at the row's
  CANONICAL marking; `GenAsmBranch` does not pin `nuP`".  The blind spot is correctly documented
  and correctly fired.

The repair is one line of Lean and is a **statement change**, so it is an owner item, recorded at
the theorem and in §4 below.

### 2.3 (c) the scoreboard's blind-spot list against its behaviour

**Does it print UNVERIFIED where it says it does?  Yes, and this was observed rather than
assumed.**  The lane's first scoreboard run, before the mirror was swept in a fresh worktree,
printed the banner `!! probe A did not elaborate; every row below is UNVERIFIED` followed by
`UNVERIFIED (probe produced no record)` on every one of the 30 rows, and
`UNVERIFIED (probe B did not elaborate)` for registration.  The degradation is loud, total, and
correct: no row silently reported a stale value.  The `OWNER ITEMS` and `A6 FREEZE` sections print
UNVERIFIED with the checkable substitute beside them, as documented.

**But one entry in the list was live, not hypothetical.**  The board printed

```
  v-10 residual move             producers: 0   [MpcPivShift]
```

while `MpcOrb.mpcOrb_shift_of_marking` (`Instances/MpcOrbit.lean:156`) concludes `MpcPivShift 2`.
Machine-confirmed by re-running the script's own `sbProducers` scan with `MpcOrbit` imported:

```
PROD|GQ2.Dyadic.Instances.MpcPiv.MpcPivShift|1
   GQ2.Dyadic.Instances.MpcOrb.mpcOrb_shift_of_marking
PROD|GQ2.Dyadic.LSquare.SqCupAdaptedFrameRelator|0
```

`SqCupAdaptedFrameRelator`'s zero is genuine.  `MpcPivShift`'s was not.  The cause is the
documented one: no row named a declaration in `MpcOrbit`, so a `prod` scan reading the
environment could not see it.  The same horizon silently omitted `Instances.CanonicalRecords` and
`Instances.MpcOrbit` from the REGISTRATION section; both are in fact registered
(`GQ2.lean:874,875`), so nothing was wrong there, but nothing was confirmed either.

Fixed at the script's own documented extension point, one `decl` row naming
`mpcOrb_shift_iff_marking`, which pulls the module into the import set.  The board now prints
`producers: 1` and confirms both modules registered.  Two blind-spot entries added: the incident
itself, and the fact that a `prod` scan matches only the conclusion's **head** constant, so an
`Iff`-shaped or `Nonempty`-shaped producer is never counted, `mpcOrb_shift_iff_marking` being
exactly such a statement.  `producers: 0` must be read as "nothing concludes it directly", never
as "nothing in the tree bears on it".

A `RECORD BLOCKS` group was added over the four tied rows, which turns the per-row table of §2.4
into a machine-checked line.  **This is the one non-comment change of the lane**; it is additive,
it is the procedure the script documents, and a bad row degrades to `MISSING`/`UNRESOLVED` rather
than to a wrong number.

### 2.4 (d) headline versus statement on the three new modules

`Instances/CanonicalRecords.lean`: the per-row table's two load-bearing readings **verify by
elaboration**, in both templates and identically across all four rows:

* template 1, `canRec_rowResidual_<field>`, carries `B`, `F`, `cand : WordCertificate`,
  `ExactLiftingSemantics` and `StokesDualityCertificate`, the last two at `galKProfinite K`.
  Three blocks beyond the bundle and field inputs, as the header says.
* template 2, `canRec_analytic_<field>`, carries `B`, `FF`, `F`, then the four Γ-side clauses
  `ExactLiftingSemantics`, `StokesDualityCertificate`, `ScalarHilbertCertificate`,
  `AffineDeterminantCertificate` at `GammaR deg q word`, then the same two `ASK` blocks at
  `galKProfinite K`.

So reading 1 ("`ASK` `determinant` is gone ... the record costs **two** `ASK` blocks, not three")
is **correct**: there is no third `ASK` binder in either template.  One precision note was added,
because a reader who greps rather than elaborates *will* find an `AffineDeterminantCertificate`
binder in §5 and think the claim false; it is the Γ-side analytic clause, not an `ASK` block.
Reading 2 ("the residue is uniform") is confirmed exactly: the binder lists are identical across
the four rows.

`Instances/MpcOrbit.lean`: headlines check out.  `mpcOrb_defect` is the closed form claimed;
`mpcOrb_shift_iff_marking` is a genuine two-way equivalence, both directions present;
`mpcOrb_shift_of_marking`'s claim that "the *only* real content a caller must supply is `hrel`"
is fair, the other three clauses being generation, the four χ-values and the row shift.  §3's
heading "The frame level cannot obstruct" is supported in the weak and correct sense: neither
statement mentions the `M6` substitution, both being identities about the *values* of an
arbitrary `ν'`, which is exactly the claim that the shift respects the only relation the frame
carries.  Worth knowing when citing them: they are compatibility checks, not a derivation that
`M6` exists.  The "What does not land" section is exemplary, and states the decision honestly.

`Instances/OddFrame.lean`: see §2.1 for `oddFrame_supply`; the fuller audit of §1 to §3 and §5 is
reported at the end of this section.

One phrasing worth flagging without correcting: `OddFrame.lean:393` describes
`oddFrame_realization_of_clear` as having "no clearing binder on the `K` side", and the theorem
does take `hclear`.  The sentence is accurate on its intended reading, that the binder it carries
is not K-indexed, but it reads at a glance as though there were no clearing binder at all.

### 2.5 (e) the `HEq` conjunct pattern

**Verdict: the `HEq` choice is correct and is not itself worth an owner item.**  Inventory: 13
occurrences of the wave-83 pattern (5 producers, 8 restatements/hypotheses), introduction always
`HEq.rfl`, elimination at exactly **one** site, `CanonicalRecords.lean:328`.  Five pre-existing
occurrences of the same shape, `selectedWord_{L,N0,Npc,M0,Mpc}` in `CertificateSupplyRN.lean`,
each of which inlines the same destructure-and-`subst` dance five separate times, never factored:
the tree's own precedent is worse than what wave 83 did.  `heq_iff_eq`, `Subsingleton.helim` and
the `▸` repair appear nowhere in `GQ2/`.

The recovery is genuinely three lines, genuinely written once, and genuinely general: it is stated
at implicit variable `row` and `nu0`, so all seven downstream users thread their producer's output
verbatim and never see an `HEq`.  The "does not elaborate" claim about `hp ▸ G.nuP = nu0` is
plausible as stated and its diagnosis is essentially right, though loosely worded (what matters is
the equation's *sides*, not its type).  Of the alternatives, only indexing the record at `pres`
buys anything real, and its case rests on unifying the `L` row rather than on the `HEq`.

**The friction that is real is not the `HEq`.**  Two items, both listed in §4:

1. The `√−10` site of §2.2, which is the highest-value one-line fix found this round.
2. **A two-idiom split on the `L` row.**  The odd chain drops the marking at
   `OddIdentification.lean:206`, while `Instances/LRowCand.lCandBranch` rebuilds the same datum as
   a *definition* so that `nuP` is definitionally `lNu h` (`lCandBranch_nuP` is `rfl`).  The tree
   now has two incompatible idioms for one problem and no bridge between them.  This, not the
   `HEq`, is the design question worth a ticket.

Also noted, and already the wave-83 note's own owner item: `canRec_rowResidual_{M0,N0}_of_analytic`
take the `HEq` hypothesis at **free** `h`, but the only producers supplying that conjunct are the
level-zero ones, so at `h ≠ 0` those shape lemmas have no supplier.  Sites 6 and 7
(`genAsm_branch_of_evenN`/`_evenM`) are why.

---

## 3  Ticket 3: the endgame board

Everything in this section is from the scoreboard run at lane end unless marked otherwise.

### The odd route: one model statement

`SqMarkedForwardSupply B h` has **14 producers** in the environment the rows reach.  The cheapest
is no longer frame-shaped: `oddFrame_supply` carries `MarkedRecip, DyadicUnitFiltration, Eq,
SqNuOrientedClearAtUnitPivot`, so beyond the bundle, the filtration and the degree the odd route
costs exactly **one model-side Prop**, `SqCore.SqNuOrientedClearAtUnitPivot h`, verified in §2.1
to be a pure `ℕ → Prop`.

That Prop has **3 producers**: `sqNuOrientedClearAtUnitPivot_of_families` (carries
`SqHandleMixFixesCore` plus two functions), `sqNuOrientedClearAtUnitPivot_of_pivotMoves` (carries
`SqHandleMixFixesCore` plus one function, and is the **stronger** ask despite the smaller count,
which the board warns about), and `oddFrame_clearAtUnitPivot_zero`, which carries nothing and
closes `h = 0`.  So the route is closed at `h = 0` and open at `h ≥ 1`, where the two
one-parameter pivot families `SqPivotTranslation` and `SqPivotScaling` plus the handle stratum are
the graded lanes' open moves.  **The odd route is at one model statement, not closed.**

The seam's other equivalent forms are all present and cheap: `oddSeam_supply_iff_cupAdaptedFrame`,
`oddSeam_supply_iff_fullMarking`, `oddId_supply_iff_certificate` and
`oddFrame_supply_iff_clearInstance`.  `SqCupAdaptedFrameRelator` has **0 producers**, genuinely;
`SqCupAdaptedFramePresentation` has 1.

### The selector: four tied free, and the M6 question

Four rows carry a tied, unconditional branch datum: `ℚ₂(√−2)`, `ℚ₂(√2)`, `ℚ₂(√5)`, `ℚ₂(√10)`.
Each `fieldUni_`/`fieldFive_`/`mpcNorm_` row carries exactly `MarkedRecip`.

The fifth, `ℚ₂(√−10)`, is where §2.2 changes the reading.  Three statements exist:
`mpcNorm_genAsmBranch_sqrtNegTen_of_pivot` (carries `MarkedRecip, Exists`),
`mpcPiv_genAsmBranch_sqrtNegTen_of_shift` (carries `MpcPivShift, MarkedRecip`) and
`mpcPiv_genAsmBranch_sqrtNegTen` (carries `MarkedRecip`).  **None of them is tied.**  The row
therefore needs two things, not one: `MpcPivShift 2`, and a one-line statement change.

`MpcPivShift 2` itself is **open**, and after this round the board shows it correctly with **1
producer**, `mpcOrb_shift_of_marking`, carrying six `Eq`s and one function.  W83-ORBIT reduced it
to an explicit word problem in `D_M 2 0` via `mpcOrb_shift_iff_marking`, an equivalence, and
computed the `M6` defect in closed form as a product of four conjugates of `u`.  The ruling that
made it look decided in the negative is now known to be unsound as an argument (§1), so the
question is genuinely open in both directions rather than presumed false.

### The record blocks per row, under the two-template residue

Measured, identical across all four tied rows (§2.4).  Beyond `B` and the field inputs `F`:

| template | what remains |
| --- | --- |
| `canRec_rowResidual_<field>` | `cand : WordCertificate`, `ASK` exactLifting, `ASK` stokes |
| `canRec_analytic_<field>` | four Γ-side clauses (exactLifting, stokes, scalarHilbert, affineDeterminant), `ASK` exactLifting, `ASK` stokes |

**Two `ASK` blocks per row, not three**: the determinant is discharged through
`mpcRow_genAsmRowResidual_of_counting` from `affineDeterminant_galK`.  The `CAND` producers are
all present and all std-3, which is the sharp fact here: placing the committed word certificate on
the row's canonical marking costs **no campaign axiom** at any of the three branch shapes.

The `ASK` block itself: `askCStageVanishing` exists and carries 4; `askC_exactLifting_iff_stageVanishing`
carries 2; the four `_galK` rungs are all present, with `affineDeterminant_galK` the expensive one
at 12 binders.

### The even route: one surviving point, unchanged

Unchanged since wave 74, and nothing this round touched it.  The surviving point is `Hfam`
(`EvenRouteFinalFamily{N,M} h K`), which `EvenFamilyStatus.lean` proves is **equivalent** to the
even classification at that field, not weaker: `hfamFinal_family{N,M}_iff_orientedEquiv`.  So it
can be neither refuted without refuting the classification there, nor discharged by soft means.
Its arithmetic form is `EvenFamParitySupply{N,M}`, mod-2 surjectivity of
`Z¹(χ mod 2^{k+1}) → Z¹(𝔽₂)` on prescribed coordinates: higher Kummer theory at `K`, the even
clone of the odd route's `SqStageTwistedCocycleParitySupply`.

---

## 4  Owner items: nine standing

Seven inherited, plus the bridge re-cut already among them, plus two opened this round.  None is
takeable by a comment-only lane; all are statement changes or policy calls.

1. **ASK restatement.**  Restate the row records against `ExactLiftingSemanticsRN`, or prove
   `askCStageVanishing`.  Unchanged.
2. **Pilot spelling** (`w74-critical-path.md` §1.5).  Unchanged.
3. **The A6 freeze** (`GQ2/Roe/*`): **eleven** review rounds without motion.  `git diff 45f9c42d
   HEAD` on `GQ2/Roe/` and on `GQ2.lean` is **empty** for this lane, checked.  The board prints
   the substitute: last commit `4341a1a3`, 2026-08-10, comment-only; **12** house notes added
   since.
4. **Line length.**  Policy call still owed.  Not re-measured this round.
5. **The forgotten marking.**  Wave 83 discharged **five of eight** sites.  Three remain:
   `genAsm_branch_of_evenN` and `genAsm_branch_of_evenM` (`GeneralAssembly.lean:717,732`, the
   free-`h` even producers, which is why the free-`h` shape lemmas of `CanonicalRecords` have no
   supplier at `h ≠ 0`), and **new this round** the `√−10` site of §2.2.
6. **`askCStageVanishing`: fact or wrong ask?**  Unchanged, and still the sharpest open item on
   the arithmetic side.
7. **The `hclear` re-cut** (S5).  `GammaLOddDegreeBridgePivot`'s consumers take `hclear` **and**
   `hsupply`; since `oddFrame_supply` derives the supply from the clearing, they should take
   `hclear` alone.  Unchanged.
8. **NEW: tie the `√−10` shift statement.**  At `Instances/MpcPivot.lean:478`, add
   `∧ HEq G.nuP (mpcNu 2 1 (p true 1) _)` to the conclusion and delete the `Exists.imp`; the proof
   already has it in hand.  One line.  It would make this the genuine tied statement at the row and
   admit `ℚ₂(√−10)` to `CanonicalRecords` as a fifth row modulo `MpcPivShift 2`, and it would let
   the two frozen lane notes' claims become true.  Recorded at the theorem.
9. **NEW: the two-idiom split on the `L` row** (§2.5).  The odd chain drops the marking while
   `LRowCand.lCandBranch` rebuilds the datum definitionally to get it back.  Either restate the
   odd chain to keep the conjunct and route it through `canRec_rowResidual_of_tied`, or index the
   record at `pres` tree-wide.  A design question, not a one-liner.

---

## 5  What this lane did not do

No statement was changed anywhere in `GQ2/`; every tree edit is a comment.  I did not touch
`GQ2.lean` or `GQ2/Roe/*`, and I did not create or touch `SqCore/GradedClearing.lean`,
`Instances/MpcWord.lean` or `Instances/RowClauses.lean`.  I did not edit the four frozen wave-83
lane notes, whose two incorrect claims are reported in §2.2 rather than rewritten.  I did not
attempt the model clearing, `MpcPivShift`, or `askCStageVanishing`, and I did not wire the
scoreboard into any gate.  The one behaviour change outside the tree is the scoreboard's row table
and blind-spot list, §2.3.
