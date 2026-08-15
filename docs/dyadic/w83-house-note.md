# W83-HOUSE: the scoreboard, AB-0, watch round 20, and the endgame board

**Lane W83-HOUSE, branch `claude/w83-house`, base `23041e0f`.**  Standing verification lane
plus two structural tickets.  Comment-only in the tree throughout: no statement anywhere was
changed, no theorem added or removed, no `sorry`, no axiom, no import, no `GQ2.lean` edit, no
`GQ2/Roe/` edit.  One new file, `scripts/scoreboard.sh`, which is a reporting tool and is wired
into no gate.

Verification of record: `scripts/mirror.sh sweep` at lane start (5973 artifacts), `gen` on
`GQ2.Dyadic.Instances.OddFrame` and `GQ2` after the base advanced, `check` on every edited
module, all green.  `scripts/mirror.sh check GQ2/AxiomLedger.lean` green, exit `0`, **0 terminal
violations**.  **No `lake` command was run.**

**`dyadic` advanced past this lane's base twice mid-round.**  First to `db6fcedf` (W83-FRAME's
`Instances/OddFrame.lean`): merged, both oleans regenerated, and **everything re-measured**,
rather than reporting a board known to be stale.  Then again to `9f05fb98` (W83-RECORDS), after
the board was taken and with the shared cache still at `db6fcedf`; that one is reported as a
read-not-elaborated delta in §4 rather than merged, for the reason given there.  So: §4's board
is as of `db6fcedf`, its delta subsection is as of `9f05fb98`, and every tree annotation says
which tree it is as of.

---

## Headline

**The status tables are retired, and the tool that replaces them found the sixth instance of the
own-base pattern before it found anything else.**  `scripts/scoreboard.sh` elaborates the
campaign's load-bearing status facts on every run: per frozen row, per seam statement and per
record block it prints EXISTS/MISSING, the explicit binders a caller must supply, and the axiom
census, all re-derived; and for a named `Prop` it enumerates **every producer in the tree**,
which is the check that a "no theorem produces X" claim cannot survive.  It carries no
hand-maintained data beyond declaration names, and where a fact is not cheaply machine-checkable
it prints UNVERIFIED rather than a value.

The first thing it printed was that `ℚ₂(√5)` carries nothing, which
`docs/dyadic/w82-pivot-note.md` §7 denies.  That claim has now been made by **three consecutive
lane notes**, was corrected in the tree at wave 79, and was corrected in prose twice inside the
pivot lane's own base.  The scoreboard exists because that keeps happening; it printed the
counterexample in its first run.

**AB-0 turned out not to be a statement change.**  Six waves of notes recorded AB-0 as blocked
because "rewriting an inventory table is more than a marker".  It is comment-only, it took one
pass, and doing it surfaced two facts nobody had: `KSupply.toSourceN`'s docstring says "nine
projected" where the record projects eleven, and the five CAND row producers do **not** carry
the same four clauses.

---

# Findings, by severity

## S1.  `ℚ₂(√5)`: the third consecutive note, from a lane whose sibling had just corrected it

**`docs/dyadic/w82-pivot-note.md` §7 row 3**, verbatim:

> | 3 | `ℚ₂(√5)` | `.M0 2 0` | **no**: `fieldUni_TwoIsUniformizer KSqrtFive` | (yes, once it lands) |

and **§9 item 3**:

> 3. **`fieldUni_TwoIsUniformizer KSqrtFive`** (row 3), still open and unchanged by this lane.

**Correction, elaborated.**  `fieldFive_genAsmBranch_sqrtFive` carries exactly one explicit
binder, `B : MarkedRecip Rec KSqrtFive`, and nothing else; `fieldFive_twoIsUniformizer`
(`Instances/FieldSqrtFiveUnramified.lean:209`) proves the clause with **no hypotheses**.  Both
landed at wave 79 (`b1bd2e64`).  Corrected, the row table's closing sentence reads: **five of
the five rows carry a branch datum over the bundles alone**, four of them at the row's canonical
marking, and row 5's is untied.

**Why this is S1.**  It is not the error, it is the trajectory:

1. `w80-rowdata-note.md` §7 item 4 said it (corrected in place, that note's own §263);
2. `w81-norms-note.md` §6 and §8 said it (W82-HOUSE S2 corrected it);
3. `w82-pivot-note.md` says it again.

And the third time is the worst of the three.  `w81-house-note.md` §3.5 is **in the pivot lane's
own base** `a45bc557` and records the correction.  `w82-house-note.md` §S2 was committed at
11:38, from the same base, in the same wave; the pivot note at 11:39.  Two prose corrections and
a five-wave-old theorem were all in scope, and none was read.  This is the sixth recorded
instance of the own-base pattern and the first where the correcting text was **already written
and already committed** when the error was made.

Both sites annotated.  This is the row the scoreboard prints first.

## S2.  `DsqDemushkin.lean` claims a theorem of the tree is proved nowhere in it

**`GQ2/Dyadic/SqCore/DsqDemushkin.lean:70`**, verbatim:

> `demushkinQ (D_sq h) = 2` is **not** proved, here or anywhere in the tree.  Both precedents get
> it from an explicit abelianization decomposition … and the square family has no such frame yet.

**Correction.**  `oddSeam_demushkinQ_DSq (h) : demushkinQ (DSq h) = 2` (`Instances/OddSeam.lean`,
W82-SEAM, `96b7808b`) proves it at every handle count, and it prints **std-3 exactly** (verified
by elaboration, not by reading the pin block).  The paragraph's diagnosis was right on the nose:
the proof builds precisely the missing frame, `oddSeamAbEquiv h`, and reads the count off the
same generic `demushkinQ_of_torsionEquivZMod` the `N` precedent uses.

Flagged by W82-SEAM's own handover (`w82-seam-note.md` item 3) and superseded here.  The
paragraph's last sentence, "nothing below uses it", is still true of that file.

## S3.  The `√−2` row's CAND residue is not the others', and two notes say it is

**`docs/dyadic/w82-cand-note.md`** item 4, verbatim:

> This is the honest residue of the CAND field after the lane, and it is the **same residue the
> `M0` and `N0` rows carry**, so it is now uniform across all three `CorePresentation`-backed
> rows.

**Correction, elaborated, four producers side by side.**  `mWordCertificate`,
`mpcWordCertificate`, `genCertNpcWordCertificate` and `lCand_wordCertificateCanonical` carry the
four bundles verbatim: `ExactLiftingSemantics`, `StokesDualityCertificate`,
`ScalarHilbertCertificate`, `AffineDeterminantCertificate`.  `sqrtNegTwoWordCertificate` carries
`PilotHsimp`, `PilotStageSep`, `PilotStageZ`, `PilotDet`.  Only `PilotDet` is one of the four
(it **is** an `AffineDeterminantCertificate`); `PilotHsimp` is a per-simple-module
`StokesDuality`, i.e. an *input* to the count rather than the count, and `PilotStageSep` /
`PilotStageZ` are `stageR136`'s two recursion-side residues.

So the `√−2` row's residue sits **one layer below** the others' and is strictly narrower.  The
uniform claim is true across `M0`, `Mpc`, `Npc` and `L`, four rows and not three.  W82-HOUSE's
S4 correction to `GeneralAssembly.lean` happens to name exactly those four and is therefore
right; the CAND note and `CertificateMain.lean` §2b were not.  Both corrected.

This one is a scoreboard dividend: nobody would have caught it by reading, because all five
producers *look* alike at the call site.

## S4.  `w80-rowdata-note.md` §3.3's missing identity is a theorem, and the ticket it wrote was taken

**`docs/dyadic/w80-rowdata-note.md:127`**, verbatim:

> The displayed identity for `ν'(ker χ_M)` is not a theorem of this tree … That is the single
> missing input, and it is a statement about `ℤ₂ˣ` alone, so it is cleanly ticketable.

**Correction.**  Wave 81 landed the freeness (`mpcNorm_free_unique`), wave 82 landed the
identity in both directions: `mpcPiv_kerChi_le` / `_ge` (`Instances/MpcPivot.lean:200`, `:216`),
both **std-3**, at every marking of `D_M 2 0` and with no level hypothesis.  Checked term by term
against the note's displayed form `ν'(ker χ_M) = ⟨ν'(C̄₀), 2·ν'(B̄)⟩`: the `le` half concludes
`∃ m y, ν'(x) = m·ν'(C̄₀) + 2y·ν'(B̄)` from `χ_M(x) = 1`, the `ge` half attains every such
combination by the explicit class `C̄₀^m·B̄^{2y}`, and the two together are the ℤ₂-span on the
nose.  The `ν'(Ā)` term this note drops by `nu_dmA_eq` is dropped the same way in the proof
(`mpcPiv_gens_mem`, unconditional at `α = 2`), and `ν'(D̄)` falls out because freeness kills the
`(mUnit 2)`-exponent, which is why no hypothesis on the marking is needed.

Both conclusions the note drew survive, and one is now a theorem instead of a hand check.
Annotated.  This is a lane doing exactly what it should: writing a sharp ticket, and the ticket
being taken two waves later.  The only failure is that nobody closed the loop in the note.

## S5.  `GammaLOddDegreeBridge`'s "the repair must be P3's supply" no longer follows

**`GQ2/Dyadic/Instances/GammaLOddDegreeBridge.lean:34-46`**, in summary: the pivot parity is an
invariant of the target, so no model-side work can supply it; *therefore* the repair is
arithmetic and is P3's `SqMarkedForwardSupply B h`.

**Correction, as of `db6fcedf`.**  The premise stands and `PivotClimb` §4 is unrefuted.  The
inference does not: W83-FRAME **computed** the invariant instead of routing around it.
`oddFrame_isUnit_transported_sqPivot` (std-3 + {B1, B6, B11a}) makes `sqPivotExp` a unit, so the
transported pivot row's parity *is* the `ν̄`-row sum, and the cup form pins that sum to `1` at
every odd-degree `K`.  The unit pivot therefore holds at **every** oriented equivalence with no
supply and no frame clause.  Annotated at the site; the re-cut of the consumers that take
`hclear` **and** `hsupply` is a statement change and is a new owner item.

## S6.  Precision items, none an error

* **`OddSeam.lean` §6's "std-3 only"** is read as "no census axiom", which is its job.  Seven §1
  declarations print a strict subset: `oddSeamCoreMark` and `oddSeamCoreMark_eq_one` print
  `[propext]` alone; `oddSeamHandleIdx`, `oddSeamHandleIdx_val`, `oddSeamHandleMark`,
  `oddSeamHandleMark_self`, `oddSeamHandleMark_of_ne` print `[propext, Quot.sound]`.
* **"Overshoots the seam by exactly its quantifier"** (`OddSeam.lean` §3) is one quantifier
  short.  `SqCupAdaptedFrameRelator K` is `∀ h, ∀ F cup-adapted, sqRelWord = 1`; the seam's frame
  form is `∃ F` at ONE `h` with **three** conjuncts under the `∃`, of which the clause mentions
  one.  The rows are paid out of `B` and `FF`, which is why `oddSeam_supply_of_relator` binds a
  filtration and `oddSeam_supply_iff_cupAdaptedFrame` binds none.  Both annotated in place.
* **`KSupply.toSourceN`'s docstring said "nine projected"** where the record projects eleven, and
  the module docstring in the same file says eleven.  Fixed under AB-0.
* **The line-length owner item, re-measured at `db6fcedf`**: **706** lines over 100 codepoints in
  **250** files (707 / 250 at wave 82; the wave-82 lane's own fix accounts for the one).  The
  three wave-82 modules are clean at 0, 0, 0; `LRowCand.lean:329` is the wave's one regression,
  at 107.  Every line this lane wrote, in tree and in docs, is under 100.

---

# Ticket 1: `scripts/scoreboard.sh`

`bash -n` clean.  Read-only, runs `mirror.sh check` on generated probe files in a temp dir, runs
**no `lake` command**, wired into no gate.  Output in §4.

## The design, and why it is this design

The failure this replaces always has the same shape: a note asserts a status, the theorem that
refutes it predates the note, nobody re-elaborates.  So the tool does not store status.  It
stores **declaration names** and derives everything else on each run:

* the file is found by grep; the **fully-qualified name** is rebuilt from the namespace stack
  (tracking `namespace` / `section` / `end`), and the **module to import** from the path.  No
  namespace, module, path or line number is written down in the script, because those are the
  things that rot;
* two probes are generated.  Probe A imports exactly the modules the rows need and, for each
  row, reports existence, the types of the **explicit** binders (instance-implicit and implicit
  dropped: what a caller must actually supply), and the axiom census as `std-3` plus the
  non-standard names.  Probe B imports **only `GQ2`**, so a name it cannot see is a name no
  `import GQ2` consumer can see: that is the registration check, and it is exact rather than a
  grep of the umbrella;
* a `prod` row names a `Prop` and the tool enumerates **every declaration in the `GQ2` root
  whose conclusion has that name as its head constant**, each with its own binders and census.
  This is the row type that kills "no theorem in this tree produces X".

Adding a row is one `GROUP|LABEL|KIND|SHORT-NAME` line; the header documents it.  Facts that are
not cheaply checkable print **UNVERIFIED** with the nearest checkable substitute beside them
(the owner items' *status*, and the A6 round count, whose origin wave is not in git).  The four
things the board cannot see are printed on the board itself.

## What it found on its first two runs

* `ℚ₂(√5)` carries **nothing** (S1), and `mpcPiv_genAsmBranch_sqrtNegTen` carries nothing either;
* `MpcPivShift` has **0 producers** and `SqCupAdaptedFrameRelator` has **0 producers**: the two
  named residuals are genuinely unproduced, not merely unrecorded;
* `SqMarkedForwardSupply` had **11** producers at `23041e0f` and **14** at `db6fcedf`, against
  the "three" the notes inventory.  Every one of the 14 carries a frame clause, the equivalent
  certificate, the model clearing, or a degree-one pin, so the notes' *substance* is right and
  their count is not;
* the CAND split of S3, which is invisible to reading;
* `SqNuOrientedClearAtUnitPivot` has **3** producers, one of which
  (`oddFrame_clearAtUnitPivot_zero`) carries **nothing** but is pinned at `h = 0`.

## Two limits the mid-round re-run exposed, now printed on the board

1. **A `prod` scan sees only modules some row imports.**  `OddFrame.lean` was invisible until a
   row named a declaration in it.  This is the one way the board can be stale, and it is why the
   tool is not a gate.
2. **The `carries` column counts binders, not strength.**
   `sqNuOrientedClearAtUnitPivot_of_pivotMoves` carries 2 against `_of_families`' 3 and is the
   **stronger** ask (the whole unit-determinant pivot family, against two one-parameter ones).
   A reader who ranks routes by binder count will pick the wrong one.

---

# Ticket 2: AB-0, executed

`docs/dyadic/followup/analytic-bridges-plan.md` §6 item 1, queued at wave 77, never done while
AB-1 through AB-7 all landed, and named by W82-HOUSE as the root cause of an eleven-site
straggler field.  **Comment-only, as the plan specified.**  Marked done in the plan.

**`Instances/KSupply.lean`.**  The inventory now separates two words the wave-77 form ran
together, and that conflation is the whole bug: **carried** means "a structure field of this
record", a fact about the file; **owed** means "no theorem anywhere produces it at `G_K`", a
fact about the tree.  A leaf can be carried and not owed for many waves, because converting a
field into a call is a statement change.  Truth-synced: ten proved, eleven carried, of which
**two are owed** (`pro2`, `ker_pro2`, unchanged since wave 77), **eight have a landed supplier**,
and **one is one coefficient short** (`stageR136`).  The "what this file does not do" paragraph,
the `lem86_galK` docstring and the §6 handover are rewritten the same way; the wave-79 and
wave-82 pointer annotations are removed with their content folded in, per the ticket.

The §6 handover's framing was itself the stale thing: it grouped the leaves by "the `ℚ₂` object
whose `K`-clone would discharge them", and three of its four items were answered by a `Γ`-generic
layer rather than a clone.  Its item 3 predicted exactly that and is left in place saying so.

**`CertificateMain.lean`.**  The `ExactLiftingSemantics` docstring's "at general `K` it has no
owner" is a claim about **both** carriers this `Prop` is instantiated at, and they are in
different states: owned at `galKProfinite K`, genuinely unowned at `GammaR n q word` (AS1
divergence 4).  Running them together is what seeded the straggler field, so the sentence is now
split by carrier.  §2b's two-producer sentence is replaced by the five-row producer inventory,
including the S3 split.

Two facts the pass turned up, both new: the "nine projected" miscount (S6), and S3.

---

# Ticket 3: watch round 20, item by item

## (a) `oddSeam_demushkinQ_DSq`: statement and axiom-freeness verified exactly

```
theorem oddSeam_demushkinQ_DSq (h : ℕ) : demushkinQ (DSq h : Type) = 2 :=
  demushkinQ_of_torsionEquivZMod (oddSeamAbEquiv h) (oddSeamTorsionEquiv h)
```

Elaborated at this tree: `[propext, Classical.choice, Quot.sound]`, i.e. **std-3 exactly, no
census axiom**.  The headline "at every handle count" is the statement: `h` is a free explicit
binder and there is no hypothesis.  All **64** pins in the module were re-elaborated (64 pin
lines, 64 outputs, zero unpinned declarations) and **the four-way split of §6 is exact on every
one**, measured at `23041e0f` rather than at the module's own `a45bc557`.  Two precision items in
S6.

## (b) The seam-iff-frame equivalence: binders check, one reading does not

```
theorem oddSeam_supply_iff_cupAdaptedFrame (B : MarkedRecip Rec K) {h : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 1) :
    SqMarkedForwardSupply B h ↔
      ∃ F : SqCyclotomicFrattiniFrame K h, F.IsCupAdapted ∧ sqRelWord F.generators = 1 ∧
        nuUrKTwo B (F.generators 0) = ofAdd (1 : ℤ_[2]) ∧
          nuUrKTwo B (F.generators 1) = ofAdd (0 : ℤ_[2])
```

Two explicit binders, `B` and `hdeg`, no clause, no filtration; std-3 + {B1, B6, B7}, which is
the backward direction's rigidity.  The forward direction alone
(`oddSeam_cupAdaptedFrame_of_supply`) drops `hdeg` and B7, as the module says.  The near-miss is
in the *reading*, not the statement: see S6's second bullet.

## (c) `mpcPiv_kerChi_le/ge` against wave 80's displayed identity: exact match

Checked in S4, term by term, in both directions, including the two terms wave 80's display drops
(`ν'(Ā)` by `nu_dmA_eq`, `ν'(D̄)` by freeness) and the absence of any hypothesis on the marking.
Both std-3.  Wave 80's §3.3 annotated.

## (d) `DsqDemushkin.lean`'s stale sentence: superseded

S2.  Comment-only; the file's own mathematics is untouched and its closing "nothing below uses
it" still holds.

## (e) Headline versus statement, the three wave-82 modules

| module | decls | pins | headline claims checked |
|---|---|---|---|
| `OddSeam.lean` | 56+ | 64, 0 unpinned | four-way axiom split **exact**; T1 std-3; T2 three statements verified |
| `MpcPivot.lean` | 18 | 19, 0 unpinned | three-set split **exact** |
| `LRowCand.lean` | 27 | 27, 0 unpinned | "25 of 27 at most std-3, `lCand_row_degree` none at all" **exact** |

`MpcPivot`'s sharpest pin claim holds: `mpcPiv_genAsmBranch_sqrtNegTen_of_shift` sits at
**exactly** `mpcNorm_genAsmBranch_sqrtNegTen_of_pivot`'s axiom set, and the untied
`mpcPiv_genAsmBranch_sqrtNegTen` differs from it by `peripheralCyclotomicAction` alone, which is
that lane's own reading (B8 enters only through normalizing the marking).  `LRowCand`'s
"thirteen of the seventeen fields proved" checks against a field count of the `WordCertificate`
structure: 17 fields, 4 analytic clauses carried, and `lCand_wordCertificateCanonical`'s explicit
binders are `(h, q, hq0, hqe)` plus exactly those four.

## (f) The constructor table and the scoreboard-adjacent prose against the CAND landing

W82-HOUSE's corrections to `GeneralAssembly.lean:297-306` and `OddIdentification.lean:232` are in
place and are right, including the "four of the five rows" count.  What was **not** swept is the
finer claim inside them, that the four carry "the same four analytic clauses" as `N0`: they do
not, and the two documents that say so are corrected (S3).  Registration is current: all
twenty-one modules the board names are visible to an `import GQ2` consumer, `OddFrame` included.

---

# Ticket 4: the endgame board

Below is `scripts/scoreboard.sh`'s output, at `db6fcedf` plus this lane's comment-only commits.
Every EXISTS line, binder list and axiom census in it was elaborated by that run.

```
=======================================================================
 GQ2 DYADIC CAMPAIGN SCOREBOARD
 tree 3b79b72a 2026-08-15   branch claude/w83-house   generated 2026-08-15 12:42
 every EXISTS / binder / axiom line below was elaborated by this run
=======================================================================

## FROZEN ROWS
  Q2(v-2)  .N0 2 0               EXISTS   GQ2.Dyadic.FieldUnimod.fieldUni_genAsmBranch_sqrtNegTwo
      carries 1  : MarkedRecip
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  Q2(v2)   .M0 3 0               EXISTS   GQ2.Dyadic.FieldUnimod.fieldUni_genAsmBranch_sqrtTwo
      carries 1  : MarkedRecip
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  Q2(v5)   .M0 2 0               EXISTS   GQ2.Dyadic.FieldSqrtFive.fieldFive_genAsmBranch_sqrtFive
      carries 1  : MarkedRecip
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  Q2(v10)  .Mpc F                EXISTS   GQ2.Dyadic.Instances.MpcNorm.mpcNorm_genAsmBranch_sqrtTen
      carries 1  : MarkedRecip
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  Q2(v-10) .Mpc T                EXISTS   GQ2.Dyadic.Instances.MpcNorm.mpcNorm_genAsmBranch_sqrtNegTen_of_pivot
      carries 2  : MarkedRecip, Exists
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  Q2(v-10) via shift             EXISTS   GQ2.Dyadic.Instances.MpcPiv.mpcPiv_genAsmBranch_sqrtNegTen_of_shift
      carries 2  : MpcPivShift, MarkedRecip
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  Q2(v-10) untied                EXISTS   GQ2.Dyadic.Instances.MpcPiv.mpcPiv_genAsmBranch_sqrtNegTen
      carries 1  : MarkedRecip
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  v-10 residual move             producers: 0   [MpcPivShift]

## ODD SEAM
  the seam Prop                  EXISTS   GQ2.Dyadic.LSquare.SqMarkedForwardSupply
      carries 2  : MarkedRecip, Nat
      axioms     : std-3
  every seam producer            producers: 14   [SqMarkedForwardSupply]
      GQ2.Dyadic.LSquare.MarkedFrame.oddDegreeGalKSqMarkedForwardSupply
        carries 5  : MarkedRecip, Odd, Eq, NuUrOmegaCupOne, SqCupAdaptedFramePresentation
        axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
      GQ2.Dyadic.LSquare.MarkedFrame.sqMarkedForwardSupply_of_forwardGeneratorData
        carries 5  : MarkedRecip, Odd, SqCyclotomicForwardGeneratorData, Eq, Eq
        axioms     : std-3 + tateDualityAt, absGalQ2_localEulerCharacteristic
      GQ2.Dyadic.LSquare.NuKummer.sqMarkedForwardSupply_of_presentation
        carries 4  : MarkedRecip, Odd, Eq, SqCupAdaptedFramePresentation
        axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
      GQ2.Dyadic.LSquare.sqMarkedForwardSupply_oddDegree
        carries 4  : MarkedRecip, DyadicUnitFiltration, Odd, SqCupAdaptedFramePresentation
        axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
      GQ2.Dyadic.LSquare.sqMarkedForwardSupply_of_certificate
        carries 2  : MarkedRecip, MarkedCoreCertificateKTwoSq
        axioms     : std-3
      GQ2.Dyadic.LSquare.sqMarkedForwardSupply_of_presentingFrame
        carries 6  : MarkedRecip, Odd, SqCyclotomicFrattiniFrame, Eq, Eq, Eq
        axioms     : std-3 + tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
      GQ2.Dyadic.LSquare.sqMarkedForwardSupply_of_shiftedFrame
        carries 8  : MarkedRecip, Odd, SqCyclotomicFrattiniFrame, (function), (function), Eq, Eq, Eq
        axioms     : std-3 + tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
      GQ2.Dyadic.oddFrame_supply
        carries 4  : MarkedRecip, DyadicUnitFiltration, Eq, SqNuOrientedClearAtUnitPivot
        axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
      GQ2.Dyadic.oddFrame_supply_degreeOne
        carries 3  : MarkedRecip, DyadicUnitFiltration, Eq
        axioms     : std-3 + dyadicOrientation, hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
      GQ2.Dyadic.oddFrame_supply_of_families
        carries 6  : MarkedRecip, DyadicUnitFiltration, Eq, SqHandleMixFixesCore, (function), (function)
        axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
      GQ2.Dyadic.oddId_markedSupply_degreeOne
        carries 3  : MarkedRecip, DyadicUnitFiltration, Eq
        axioms     : std-3 + dyadicOrientation, hilbertSymbol_normCriterion_finiteDyadic, peripheralCyclotomicAction, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
      GQ2.Dyadic.oddId_markedSupply_of_presentation
        carries 4  : MarkedRecip, DyadicUnitFiltration, Eq, SqCupAdaptedFramePresentation
        axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
      GQ2.Dyadic.oddSeam_supply_of_presentingFrame
        carries 6  : MarkedRecip, Eq, SqCyclotomicFrattiniFrame, Eq, Eq, Eq
        axioms     : std-3 + tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
      GQ2.Dyadic.oddSeam_supply_of_relator
        carries 4  : MarkedRecip, DyadicUnitFiltration, Eq, SqCupAdaptedFrameRelator
        axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  seam = marked-core cert        EXISTS   GQ2.Dyadic.oddId_supply_iff_certificate
      carries 2  : MarkedRecip, Nat
      axioms     : std-3
  seam = one cup-adapted frame   EXISTS   GQ2.Dyadic.oddSeam_supply_iff_cupAdaptedFrame
      carries 2  : MarkedRecip, Eq
      axioms     : std-3 + tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  seam = the full marking        EXISTS   GQ2.Dyadic.oddSeam_supply_iff_fullMarking
      carries 2  : MarkedRecip, Nat
      axioms     : std-3
  halved relator clause          producers: 0   [SqCupAdaptedFrameRelator]
  frame presentation clause      producers: 1   [SqCupAdaptedFramePresentation]
      GQ2.Dyadic.LSquare.sqCupAdaptedFramePresentation_of_relator
        carries 1  : SqCupAdaptedFrameRelator
        axioms     : std-3 + tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated
  model clearing clause          producers: 3   [SqNuOrientedClearAtUnitPivot]
      GQ2.Dyadic.SqCore.sqNuOrientedClearAtUnitPivot_of_families
        carries 3  : SqHandleMixFixesCore, (function), (function)
        axioms     : std-3
      GQ2.Dyadic.SqCore.sqNuOrientedClearAtUnitPivot_of_pivotMoves
        carries 2  : SqHandleMixFixesCore, (function)
        axioms     : std-3
      GQ2.Dyadic.oddFrame_clearAtUnitPivot_zero
        carries NOTHING            axioms: std-3 + dyadicOrientation, peripheralCyclotomicAction
  seam = clearing instance       EXISTS   GQ2.Dyadic.oddFrame_supply_iff_clearInstance
      carries 3  : MarkedRecip, ContinuousMulEquiv, (function)
      axioms     : std-3
  q-invariant of D_sq h          EXISTS   GQ2.Dyadic.oddSeam_demushkinQ_DSq
      carries 1  : Nat
      axioms     : std-3
  odd oriented equivalence       EXISTS   GQ2.Dyadic.LSquare.nonempty_orientedEquiv_oddDegree
      carries 2  : MarkedRecip, Odd
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic

## ASK BLOCK
  frozen: surviving Prop         EXISTS   GQ2.Dyadic.askCStageVanishing
      carries 4  : ProfiniteGrp, Nat, ProfiniteGrp, ContinuousMonoidHom
      axioms     : std-3
  frozen <-> stageVanishing      EXISTS   GQ2.Dyadic.askC_exactLifting_iff_stageVanishing
      carries 2  : Eq, le
      axioms     : std-3 + tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  corrected RN at G_K            EXISTS   GQ2.Dyadic.exactLiftingSemanticsRN_galK
      carries 1  : Eq
      axioms     : std-3 + tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated, absGalQ2_localEulerCharacteristic
  stokes at G_K                  EXISTS   GQ2.Dyadic.stokesDualityCertificate_galK
      carries 2  : IntermediateField, Eq
      axioms     : std-3 + tateDualityAt, absGalQ2_localEulerCharacteristic
  determinant at G_K             EXISTS   GQ2.Dyadic.affineDeterminant_galK
      carries 12 : IntermediateField, FieldParameters, Eq, Eq, Eq, (function), (function), ContinuousMonoidHom, Surjective, ContinuousMonoidHom, (function), (function)
      axioms     : std-3 + hilbertSymbol_normCriterion_finiteDyadic, relativeStiefelWhitney_dyadic, tateDualityAt, absGalQ2_localEulerCharacteristic
  scalar at G_K                  EXISTS   GQ2.Dyadic.scalarHilbert_galK
      carries 3  : IntermediateField, Eq, Eq
      axioms     : std-3 + tateDualityAt, absGalQ2_localEulerCharacteristic

## CAND BLOCK
  M0 a h                         EXISTS   GQ2.Dyadic.Instances.MCompactCore.mWordCertificate
      carries 13 : Nat, Nat, Nat, le, Ne, Even, ContinuousMonoidHom, Eq, (function), ExactLiftingSemantics, StokesDualityCertificate, ScalarHilbertCertificate, AffineDeterminantCertificate
      axioms     : std-3
  Mpc a r p q                    EXISTS   GQ2.Dyadic.Instances.MProcyclicCore.mpcWordCertificate
      carries 14 : Nat, Nat, Nat, Nat, le, Ne, Even, ContinuousMonoidHom, Eq, (function), ExactLiftingSemantics, StokesDualityCertificate, ScalarHilbertCertificate, AffineDeterminantCertificate
      axioms     : std-3
  N0 a h                         EXISTS   GQ2.Dyadic.SqrtNeg2.sqrtNegTwoWordCertificate
      carries 6  : Ne, Even, PilotHsimp, PilotStageSep, PilotStageZ, PilotDet
      axioms     : std-3
  Npc a r h q                    EXISTS   GQ2.Dyadic.genCertNpcWordCertificate
      carries 13 : Nat, Nat, Nat, Nat, Ne, Even, ContinuousMonoidHom, Eq, (function), ExactLiftingSemantics, StokesDualityCertificate, ScalarHilbertCertificate, AffineDeterminantCertificate
      axioms     : std-3
  L h                            EXISTS   GQ2.Dyadic.Instances.LRowCand.lCand_wordCertificateCanonical
      carries 8  : Nat, Nat, Ne, Even, ExactLiftingSemantics, StokesDualityCertificate, ScalarHilbertCertificate, AffineDeterminantCertificate
      axioms     : std-3

## REGISTRATION (visible to an `import GQ2` consumer)
  GQ2.Dyadic.GaussZ.FinalDK                                  registered
  GQ2.Dyadic.GeneralCertificates                             registered
  GQ2.Dyadic.Instances.AskCounting                           registered
  GQ2.Dyadic.Instances.Cores                                 registered
  GQ2.Dyadic.Instances.FieldSqrtFiveUnramified               registered
  GQ2.Dyadic.Instances.FieldUnimodularity                    registered
  GQ2.Dyadic.Instances.GammaLSqCupAdaptedFrameGeneration     registered
  GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteCubicNeutral registered
  GQ2.Dyadic.Instances.GammaLSylowPreimageMarkedFrame        registered
  GQ2.Dyadic.Instances.GammaLSylowPreimagePivotNu            registered
  GQ2.Dyadic.Instances.KAnalytic                             registered
  GQ2.Dyadic.Instances.KExactLiftingGalK                     registered
  GQ2.Dyadic.Instances.KSupply                               registered
  GQ2.Dyadic.Instances.LRowCand                              registered
  GQ2.Dyadic.Instances.MpcNormValues                         registered
  GQ2.Dyadic.Instances.MpcPivot                              registered
  GQ2.Dyadic.Instances.OddFrame                              registered
  GQ2.Dyadic.Instances.OddIdentification                     registered
  GQ2.Dyadic.Instances.OddSeam                               registered
  GQ2.Dyadic.Instances.SqrtNeg2                              registered
  GQ2.Dyadic.SqCore.PivotClimb                               registered

## OWNER ITEMS
  latest house note        docs/dyadic/w83-house-note.md
  numbered items in it     7
  status of each           UNVERIFIED (prose; not machine-checkable)

## THE A6 FREEZE (GQ2/Roe/)
  last commit touching it  4341a1a3 2026-08-10  drop the line numbers this batch invalidated in 18 cross-references
  house notes added since  11
  review rounds frozen     UNVERIFIED (the campaign counts from the A6
                           adoption wave, which is not recorded in git)

## WHAT THIS BOARD CANNOT SEE
  * whether a clause a row CARRIES is discharged somewhere else in the
    tree at the same instantiation: only the binder is machine-checked.
  * whether a producer's conclusion is at the row's CANONICAL marking;
    `GenAsmBranch` does not pin `nuP` (GeneralAssembly.lean, W82-PIVOT).
  * STRENGTH.  The carries column counts binders, and fewer binders is
    not a weaker hypothesis: sqNuOrientedClearAtUnitPivot_of_pivotMoves
    carries 2 against _of_families' 3, and is the STRONGER ask (the whole
    unit-determinant pivot family, against two one-parameter ones).
  * producers in modules no row imports.  A `prod` scan reads the
    ENVIRONMENT, so it sees exactly the modules the rows above pull in.
    A new module with a new producer is invisible until some row names a
    declaration in it.  This is the one way the board can be stale.
  * prose.  Every headline, table and inventory in the tree and in
    docs/dyadic/ is outside this tool and stales on its own.
```

## What the board cannot verify, and what fills the gaps

The board prints its own four blind spots.  Reading them against this round:

1. **Whether a carried clause is discharged elsewhere at the same instantiation.**  This is the
   whole of the ASK story and the board cannot see it: it shows `stokesDualityCertificate_galK`
   EXISTS and shows `KSupply.stokes` carried, and cannot connect them.  AB-0 is the human half of
   that check, and it is now written down in the file rather than in a note.
2. **Whether a branch datum is at the row's canonical marking.**  The board shows
   `mpcPiv_genAsmBranch_sqrtNegTen` carrying nothing, which is true and misleading:
   `GenAsmBranch` does not pin `nuP`, so that datum cannot serve `GenAsmRowResidual.cand`.  Wave
   82's §4 warning is load-bearing and is not machine-checkable here.
3. **Producers in unimported modules** (Ticket 1's limit 1).  This is exactly how the board went
   stale mid-round, and it went stale in the direction that matters: the seam.
4. **Prose.**  Every finding in this note is outside the tool.

Three further things the board does not say, which the round establishes:

* the **odd seam's cheapest producer is no longer frame-shaped**.  At `23041e0f` it was
  `oddSeam_supply_of_relator` over `SqCupAdaptedFrameRelator K`; at `db6fcedf` it is
  `oddFrame_supply` over `SqCore.SqNuOrientedClearAtUnitPivot h`, a statement about `D_sq(h)`
  with no field, bundle, frame or cup form in it.  The board shows both, with identical binder
  counts and identical censuses; which is *cheaper* is a judgement it does not make;
* the **`√−10` pivot is unmoved**: `MpcPivShift` has zero producers, and wave 82 showed no
  image-level argument can decide it;
* the **even route is unchanged since wave 74**, and nothing this round touched it.

## ⚠ The base advanced a SECOND time, after the board was measured

At commit time `dyadic` is at **`9f05fb98`** (W83-RECORDS: `Instances/CanonicalRecords.lean`
plus edits to `GeneralAssembly.lean`, `FieldUnimodularity.lean`, `MpcCertificate.lean`,
`MpcPivot.lean`, `OddIdentification.lean`).  **The board above is as of `db6fcedf` and does not
include it.**  This lane did not merge it: the shared olean cache has not advanced past
`db6fcedf`, five of the touched modules are central, and regenerating a central module without
its dependents is precisely the false-clean trap `mirror.sh`'s header documents.  Running `lake`
is out of protocol.

So the delta below is **read, not elaborated**, and is marked as such.  From
`docs/dyadic/w83-records-note.md` and that lane's diff:

* **FROZEN ROWS: substance unchanged.**  Ticket A of that lane strengthened five branch-producer
  existentials to carry the marking, and its §1 records that *every re-export keeps its old
  statement*, the extra conjunct being dropped at the call site.  The five names this board
  prints are re-exports, so their binder lists and censuses should re-measure identically.
  **Unverified here.**
* **Owner item 5 narrows, and W82-HOUSE's census of it was wrong.**  That item's site count was
  recorded as four; it is **eight**, verified against the Lean by W83-RECORDS §0.  Five are now
  taken, sites 6 and 7 (the free-`h` even producers `genAsm_branch_of_evenN` / `_evenM`) remain,
  and site 8 (`mpcPiv_genAsmBranch_sqrtNegTen`) **cannot** be taken, because its datum is built
  at the transported marking and no comparison with `mpcNu 2 1 1` exists at this tree.  Item 5
  below is stated in its wave-82 form because that is the form this lane measured; read it
  against W83-RECORDS.
* **The ASK block per tied row drops from three to two.**  `canRec_rowResidual_*` assembles
  `determinant` through `mpcRow_genAsmRowResidual_of_counting` out of `affineDeterminant_galK`,
  so it is no longer a binder.  That closes, at the general record, the wiring W79-HOUSE and
  W82-HOUSE both called a wiring job.  The board's ASK section does not know this.
* **CAND is instantiated at the four tied quadratic rows**, with a uniform four-clause residue,
  which extends S3's corrected reading from the `CorePresentation`-backed rows to the tied set.
  Note that the `√−10` row is not among the four, for the site-8 reason.
* **Two of my ticket-3(f) sites are handed back**: W83-RECORDS §3 item 2 records that
  `GeneralAssembly.lean`'s constructor-table `L h` cell and
  `oddId_candidate_equiv_galK_of_supply`'s docstring still carry their wave-82 text under the
  W82-HOUSE annotation, i.e. annotated but not rewritten.  Rewriting them is the AB-0 treatment
  applied to those two sites; it belongs to whoever holds `GeneralAssembly.lean` next, and this
  lane could not do it without merging a tree it cannot elaborate.

**The fix is one command.**  `bash scripts/scoreboard.sh` once the shared cache advances past
`9f05fb98` reprints every row above from the tree.  That is what the tool is for, and this
subsection is the last hand-written status delta this note contains.

## Owner items: seven standing, one closed and one opened

**AB-0 comes off the list**, closed this round; it was comment-only all along.  One new item
opens, so the count is unchanged at seven.  The list is numbered so that the scoreboard's
`OWNER ITEMS` count, which greps this section, agrees with this sentence.

1. **ASK restatement.**  Restate the row records against `ExactLiftingSemanticsRN`, or prove
   `askCStageVanishing`.  Statement change.  The board shows the RN bundle carrying only `hdeg`.
2. **Pilot spelling** (`w74-critical-path.md` §1.5).  Unchanged.
3. **The A6 freeze** (`GQ2/Roe/*`): **ten** review rounds without motion.  Nothing in this lane
   touched `GQ2/Roe/` or `GQ2.lean`: `git diff db6fcedf HEAD` on both paths is empty, which is
   the honest form of the check after the mid-round merge (`git diff 23041e0f HEAD` shows one
   `GQ2.lean` line, W83-FRAME's registration, which arrived through that merge).  The board
   prints this UNVERIFIED with the checkable substitute beside it (last commit `4341a1a3`,
   2026-08-10, comment-only; eleven house notes added since), because the count runs from the A6
   adoption wave, which is not recorded in git.
4. **Line length**: re-measured, **706** lines over 100 codepoints in **250** files.  Policy call
   still owed.
5. **The forgotten marking**: the existential branch producers return `∃ G, G.pres = …` and drop
   `G.nuP`, while `cand` is stated at `G.nuP`.  Statement change.
6. **`askCStageVanishing`: fact or wrong ask?**  Unchanged, and still the sharpest open item on
   the arithmetic side.
7. **NEW: the `hclear` re-cut** (S5).  `GammaLOddDegreeBridgePivot`'s consumers take `hclear`
   **and** `hsupply`; since `oddFrame_supply` derives the supply from the clearing, they should
   take `hclear` alone.  Statement change, handed over by `w83-frame-note.md` item 3.

---

# What this lane did not do

No statement was changed anywhere; every tree edit is a comment.  I did not touch `GQ2.lean`,
`GQ2/Roe/*`, or the sibling-owned `Instances/OddFrame.lean`, `Instances/MpcOrbit.lean`,
`Instances/CanonicalRecords.lean` (`OddFrame.lean` arrived through the merge and was read, not
edited).  I did not wire the scoreboard into any gate, and I did not attempt the model clearing,
`MpcPivShift`, or `askCStageVanishing`.  The eight wiring and restatement items above are all
statement changes and are reported, not made.
