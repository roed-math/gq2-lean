# W87-HOUSE lane note (watch round 24)

Base `1541635f`, branch `claude/w87-house`. Verification is `scripts/mirror.sh` and
`scripts/scoreboard.sh` only; no `lake` command was run in this lane.

Round 24 watches the wave-86 landings: `SqCore/GradedRowLadder.lean`,
`Instances/MpcLadder.lean`, `Instances/WordPhase.lean`, the four wave-86 merges, the
annotation commits `aa31e767` and `1d286428`, and the notes `w86-house-note.md`,
`w86-ladder4-note.md`, `w86-ladder5-note.md`, `w86-phase-note.md`.

---

## 0 The baseline board (T3)

`scripts/scoreboard.sh` at `1541635f`, FROZEN ROWS block, elaborated this round. This is the
wave-87 baseline; a later wave that wants to know whether a row moved compares against it and
does not read a table anyone maintained by hand.

```
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
  v-10 residue = word prob       EXISTS   GQ2.Dyadic.Instances.MpcOrb.mpcOrb_shift_iff_marking
      carries NOTHING (no explicit binder)
      axioms     : std-3
  v-10 finite-class route        EXISTS   GQ2.Dyadic.Instances.MpcWord.mpcWord_shift_of_forall_class_four
      carries 1  : (function)
      axioms     : std-3
  v-10 residual move             producers: 11   [MpcPivShift]
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_bracket_supply
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_forall_class
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_forall_class_five
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_full_supply
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_word
        carries 14 : carrier, carrier, carrier, carrier, mem, mem, mem, mem, Eq, Eq, Eq, Eq, (function), Eq
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_wide_shift_of_forall_class_five
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcLad.mpcLad_shift_of_exists_supply
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcOrb.mpcOrb_shift_of_marking
        carries 7  : Eq, Eq, Eq, Eq, Eq, Eq, (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcWord.mpcWord_shift_of_forall_class
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcWord.mpcWord_shift_of_forall_class_four
        carries 1  : (function)
        axioms     : std-3
      GQ2.Dyadic.Instances.MpcWord.mpcWord_shift_of_word
        carries 14 : carrier, carrier, carrier, carrier, mem, mem, mem, mem, Eq, Eq, Eq, Eq, (function), Eq
        axioms     : std-3
```

Two readings worth carrying:

* `MpcPivShift` now shows **11** producers. Wave 85's board printed 1 against a true 4 because
  the probe imported only the rows' modules; wave 86 put the probe on the umbrella and wave 86's
  own `MpcLad.mpcLad_shift_of_exists_supply` is visible here without a row naming it. The
  structural fix is doing what it was built for.
* REGISTRATION at this base reports **966** modules on disk and exactly one outside the
  umbrella, `GQ2.AxiomLedger`, which imports `GQ2` itself and so cannot be registered. The two
  wave-86 modules that W86-HOUSE flagged are in, landed by `ed382b2e`.

---

## 1 Findings, ranked

Every finding below was re-verified at this tree, not read off a note. Fixes are comment and
prose only; every module edited was re-elaborated with `scripts/mirror.sh check` and came back
`OK` with its pins unchanged.

### HIGH

**1.1 The commit that removed wave 86's inversion inspected the fifth site and cleared it.**
`1d286428`'s own message says: "The `mpcLad_five_empty_of_no_supply` docstring already said
'ansatz' and stands." That is true of the body and false of the headline, which read **"The
class-five refutation, spelled out"** with no qualifier, and it says nothing about the citation,
which is where the damage was. The docstring attributed its claim to `mpcWord_shift_of_forall_class`,
which at `MpcWord.lean:390` is `(∀ k, (mpcWordSet k).Nonempty) → MpcPivShift 2`. Its
contrapositive gives emptiness FROM a refutation, never a refutation from emptiness, so it
supports neither the ansatz reading nor the shift reading. W86-HOUSE counted four sites; this is
a fifth, 470 lines below one that was scoped, in the same file the scoping commit edited.

FIXED, comment-only. The headline now says ANSATZ, the citation is dropped, and the block records
that the ansatz reading needs no citation at all (a quadruple solving the identity lies in every
rung, since every `twoCentralSeries` term contains `1`).

**1.2 `GradedRowLadder`'s lead sentence claims the first open rung; a quarter of it landed.**
Line 15 read "This module climbs the first open rung and equips every higher one." The only
rung-4 nonemptiness theorem is `gLad_nonempty_four_quarter`, binding `4 ∣ A - 1` and `4 ∣ B`.
The reduction two lines above is stated on the unit locus `IsUnit (A - c0 B)`, and the quarter
locus is a proper sub-locus of it. The module's own "What does not land" says "The rungs off the
quarter locus", and the lane note says "the first quarter of rung 4 as a theorem". The lead
sentence is the one a reader keeps. FIXED in place.

**1.3 The owner memo's wave-86 block deleted the wave-85 heading, and its count does not follow
from its own arithmetic.** `1541635f` wrote the block by REPLACING `## Status at wave 85
(2026-08-15)` rather than inserting above it, so wave 85's record was orphaned inside wave 86's
and the section read as asserting "Nine items await you" twice, with A6 at thirteen rounds and at
twelve. Separately, nine is the correct count at the tree but not by the route given: from wave
84's nine, discharging one and opening two is ten. The unrecorded step is that W86-HOUSE opened a
TENTH item, "register the two wave-86 modules", and `ed382b2e` discharged it in the same wave.
The block also puts the ansatz-exhaustiveness question in the vacated slot, which W86-HOUSE never
opened as an owner item. FIXED: heading restored, no block text altered, dated annotation added.
The count itself is the owner's and was left at nine.

**1.4 The scoreboard's OWNER-ITEMS row read the wrong file, on a contract most house notes do not
meet, and reported the miss as a number.** It matched `^#+ +Owner items` against the latest house
note alone. Six of the ten notes w77 to w86 do not meet that shape: w77 to w80 use "### N.M  The
owner items", w83 "## OWNER ITEMS", w84 "## 4  Owner items: nine standing", and w85 has no such
heading at all. All score zero, and the board printed `numbered items in it  0` for waves 84 and
85 with no reader querying it. At wave 86 it matched and printed **10** against the memo's nine.
FIXED on the board side (T2): the row now reads the owner memo as the authority and the house note
as the frozen lane artifact, prints the count each asserts, prints AGREE or DISAGREE, and prints
NOT FOUND (with the heading it did match) instead of a zero. The contract for both files is
recorded in the script header with the history that motivated it. Verified: the row now prints 9
from the memo.

**1.5 `WordPhase` says the two rows take the same statement; they take two instances.**
`wPh_candidate_equiv_galK_sqrtNegTwo_branchFree`'s docstring said its binder "is **literally the
same statement** as the one the `√5` row now takes". The two `Sdet` binders instantiate
`wPhBranchFreeSupply` at different `q` (`qOf KSqrtNegTwo FF` against `qOf KSqrtFive FF`),
different `nuP` (`nNuZtwo 2 0` on `DN 2 0` against `fieldId_mNuZtwo 2 0 _` on `DM 2 0`) and
different words (`nCompactW 2 0` against `mCompactW 2 0`). The consequence is an endgame-count
consequence: discharging one does not discharge the other, so this is two obligations of one
shape, not one obligation. §5's own header states it correctly; §7's header ("one `Prop`, shared
by both") and `wPh_wordPhaseSupplyN_of_branchFree` ("at the same statement") carry the same
escalation. FIXED at the site, with the other two named.

### MEDIUM

**1.6 `GradedRowLadder`'s engine is credited to a module outside its own import cone, while an
in-cone equivalent predates it by seven waves.** Three sites credit the wave-85 `mpcBld_incr_*`
pattern of `Instances/MpcBuild.lean`. That module is not in the cone (737 modules; computed by
transitive closure of the `import` lines). `GradedExtraction.gExt_dress_move`, W79-EXTRACT, IS in
the cone and reads

    sqRelWord (fun i => m i * c i) = sqRelWord m * gExtMove k m c    under 2 ≤ k

against `gLad_relWord_incr`'s `sqRelWord (fun i => m i * ε i) = sqRelWord m * gLadCost m ε` under
`2 ≤ j`: the same statement on the same relator, with `gExtMove` for `gLadCost`, and the two costs
agree factor for factor, differing only as `List.ofFn f` against `(List.finRange n).map f`.
`gLadCost` is the more general definition (an arbitrary group rather than `levelQuot`), but
`gLad_relWord_incr` instantiates it exactly where `gExt_dress_move` already lives. The prose half
is FIXED. Whether to deduplicate is a statement question and is FLAGGED, not taken.

**1.7 "and nothing else moves" is a converse `GradedRowLadder` does not prove**, claimed twice
(the chain item and `gLad_step`'s docstring). `gLad_step` is one implication. The converse, that
every rung-`(j+2)` solution is `c · ε` for a rung-`(j+1)` solution and `ε ∈ λ_j`, is what makes
the reduction exhaustive, and for two carrier solutions only `c'c⁻¹ ∈ λ₂` is known. Worth more
than a flag: W86-LADDER5 settled precisely this converse for the `M6` ladder in the same wave, out
of antitonicity plus the identity move, and `GradedRowMove.gRowSet_antitone` is already in this
cone. What is missing is the identity-move computation `gLadCost m (fun _ => 1) = 1` and the
packaging. FIXED as an annotation carrying that route; the statement is not mine.

**1.8 `WordPhase` repeats a headline the campaign corrected one module over in the same wave.**
`wPh_nCand_stokes`'s "**unconditionally at `2 ≤ α`**" is word for word
`RecordBlocks.recBl_mCand_stokes`'s, which carries a W86-HOUSE block correcting it. The statement
binds `2 ≤ α`, `q ≠ 0` and `Even q`, and `NCompact.uniformPushedHsimp` binds `Even q` as well (the
proof passes `hqe` to it). The `N` twin landed the same wave without the annotation. FIXED by
carrying the correction across.

**1.9 One finding, two as-of hashes, one of them impossible to check out.** `MpcLadder`'s scope
block was stamped "as of `f0de6ad5`". `git cat-file -e f0de6ad5:GQ2/Dyadic/Instances/MpcLadder.lean`
fails: the file is created at `d18f840e`. The block was written by `1d286428` after the house lane
closed and carried that lane's own base hash onto a file the lane never saw; `MpcBuild.lean`
stamps the same finding `0a479c6e`, correctly. FIXED, with the cause recorded so the as-of
protocol survives the next post-close annotation.

**1.10 `WordPhase`'s header section map is wrong and stale in both directions.** The bullet headed
"§3, the word-phase supply itself" describes content that is not in §3 (which is the `ℚ₂(√−2)`
row); the phase is §4, the reduction §5, the named gap §6. The same bullet says §3 "records what
the even-degree wall analysis needs and where the tree stops short of it", while the module builds
the phase and reduces both compact supplies to one residual. FIXED.

**1.11 `GradedRowLadder` §7 states an iff with one direction proved.** "the first rung the carrier
was built for opens **exactly where** the mod-4 data of `(A, B)` is trivial." Only
`gLad_defect_bare_quarter` is proved; nothing shows the defect nontrivial or rung 4 unsolvable off
the quarter locus, and the lane note says the rungs off it are neither discharged nor refuted.
FIXED.

**1.12 `wPh_branchFree_of_phaseModel` undercounts its own input.** Its docstring says the Gauss
value's "two hypotheses" are the `DescData` fields `hquad` and `hns`;
`wPh_compactWallHandlePhase_gaussSum_standardRam` binds `hq`, `hns` and `hcard`, and the proof
supplies `hcard` from the enrichment's card equation, not from `DescData`. §6's header gets it
right. FIXED.

**1.13 `WordPhase` §4 has a dependency backwards.** "This is what makes `gaussUnram = gaussRam`
true on the nose at even degree" credits the equality to the head being split with Arf invariant
`0`. `wPh_gaussUnram_eq_gaussRam_of_even` is `show (-1)^n * 2^(n*m) = 2^(n*m)` closed by
`(-1)^even = 1`: it names no form, no Arf and no `plusFormD`, and holds for every even `n` and
every `m`. The Arf-`0` structure is why the endpoint FORM attains that value with no Arf
hypothesis, a different theorem. FIXED.

### LOW

**1.14** `GradedRowLadder` elides two binders in prose that reads unconditional: `2 ≤ j`, carried
by `gLad_incr_pair`, `gLad_incr_handle`, `gLad_sqWord_incr`, `gLad_relWord_incr` and `gLad_step`
but genuinely absent from `gLad_incr_s`, `gLad_incr_x`, `gLad_incr_y`, while "uniform in the
class" treats all eight alike; and `gLad_nonempty_four_of_kill`'s `2 ∣ A - 1 - B`, which is free
on the unit locus by `GradedRowMove.gRow_even_of_unit`. Both recorded.

**1.15** `WordPhase`'s axiom audit does not close: "22 std-3 ... and `wPh_even_two_mul_add_two`
pins `propext` alone" plus "4 with campaign axioms" is 26 only if the `propext`-only declaration
sits inside the 22. Elaborated here the split is **21 std-3, one `propext` alone, four with
campaign axioms**. Recorded. Everything else in that audit is exact, including the five-versus-six
campaign-axiom gap between the rows.

**1.16** `GradedRowLadder`'s "Every declaration prints std-3 or a subset" overshoots by two: the
unpinned names are the `private` helpers `gLad_listProd_succ` and `gLad_handleWord_succ`, correctly
excluded from the pin block. Recorded as "every PUBLIC declaration".

**1.17** `gLad_clearing`, in "What does not land", is written as a backticked declaration name and
resolves to nothing in the tree. Honest in intent (it names what the lane did not build) but it
reads as a citation. Recorded.

**1.18 FLAGGED, not fixed (statement change).** `MpcLadder.mpcLad_mem_of_supply` concludes
`∃ q ∈ mpcWordSet (j + 2), True`, discarding the explicit solution its proof builds through
`mpcBld_step`. Nothing false is claimed and the witness is recoverable from `mpcBld_step`
directly, but a ladder-climbing consumer reading only `MpcLadder` cannot get it.

**1.19 FLAGGED, no fix needed.** `MpcLadder.mpcLad_reach_base_indep`'s headline is the set claim
("The reachable set does not move along the orbit") while the statement is the pointwise one, an
equality of single increments. The set equality follows at once, since the theorem's hypotheses
are weaker than `MpcLadMove`'s, and `mpcLad_defect_orbit`'s docstring uses the set reading.

---

## 2 Checked and clean

Recorded so the next round does not redo it. All elaborated or computed at `1541635f`.

* **The three merge messages' line counts are exact**: `GradedRowLadder.lean` 1227 at `57354d40`,
  `MpcLadder.lean` 773 at `0a479c6e`, `WordPhase.lean` 1033 at `70af2cf2`.
* **Their declaration counts are exact**, read as public declarations: gLad 57 (plus 2 `private`),
  mpcLad 49 (plus 1 `private`), wPh 26. **Pins are complete at all three**: one `#print axioms`
  per public declaration, no pin naming a declaration that is not there, no public declaration
  without a pin, `private` helpers correctly excluded.
* **The axiom claims hold.** gLad: every pin std-3 or a subset (four print `[propext]` alone, one
  prints no axioms). wPh: four row statements on campaign axioms, and the `√−2` row costs five
  campaign axioms where `√5` costs six, exactly as claimed.
* `gLad_clearing` indeed did not land, as `57354d40` says.
* `aa31e767`'s citation `Certificates/N0.lean:1067` points exactly at
  `nCompact_handle_form_gaussSum`.
* **The ansatz-scoping sweep found no remaining site reading rung emptiness as refuting
  `MpcPivShift 2` itself**, beyond the fifth site at 1.1. `MpcBuild.lean:900` and `:960` are both
  annotated in place; `MpcBuild.lean:858` states the scope correctly on its own; `MpcBuild.lean:50`,
  `MpcOrbit.lean:55`, `MpcPivot.lean:83`, `MpcWord.lean:55` and `MpcLadder.lean:44` all say only
  "neither proved nor refuted", which is right.
* **The em-dash scrub was done.** Zero U+2014 and zero U+2013 across the three modules and the
  four `w86-*` notes, and no ASCII `--` used as a prose dash (all 164 occurrences are `/--`
  openers, `---` rules, table separators, or a `git` flag inside backticks). The 16 U+2212 are
  mathematical minus signs inside field names, which is house convention.
* **No wiki-links.** The twelve `[[` / `]]` occurrences are all Lean nested brackets or commutator
  notation inside backticks.
* **No stray artifacts** on the three modules or the four notes: no TODO/FIXME/XXX/WIP/TBD, no
  unbalanced `**` or backticks at paragraph scope, no unclosed docstring, no doubled words in
  prose, no literal `\n`, no trailing whitespace, no mojibake or U+FFFD, no CRLF, no BOM.
* **Registration is clean**: 966 modules on disk under `GQ2/`, one outside `import GQ2`, and that
  one is `GQ2.AxiomLedger`, which imports `GQ2` itself.
* **`MpcPivShift` shows 11 producers here against `6f9e2f3f`'s "true 10".** Not a discrepancy: the
  eleventh is `MpcLad.mpcLad_shift_of_exists_supply`, invisible until `ed382b2e` registered
  `MpcLadder`. The registration item paying off, on the board, without a row naming it.

---

## 3 The line-length record (T4, owner item 4)

Measured in **codepoints**, not bytes, at `1541635f`:

| module | lines | over 100 | max |
|---|---|---|---|
| `SqCore/GradedRowLadder.lean` | 1227 | **0** | 95 |
| `Instances/MpcLadder.lean` | 781 | **0** | 100 |
| `Instances/WordPhase.lean` | 1033 | **7** | 128 |

`WordPhase`'s seven are lines 48, 50, 51, 52, 512 and 718, all markdown table rows inside `/-!`
module docs where wrapping breaks the table, and line 388, which is ordinary docstring prose and
is the only one wrappable without loss. `MpcLadder` touches exactly 100 and never exceeds it.

**A measurement warning for whoever takes item 4.** A byte-based count is useless on this tree: my
own first pass with `awk 'length>100'` reported 6, 14 and 18 over-100 lines for these three
modules against the true 0, 0 and 7, because the prose is dense in Unicode. Wave 83's standing
figure of "707 lines over 100" should be re-measured in codepoints before the policy is decided,
or the policy will be adopted against an inflated number.

> **[W88-HOUSE, as of `ad8c2b62`: the first half of this paragraph is right and the inference
> about wave 83 is wrong.]**  The `awk` observation is real and reproduces.  But 707 was
> already a codepoint figure: `docs/dyadic/w82-house-note.md` S5 states it as "Counting
> codepoints, `GQ2/` carries 707 such lines in 250 files", and raised it precisely to correct
> wave 81's claim that the corpus had lines over 100 bytes but none over 100 codepoints.
> Re-measuring wave 83's own base `db6fcedf` gives 707 over 100 codepoints in 251 files
> against 9283 over 100 BYTES in 687 files, so the standing figure cannot have been a byte
> count: a byte count of this tree has never been within an order of magnitude of 707.  The
> number was not inflated and the policy was never at risk from it.  Re-measured tree-wide at
> `ad8c2b62`: 720 in 254 files; method and per-module distribution in
> `docs/dyadic/w88-house-note.md` S2, memo corrected at its wave-87 block.

Nothing was rewrapped. The item is "record-or-adopt" and adopting is the owner's call, not a
lane's.

---

## 4 What this lane did not do

No statement changed anywhere in `GQ2/`; every tree edit is a comment. `GQ2.lean` and `GQ2/Roe/*`
untouched, checked. The sibling-owned paths `SqCore/GradedRowResidue.lean`,
`Instances/WordPhaseModel.lean` and `Instances/MpcFive.lean` do not exist at this tree and were
neither created nor touched. No `lake` command was run: verification is `scripts/mirror.sh check`
on the three modules edited, plus `scripts/scoreboard.sh` twice (at the base and after the T2
fix). `MpcPivShift 2`, `askCStageVanishing`, the model moves and the ansatz-exhaustiveness question
were not attempted. The one behaviour change is `scripts/scoreboard.sh`'s OWNER ITEMS section.

---

## Owner items

**Nine standing**, matching the wave-86 memo block: items 1 to 9 of `docs/dyadic/w86-house-note.md`,
that note's item 10 having been discharged by `ed382b2e`. None is takeable by a comment-only lane;
all are statement changes or policy calls. Nothing was opened or discharged by this lane.

1. **ASK restatement.** Restate the row records against `ExactLiftingSemanticsRN`, or prove
   `askCStageVanishing`. Unchanged.
2. **Pilot spelling.** Unchanged. Consumer list at W85-HOUSE §2.3.
3. **The A6 freeze** (`GQ2/Roe/*`): **fourteen** review rounds without motion. `git diff 1541635f
   HEAD` on `GQ2/Roe/` and on `GQ2.lean` is empty for this lane, checked. The board's machine
   substitute at this base: last commit `4341a1a3`, 2026-08-10, comment-only; 16 house notes added
   since.
4. **Line length.** Policy call still owed, and now measured for the wave-86 modules at §3 above,
   with a warning that the campaign's standing figure was taken in bytes.
5. **The forgotten marking.** Two sites, `genAsm_branch_of_evenN` and `genAsm_branch_of_evenM`.
   Unchanged.
6. **`askCStageVanishing`: fact or wrong ask?** Unchanged, and still the sharpest open item on the
   arithmetic side.
7. **The `hclear` re-cut.** `GammaLOddDegreeBridgePivot`'s consumers should take `hclear` alone.
   Unchanged.
8. **The two-idiom split on the `L` row.** A design question. Unchanged.
9. **Weaken `mpcBld_shift_of_bracket_supply`'s hypothesis** to the per-solution form. Verified
   against the Lean this round: the binder is `∀ j, 3 ≤ j → ∀ g ∈ twoCentralSeries (DM 2 0) (j+1),
   ...`, so it does quantify over every element of the layer, and the proof consumes it only at the
   defect (`H j _ _ hp5`). The memo's description of this item is accurate. As of `0a479c6e` the
   better disposition may still be to deprecate it in favour of
   `MpcLadder.mpcLad_shift_of_exists_supply`.

**One owner call this lane surfaced and did not take.** The wave-86 memo block lists the
ansatz-exhaustiveness question as one of the two items opened that wave, in the slot vacated by the
discharged registration item; W86-HOUSE did not open it as an owner item, and its own "not opened
as owner items" list does not name it. Whether it joins the list as a tenth is the owner's to
decide. Two facts for that decision, both checked here: it has **no statement anywhere in the
tree** (the only occurrences of the question are prose, at `MpcBuild.lean:974`,
`MpcLadder.lean:247` and `MpcLadder.lean:728`), so it cannot be actioned as a statement change the
way item 9 can; and it is exactly the distance between "the ansatz is refuted" and "`MpcPivShift 2`
is refuted", which is now the tree's only negative route.

**Recorded for a lane that wants it, not opened as owner items.** The `gExt_dress_move` versus
`gLad_relWord_incr` duplication (§1.6); the row-ladder converse that would make `gLad_step` an iff,
with its route (§1.7); and `mpcLad_mem_of_supply`'s discarded witness (§1.18).
