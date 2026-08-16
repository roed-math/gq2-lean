# W88-HOUSE lane note (watch round 25)

Base `ad8c2b62`, branch `claude/w88-house`. Verification is `scripts/mirror.sh` and
`scripts/scoreboard.sh` only; no `lake` command was run in this lane.

Round 25 watches the wave-87 landings: `SqCore/GradedRowResidue.lean`,
`Instances/MpcFive.lean`, `Instances/WordPhaseModel.lean`, the four wave-87 merges
(`f56465a5`, `55c9173f`, `e92cac88`, `fa8b66c4`), the orchestrator annotation commits
`7bba7aca`, `7a36073c`, `fc2dc985`, and the notes `w87-block-note.md`, `w87-five-note.md`,
`w87-house-note.md`, `w87-normal-note.md`.

Staleness discipline: every finding below was re-checked against this lane's own base
`ad8c2b62` before it was written down, and every citation carries an as-of hash. Where a
finding is about a count or a measurement it was re-derived, not read off a note; the two
HIGH findings are both cases where a previous round read a note instead.

---

## 0 The baseline board (T3)

`scripts/scoreboard.sh` at `ad8c2b62`, FROZEN ROWS block, elaborated this round. This is the
wave-88 baseline; a later wave that wants to know whether a row moved compares against it and
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
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_bracket_supply       carries 1 : (function)   std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_forall_class         carries 1 : (function)   std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_forall_class_five    carries 1 : (function)   std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_full_supply          carries 1 : (function)   std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_shift_of_word                 carries 14               std-3
      GQ2.Dyadic.Instances.MpcBld.mpcBld_wide_shift_of_forall_class_five  carries 1 : (function)   std-3
      GQ2.Dyadic.Instances.MpcLad.mpcLad_shift_of_exists_supply        carries 1 : (function)   std-3
      GQ2.Dyadic.Instances.MpcOrb.mpcOrb_shift_of_marking              carries 7                std-3
      GQ2.Dyadic.Instances.MpcWord.mpcWord_shift_of_forall_class       carries 1 : (function)   std-3
      GQ2.Dyadic.Instances.MpcWord.mpcWord_shift_of_forall_class_four  carries 1 : (function)   std-3
      GQ2.Dyadic.Instances.MpcWord.mpcWord_shift_of_word               carries 14               std-3
```

The producer rows are abridged to one line each; the full block is what
`bash scripts/scoreboard.sh` prints. Two things to read off it.

* **No row moved this wave**, and none was expected to: wave 87 climbed two ladders and
  landed one row instantiation, none of which is a frozen-row producer.
* **`MpcPivShift` still has 11 producers, the same 11 as at `1541635f`.** `MpcFive.lean` adds
  none, correctly: `mpcFv_nonempty_five` is a statement about a solution set, not a shift
  producer. This is the machine-side confirmation of the honesty split in that lane's note.

Registration is clean: 969 modules on disk under `GQ2/`, all inside `import GQ2`'s closure
except `GQ2.AxiomLedger`, which imports `GQ2` and would cycle. `8e988543` registered all
three wave-87 modules, so wave 86's invisible-module failure did not recur.

---

## 1 Watch round 25, findings ranked (T1)

### HIGH 1. `GradedRowResidue.lean` says the two ladders are level

They are one rung apart, and were already when it merged.

Three sites, all asserting the same thing:

* `GQ2/Dyadic/SqCore/GradedRowResidue.lean:44` (module docstring): "the residual of the row
  ladder starts at class FIVE, the same threshold as the M6 ladder after
  `mpcBld_nonempty_four`".
* `GQ2/Dyadic/SqCore/GradedRowResidue.lean:1409` (`gRsd_nonempty_four`'s docstring): "the same
  threshold as the M6 ladder".
* `docs/dyadic/w87-block-note.md:12`: "level with the M6 ladder after `mpcBld_nonempty_four`".

`mpcBld_nonempty_four` stopped being the M6 ladder's frontier earlier in the same wave.
W87-FIVE merged at `55c9173f`, W87-BLOCK at `f56465a5`, and
`Instances/MpcFive.lean`'s `mpcFv_nonempty_five : (mpcWordSet 5).Nonempty` puts the M6
residue at class SIX. So the reading is five against six, one rung apart with M6 ahead, and
the module was stale at its own landing.

Two things make this worth a HIGH rather than a note. First, it is the same failure
`GradedRowMove.lean:67` already carries a W86-HOUSE annotation for, one wave earlier and
with the sign reversed: that time the row ladder was behind, this time it is ahead, and both
times the module asserted equality against a sibling that had merged first. Second, the
orchestrator merged `55c9173f` with the headline "the M6 residue starts at class six" and
then merged `f56465a5` whose module says otherwise, so the contradiction is between two
merge messages of the same wave.

**Fixed** at all three sites by dated W88-HOUSE annotation (`7f1bb919`). The annotations also
record the asymmetry the equality was hiding, which is the part a consumer would act on: this
lane's `k >= 5` chain is a PRODUCER (`gRsd_pair_of_forall_class_five` and its two siblings),
while the M6 side has **no class-six producer at all**; its sharpest is still
`mpcBld_shift_of_forall_class_five`, so a consumer wanting the `k >= 6` residue must compose
that with `mpcFv_nonempty_five` by hand. "One rung ahead" and "one rung better supplied" are
not the same statement and the tree only supports the first.

### HIGH 2. The memo's line-length premise is false (T2)

707 was a codepoint figure all along.

The memo's wave-87 block, `docs/dyadic/owner-items-2026-08-05.md:8`, says the wave-83 figure
"was measured in bytes and needs re-measuring in codepoints before the record-or-adopt policy
call". It was not measured in bytes. Provenance and arithmetic, both re-derived here:

* `docs/dyadic/w82-house-note.md:188` states it verbatim as "Counting codepoints, `GQ2/`
  carries **707** such lines in **250** files", and raised it precisely to correct wave 81's
  owner item 2, which had claimed the corpus has lines over 100 *bytes* but none over 100
  *codepoints*. The figure exists BECAUSE somebody counted codepoints.
* Re-measuring wave 83's own base `db6fcedf`: **707** lines over 100 codepoints in 251 files,
  against **9283** over 100 bytes in 687 files. The byte count of this tree has never been
  within an order of magnitude of 707, so the standing figure could not have been one.

The route to the error is worth recording because it is a clean instance of the discipline
this lane exists to enforce. W87-HOUSE ran `awk 'length>100'` over three modules, correctly
found it inflated 0/0/7 to 6/14/18, and generalized a real local observation into a
provenance claim about a tree-wide figure it did not re-derive. The orchestrator then copied
the inference into the memo as a fact. Nobody read `w82-house-note.md`, where the answer was
in the sentence that introduced the number.

**Fixed**: memo annotated at its wave-87 block with the correction, the honest number and the
method (`f81c92b5`); the w87-house note annotated at §3, the site the memo copied from
(`d9c1f189`). The item itself does not move: it is still record-or-adopt and still the
owner's.

### MEDIUM 3. Five wave-86 annotation sites have themselves gone one rung stale.

The W86-HOUSE annotations that fixed the previous round's class-status drift now carry the
previous round's numbers:

| site | says | now |
|---|---|---|
| `Instances/MpcWord.lean:409` (§7 prose) | M6 obstructs from class FIVE | class SIX |
| `Instances/MpcWord.lean:499` (`mpcWord_mem_three`) | class five | class SIX |
| `Instances/MpcWord.lean:556` (`mpcWord_shift_of_forall_class_four`) | `k >= 5` | `k >= 6` |
| `SqCore/GradedRowMove.lean:67` (module docstring) | row 4 against M6 five | five against six |
| `SqCore/GradedRowMove.lean:943` (`gRow_pair_of_forall_class_four`) | row 4, M6 5 | 5 vs 6 |

None of the five theorems is affected; in every case the theorem is exactly true and only the
superlative moved, which is what the wave-86 annotations themselves said about wave 85.
**Fixed** by a second dated annotation at each (`7f1bb919`) rather than by rewriting, which is
the campaign's convention and keeps the drift itself readable. The `MpcWord.lean:556`
annotation additionally records that the sharp producer did NOT move with the residue.

### MEDIUM 4. The memo's wave-87 block again omits the register-the-modules open-and-discharge.

W87-HOUSE's correction to the wave-86 block was that the block's stated arithmetic did not
reach its own count because it recorded neither the opening of a tenth item ("register the two
wave-86 modules") nor its same-wave discharge by `ed382b2e`. The wave-87 block repeats the
shape: `8e988543` registered the three wave-87 modules, discharging the identical item, and no
status block records that the item existed. The count is unaffected (nine, verified in S3), so
this is bookkeeping, not arithmetic. **Flagged, not fixed**: whether a same-wave
open-and-discharge should appear in the memo at all is an owner convention question, and it has
now cost two rounds of house time to re-derive. Recommend one sentence of convention either way.

### LOW 5. The module docstring's half locus drops a conjunct its theorem carries.

`GradedRowResidue.lean:31` writes the free locus as "the half locus `4 | A - 1 - B`". The
theorem, `gRsd_nonempty_four_half:1141`, binds `2 | B` **and** `4 | A - 1 - B`, and the merge
message `f56465a5` states it correctly as `2|B, 2|t`. The docstring sentence carries `2 | B`
in its own premise clause ("On the even locus `2 | B` the defect is `1` for `t` even, so...")
so a reader of the whole sentence is not misled; a reader who lifts the backticked condition
is. Left as written: the sentence is defensible and the fix is a rewrite of load-bearing prose
rather than an annotation. Recorded so a later reader does not re-derive it.

### LOW 6. "Half locus" and "quarter locus" are names, not fractions.

Parametrizing the unit locus by `(B mod 2, t mod 2)` with `A - 1 = B + 2t`, the four cases the
module splits on are equal in measure, and the free one is a QUARTER of the unit locus. Wave
86's "quarter locus" (`4 | A - 1`, `4 | B`) is an eighth. The relative claim at
`GradedRowResidue.lean:1140`, "the quarter-locus result of wave 86, doubled", is exact, and
the stress pin at `:1523` proves the containment. Only the absolute fractions the two names
suggest are wrong, and they are inherited names, not measurements. No action.

### LOW 7. The board's A6 row counts the in-flight wave's own house note.

`## THE A6 FREEZE` prints "house notes added since 17" at this base. Sixteen were added
between `4341a1a3` and `ad8c2b62`; the seventeenth is `w88-house-note.md`, created by this
lane before the board was run. Any house lane that runs the board mid-wave will see its own
note counted, so the machine substitute reads one high exactly when it is being read. Not
fixed: it is one line of the script and the board is a shared artifact, so it is flagged for a
lane with a script ticket rather than taken here.

### Checked and clean

Everything below was verified against the tree, not read off a note.

* **Pin honesty splits, all three wave-87 modules, elaborated via `mirror.sh check`.**
  `GradedRowResidue.lean`: 101 `#print axioms`, 101 records, and 101 is exactly the count of
  PUBLIC declarations (116 top-level, of which 5 are `example` and 15 are `private`; every
  public one is pinned and no private one is). 99 print std-3; the two §9b seam composites
  print std-3 plus exactly the four census members §11 names
  (`hilbertSymbol_normCriterion_finiteDyadic`, `tateDualityAt`,
  `absGalQ2_isTopologicallyFinitelyGenerated`, `absGalQ2_localEulerCharacteristic`), with
  `localReciprocity` and `markedRecipAt` binders. The claim "no census axiom enters the rung-4
  decision anywhere" holds. `MpcFive.lean`: 49 pins, 49 records, 48 std-3 and
  `mpcFv_commP_self` on `propext` alone, matching its §7 prose word for word.
  `WordPhaseModel.lean`: 17 pins, 15 std-3 and 2 on the row's six-axiom set, matching merge
  `fa8b66c4`'s "15 std-3, 2 on the row's existing six-axiom set" exactly. Three modules, three
  exact splits; this is the cleanest pin round the house has audited.
* **`gRsd_pivotExp_congr`'s arithmetic.** Statement is `(4 : Z_2) | sqPivotExp + 1`, which is
  `c_0 = 3 mod 4` as both docstrings say. The proof is the route the prose describes: oddness
  plus the negation gives `c_0 = 1 + 4e`, `S X^{-1}` becomes a `Z_2`-power of `X^4` inside the
  closed subgroup `1 + 16 Z_2` via `gRsd_isClosed_sixteen` and
  `zpowZtwo_mem_topologicalClosure`, and that contradicts `gRsd_Sval_sub_rootX`'s exact level
  `S - X = 8 * odd`. The `X = 5`, `S = 13 mod 16` seed is consistent with it (`13 - 5 = 8`)
  and is what `Sval_toZModPow_four` / `rootX_toZModPow_four` supply. No gap.
* **`MpcFive`'s witness-defect closed form against its docstring.** The docstring's three
  central involutions are the statement's three factors term for term:
  `commP (dmB^4) (dmA) * commP (dmC) (dmB^2)^2 * commP (commP (dmB^2) (dmD)) (dmC)`. The
  supply move in the docstring (`us = 1`, `ut = B^4`, `um = 1`, `un = B^4 [B^2,D]`) matches
  `mpcFv_supply_witness`'s tuple against `mpcFvUt:767` and `mpcFvUn:771`, and matches the
  annotation `7a36073c` wrote into `MpcLadder.lean:709`. The wave-86 supersession claim is
  also right: of the two terms `mpcLad_pow_letC_five` predicted, only `[C_0, B^2]^2` survives.
* **The ansatz scoping held in the positive direction.** `mpcFv_nonempty_five` carries an
  explicit scope block saying it is a statement about the ansatz and says nothing about
  `MpcPivShift 2`, and the lane note §2 states the mirror-image discipline. The wave-86
  inversion failure did not recur.
* **The `cfourDef_jacobi_solve` citation resolves.** `SqCore/GradedClassFourDefect.lean:96`,
  added by `6bafbe94` (2026-08-12), so the note's "committed since W72" is right about the
  fact and the era. The rotation it drives, `gRsd_zeta_Y:1124`, is stated as the note
  describes it.
* **`GradedRowLadder.lean:58`'s W87-BLOCK annotation** (from `fc2dc985`) is accurate at this
  base: rung 4 IS a theorem on the whole unit locus and the residual of THAT ladder does start
  at class five. It makes no M6 comparison, which is why it escaped finding 1.
* **Em-dashes: zero** in all four `w87-*.md` notes and all three wave-87 modules (T4).

---

## 2 The codepoint re-measurement (T2)

**Tree-wide at `ad8c2b62`: 720 lines over 100 codepoints, in 254 files.**

Method, stated because the last two rounds turned on it: every `.lean` file under `GQ2/` plus
`GQ2.lean` itself, 970 files, split on `\n`, each line decoded as UTF-8 and counted in
codepoints, strictly greater than 100. The same corpus in bytes gives **9481** lines in 701
files, a factor of thirteen. Any figure in this campaign quoted without its unit is
unusable; that is the whole content of the wave-83 confusion.

History, all re-derived rather than quoted: 707 in 251 files at `db6fcedf` (wave 83's own
base), 720 in 254 at `ad8c2b62`. The growth of thirteen is four waves of new modules, so no
wave regressed the figure materially and no wave fixed it.

### The distribution (top ten)

| # | module | lines over 100 | longest | module lines |
|---|---|---|---|---|
| 1 | `GQ2/SectionSix.lean` | 25 | 124 | 1057 |
| 2 | `GQ2/RStage/GammaA.lean` | 21 | 113 | 1200 |
| 3 | `GQ2/AffineTLift.lean` | 15 | 116 | 887 |
| 4 | `GQ2/OrbitVanish.lean` | 13 | 122 | 741 |
| 5 | `GQ2/SectionThree.lean` | 13 | 113 | 1475 |
| 6 | `GQ2/Dyadic/CertificateMain.lean` | 12 | 383 | 762 |
| 7 | `GQ2/Dyadic/Instances/GammaLSylowPreimageFieldLabuteHilbertTail.lean` | 12 | 126 | 454 |
| 8 | `GQ2/Dyadic/Instances/EvenRouteCarried.lean` | 11 | 194 | 925 |
| 9 | `GQ2/Demushkin.lean` | 11 | 141 | 540 |
| 10 | `GQ2/Shapiro/Deepness.lean` | 11 | 121 | 282 |

### What the shape of the distribution says about the policy call

The three facts that bear on record-or-adopt, none of which was available before:

1. **It is a long tail, not a hotspot.** The top ten carry 144 of the 720, twenty percent.
   The median offending file has TWO such lines and 113 of the 254 files have exactly one.
   Adopting a 100-codepoint limit therefore touches 254 files for a median of two lines each;
   it is not a matter of rewrapping a handful of bad modules.
2. **It is old code, not current work.** Not one of the top ten is recent; the worst are the
   Section modules and the `RStage`/`Shapiro` foundations. The three wave-87 modules measure
   **0** (`SqCore/GradedRowResidue.lean`, 1688 lines), **0** (`Instances/MpcFive.lean`, 962
   lines) and **3** (`Instances/WordPhaseModel.lean`, at `:44`, `:46`, `:268`, all markdown
   table rows in docstrings where wrapping breaks the table). The wave-86 figures were 0/0/7.
   Lanes have in practice been holding the line for at least two waves without a policy.
3. **The extreme outliers are single lines, not module-wide habits.** The longest line in the
   tree is `CertificateMain.lean` at 383 codepoints, in a module carrying only 12 over-100
   lines at all. If the owner wants a cheap partial, capping the tail (say, everything over
   150) is a far smaller job than the limit itself.

Nothing was rewrapped. The item is record-or-adopt and adopting is the owner's call.

---

## 3 Memo hygiene (T3)

The wave-87 block's three checkable claims, each verified against the tree at `ad8c2b62`:

* **"Nine items await you, unchanged from wave 86's standing list (items 1 to 9 of
  `w86-house-note.md`)": TRUE.** That note lists ten, its item 10 being "register the two
  wave-86 modules", discharged by `ed382b2e`; items 1 to 9 stand. No wave-87 lane opened or
  discharged an owner item: `w87-house-note.md` says so of itself, and `w87-block-note.md`,
  `w87-five-note.md` and `w87-normal-note.md` contain no owner-item section at all (grepped
  and read). The nine are unchanged.
* **"A6 stands at fourteen review rounds": TRUE, and now with its origin pinned.** The freeze
  was opened as an owner item at **wave 73** (`owner-items-2026-08-05.md:288, :304, :325,
  :350` trace it back), so rounds 74 through 87 inclusive are fourteen. The per-wave increments
  in the memo blocks (nine at 82, ten at 83, eleven at 84, twelve at 85, thirteen at 86,
  fourteen at 87) are consistent with that origin. This is the first round the count has been
  checked against its start rather than against the previous block, so it can stop being
  re-derived: **A6 round N = wave N - 73.**
* **The codepoint figures: the wave-86 "0/0/7" is right; the byte-provenance claim is wrong.**
  See finding HIGH 2 and S2. Corrected at the memo (`f81c92b5`).

**The board agrees.** `## OWNER ITEMS` reads the memo as authority and the highest-numbered
house note as the frozen artifact. The memo asserts nine; S5 below lists nine under an
`Owner items` heading the board's tolerant contract matches; the board prints AGREE.

---

## 4 The scrub and the artifacts (T4)

* **Em-dash scrub: nothing to scrub.** Zero em-dashes in `docs/dyadic/w87-block-note.md`,
  `w87-five-note.md`, `w87-house-note.md`, `w87-normal-note.md` and in
  `SqCore/GradedRowResidue.lean`, `Instances/MpcFive.lean`, `Instances/WordPhaseModel.lean`.
  Every prose edit this lane made is also em-dash free and under 100 codepoints, checked.
  Recorded because a clean scrub is a fact about the wave, not an absence of work: this is the
  first wave in the run where the scrub found nothing.
* **The tree is otherwise clean.** No stray artifacts, no `sorry`, no `native_decide`, no
  `maxHeartbeats` and no `maxRecDepth` in any of the three wave-87 modules (grepped; the only
  hits are the module docstrings asserting their absence). The worktree carries no untracked
  or modified files outside this lane's own commits.
* **`work/` at the repo root: 822 MB, untracked, and not ignored.** Report only, nothing
  deleted or moved. It lives in the main clone
  (`/Users/roed/claude/cla/work/gq2-dyadic-campaign/work`), not in any worktree, and holds 50
  entries, all of them dead campaign scaffolding: 37 one-off `check_waveNN.lean` probes for
  waves 2 to 38, `AxiomAuditCurrent.lean` and `CheckDev.lean`, five `w50-*.log` build logs
  totalling about 2.8 MB, and seven olean cache trees (`olean/`, `olean-clone/`, `olean-full/`,
  `olean-local/`, `olean-wave37/`, `olean-wave38/`, `fresh/`) which are essentially all of the
  822 MB. The newest file is dated 2026-08-07, wave 50; nothing has been written for
  thirty-seven waves. It appears in `git status` as `?? work/` on every run because it is
  **not** in `.gitignore`, so it is also a standing invitation to `git add -A`. Two
  dispositions, both the owner's: add `/work/` to `.gitignore` and leave the bytes, or delete
  the six superseded olean trees and keep the probes. This lane does neither.

---

## 5 Owner items

**Nine standing**, matching the memo's wave-87 block: items 1 to 9 of
`docs/dyadic/w86-house-note.md`, that note's item 10 having been discharged by `ed382b2e`.
None is takeable by a comment-only lane; all are statement changes or policy calls. **Nothing
was opened or discharged by this lane**, and nothing was opened or discharged by wave 87.

1. **ASK restatement.** Restate the row records against `ExactLiftingSemanticsRN`, or prove
   `askCStageVanishing`. Unchanged.
2. **Pilot spelling.** Unchanged. Consumer list at W85-HOUSE §2.3.
3. **The A6 freeze** (`GQ2/Roe/*`): **fifteen** review rounds without motion, the freeze
   having opened at wave 73 (S3 pins the origin, so the count is now derivable rather than
   inherited: round N = wave N - 73). `git diff ad8c2b62 HEAD` on `GQ2/Roe/` and on `GQ2.lean`
   is empty for this lane, checked. The board's machine substitute at this base: last commit
   `4341a1a3`, 2026-08-10, comment-only; 16 house notes added since, plus this one (see
   finding LOW 7).
4. **Line length.** Policy call still owed, and now for the first time measured tree-wide with
   its method attached: **720 lines over 100 codepoints in 254 files** at `ad8c2b62`, S2, with
   the distribution and the three facts that bear on the call. The wave-83 premise that this
   figure was a byte count is refuted (finding HIGH 2). The measurement half of this item is
   discharged; only the policy remains.
5. **The forgotten marking.** Two sites, `genAsm_branch_of_evenN` and `genAsm_branch_of_evenM`.
   Unchanged.
6. **`askCStageVanishing`: fact or wrong ask?** Unchanged, and still the sharpest open item on
   the arithmetic side.
7. **The `hclear` re-cut.** `GammaLOddDegreeBridgePivot`'s consumers should take `hclear` alone.
   Unchanged.
8. **The two-idiom split on the `L` row.** A design question. Unchanged.
9. **Weaken `mpcBld_shift_of_bracket_supply`'s hypothesis** to the per-solution form.
   Unchanged, and W87-HOUSE's verification against the Lean stands. As of `0a479c6e` the
   better disposition may still be to deprecate it in favour of
   `MpcLadder.mpcLad_shift_of_exists_supply`.

**Recorded for a lane that wants them, not opened as owner items.** The memo convention
question from finding MEDIUM 4 (should a same-wave open-and-discharge appear in a status
block at all); the board's A6 self-count from finding LOW 7, which needs a script ticket; and
the disposition of `work/` from S4, which needs a `.gitignore` line or a delete and neither is
a lane's to choose.

---

## 6 What this lane did not do

No statement changed anywhere. Every tree edit is a comment or a docstring annotation, in five
files: `SqCore/GradedRowResidue.lean`, `SqCore/GradedRowMove.lean`, `Instances/MpcWord.lean`
(class-status annotations) and the two docs `owner-items-2026-08-05.md`, `w87-house-note.md`
(line-length corrections), plus `w87-block-note.md`. `GQ2.lean` and `GQ2/Roe/*` untouched,
checked. The sibling-owned paths `SqCore/GradedRowUniform.lean`,
`Instances/WordPhaseSeam.lean` and `Instances/MpcSix.lean` do not exist at this tree and were
neither created nor touched.

No `lake` command was run. Verification is `scripts/mirror.sh check` on the three wave-87
modules (which is also where the pin audit in S1 comes from) and `scripts/scoreboard.sh`.
`MpcPivShift 2`, `askCStageVanishing`, the class-six rungs of either ladder and the
ansatz-exhaustiveness question were not attempted. Nothing in `work/` was deleted or moved.
