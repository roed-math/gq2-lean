# W75 supplementary sweep: counts and citations over the wave-74 artefacts

**[W76-HOUSE, and this file is now closed.**  All 23 items were re-verified at `97d51e93` and
then applied, except item 7, which is declined with reason.  Four of the sweep's own figures
needed amending in the course of applying them, and the amended values are what landed:

* **item 6**: "two lines exceed 100 characters" undercounts.  `GradedUniformTower.lean` has 25
  such lines, 8 of them Lean source rather than comment.  The two named are rewrapped; the rest
  are left, because the campaign enforces no 100-character limit anywhere (25 `SqCore` modules
  carry 19 or more).  That is now an owner call on the W77 queue.
* **item 11**: "43 carry a numbered pins heading" is the complement of the true reading.  At
  `4fff1592`, of 91 `SqCore` modules 88 contain `#print axioms`; **45** carry a numbered pins
  heading and **43** carry the pins with no numbered heading.
* **item 17**: `evenDegreeNCyclotomicFrattiniFrameSupply_holds`'s declaration landed
  **2026-08-07** (`61c51c9e`), not 08-05; the 08-05 commit carries the name only as a planned
  statement in the EV-3c skeleton.  The substance (before the wave-51 window) stands.
* **item 22**: the `Q_2(zeta_8)` sentence in `w72-stratum-note.md` is at **`:170`**, not `:169`.

One disagreement with the sibling W75 document is resolved in this file's favour: item 10's
`w74-critical-path.md:135` is right and `w75-house-note.md` §4.5(b)'s `:134` is the line above.
See `docs/dyadic/w76-house-note.md` §1 for the item-by-item accounting.]**

Recorded by the orchestrator at the W75 close.  The W75-HOUSE lane dispatched an exhaustive
count-and-citation sweep as a background agent; it returned after the lane's branch had merged,
so its findings are recorded here for the W76 house lane to apply.  Method: every citation was
checked at the document's own lane commit, so drift caused by W75's own edits is separated from
defects; axiom-set claims were out of scope (no `lake` in a lane).

## Module comment fixes (comment-only, all in wave-74/75 modules)

1. `GQ2/Dyadic/SqCore/GradedDeltaFunctionals.lean:64` cites `gDelta_handle_tower`; the
   declaration is `gDelta_handleU_tower` (`:747`).
2. Same file `:65` cites `gDelta_handle_tower_notMem`; the declaration is
   `gDelta_handleU_tower_notMem` (`:804`).  The func note has both names right at `:223`.
3. Same file: the `## Contents` list (`:24-103`) enumerates §1-§7 of a nine-section file.  §8
   (`:1210`, holding the lane's own headline `gDelta_cfourCmp_span_hyp_false`) and §9 (axiom
   pins) are absent.
4. `GQ2/Dyadic/SqCore/GradedUniformTower.lean:35` cites `gTower_tower_rows`; the row-reading
   lemmas are `gTower_tower_nuLam` (`:233`) and `gTower_tower_nu` (`:239`).
5. Same file `:899` cites `gTower_layer_step`; the declaration is `gTower_full_layer_step`
   (`:1293`).  The engine note has it right.
6. Same file: the module docstring narrates §1-§3 and the dictionary, then stops; §4-§8,
   including both interfaces and the crown lemmas, have no docstring entry.  Two lines exceed
   100 characters: `:878`, `:886`.
7. `GQ2/Dyadic/Instances/EvenStratumRowFrame.lean:864` (and `docs/dyadic/w74-even-note.md:139`)
   carry the shortened `evenRawShiftSpan_eq_zLayer` inside a verbatim quotation; the
   declaration is `evenRawShiftSpan_eq_zLayer_of_pureSquares`.  Third and fourth sites of
   round 11 §4.3(h)'s finding, created the same wave it was raised.
8. `EvenStratumRowFrame.lean:336` cites `StageAbstractionEvenFrameCore.lean` "§4.1", a label
   that file's headings do not carry (its §4 prose names "§4.1" without a heading).

## Note corrections

9. `docs/dyadic/w74-func-note.md:212`: "105 declarations" should be **103** (the pins figure on
   the next line is right).
10. `docs/dyadic/w74-critical-path.md:135` and `w74-house-note.md:79`: the `SqCore/Graded*`
    family is **66** modules at the stated tree `4fff1592`, not 68 (68 is post-wave-74).
11. `w74-house-note.md:417`: "the 40 `SqCore` modules with a pins block" has no supporting
    reading; at `4fff1592` **88** `SqCore` modules contain `#print axioms` and **43** carry a
    numbered pins heading.  The substance (GradedClassFourCompose the only numbering gap) is
    right.
12. `w74-house-note.md:641`: "Eleven more" enumerates **ten** sites; the headline "fourteen"
    reconciles only by counting one item at two places.
13. `w74-house-note.md:350`: 55 + 35 + 33 = **123** against a ledger delta of 124; one
    declaration of slack is presented as exact agreement.
14. `w74-critical-path.md:130` says "the tree's 930 `GQ2` modules"; `GQ2/` holds **929** `.lean`
    files (930 only if the root `GQ2.lean` is counted).  The numerator 427 is exact.
15. `w74-house-note.md:723`: "ten of the 29 have a second site" undercounts; the second-site
    findings number **fifteen**.
16. `docs/dyadic/w74-even-note.md:201`: the 42 is right but the named blocks sum to 40; the two
    missing are §3's `evenStratumRow_omegaClass_ne_zero` and `evenStratumRow_coord_headSecond`.
17. `w74-even-note.md:194`: of the eight comparison statements, seven date to waves 51/72/73 as
    claimed; `evenDegreeNCyclotomicFrattiniFrameSupply_holds` landed 2026-08-05, before the
    wave-51 window.
18. `w74-even-note.md:195`: "re-declared because the originals are private" is false of one of
    the three: `evenStratumRowAssembleM` is NOT a re-declaration of `evenRawAssembleM` (eight
    slots and three hypotheses against seven and two; the extra slot is the coordinate-2 atom
    that is the point of the M twin).  Same wording defect round 11 §4.3(c) reported one wave
    earlier at `EvenStratumShift.lean:75`.

## Citations that drifted or misresolve (all in `w74-house-note.md` unless said)

19. `:254` cites `EvenStratumFrame.lean:585` for a comment its own lane's edit moved to
    `:598-600`.
20. `:289` cites `w72-house-note.md:707`, moved to `:752` by its own lane's edits.
21. `:481` cites `w73-stratum-note.md:41` for a sentence at `:47`.
22. `:626` cites `w72-stratum-note.md:163` for the `Q_2(zeta_8)` sentence at `:169` (post-edit).
23. Minor: `:644` bare `tickets.md:1850` (three files of that name exist); `w74-func-note.md:65`
    and `:139` have name-number pairs reversed (`:145`/`:150`, `:295`/`:303`);
    `w74-critical-path.md:208` cites `:519` for a quotation starting at `:517`.

## Clean, for the record

Every other count checked out exactly, including: the engine note's 94/94; the even note's
49 = 46 + 3 and 54 pins with all eight external comparanda resolving; the critical-path record
table (all six line numbers, all field counts); the 427-module closure and its four SqCore
members; the house note's batch-B recount (929/843/928/1/85/27, every figure); all three lanes'
commit lists; and all 109 backticked file paths except the deliberately-nonexistent
`GQ2/Roe/DRH2.lean`.
