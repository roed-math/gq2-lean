# W76-HOUSE: the sweep applied, round 12 discharged, and round 13 catches wave 75 refuting round 12

Lane W76-HOUSE, branch `claude/w76-house`, base `97d51e93`.  Standing verification and
housekeeping.  **No `lake` command was run**, and `scripts/check_dyadic.sh` was not run either.
Verification is `scripts/mirror.sh` throughout.

## Headline

**Watch round 13's finding is that watch round 12 was overtaken by its own wave, twice, and
nobody noticed for a full wave.**  The W75-JOIN lane's `GradedUniformJoin.lean` landed at
`87003e9d` (04:31:24) and merged into `dyadic` at `71975be8` (04:33:51).  The W75-HOUSE note
recording round 12 was written at `6eceb48c` (04:46:17), **12 min 26 s later**, and it carries
forward two items that module had already settled:

* round 12 §4.1(e)'s second bullet, "`GDeltaDefectVanishing` as committed serves only the base
  of the recursion", is **refuted**.  `gJoin_chiSq_of_gammaTwo` proves that a `γ₂`-valued
  admissible correction is `χ_sq = 1` **exactly**, by pinning opposite residues: the `λ`-row
  gives `±1`, `γ₂`-membership gives `≡ 1 mod 8`, and `-2` is not `8`-divisible in `ℤ₂`.
  `gJoin_chiSq_mul_correction` carries the clause through every step, so the exact hypothesis
  is free along the **whole** recursion.
* §5.3's "it is now visible from three sides at once and has never been attacked directly",
  about the functional-invisible `x̃₁` tower, is **overtaken**.  `gJoin_xOne_tower_knob` proves
  that tower **is** a knob at every depth `k ≥ 1`, manufactured by the `x₁`-slot bundle: this
  is exactly the structural argument that paragraph asks for, and the paragraph's own premise
  is why it had to exist.

§5.1's whole W76 ticket goes with them.  The module it proposes exists (under a different
name), it threads the **exact** `χ`-clause instead of the proposed mod-8 one, and its ⚠ owner
call never arose because the new Prop sits **beside** the committed one rather than replacing
it.

The lane's own ticket-2 pass then reproduced both refuted halves verbatim, because ticket 2's
brief is to apply round 12 and round 13 had not run yet.  Both are **amended in lane**.  That
is the half-a-fix rule biting the lane that wrote the rule down, and it is the argument for
running the staleness check *before* the application pass, not after: see the W77 queue.

Everything else: the 23 sweep items are accounted for one by one (22 applied, 4 of those with
an amendment to the sweep's own figure, 1 declined with reason), and round 12's reported
findings are applied except the three that are statement changes or the owner's.

## 1.  Ticket 1: the 23 sweep items, one by one

Every item was re-verified at this tree before it was touched.  Four of them needed the
sweep's own figure amended; one is declined.

| # | site | verdict |
| --- | --- | --- |
| 1 | `GradedDeltaFunctionals.lean:64` | **applied**: `gDelta_handle_tower` → `gDelta_handleU_tower` |
| 2 | same `:65` | **applied**: `..._notMem` likewise |
| 3 | same, `## Contents` | **applied**: §8 (the tower obstruction, holding the lane's own headline) and §9 (pins) added, so the list covers all nine sections |
| 4 | `GradedUniformTower.lean:35` | **applied**: `gTower_tower_rows` does not exist; the row-reading lemmas are `gTower_tower_nuLam` and `gTower_tower_nu` |
| 5 | same `:899` | **applied**: `gTower_layer_step` → `gTower_full_layer_step` |
| 6 | same, module docstring | **applied and amended** (below) |
| 7 | `EvenStratumRowFrame.lean:864`, `w74-even-note.md:139` | **declined**, with reason (below) |
| 8 | `EvenStratumRowFrame.lean:336` | **applied**: the cite now names `StageAbstractionEvenFrameCore.lean` §4 (a real heading) and says its §4 prose names a "§4.1" its headings do not carry |
| 9 | `w74-func-note.md:212` | **applied**: 105 → **103** declarations |
| 10 | `w74-critical-path.md:135`, `w74-house-note.md:79` | **applied at both**: 68 → **66** at `4fff1592` |
| 11 | `w74-house-note.md:417` | **applied and amended** (below) |
| 12 | `w74-house-note.md:641` | **applied**: "Eleven more" → **ten**; the headline "fourteen" reconciles only by counting item 1 at both its places, and now says so |
| 13 | `w74-house-note.md:350` | **applied**: `55+35+33 = 123` against a ledger delta of **124**; one declaration of slack was presented as exact agreement |
| 14 | `w74-critical-path.md:130` | **applied**: 930 is right *with the convention stated* (929 `.lean` files under `GQ2/`, 930 counting the root `GQ2.lean`); the numerator 427 is exact either way |
| 15 | `w74-house-note.md:723` | **applied**: ten → **fifteen** second-site findings, recounted finding by finding |
| 16 | `w74-even-note.md:201` | **applied**: the named blocks summed to 40 against the row's own 42; §3's two lemmas are now named |
| 17 | `w74-even-note.md:194` | **applied and amended** (below) |
| 18 | `w74-even-note.md:195` | **applied**: `evenStratumRowAssembleM` is not a re-declaration |
| 19 | `w74-house-note.md:254` | **applied**: `EvenStratumFrame.lean:585` → `:598-600` |
| 20 | `w74-house-note.md:289` | **applied**: `w72-house-note.md:707` → `:752` |
| 21 | `w74-house-note.md:481` | **applied**: `w73-stratum-note.md:41` → `:47` |
| 22 | `w74-house-note.md:626` | **applied and amended** (below) |
| 23 | four minor citations | **applied**: `tickets.md:1850` written out as `docs/dyadic/tickets.md` (three files of that name exist and only that one reaches line 1850); both reversed name-number pairs put in order; `EvenUnramified.lean:519` → `:517-519` |

### 1.1  The four amendments to the sweep's own figures

**Item 6, "two lines exceed 100 characters", undercounts.**  The two named lines (`:878`,
`:886`, the `gTowerTowSet` and `gTowerReach` signatures) are rewrapped at a binder, token
stream unchanged, in the style the file's own `gTowerFullReach` already uses.  But
`GradedUniformTower.lean` has **25** lines over 100 characters, of which **8** are Lean source
rather than comment (`:152`, `:308`, `:861`, `:878`, `:886`, `:901`, `:1054`, `:1423`).  Two of
the six remaining source lines, `:861` and `:901`, are sibling definitions in the same block as
the two that were named, so the file now has two of four wrapped, which is worse local
consistency than either extreme.  **The reason it is left there and not fixed:** the campaign
does not enforce a 100-character limit anywhere.  25 `SqCore` modules carry 19 or more such
lines each, led by `GradedContain.lean` at 35.  Either the convention is adopted and swept, or
this item is cosmetic; that is an owner call, not a house lane's, and it is on the W77 queue.

**Item 11, "43 carry a numbered pins heading", is the complement of what it says.**  The "40
`SqCore` modules with a pins block" figure had no supporting reading and is struck.  Recounted
at `4fff1592`: of **91** `SqCore` modules, **88** contain a `#print axioms` line; of those,
**45** carry a numbered pins heading (**42** labelled "Axiom pins", 3 "Stress pins") and **43**
carry the pins with **no** numbered heading.  The sweep's 43 is the count that do *not* carry
one.  The finding's substance is unaffected.

**Item 17's date is two days early.**  `evenDegreeNCyclotomicFrattiniFrameSupply_holds`'s
*declaration* landed at `61c51c9e`, **2026-08-07**, not 08-05; the 08-05 commit `de1b361f` is
the EV-3c skeleton, where the name appears as a planned statement in a comment.  The substance
stands: 08-07 is before the wave-51 window, so the even note's "eight comparison statements
from waves 51, 72 and 73" is right about seven of the eight.

**Item 22's target line is `:170`, not `:169`.**  The `Q_2(zeta_8)` sentence in
`w72-stratum-note.md` is at `:170` at this tree.  Applied at `:170`.

### 1.2  The one declined item, and why

**Item 7 is not applied, and should not be.**  Both sites carry the shortened
`evenRawShiftSpan_eq_zLayer` **inside a verbatim quotation** of wave 73's prediction, and both
are followed within a few lines by a correct use of the full name.  W75-HOUSE faced exactly
this and ruled the other way round: it *reverted* an in-place correction at the quotation's
source (`w73-stratum-note.md`) precisely because wave 74 quotes the sentence, short name and
all, at these two sites, and an in-place rewrite would make two shipped quotations misquote
their source (`w75-house-note.md:84-95`).  Correcting the quotations instead would produce the
same defect from the other end.  The correction already sits under the source sentence as a
`[W75-HOUSE]` block naming both quoting sites, which is where a reader resolving the short name
will look.  Nothing to do.

## 2.  Ticket 2: round 12's reported findings

Applied, prose and comment only:

* **§4.2(b), the oldest item on the list and the cheapest.**  `EvenUnramified.lean:70` hedged
  "documented false at `α = 1`" and `:395` "recorded false at `α = 1`", where
  `evenStratum_no_rawStageShift_one` (`EvenStratumShift.lean:333`) **proves** it, at the
  profinite-group quantifier `evenRawStageShift_n` actually carries, on the cyclic group of
  order eight; `evenStratumRow_no_rawStageShift_m_one` (`EvenStratumRowFrame.lean:848`) is the
  `M` twin.  Both sites now say **proved** and cite both theorems.  `:395` also keeps the scope
  caveat the refutation's own docstring makes and the hedged version silently carried: it
  decides nothing at any *particular* field, that question reducing through
  `evenStratumShift_diagonalAtom_eq_one_of_rawShift` to whether the diagonal atom vanishes
  there.  Named by a wave-73 queue and again by a wave-74 queue; two waves unapplied.
* **§4.3(a), an impossibility claim on a containment theorem, at both sites.**
  `EvenStratumRowFrame.lean` §7's header and `w74-even-note.md:151` both said the `Hsq` input
  "cannot be obtained from the `α = 1` rows **at all**".  What
  `evenStratumRow_sq_mem_bracketSpan_of_isShift` proves is: *if* `p²` is an `α = 1` shift then
  `p²` lies in the bracket span.  Nothing rules out a **product** of shift values equalling a
  square, and `EvenRawPureSquareSpanSupply` asks for membership in a *span*, not for a row
  value.  Both now say the input is not *supplied* by the rows, no row emitting a square, which
  is what is proved and is the sentence's actual point.
* **§4.1(c) and (d), in `w74-func-note.md` §4.3.**  Item 2's first sentence contradicted its
  second one line apart; the ENGINE's right-hand side is `gTowerReach` = knobs **together with**
  the admissible towers, and the statement is open only at the base `k = 2`, because
  `gTower_layerReach_step` inducts and `gTower_layerReach_of_base` closes every `k ≥ 2`.  Item
  3's "all committed plumbing" is not committed: `cfourCmp_residual_of_core_vanish`
  (`GradedClassFourCompose.lean:601`) takes the core defect's **vanishing**, not its knob-span
  membership, and none of that module's three routes starts from "the core defect is a knob".
* **§4.1(e) and (f)**, applied and then **amended in lane** by round 13; see §3.1.
* **§4.1(g).**  `GradedUniformTower.lean`'s `GTowerKnobRealizable` docstring cited
  `w73-knob-note.md` §"the multi-handle composition lemma"; that is §9's wave-74 queue item 2,
  not a section, and now says so.
* **§4.3(b) and (c), in `w74-engine-note.md`'s W75 list, one annotation on one item.**
  "Unconditional" means only "no longer conditional on the base hypothesis" - the theorem keeps
  six binders.  "From the committed class-four record" is a **construction**, not a citation:
  `cfourCmp_zLayer_le_gens` quantifies over all of `Q₄` where `GTowerLayerReach` asks only
  about exactly row-trivial elements, and the row restriction is what keeps this item clear of
  wave 74's own refutation `gDelta_cfourCmp_span_hyp_false`.
* **§4.2(a), the registration finding, and the convention that ends it.**  Applied at both
  wave-74 sites and, under round 13, at both wave-75 sites.  See §3.3.

Reported and not applied:

* **§4.1(a)** is a statement change (weakening `GTowerDefectVanishing` to carry an `x₁`-tower
  coefficient) and therefore an owner call.  It is annotated on the engine note as the join
  lane's briefing rather than made - and round 13 then found that wave 75 chose the other
  branch of that same disjunction and closed it; see §3.1.
* **§4.1(e)'s recursion threading**, for the same reason; and it, too, turned out already done.
* **§4.2(c)**, the owner memo's missing wave-74 ledger figure.  The memo's status blocks are the
  owner's.  Recomputed here for the wave-75 tree: **32488 tracked declarations, gap map 0,
  ALARM 0, 0 terminal violations**, a rise of **152** over the wave.
* **§4.1(b)** is an addition rather than a correction ("worth a paragraph in whichever note the
  join lane writes").  The join lane wrote it: `w75-join-note.md`'s T2 says the `σ⁴` worry is
  empty because `σ⁴` is `w⁴x₀^{4c}` modulo the layer, so the refutation bites the knob subgroup
  (which has no towers at all) and not the reach.  Consistent with §4.1(b), independently
  derived, and now cross-referenced from the engine note's annotation.

## 3.  Ticket 3: watch round 13

Scope: `GeneralAssembly.lean`, `GradedUniformJoin.lean`, the three w75 lane notes,
`w75-sweep-findings.md` itself, and the ledger-gate scripts' new annotations.  The full
standing checklist, plus the interface-blindness item, which produced the round's headline for
the second wave running.

### 3.1  HIGH.  Intra-wave staleness, from a sibling lane's *merged* work

Set out in the headline.  The mechanics are worth stating separately from the mathematics,
because this is the third distinct shape the staleness finding has taken:

* round 11 and round 12 found notes stale against the **orchestrator's** later commits
  (registration, minutes);
* round 12 §4.2(d) found ordinary **line drift** and recorded it so round 13 would not
  re-derive it (it did not have to; correctly predicted);
* round 13 finds a note stale against a **sibling lane already merged into `dyadic`** at the
  moment of writing.  This one is not a timestamp problem: `71975be8` was on the branch the
  house lane's own base descends from.  A `git log --oneline <base>..HEAD` at note-writing time
  would have shown it.

Applied at four sites: `w75-house-note.md` §4.1(e) (struck through, refutation recorded),
§5.1 (whole W76 ticket struck, point by point against what actually landed), §5.3 (the
structural argument it calls for, named), and `w74-func-note.md`'s two W76-HOUSE annotations
from this lane's own ticket-2 pass, amended in place.

**What survives of §4.1(e), and it matters for the W77 briefing:** the *first* bullet is
right.  Joining at mod-8 would prove something strictly weaker than `GTowerDefectVanishing`.
The join lane's answer was not to join at mod-8 at all but at the **exact** clause, which
`gJoin_chiSq_of_gammaTwo` makes available, and to put the weaker Prop `GJoinDefectVanishing`
**beside** `GTowerDefectVanishing` in a new module with `gJoin_defectVanishing_of_tower`
recording the implication.  No committed statement changed.  The ⚠ that round 12 raised was
raised correctly and was routed around rather than paid.

### 3.2  MEDIUM.  Headline-versus-statement, three sites

* **`GradedUniformJoin.lean` §8's header contradicts its own theorem, 45 lines apart, inside
  one file.**  The header said the `χ`-restricted vanishing interface "*and with it*
  `SqClassClearingSupply h k` at every class, and the whole `h ≥ 1` residual" follows from
  "exactly **two** further inputs", and listed `GTowerLayerReach h ν' 2` and
  `GJoinTowerSeparation`.  The vanishing interface does follow from two
  (`gJoin_defectVanishing_of_base`).  The supply and the residual need a **third**,
  `GTowerKnobRealizable h`, which `gJoin_markTransitivity_of_base`'s own ⭐⭐⭐ docstring names
  ("from three named inputs"), and which `w75-join-note.md`'s headline also names.  The header
  now separates the two claims and names the third input.  It also now uses the Prop names the
  theorems actually take (`GJoinBase`, `GJoinSeparationAll`) rather than the per-instance forms.
* **"The far span **is** `χ ≡ 1 (mod 4)`" is an identity headline on a one-way containment, at
  two sites.**  `gTowerFar` is defined by **generators** (`GradedUniformTower.lean:895`: the
  topological closure of the subgroup generated by `σ`, `x₀` and the `2h` handle letters).
  `gJoin_chi_far` proves `gTowerFar h ≤ gJoinChiFour h` and nothing shows the converse.  The
  note's form was stronger still: "**The far span's *definition* is exactly the `chi = 1 mod 4`
  condition**".  Both corrected; the containment is all the argument needs.
* **"`GTowerLayerReach h nu' 1` is false" is bolded as a fact and is an argument**
  (`w75-join-note.md`'s T2 warning).  Nothing in the tree refutes it.  The argument is also
  incomplete as given: showing that neither *generator family* produces `[σ, x₀]` does not show
  it is outside the *closure* of the two families, which is what `gTowerReach` is.  The note's
  own honesty markers are scrupulous about exactly this distinction three paragraphs later
  ("arguing is not proving").  Annotated; the operational advice (do not induct down to depth
  1) is sound either way, which is why it is a warning and not a queue item.

### 3.3  MEDIUM.  The registration finding recurs for a fourth wave, on both W75 notes

* `w75-join-note.md`'s "`GQ2.lean` untouched per protocol" against `8c3d6317` (04:34:05),
  **1 min 13 s** after the note's own commit `6cb7a794`;
* `w75-state-note.md` §6 item 4, "A later wave should add it", against `a19fac5a` (04:18:12),
  **1 min 28 s** after the lane's last commit `88a29ef7`.

Round 11 raised this on three wave-73 notes, round 12 on three wave-74 notes, round 13 on both
wave-75 notes: **four waves, eight notes**.  The behaviour is right every time; only the
timestamp is missing.  `w75-house-note.md` §8 item 4 proposed the fix and could not apply it,
having been written after both notes.  **Applied this wave at all four live sites** (the two
wave-74 notes under ticket 2, the two wave-75 notes here), in the proposed form: a lane note's
claim about `GQ2.lean`, or about a module being unwired, is written **as of** the lane's last
commit, because that is the only tree a lane can speak for.

### 3.4  MEDIUM-LOW.  Counts and citations

* **`w75-house-note.md:458-460` describes two objects that do not exist.**  Its recount block
  says "the two unpinned declarations and the two subset prints are as the note describes",
  inferring the two unpinned from `w74-func-note.md`'s 105 minus 103.  There are **none**:
  `GradedDeltaFunctionals.lean` has 103 declarations and 103 pins, and the map between them is
  a bijection - every declaration pinned exactly once, no pin naming anything outside the file.
  This is sweep item 9's error propagating one document further in the same wave that reported
  it.  The **method** is worth recording because it is what produced the 105: a line-start grep
  on `theorem|def|...` overcounts by matching prose words ("defect", "classes", "defined") and
  undercounts by missing the nine `@[simp]`/`@[reducible]`-prefixed declarations.  The ERE that
  gets it right allows an optional same-line attribute.  Both the source and the downstream site
  are corrected.
* **The two W75 documents disagree by one line about the same citation.**
  `w75-house-note.md` §4.5(b) cites `w74-critical-path.md:134` for the "68 modules" sentence;
  `w75-sweep-findings.md` item 10 cites `:135`.  At the W75 base `f0a71688` it is `:135`.  Both
  corrected, and the disagreement recorded at the house note's site.
* **`w75-join-note.md`'s "67 declarations, all 65 pinned declarations" is exact**, and the
  phrasing is honest (it does not claim all 67 are pinned).  For the record, the two unpinned
  are `gJoin_rowU_core` and `gJoin_rowV_core`, both small `if`-index helpers.  Compare
  `w74-engine-note.md`'s "94 declarations, every one pinned", which is also exact.

### 3.5  The specific check the ticket named: CLEAN

`GeneralAssembly.lean` §4.2's five anti-drift theorems **do** consume the committed
`rowEquiv_*` terms rather than re-proving them.  Each one's entire proof body is the committed
term applied to the same two hypotheses:

```
genAsm_rowEquiv_sqrtNegTwo F S := rowEquiv_sqrtNegTwo F S      (Main.lean:592)
genAsm_rowEquiv_sqrtTwo    F S := rowEquiv_sqrtTwo    F S      (Main.lean:602)
genAsm_rowEquiv_sqrtFive   F S := rowEquiv_sqrtFive   F S      (Main.lean:612)
genAsm_rowEquiv_sqrtTen    F S := rowEquiv_sqrtTen    F S      (Main.lean:622)
genAsm_rowEquiv_sqrtNegTen F S := rowEquiv_sqrtNegTen F S      (Main.lean:633)
```

The check is not vacuous, which is the thing worth verifying about an anti-drift check.  The
committed conclusion is over `candidateGroup 2 (qOf K FF) FrozenQuadRow.sqrtNegTwo.word`; the
general-shaped one is over `candidateGroup (SelectedPresentation.N0 2 0).degree (qOf K FF)
(SelectedPresentation.N0 2 0).word`, which is `genAsm_candidate_equiv_galK`'s conclusion at that
row's pin, since `GenAsmBranch.degree` and `.word` are `pres.degree` and `pres.word`.  The term
typechecks only because §4.1's ten `rfl`s hold definitionally, which is exactly the drift the
check exists to catch.

Two things the check does **not** do, and the note is explicit about both: it does not verify
that the general **record** suffices at a frozen row (the five theorems take
`ResidualSqrtNegTwo` and friends, not `GenAsmRowResidual`), and it therefore does not exercise
the retirement of the pilot's three abelianization fields `piAb`/`hpiAb`/`hpiNu`.  That
retirement is a claim about spellings (`w75-state-note.md:91`: the slot exists only in the older
`marked_matching_certificate_KN` spelling), and the general route reaches the conclusion through
`KSupply.ofMarkedCoreRealization` without them.  The note's F3 states the asymmetry and why it
is structural rather than a defect: the tree has equivalence ⇒ supply and no converse.  Headline
and statement agree.

### 3.6  What came up clean, said in detail

* **Docstring attachment: clean** on both wave-75 modules.  All eight ⭐⭐⭐ docstrings in
  `GradedUniformJoin.lean` sit on the declaration their headline names.
  `GeneralAssembly.lean` carries no ⭐ markers at all.
* **Hypothesis satisfiability: clean.**  `GJoinDefectVanishing` is strictly weaker than
  `GTowerDefectVanishing` and the implication is recorded (`gJoin_defectVanishing_of_tower`);
  `GJoinSeparationAll` is proved outright at `h = 0` (`gJoin_towerSeparation_handleFree`);
  `GenAsmBranch` is explicitly flagged in its own docstring as a hypothesis about which family
  member `K` is, with the ⚠ "no theorem produces one at an arbitrary ramified-`i` `K`".  None
  of the new Props is refuted by anything in the tree, including by wave 74's own refutation,
  for the row-triviality reason round 12 §4.1(b) gave.
* **Cross-module names: clean.**  Every declaration name `w75-join-note.md` uses for the two
  wave-74 modules exists there with the shape described, including the ones its analysis leans
  on hardest (`cfiveCommHom`, `sqMixPivotElem`, `gThreeFour_jacobi`, `cfourKnob_sq_knob_pair`,
  `cfourCmp_zLayer_le_triple`, `sqClassThree_supply`).  `w = sqPivot h = σ·x₀^{-c}` checks out:
  `sqPivot h = sqMixPivotElem h sqPivotExp` and `sqMixPivotElem h c = σ·(x₀^c)⁻¹`.  The one
  name that does not resolve, `nWordCertificate`, is correctly presented as something to build.
* **Record field counts: clean.**  `GenAsmFieldInputs` six fields, `GenAsmBranch` five,
  `GenAsmRowResidual` four, exactly as `w75-state-note.md` §1.2 says.
* **Both ledger-gate scripts: clean as behaviour and as prose.**  `bash -n` clean on both.  The
  exit-3 branch sits after the `fail` test and before the success line, so a failing fixture
  still exits 1 and a parsing fixture exits 3; the annotation at `check_ledger.sh:100-113`
  describes the mechanism correctly, including that the old wave-73 justification did not hold
  and why.  The standing lesson it records (the skip is visible in the transcript, not in the
  exit code, and the exit code is what D6 reads) is exactly right.  The other six annotations
  (`check_ledger.sh:15`, `:49`, `:66`; `check_dyadic.sh:30`, `:39`, `:90`) match the code they
  sit on.
* **The axiom ledger passes from inside a lane, without `lake`.**
  `scripts/mirror.sh check GQ2/AxiomLedger.lean`: **32488 tracked declarations, gap map 0,
  ALARM 0, 0 terminal violations**.  Four of the five terminal certificates print "identical to
  twin ... (12 axioms)" and the fifth (`admissibleCountR_eq_admissibleCount`) prints "12 axioms,
  all in the census".
* **Half-a-fix, grepped tree-wide.**  The subjects of this round's findings were grepped across
  `docs/`, `GQ2/` and `scripts/`: "serves only the base", "attacked directly",
  "GradedDeltaTowerJoin", "two unpinned", the far-span identity, and the registration wording.
  Every live site is listed above and every one is corrected; the grep is how this lane found
  that its own ticket-2 annotation was a second site of a refuted claim.

## 4.  Ticket 4 (report only): the shape of the W77 queue

Four sources, in the order a wave should read them.

### 4.1  What the join's landing leaves: three items, and only one is new

`gJoin_markTransitivity_of_base` reduces the whole `h ≥ 1` residual to three named Props.  The
functional half of Labute's Lemma 4 is finished; nothing on that side remains.

1. **`GJoinBase h`** - wave 74's depth-`2` base `GTowerLayerReach h ν' 2` at every selected
   marking.  Open since wave 74, **and it now has a route**: `w75-join-note.md`'s T2 works it
   down to a single missing ingredient, the degree-3 consequence of the relator's leading form,
   `[[c, x₁], x₁] ∈ [Λ²V, far]`, which the tree does not appear to carry in usable form.  The
   rest of the route is committed (`gTower_cut`, `cfourCmp_zLayer_le_gens`,
   `cfourCmp_zLayer_le_triple`, `gThreeFour_jacobi`).  **This is the highest-value W77 ticket on
   the graded side**: it is a named lemma, the surrounding argument is written out, and it
   closes a two-wave-old interface.  Carry the T2 warning with it (do not induct down to depth
   1), and carry §3.2's amendment (that warning is an argument, not a theorem).
2. **`GTowerKnobRealizable h`** - wave 74's extraction interface, untouched by two waves now.
   The ENGINE note's mod-2 far-slot route is still unexamined; `gJoin_chi_far` is likely useful
   there, in its corrected containment form.
3. **`GJoinSeparationAll h`** - the only genuinely new item, created by the join lane's own
   reduction, and it is bookkeeping rather than mathematics: `𝔽₂`-independence of the `2h`
   handle-tower generators inside a non-commutative `Q_{k+2}`.  The join note scopes two routes
   and calls each a lane-sized chunk.  Proved at `h = 0`.

### 4.2  What the statement finish leaves

`w75-state-note.md` §6, five items, all still live and none touched this wave:

1. a `WordCertificate` core transport along a marked core equivalence (F1) - one restatement,
   and reusable;
2. the compact-`N` word certificate at free `(α, h)` (F2), the `nWordCertificate` sibling of
   `mWordCertificate`, which does not exist; the `Npc` row needs one from scratch and the
   procyclic-`M` one needs lifting off `h = 0`;
3. the `α` pin - `range chiCycKTwo = imChiN α` per field - which is **the same item** as the
   flagship's item 1 below.  It appears on two lists and should be scheduled once;
4. registration of `GeneralAssembly.lean` - **done**, `a19fac5a`, see §3.3.  Struck;
5. nothing on the `L`-row marking; already wired.

Worth carrying forward as an orchestration note rather than a ticket: the state note's §4
observation that the critical-path memo's "the whole `Sq` graded programme is not on the path"
is correct **for the frozen quadratic table** and false for the general statement, where
`SqLamMarkTransitivity h` is a named input to the `L` row's selector at every `h ≥ 1`.  That
makes §4.1's three items path-relevant for the general theorem even though they are not for the
flagship.

### 4.3  The quadratic flagship's eight items: unchanged this wave

`w74-critical-path.md`'s list stands exactly as written; no wave-75 or wave-76 work moved any of
it.  Restated in queue order rather than group order, because two of the eight are the same
mathematics:

* **item 1**, the branch identification `range chiCycKTwo = imChiN α` per field.  Still the
  smallest genuinely-open item, still gating all five rows, and still the one that turns the
  even route's existential into a row.  Duplicated at §4.2 item 3.
* **item 5 / item 7's `hdet`**, the Gauss-`Z` determinant residue.  The sharpest statement on
  the list: the only place where **both** sides of the two-sided architecture are carried and
  neither has a supplier lane.  ⚠⚠ on both sides.
* **item 3**, `ExactLiftingSemantics` at `G_K`, narrowed by `KSupply.lean` to one existential
  (the `K` analogue of `exists_good_twist`).
* **item 4**, `StokesDualityCertificate` at `G_K`.
* **item 6**, the four certificate ⇒ count bridges at `GammaR n q word` - four statements, not
  sixteen, being uniform in the row.
* **item 2**, the `KTwoN`/`KTwoM` adapter - a restatement, and §4.2 item 1's transport is
  adjacent to it.
* **item 8**, the `nuP` construction for the four `M` rows - a build, hand-verified satisfiable.

### 4.4  The owner items

* **The A6 freeze on `GQ2/Roe/*` is still open and still blocks the two R6 hazards**, carried
  from round 11 through W75 §8 item 6 and untouched here (this lane touched nothing under
  `GQ2/Roe/`).  It is the oldest live owner item in the campaign's housekeeping trail.
* **The 100-character question** (§1.1): adopt and sweep, or declare the item cosmetic.  25
  `SqCore` modules carry 19 or more over-long lines; two of four sibling definitions in one
  block are now wrapped and two are not, which is the least good state.
* **Two owner calls carried from round 11 and W75, untouched**: `chifree-clearing-note.md`'s
  rewrite, and `mc-design.md`'s third `q`.
* **`w75-house-note.md` §5.2's class-five mod-16 kit** is untouched by the join lane and carries
  forward intact, including its two scoping corrections (state it at a parameter `m`, not at 16;
  and the class-five argument as written does not transfer to the ENGINE's frames).

### 4.5  One process item, earned twice

**Run the staleness check before the application pass, not after.**  This wave applied round 12
and then discovered, in round 13, that two of the items it had just applied were refuted by
work merged before round 12 was written - so the lane had to amend its own annotations in the
same session.  The checklist item that catches this is cheap: at the start of an application
pass, `git log --oneline <the-reported-round's-base>..HEAD` and read the sibling lanes' landings
before touching anything.  Round 12's own §4.2(d) shows the lane already thinks this way about
line drift; it needs to think that way about content.

## 5.  Verification record

* Lane `claude/w76-house`, base `97d51e93`.  Four commits, all path-limited.  **Not pushed.**
* **No `lake` command was run**; `scripts/check_dyadic.sh` and `scripts/check_axioms.sh` were
  not run.
* `scripts/mirror.sh sweep` once at lane start (5873 artifacts), then `scripts/mirror.sh check`
  on every edited module after every edit.  **All five modules `OK`**, with no errors and no
  warnings.
* **Comment-only discipline, verified mechanically.**  Every edited `.lean` file was
  comment-stripped (nested block comments and line comments removed, then whitespace collapsed)
  and compared against its content at the lane base.  **All five print IDENTICAL**, so no
  statement, term, binder, name or proof changed anywhere in this lane, including the two
  rewrapped definition signatures:

  ```
  GQ2/Dyadic/Instances/EvenStratumRowFrame.lean   IDENTICAL
  GQ2/Dyadic/Instances/EvenUnramified.lean        IDENTICAL
  GQ2/Dyadic/SqCore/GradedDeltaFunctionals.lean   IDENTICAL
  GQ2/Dyadic/SqCore/GradedUniformJoin.lean        IDENTICAL
  GQ2/Dyadic/SqCore/GradedUniformTower.lean       IDENTICAL
  ```

* **The axiom ledger was exercised without `lake`**: `scripts/mirror.sh check
  GQ2/AxiomLedger.lean` elaborates it against the mirror and prints its whole report - 32488
  tracked declarations, gap map 0, ALARM 0, 0 terminal violations.
* No line over 100 characters was added to any Lean file, and two inherited over-long signature
  lines were rewrapped.  No em-dash was added to any prose.
* `GQ2.lean` was not touched; nothing under `GQ2/Roe/` was touched (plan A6); neither
  `SqCore/GradedJoinBase.lean` nor `GQ2/Dyadic/GeneralCertificates.lean` was created or touched.

## 6.  Files edited

**Lean (comment-only, 5):** `Dyadic/Instances/EvenStratumRowFrame.lean`,
`Dyadic/Instances/EvenUnramified.lean`, `Dyadic/SqCore/GradedDeltaFunctionals.lean`,
`Dyadic/SqCore/GradedUniformJoin.lean`, `Dyadic/SqCore/GradedUniformTower.lean`.

**Docs (8):** `w76-house-note.md` (new); `w74-critical-path.md`, `w74-engine-note.md`,
`w74-even-note.md`, `w74-func-note.md`, `w74-house-note.md`, `w75-house-note.md`,
`w75-join-note.md`, `w75-state-note.md`.

## 7.  For the wave-77 queue

Section 4 is the queue.  In one line each, in priority order:

1. **`GJoinBase h`** via the relator's degree-3 leading form, `[[c, x₁], x₁] ∈ [Λ²V, far]` -
   named lemma, written-out route, closes a two-wave-old interface (§4.1).
2. **The `α` pin**, `range chiCycKTwo = imChiN α` per field - on two lists, schedule once
   (§4.2 item 3 = §4.3 item 1).
3. **`GTowerKnobRealizable h`** - untouched for two waves; start from the ENGINE note's mod-2
   far-slot route and `gJoin_chi_far` (§4.1).
4. **`GJoinSeparationAll h`** - bookkeeping, two scoped routes, lane-sized (§4.1).
5. **Round 13's reported items**: §3.2's three headline-versus-statement sites are applied here,
   so what carries is only the owner calls of §4.4.
6. **Round 14's checklist**: keep all six items of round 12 plus §4.5's new one - run the
   staleness check *before* the application pass.  The interface-blindness item has now produced
   the headline finding two rounds running and should be run at every wave where two lanes state
   interfaces for each other.
