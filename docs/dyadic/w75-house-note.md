# W75-HOUSE: the inherited state salvaged, round 11 applied, and watch round 12

Lane `claude/w75-house`, base `f0a71688`, cache at `4342` jobs (umbrella green).
Verification of record: `scripts/mirror.sh` (sweep, check).  **No `lake` command was run**, and
`check_dyadic.sh` was not run either (its default path reaches `lake env lean` twice through
`check_axioms.sh`).

**This lane is a relaunch.**  A predecessor banked one commit (`47094a9c`, ticket 1) and stalled
with seven files modified and unverified in the worktree.  §1 accounts for every one of them.

## Headline

**Ticket 0 (the inherited state).**  All seven inherited files are **kept**, six of them
unchanged in substance and one with an in-place rewrite reverted to an annotation.  Nothing was
blanket-committed and nothing was blanket-reverted.  Four defects were found in the inherited
edits and fixed before committing: one over-long Lean line, one citation that lands a line past
what it is cited for, one finding applied in a form weaker than the tree supports, and one
in-place correction that silently desynchronised two verbatim wave-74 quotations.  §1.

**Ticket 1 (the refuted-condition trail).**  The predecessor annotated seven sites; four more
were found by the tree-wide grep, and three of them carry the sweep's real result:

> **The correct diagnosis was in the tree at wave 70 and was lost.**
> `w70-cfour-note.md` §4's paragraph "What `K` misses" says the knob subgroup misses `V^{[4]}`,
> represented by `σ^{[4]}` and `x₀^{[4]}`, and wave 71 §2 explicitly endorsed it as "not wrong
> as a statement about the knob subgroup" while setting it aside as not about the leftover.
> Wave 73's `cfourCmp_residual_of_span` then demanded of the knob subgroup exactly what those
> two notes say it misses, and priced the whole difficulty at the triple brackets.  Wave 74
> refuted it with `(levelMk σ)⁴`, the element wave 70 named.  Nothing between waves 71 and 74
> noticed.

**Ticket 2 (round 11's 29 findings).**  All 29 verified against the Lean and applied, except the
one that is Lean source and stays reported (§4.5's third).  **Three findings needed correcting
before they could be applied** and one is applied as an annotation rather than as the rewrite it
asked for; §3.2.  Four second sites were found by grepping the corrected phrases, two of them
created by wave 74 *after* round 11 named the other five.  §4.4(a) turned out to have been
**decided by the owner inside wave 74** (`2c8af4bd`), so the prose that moved is the reason, not
the claim.

**Ticket 3 (watch round 12).**  Wave-74 landings.  The new interface-blindness item is where the
round pays for itself:

> **`GTowerDefectVanishing` cannot be supplied by the delta-functionals, and the obstruction is
> a theorem in the FUNC lane's own file.**  The ENGINE's admissible tower set
> (`gTowerXLetters`) contains the cleared `x₁`-letter, and `gDelta_x1_tower_dvd`
> (`GradedDeltaFunctionals.lean:845`) proves that **no** functional sees the `x₁` tower.  So the
> functionals can kill the two Eichler-tower coefficients of the defect and provably cannot kill
> the third.  `w74-engine-note.md`'s W75 item 3, "`GTowerDefectVanishing h` **from the FUNC
> lane's delta-functionals**", is not achievable as stated.  §4.1(a).

> **And the refutation does not touch the ENGINE route, for a reason neither note gives.**
> `gDelta_cfourCmp_span_hyp_false`'s witness is `(levelMk σ)⁴`, whose row vector is `(4c₀, 4)`,
> so it is **not** exactly row-trivial; σ is not one of the ENGINE's cleared letters, and its
> tower sits in the *complement* `gTowerTowXW`.  Every ENGINE hypothesis quantifies only over
> row-trivial elements, and the defect provably has no complement-tower coefficients
> (`gTower_frame_row_nuLam`, `gTower_frame_row_nu`).  The two lanes are consistent, and the
> reason is structural, not a coincidence.  §4.1(b).

**Ticket 4 (report-only).**  The torsion gap is **not** the blocker the FUNC note prices it as,
and the mod-16 kit is the wrong shape for the assembly that needs it.  Two W76 tickets in §5,
with a third that the two of them expose.

---

## 1.  Ticket 0: every inherited file, accounted for

`47094a9c` (banked by the predecessor) is ticket 1 and is kept as is; §2 extends it.

The seven uncommitted files were **all** verified before use: each of the three Lean files is
IDENTICAL to its content at the lane base `f0a71688` under a comment-stripped diff (block
comments, docstrings and line comments removed, blank lines dropped), and each passes
`scripts/mirror.sh check`.  Every finding the edits implement was re-derived against the Lean.

| inherited file | disposition | why |
| --- | --- | --- |
| `SqCore/GradedClassFiveJoin.lean` | **committed** (`aa8b9f65`) | round 11 §4.2(a),(b),(c),(f),(j).  All five verified.  §4.2(c)'s applied text is *better* than the finding; see §3.2. |
| `SqCore/GradedClassFourCompose.lean` | **committed, amended** (`aa8b9f65`) | round 11 §4.2(d),(e),(g),(h),(i),(k).  Amended twice: one added line was 108 characters, and the `LamFrames.lean:301` citation is one line past the definition it cites (`:300`). |
| `Instances/EvenStratumShift.lean` | **committed, amended** (`aa8b9f65`) | round 11 §4.3(a)-(g).  Amended once: §4.3(f)'s "literal shift" survived inside the very docstring §4.3(a)'s fix rewrote, so the fix was half-applied within one declaration. |
| `docs/dyadic/w72-stratum-note.md` | **committed** (`aa8b9f65`) | §4.3(e), two sites, both verified. |
| `docs/dyadic/w73-five-note.md` | **committed** (`aa8b9f65`) | §4.2(a) second site, verified against `GradedLimit.lean:236` and `GradedGammaFourFive.lean:726`. |
| `docs/dyadic/w73-knob-note.md` | **committed, amended** (`aa8b9f65`) | §4.2(e),(g) second sites.  Same `:301` → `:300` amendment. |
| `docs/dyadic/w73-stratum-note.md` | **committed, one hunk REVERTED to an annotation** (`aa8b9f65`) | §4.3(b),(e),(g) kept; §4.3(h) reverted and re-applied as an annotation.  See below. |

**The one revert, and it is the inherited edits' only real defect.**  Round 11 §4.3(h) asks for
the shortened `evenRawShiftSpan_eq_zLayer` in `w73-stratum-note.md` to be corrected to
`evenRawShiftSpan_eq_zLayer_of_pureSquares`.  The predecessor corrected it in place.  But wave 74
**quotes that sentence verbatim, short name and all**, at `EvenStratumRowFrame.lean:864` and
`docs/dyadic/w74-even-note.md:139`, in both cases immediately above a correct use of the full
name.  An in-place rewrite makes two shipped quotations misquote their source.  So the sentence
is restored and the correction sits under it as a `[W75-HOUSE]` block naming both quoting sites,
and the shortened name is fixed at its actual origin, `StageAbstractionEvenRawSpan.lean`'s
Contents list, which is where round 11 said it came from.

## 2.  Ticket 1: the refuted-condition trail

The subject was grepped tree-wide: `cfourCmp_residual_of_span` / `cfourCmp_supply_of_span`,
`gDelta_cfourCmp_span_hyp_false`, `cfourDefCore`, the "one condition" prose, the `x₁`-bracket
phrasing, and the `cfiveJoin` join prose.

**Covered by the predecessor (`47094a9c`), all verified as correct here:**
`GradedClassFiveJoin.lean` module docstring; `GradedClassFourCompose.lean` at five sites (module
§0, the honesty markers, `cfourCmp_zLayer_le_triple`, `cfourCmp_residual_of_span`,
`cfourCmp_supply_of_span`); `owner-items-2026-08-05.md`'s wave-73 block; `w72-defects-note.md` §4;
`w72-five-note.md` queue item 1; `w73-five-note.md` at three sites; `w73-knob-note.md` at seven.

**Added here (`e22752e4`), four sites:**

1. **`w70-cfour-note.md` §4** gets a second banner.  The wave-71 withdrawal banner covers the
   `L₃(V)` spanning claim and the `w⁴` cancellation and leaves the fourth-power paragraph
   standing, which is exactly the half wave 74 proved.  A reader who takes the existing banner as
   covering the whole section reads the one correct paragraph as withdrawn.
2. **`w71-cfour-note.md` §2**, first bullet: "not wrong as a statement about the knob subgroup" is
   now proved, for the `σ^{[4]}` half.  This is the last place before wave 74 where the tree said
   the right thing about the fourth powers.
3. **`owner-items-2026-08-05.md`**, the **wave-72** block: "that is where class four now stands"
   of "is `cfourDefCore` a knob".  Annotated with what does *not* follow: the position has moved
   twice, and that question is **still open**, because wave 73's replacement was strictly
   stronger.  (The predecessor annotated the wave-73 block; this is the wave-72 one.)
4. **`GradedClassFourCompose.lean`, `cfourCmp_zLayer_le_triple`** (comment-only): the bundled form
   is **not** a way round the refutation.  Given `htriple`, the clauses `hbSq` and `hbPow` are
   equivalent to the bare `⁅p, q⁆² ∈ S` and `p⁴ ∈ S` - that equivalence is the first half of the
   theorem's own proof - so an all-knob subgroup meeting the three clauses here meets
   `cfourCmp_residual_of_span`'s three families too, and the same `(levelMk σ)⁴` kills it.  Worth
   saying because the sharper reduction is the obvious place a lane would look for a survivor;
   **no un-refuted restatement of the route survives in the module.**

**Deliberately not annotated.**  `w71-cfour-note.md` §4's three remaining factors are about
whether particular *elements* are reachable, not about a subgroup containing whole families; the
refutation does not reach them, and annotating them would over-claim.

## 3.  Ticket 2: round 11's 29 findings

### 3.1  Where they landed

| source | findings | applied to | commit |
| --- | --- | --- | --- |
| §4.2(a),(b),(c),(f),(j) | 5 | `SqCore/GradedClassFiveJoin.lean` | `aa8b9f65` |
| §4.2(d),(e),(g),(h),(i),(k) | 6 | `SqCore/GradedClassFourCompose.lean` | `aa8b9f65` |
| §4.3(a)-(g) | 7 | `Instances/EvenStratumShift.lean` | `aa8b9f65` |
| §4.2(a),(e),(g); §4.3(b),(e),(g),(h) second sites | (same 7) | the three w7x lane notes | `aa8b9f65` |
| §4.4(a)-(g) | 7 | `scripts/check_ledger.sh`, `scripts/check_dyadic.sh`, `w73-house-note.md` | `0012ce42` |
| §4.5 first two | 2 | `GQ2/AxiomLedger.lean`, `StageAbstractionEvenRawSpan.lean` | `0012ce42` |
| §4.5 third | 1 | **reported only** (Lean source: the unused `private abbrev evenStratumPlane`, round 11's `EvenStratumShift.lean:416`, now `:423`) | - |

### 3.2  Corrections to the findings themselves

* **§4.2(c)'s proposed correction is incomplete.**  It names only §6's
  `cfiveJoin_family_five_of_span` and `..._six_of_span` as the consumers of
  `cfiveJoin_ad_far_mem`.  The **direct** consumers are `cfiveJoin_ad_far_lambdaTwo` (`:164`) and
  §4's `cfiveJoin_ad_far_all` (`:285`); the §6 pair reaches it only through the former.  Applied
  in the fuller form.
* **§4.2(e)'s second citation does not resolve.**  `LamFrames.lean:301` is the second line of the
  cleared-`u` docstring; the two definitions are at `:293` (`V_j = v_j·w^{−ν'(v_j)}`) and `:300`
  (`U_j = w^{−ν'(u_j)}·u_j`).  Corrected in both the module and `w73-knob-note.md`.
* **§4.5's second finding under-reports by three.**  `StageAbstractionEvenRawSpan.lean`'s
  Contents list has **four** defects, not one: seven items against six sections and one section
  high from §3 onwards (reported); "five exact coordinate rows" where §5's own subheading and its
  six `evenRawDepthShiftHom_*_apply` theorems say **six**; the shortened
  `evenRawShiftSpan_eq_zLayer` of §4.3(h); and a "`Tuple`-level bridge to the generic
  `rawDefectReachable`" that **has never been in this file** - `rawDefectReachable` occurs in it
  exactly once, in that Contents line, and the bridge is §1 of the sibling
  `StageAbstractionEvenRawSpanStep.lean`.
* **§4.2(a)'s quotation is exact, against my first reading.**  I initially took "No class-four
  witness is presupposed: the base dressing is existentially quantified" for a paraphrase of the
  module header, which says something else; it is verbatim from `cfiveKnob_supply_of_reach`'s own
  docstring (`GradedGammaFourFive.lean:726`).  Recorded so round 13 does not re-derive it.
* **§4.4(b)'s Route D citation is off by one**: the Route D gate item is `:469`, not `:468`
  (`:468` is the preceding line, "record the output in the commit message").  `:489` for Route R's
  item 4 is exact.

### 3.3  §4.4(a): decided inside wave 74, by the owner, so the *reason* is what moved

The fixture hook was closed at `2c8af4bd` (2026-08-15 02:19:33), **1 h 43 min** after the
wave-74 house merge `0933f189` and 20 minutes before the wave's own owner memo `f0a71688`:
a clean fixture parse now exits **3**, which D6 treats as a failure.  So the sentence round 11
attacked is now true - but not for the reason it gives.  What moved:

* `check_ledger.sh`'s OVERRIDES block now states the exit-3 mechanism, records that the claim was
  false as shipped, and carries the standing lesson (the skip is visible in the transcript, not in
  the exit code, and the exit code is what D6 reads).
* `check_dyadic.sh`'s header **and** its D6 block now name `GQ2_LEDGER_FIXTURE` as an inherited
  override, with the same warning.
* `w73-house-note.md`'s "it can never be used to make the gate appear to pass" carries its
  retraction, with round 11's proposed fifth checklist item attached.
* `w74-house-note.md`'s wave-75 queue item 2 ("Decide the fixture hook") is struck through as
  already decided, in the wave that wrote it (`f03b6d1c`).  This one is round 12, applied here
  because it is the second site of a ticket-2 edit.

### 3.4  Second sites found by grepping the fixes

* **`GQ2/Foundations.lean:11-13`** lists nine of the eleven axioms (B5-K and B10-K missing) and
  calls them "the nine axioms".  Same AX3/AX4 staleness as §4.5's first finding, one file over,
  in a shipped module docstring.  Fixed.
* **`docs/dyadic/w74-even-note.md:242`** is a **sixth** "`StageAbstractionEvenRawSpan.lean` §0",
  created by wave 74 one wave after round 11 named the other five.  Fixed.
* The two verbatim quotations of `w73-stratum-note.md`'s prediction (§1 above): left alone as
  quotations, with the divergence recorded at both ends.

## 4.  Ticket 3: watch round 12

Scope: `GradedUniformTower.lean`, `GradedDeltaFunctionals.lean`, `EvenStratumRowFrame.lean`,
`w74-critical-path.md`, the four w74 lane notes, and the two ledger-gate scripts after
`2c8af4bd`.  The standing checklist was run in full, together with round 11's proposed fifth item
(a "can never" claim reads like an "unconditionally") and the new interface-blindness item.

**Findings are REPORTED, not applied**, which is the campaign's rhythm.  The one exception is
§3.3's last bullet, which is the second half of a ticket-2 edit.

### 4.1  Interface blindness: `GTowerDefectVanishing` against `GDeltaDefectVanishing`

Neither module imports the other (`GradedUniformTower` imports the three wave-70-to-73 graded
modules; `GradedDeltaFunctionals` imports `GradedClassFourCompose`, `GradedLimit`,
`Roe.CrossedDerivation`, `PropOneOne`), and both are registered in `GQ2.lean` (`:774`, `:775`),
so a join module can import both without a cycle.  Every claim either note makes about the other
module was checked against that module's Lean.

**(a) HIGH.  `GTowerDefectVanishing` is not obtainable from the delta-functionals, and the
obstruction is a theorem in the FUNC lane's own file.**
`w74-engine-note.md:147`: "**`GTowerDefectVanishing h`** from the FUNC lane's delta-functionals
(his Lemma 4: `Delta o delta = 0`, `Im delta = cap ker Delta`)".  Second site
`w74-engine-note.md:97`, which calls it "the FUNC-lane interface", and third site
`GradedUniformTower.lean:1562`, "The interface for the sibling FUNC lane".

`GTowerDefectVanishing` (`:1648`) concludes
`levelMk (k+2) (sqRelWord …) ∈ Subgroup.closure (gTowerKnobSet h nu' k)` - the **knob span
alone**, no tower coefficients.  By `gTower_defect_reach_of_base` the defect already lies in
`gTowerReach` = closure(knobs ∪ **admissible** towers), so the Prop is exactly "the admissible
tower coefficients vanish".  The admissible towers are the towers of
`gTowerXLetters = {gTowerXOne} ∪ range (sqEichU) ∪ range (sqEichV)` (`:861`), and `gTowerXOne` is
the cleared `x₁`-letter.  `gDelta_x1_tower_dvd` (`GradedDeltaFunctionals.lean:845`, and the
module's own §4 summary at `:67-71`) proves `2^{m+2} ∣ gDelta h c (x₁^{2^m})` for every row `c`:
**no functional sees the `x₁` tower.**  For the *cleared* letter it looks worse still, though this
next step is a computation from committed lemmas and not a committed statement:
`χ_sq (gTowerXOne) = Y·X^{-2} = -1` exactly (`YvalUnit_eq_neg_sq`, `Roe/ChiR.lean:110`), and
`gDelta_pow` reads the tower through the geometric sum `N_{2^m}(-1)`, which is `0` for every
`m ≥ 1`.  A lane should check that before relying on it either way.

So the functionals can kill the two Eichler-tower coefficients of the defect and **provably
cannot kill the third**.  Whatever supplies `GTowerDefectVanishing`, it is not the functionals
alone, and the `x₁`-slot scarcity that waves 69-73 kept re-discovering is the same obstruction
in its third costume.  ⚠ For the join lane, not for a house lane: either
`GTowerDefectVanishing` is weakened to allow an `x₁`-tower coefficient (with
`GTowerKnobRealizable` extended to realize it - note `gTowerKnobSet`'s second clause, the
`x₁`-slot bundle, is the one knob that produces tower-type elements), or the `x₁`-tower
coefficient is killed structurally rather than functionally.

**(b) HIGH, and it is the good news.  The wave-74 refutation does not touch the ENGINE route,
and neither note says why.**  `gDelta_cfourCmp_span_hyp_false` takes its witness out of the
fourth-power clause as `(levelMk σ)⁴`.  Its row vector is `(4c₀, 4)` (λ(σ) = c₀ odd, ν'(σ) = 1),
so it is **not exactly row-trivial**; σ is not one of the ENGINE's cleared letters, and the σ
tower lies in the *complement* `gTowerTowXW` ("the complement letters are `x₀` and the pivot `w`,
uniformly in the level", `GradedUniformTower.lean` §1).  Every ENGINE hypothesis -
`GTowerLayerReach` (`:1081`), `GTowerDefectVanishing` (`:1648`), `GTowerKnobRealizable` (`:1664`)
- quantifies only over exactly row-trivial data, and the defect provably has no complement-tower
coefficients (`gTower_frame_row_nuLam` `:1587`, `gTower_frame_row_nu`).  The two lanes' results
are consistent for a structural reason, and stating it is worth a paragraph in whichever note the
join lane writes: **the refutation kills the wave-73 route because that route quantified over all
of `Q₄`; the ENGINE route never leaves the row kernel.**

**(c) MEDIUM.  `w74-func-note.md` §4.3(2) mis-states the ENGINE's shape, in the one place it
names it.**  "The Lemma 3 analogue (open; the ENGINE-shaped statement): the functional-invisible
part of the layer is spanned by knobs - `zLayer(k) ∩ (all rows' kernels) <= knob subgroup`."  The
ENGINE's statement is `GTowerLayerReach h nu' k`, whose right-hand side is `gTowerReach` =
**knobs ∪ admissible towers**, not the knob subgroup; and it is open only at `k = 2`, because
`gTower_layerReach_step` (`:1538`) inducts `k → k+1` and `gTower_layerReach_of_base` (`:1549`)
closes every `k ≥ 2` from the base.  The next sentence of the same bullet ("Equivalently: the
knob subgroup and the towers together span the layer") is right, so the bullet contradicts itself
one line apart.  Net effect: the open item is **one base case with a larger target**, not a
uniform statement about a smaller one.

**(d) MEDIUM.  `w74-func-note.md` §4.3(3)'s "all committed plumbing" is not committed.**  "1 + 2
give `cfourDefCore ∈ knobs`, hence `CfourCmpResidual h` through
`cfourCmp_residual_of_core_vanish`-style composition, hence `SqClassClearingSupply h 4` - all
committed plumbing."  `cfourCmp_residual_of_core_vanish` (`GradedClassFourCompose.lean:601`)
takes `cfourDefCore nu' j = 1`, the **vanishing** of the core defect, not its membership in the
knob span.  There is no committed theorem from "the core defect is a knob" to
`CfourCmpResidual h`: the module's three routes are `_of_span` (refuted), `_of_core_vanish`
(vanishing) and `_of_residual`.  The step the bullet needs is the ENGINE's
`GTowerKnobRealizable`, which is explicitly **not proved** in that lane.  So step 3 of the
corrected shape carries an unproved interface, and the note prices it at zero.

**(e) MEDIUM.  The two Props' dressing conditions are three different conditions, and the
proposed join hypothesis matches none of them.**  `GTowerDefectVanishing` binds
`nuLam h (a i) = 1`, `nu' (a i) = 1`, `SqModTwoIndep`.  `GDeltaDefectVanishing`
(`GradedDeltaFunctionals.lean:1005`) binds `chiSq h (a i) = 1` **exactly**.
`w74-func-note.md` §4.4 proposes joining "at the hypothesis 'dressing slots mod-8 chi-trivial'".
The three are ordered strictly: `chiSq = 1` ⟹ mod-8 chi-trivial ⟹ (nothing), while the ENGINE's
binder gives only `chiSq = ±1` (`gDelta_chiSq_of_nuLam`, `:1190`), and `-1` is not `1 mod 8`.
Two consequences the join lane should have in front of it:

* **Joining at mod-8 proves something strictly weaker than `GTowerDefectVanishing`**, so
  `gTower_clear_step` (`:1689`) cannot consume it as stated.  ⚠ Threading a mod-8 invariant
  through the recursion is a **statement change** to `GTowerDefectVanishing` and
  `gTower_clear_step`; reported, not made.
* **`GDeltaDefectVanishing` as committed serves only the base of the recursion.**
  `gTower_supply_of_vanishing` (`:1714`) starts from `sqClassThree_supply`, whose witness is
  `bridgeTuple` with `chiSq = 1` exactly (`gDelta_chiSq_bridgeTuple`, `:927`); each clearing step
  multiplies by `d i ∈ γ_k`, which is only `1 mod 8` (`gDelta_chi_gammaTwo_dvd`, `:1448`).  So the
  exact hypothesis fails from the first correction onwards.  The applicable committed statement is
  `gDelta_relWord_dvd_of_chi_mod` (`:1464`), which is a divisibility and not a vanishing.

**(f) LOW.  "This side's sharpest form" is the wrong ordering.**  `w74-func-note.md:239`.
`GDeltaDefectVanishing`'s hypothesis (`chiSq = 1` exactly) is strictly stronger than the mod-8
one and its conclusion (`= 0`) strictly stronger than `2^3 ∣ ·`; the two are **incomparable**, and
for the assembly the mod-8 form is the applicable one.  "Sharpest" invites the join lane to reach
for the wrong statement.  The same sentence's "could not be shape-matched without importing the
sibling" is **correct**: `gTowerKnobSet` lives in the ENGINE file.

**(g) LOW.  A section reference that is a queue item.**  `GradedUniformTower.lean:1662` cites
`docs/dyadic/w73-knob-note.md` §"the multi-handle composition lemma".  That is item 2 of that
note's §9 wave-74 queue, not a section.  The content is exactly as described.

### 4.2  Intra-wave staleness

**(a) MEDIUM, and it is round 11 §4.1(c) recurring one wave later.**  All three module-carrying
wave-74 lanes reported or implied their module unregistered, and all three were registered within
minutes: `w74-even-note.md` item 1 ("is unwired") against `a1579dcc`, **1 min 51 s**;
`w74-engine-note.md:159` ("`GQ2.lean` untouched per protocol") against `1bf8c40a`, **7 min 5 s**;
`w74-func-note.md` says nothing, and `1ef86cea` landed **3 min 41 s** after `dfcadf5b`.  Round 11
annotated the three wave-73 notes for exactly this and proposed nothing to stop it recurring; it
recurred.  The lane-level and orchestrator-level behaviour is right; only the annotation is
missing, again.

**(b) MEDIUM.  `EvenUnramified.lean:70` and `:395` were named by a wave-73 queue item and again
by a wave-74 queue item, and both still hedge.**  `:70` "documented false at `α = 1`", `:395`
"recorded false at `α = 1`", against `evenStratum_no_rawStageShift_one`
(`EvenStratumShift.lean:333`) for the `N` half and `evenStratumRow_no_rawStageShift_m_one`
(`EvenStratumRowFrame.lean:847`) for the `M` half, both committed.  This is the clearest instance
of round 11 §4.1(a)'s own lesson - **a queue item that no application pass owns is not applied** -
and it is now two waves old.  **Top apply-item for W76**; prose-only, two lines.

**(c) LOW.  The owner memo's wave-74 block records no ledger figure**, where the wave-73 block
records "32078 declarations, no gap-map entries, no alarms, no terminal violations".  Recomputed
here (§6): **32336 declarations, gap map 0, ALARM 0, 0 terminal violations**, a rise of 258 over
the wave.  Reported rather than added, because the owner memo's status blocks are the owner's.

**(d) Null result worth recording.**  The wave-74 line citations in `w74-func-note.md`
(`GradedClassFourCompose.lean:748` for `cfourCmp_residual_of_span`, `GradedClassFiveJoin.lean:286`
for `cfiveJoin_zLayer_le_iff`) were **exact at the wave-74 tree** and are now `:797` and `:307`
after this lane's annotations.  Ordinary drift, recorded so round 13 does not re-derive it.

### 4.3  "Can never" and "unconditionally"

**(a) MEDIUM.  An impossibility claim on a containment theorem, two sites.**
`EvenStratumRowFrame.lean:872-873`: the `Hsq` input "**cannot be obtained from the `α = 1` rows at
all**, because they emit no square"; second site `w74-even-note.md:151`, "**cannot come from the
`alpha = 1` rows at all**".  What is proved is
`evenStratumRow_sq_mem_bracketSpan_of_isShift` (`:994`): *if* `p²` is an `α = 1` shift then `p²`
lies in the bracket span - a containment, and a corollary of "every `α = 1` shift is a product of
brackets" (`:939`).  Nothing rules out a **product** of shift values equalling a square, and
`EvenRawPureSquareSpanSupply` asks for membership in a *span*, not for a row value.  The
declaration's own docstring (`:983-993`) has the safe form and even says what actually changes
("where its input could possibly come from"); the two summary sentences overstate it into an
impossibility.  The note is careful elsewhere ("proved in one direction only (`<=`)",
`w74-even-note.md` §2.1).

**(b) LOW.  "Unconditional" on a theorem with six binders.**  `w74-engine-note.md:145`: "With it,
`gTower_defect_reach_of_base` is unconditional."  It means "no longer conditional on the base
hypothesis"; the theorem retains `hsigma`, `hx0`, `2 ≤ k`, the two row clauses and the relator
clause.  Exactly the shape round 11 asked the next round to read twice.

**(c) LOW.  An unverified reduction stated as a source.**  `w74-engine-note.md:145`, same item:
`GTowerLayerReach h nu' 2` "from the committed class-four record".  The committed record
(`cfourCmp_zLayer_le_gens`) quantifies its three families over **all** of `Q₄`, while
`GTowerLayerReach` asks only about exactly row-trivial elements; the reduction therefore needs a
row-restricted form, and that restriction is precisely what keeps it clear of §4.1(b)'s
refutation.  Not wrong, but it is a construction, not a citation, and it is the wave's largest
open item.

### 4.4  What came up clean

Said in detail, because a round that reports only hits is not a check.

* **Headline-versus-statement on the ENGINE's ⭐⭐⭐ results: clean, every one I read by hand.**
  `gTower_decomp` (`:298`) really is an **exact** factorization `g = d · x₀^{λ(g)} · w^{ν'(g)}`
  with `d` in the same `γ_k` and exactly row-trivial, not a factorization modulo `γ_{k+1}`;
  `gTower_engine_bracket` (`:408`) and `gTower_engine_bundle` (`:490`) really are equalities in
  `Q_{k+3}`, i.e. the headline's "mod `γ_{k+3}`", and really are stated over an arbitrary
  topological group with `2 ≤ k`; `gTower_layerReach_of_base` (`:1549`) really does close every
  `k ≥ 2` from `k = 2`.
* **Hypothesis satisfiability, including at other layers: clean, and this is the round's
  strongest positive.**  Neither ENGINE interface is refuted by wave 74's own refutation, for the
  row-triviality reason of §4.1(b), and `GTowerLayerReach`'s target includes the admissible
  towers, so it is not the refuted span statement one class up.  Separately, the only candidate
  survivor of the refuted route - the bundled hypothesis set of `cfourCmp_zLayer_le_triple` - is
  **equivalent** to the bare families given the triple family, so it is refuted too (§2, item 4).
* **The docstring-on-the-wrong-declaration check: clean** on all three wave-74 modules.  Every
  ⭐⭐⭐ docstring sits on the declaration its headline names: eight in
  `GradedDeltaFunctionals.lean`, seven in `GradedUniformTower.lean`, and **none** in
  `EvenStratumRowFrame.lean`, which is unusual for the campaign but is not a defect.
* **Both ledger-gate scripts after `2c8af4bd`: clean as behaviour.**  `bash -n` clean on both;
  the exit-3 branch is placed after the `fail` test and before the success line, so a fixture that
  *fails* still exits 1 and a fixture that parses exits 3; D6's `if` treats both as failure.  The
  only defects were the prose ones of §3.3.
* **The wave-74 lane bases: clean.**  All four notes claim base `4fff1592`, and it is an ancestor
  of the first commit of all four lane branches.
* **Cross-module claims other than §4.1's: clean.**  Every declaration name either note uses for
  the other module exists in that module, with the shapes as described; the mismatches are of
  content, not of naming.

### 4.5  Counts and citations

**(a) MEDIUM-LOW.  A module's own summary cites two declarations that do not exist, in the file
that declares them.**  `GradedDeltaFunctionals.lean:64` cites `gDelta_handle_tower` and `:65`
cites `gDelta_handle_tower_notMem`; the declarations are `gDelta_handleU_tower` (`:747`) and
`gDelta_handleU_tower_notMem` (`:804`).  The neighbouring `gDelta_sigma_tower` (`:722`),
`gDelta_x0_tower` (`:734`) and their `_notMem` corollaries (`:768`, `:786`) all resolve exactly,
and the lane note has the right name (`w74-func-note.md:223`), so this is the module summary
alone.  The `U`/`V` asymmetry is worth a glance while fixing it: there is a `handleU` tower and
no `handleV` one, which the summary's unsuffixed name papers over.

**(b) MEDIUM.  The dependency memo's `SqCore/Graded*` count is the wave's own two landings too
high, in a memo whose preamble says every number is as-of `4fff1592`.**
`w74-critical-path.md:134` ("the whole `SqCore/Graded*` family (**68** modules)") and second site
`w74-house-note.md:79` ("any `SqCore/Graded*` module (68 of them)").  Counted from the git tree:
`4fff1592` has **66**, `f0a71688` has 68.  The two that make the difference are the wave's own
`GradedUniformTower.lean` and `GradedDeltaFunctionals.lean`, which landed **after** the house
lane's merge (`0933f189` 00:36:45, against `1bf8c40a` 01:02:13 and `1ef86cea` 01:16:09), so at
the memo's stated tree they did not exist on `dyadic` at all.  The memo's own preamble says
"Everything numeric below was recounted at this tree and is stated as-of `4fff1592`."  ⚠ The
*conclusion* is unaffected and gets stronger with the correction: 66 then, 68 now, and **zero**
of them in the closure either way.

**(c) MEDIUM-LOW.  Two denominators for "GQ2 modules" in one wave, differing by one, neither
stating its convention.**  `w74-critical-path.md:130` and `w74-house-note.md:77` say "427 of
930"; `w74-house-note.md:246` says "929 physical, 843 listed, 928 reachable, 1 unreachable",
recounted at the same commit.  Both are right: **929 excludes `GQ2.lean` itself and 930 includes
it.**  A reader reconciling the two documents cannot tell.  Recomputed here at `f0a71688` plus
this lane: 932 excluding `GQ2.lean`, 933 including, 932 reachable from `GQ2.lean`, and the single
unreachable module is `GQ2.AxiomLedger`, which is deliberate.

**Counts that verify exactly:**

* **`GQ2.Dyadic.Main`'s closure is 427**, recomputed by walking the `import` graph.  Nothing
  matching `EvenStratum*`, `EvenAlphaOne` or `NFrameAlphaOne` is in it, and **no
  `SqCore/Graded*` module** is in it, exactly as `w74-critical-path.md` §2.1 says.

**Counts, independently recounted at this tree:**

* `GradedUniformTower.lean`: **94 declarations, 94 `#print axioms`**, matching
  `w74-engine-note.md:4`'s "94 declarations, every one pinned" exactly.
* `GradedDeltaFunctionals.lean`: **1749 lines** and **103 `#print axioms`**, matching
  `w74-func-note.md:212-213` exactly ("1749 lines, 105 declarations, 103 axiom pins"); the two
  unpinned declarations and the two subset prints are as the note describes.
* `EvenStratumRowFrame.lean`: **1077 lines**; the pin block runs past the file's own declaration
  count because it re-pins comparison statements from other modules, which is the shape
  `w74-even-note.md:194-196` describes ("all 46 named public declarations ... together with
  eight ...").

## 5.  Ticket 4: the FUNC handoff's two loose ends, scoped for W76

Both come from `w74-func-note.md` §4.4.  **Nothing was built.**

### 5.1  The torsion gap: smaller than advertised, and pointed the wrong way

**What exists.**  `gDelta_chiSq_sq_of_nuLam` and `gDelta_chiSq_of_nuLam`
(`GradedDeltaFunctionals.lean:1190`): a `λ`-trivial dressing slot has `χ_sq = ±1`.
`GDeltaDefectVanishing h` (`:1005`) with `gDeltaDefectVanishing_holds` (`:1012`): the `+1` branch,
proved outright.  `gDelta_relWord_dvd_of_chi_mod` (`:1464`): the mod-8 branch, as a
`2^3`-divisibility rather than a vanishing.  `gDelta_chi_gammaTwo_dvd` (`:1448`) and
`gDelta_chiSq_bridgeTuple` (`:927`) are what put the committed calculus inside the mod-8 branch.

**What is missing, stated exactly.**  The master kill `gDelta_relWord_of_chiFrame` is proved at
the one frame datum `sqMark SvalUnit rootXUnit YvalUnit`.  The `-1` branch needs the same
identity at the sign-twisted datum, which is a finite check of the three defining relations
(`Sval_mul_denom`, `rootX_isRoot`, `Yval_eq`) at the twisted values, plus a
`GDeltaDefectVanishing`-shaped Prop whose hypothesis is `∀ i, χ_sq (a i) = 1 ∨ χ_sq (a i) = -1`.

**But the gap is not on the campaign's path, and the FUNC note does not say so.**  The assembly
that consumes this is `gTower_supply_of_vanishing`, whose recursion starts at `bridgeTuple`
(`χ_sq = 1` exactly) and multiplies by `γ_k`-corrections (`χ_sq ≡ 1 mod 8`).  Every frame it ever
holds is therefore in the mod-8 branch, and `-1 ≢ 1 (mod 8)`: **the `-1` branch never arises in
the recursion.**  What *does* bite is the mismatch of §4.1(e): the recursion leaves the exact `+1`
class after one step, so `GDeltaDefectVanishing` covers only the base.

**W76 ticket, and it is a different ticket from the one §4.4 names.**  Package the mod-8 statement
as the interface Prop, and thread the mod-8 chi invariant through the clearing recursion so the
ENGINE can consume it.  Where it would live: a new `GQ2/Dyadic/SqCore/GradedDeltaTowerJoin.lean`
importing both wave-74 modules (no cycle: neither imports the other), carrying (i) the mod-8
invariant of the accumulated dressing as a lemma, and (ii) a restatement of
`GTowerDefectVanishing` with a mod-8 chi clause.  ⚠ (ii) changes a committed statement in
`GradedUniformTower.lean`, so it is an owner call whether the new Prop replaces it or sits beside
it.  The sign-twisted datum check is then **optional**, needed only if a lane wants
`GTowerDefectVanishing` at its present full binder.

### 5.2  The class-five mod-16 kit: the wrong shape for the assembly that needs it

**What exists.**  The whole kit at `2^3`: `gDelta_chi_gammaTwo_dvd` (`γ₂ ⟹ 1 mod 8`),
`gDelta_relWord_dvd_of_chi_mod` (`:1464`), the perturbed Fox coefficient bounds
`gDelta_csR_dvd`/`gDelta_cxR_dvd`/`gDelta_cyR_dvd`, the tower formulas `gDelta_sigma_tower`
(`:722`) and its `notMem` corollaries, `gDelta_sigma_tower_not_reached` (`:1519`),
`gDelta_coreLift_eq` with `v₂(S − X) = 3` exactly, and `gDelta_coreLift_dvd_of_even` (`:1149`)
sharpening to `2^4` in one case.

**What is missing.**  The `γ₃` shadow (`γ₃ ⟹ 1 mod 16`, which is `twoCentralSeries_units_le 3`),
the `2^4` variant of `gDelta_relWord_dvd_of_chi_mod`, the class-five analogue of
`gDelta_sigma_tower_not_reached` at the tower class `σ^{2^3}`, and finally the class-five
analogue of `gDelta_cfourCmp_span_hyp_false` against `cfiveJoin_zLayer_le_iff`'s defect clause -
which is what would turn `w74-func-note.md` §4.2 from analysis into a theorem and close
`w73-five-note.md`'s open defect.

**Two scoping corrections to "one congruence pass".**

1. **State it at a parameter `m`, not at 16.**  The ENGINE's assembly is uniform in the class, so
   supplying it from the functionals needs the bound at every level, not at one more level.  The
   proofs are already parameter-shaped (`gDelta_normSum_unit` takes the exponent); it is the
   `2^3` literals in the relator-level statements that are not.
2. **The class-five argument as written does not transfer to the ENGINE's frames.**
   `w74-func-note.md` §4.2 gets `2^4` from "class-five corrections are `γ₃`-valued", which is the
   wave-72/73 class-five *route*.  Inside `gTower_supply_of_vanishing` the accumulated dressing
   still carries the class-four `γ₂` correction, so its shadow is capped at mod 8 at **every**
   class.  So there are two different targets here - the standalone class-five refutation, and the
   uniform bound the assembly needs - and §4.4 lists one.

Where either would live: alongside §5.1's join module, or as a `GradedDeltaFive.lean` sibling.
⚠ Adding declarations to `GradedDeltaFunctionals.lean` itself is a code lane's call, not a house
lane's.

### 5.3  The third loose end the first two expose

§4.1(a): the cleared-`x₁` tower is invisible to every functional, so **no** congruence kit at any
`2^m` can supply `GTowerDefectVanishing` at its `x₁`-tower coefficient.  Whatever W76 does with
§5.1 and §5.2, that coefficient needs a structural argument.  This is the same `x₁` scarcity that
wave 69 found in the bundle, wave 71 re-diagnosed, wave 73 named as its one condition and wave 74
met as Labute's `k ≠ 2` exclusion; it is now visible from three sides at once and has never been
attacked directly.

## 6.  Verification record

* Lane `claude/w75-house`, base `f0a71688`, inheriting `47094a9c`.  Five further commits, all
  path-limited.  Not pushed.
* **No `lake` command was run.**  `scripts/check_dyadic.sh` was not run either.
* `scripts/mirror.sh sweep` once at lane start (5863 artifacts), then `scripts/mirror.sh check` on
  every edited module after every edit and again at the final state.  **All six modules `OK`.**
* **Comment-only discipline, verified mechanically.**  Every edited `.lean` file was
  comment-stripped and compared against its content at the lane base `f0a71688`.  **All six print
  IDENTICAL**, so no statement, term, binder, name or proof changed anywhere in this lane:

  ```
  GQ2/AxiomLedger.lean                                 IDENTICAL
  GQ2/Foundations.lean                                 IDENTICAL
  GQ2/Dyadic/Instances/EvenStratumShift.lean           IDENTICAL
  GQ2/Dyadic/Instances/StageAbstractionEvenRawSpan.lean IDENTICAL
  GQ2/Dyadic/SqCore/GradedClassFiveJoin.lean           IDENTICAL
  GQ2/Dyadic/SqCore/GradedClassFourCompose.lean        IDENTICAL
  ```

* **The axiom ledger was exercised without `lake`.**  `scripts/mirror.sh check GQ2/AxiomLedger.lean`
  elaborates the ledger against the mirror and prints its whole report: **32336 tracked
  declarations, gap map 0, ALARM 0, 0 terminal violations**.  Of the five terminal certificates,
  four print "identical to twin ... (12 axioms)" and the fifth
  (`admissibleCountR_eq_admissibleCount`) prints "12 axioms, all in the census".  That is L1
  through L4 of the gate's content, and
  it answers `w73-house-note.md` §2.3's third bullet ("whether the ledger passes today is
  unverified by me") from inside a lane.  **Process note for the orchestrator**: a lane can verify
  the ledger's content this way; what it still cannot verify is the gate *script*, since D6 shells
  out to `lake`.
* Both shell scripts pass `bash -n`; the diff to both is comment-only, verified by stripping
  `^[+-]#` lines from the diff and finding nothing left.
* No line over 100 characters was added to any Lean file (one inherited 108-character line was
  rewrapped), and no em-dash was added to any prose.
* `GQ2.lean` was not touched; nothing under `GQ2/Roe/` was touched (plan A6); neither
  `SqCore/GradedUniformJoin.lean` nor `GQ2/Dyadic/GeneralAssembly.lean` was created or touched.

## 7.  Files edited

**Lean (comment-only, 6):** `GQ2/AxiomLedger.lean`, `GQ2/Foundations.lean`,
`Dyadic/Instances/EvenStratumShift.lean`, `Dyadic/Instances/StageAbstractionEvenRawSpan.lean`,
`Dyadic/SqCore/GradedClassFiveJoin.lean`, `Dyadic/SqCore/GradedClassFourCompose.lean`.

**Scripts (comment-only, 2):** `scripts/check_ledger.sh`, `scripts/check_dyadic.sh`.

**Docs (10):** `w75-house-note.md` (new); `owner-items-2026-08-05.md`, `w70-cfour-note.md`,
`w71-cfour-note.md`, `w72-stratum-note.md`, `w73-five-note.md`, `w73-house-note.md`,
`w73-knob-note.md`, `w73-stratum-note.md`, `w74-even-note.md`, `w74-house-note.md`.

## 8.  For the wave-76 queue

1. **Apply round 12's reported findings** (§4.1 to §4.3).  Most are prose; three carry ⚠ because
   the obvious fix is a statement change: §4.1(a) and §4.1(e) (both in `GradedUniformTower.lean`)
   and §5.2's placement.
2. **`EvenUnramified.lean:70` and `:395`** (§4.2(b)).  Named by a wave-73 queue item and a
   wave-74 queue item, still unapplied, prose-only, two lines.  **The cheapest item on this list
   and the oldest.**
3. **The join lane's briefing should start from §4.1(a) and §4.1(b)**, not from either wave-74
   note's summary of the other lane.  The two notes disagree about whether item 3 of the ENGINE's
   W75 list is a hand-off or an open problem, and the FUNC note is right for a reason it does not
   give.
4. **Retire the recurring registration finding** (§4.2(a)).  Three waves running, the annotation
   is the only missing half.  A one-line convention - a lane note's "unwired" claim is written as
   "unwired **as of** `<hash>`" - would end it.
5. **Round 13's checklist.**  Keep all five items, plus the new interface-blindness item, which
   produced the round's two HIGH findings on its first run and should be run at every wave where
   two lanes state interfaces for each other.  A sixth to consider, earned by §4.3(a) and §3.2's
   Contents-list finding: **a summary sentence about a theorem is a separate claim from the
   theorem's own docstring, and the summary is where the over-reach lands.**  In both cases the
   declaration's docstring was safe and the file's or note's summary of it was not.
6. **Two owner calls carried forward** from round 11, untouched here: `chifree-clearing-note.md`'s
   rewrite, and `mc-design.md`'s third `q`.  The two `GQ2/Roe/` R6 hazards also remain live under
   the plan-A6 freeze; this lane touched nothing under `GQ2/Roe/`.
