# W73-HOUSE: round 9's findings applied, the ledger gate wired, and watch round 10

Lane `claude/w73-house`, base `6a8fbc90`, cache at `a515b437`.
Verification of record: `scripts/mirror.sh` (sweep 5833 artifacts).
**No `lake` command was run.**

## Headline

**Ticket 1.**  **All 33** findings in `w72-house-note.md` §§2.2, 2.3 and 2.4b are applied (10 in
§2.2, 11 in §2.3, 12 in §2.4b; the ticket's "roughly 25" is an undercount, and the tables in §1
list them one per row so the figure can be re-counted).  Every one was re-verified against the
Lean first, and **all 33 checked out** at the level of the defect.  **Three needed their
correction rewritten**, and one of those is applied only in its prose half because the rest would
change a statement.  The three:

1. **§2.2(b)'s fix was still right, and is now also a forward pointer** (this is the one the
   ticket flagged as possibly superseded).  Wave 72's
   `GradedClassFourDefect.lean:17-19` opens from exactly the three-item list the round-9 finding
   said `GradedClassFourKnob.lean:93-96` should have had, and discharged two of the three.  So
   the enumeration is corrected *and* pointed at the module that took it further.
2. **§2.2(i) is right about `:123` and slightly wrong about `:128`.**  The round-9 text says "The
   'In particular' sentence that follows *is* the statement"; `:128` has no such sentence at all.
   Both headlines are fixed, differently.
3. **§2.3(g)'s recommended fix is a STATEMENT change and was not made.**  Reported in §3 below.

**Ticket 2.**  `scripts/check_ledger.sh` is new and `check_dyadic.sh` has a **D6** that calls it
only under `GQ2_LEDGER_GATE=1` or `--ledger`.  The default path is unchanged and now prints a
SKIP line naming the gate.  **I could not run it** (it invokes `lake`); what I could verify, and
did, is in §2.  One protocol finding fell out of writing it, and it is the sharpest thing in this
note after the census claim:

> **`check_dyadic.sh`'s default path already runs `lake env lean` today, twice.**  Not through my
> D6, which is opt-in, but through `check_axioms.sh` check 5 (`scripts/check_axioms.sh:280` and
> `:363`).  Those blocks self-skip only when the oleans are absent, and every campaign worktree
> with the shared cache linked **has** them: `.lake/build/lib/lean/GQ2/Roe/Main.olean` and
> `.lake/build/lib/lean/GQ2.olean` are both present in this worktree right now.  So the premise
> "a lane running `check_dyadic.sh` does not touch `lake`" was false before this wave.  I did not
> run `check_dyadic.sh` end to end for exactly this reason.

**Ticket 3.**  **27 findings in the four wave-72 modules** (5 high, 7 medium, 7 medium-low, 8
low), plus the lane-note findings of §3.5.  Counted one per label: §3.1 has 14 (a-n), §3.2 has 9
(a-i), §3.3 has 4 (a-d).  The three worth reading first:

1. **A ⭐⭐⭐ docstring is on the wrong theorem.**  `GradedClassFourDefect.lean:435-455` states
   `cfourDef_leftover_reduce`'s conclusion verbatim but sits on `cfourDef_relator_step`, which
   concludes something else and produces neither `cfourDefCore` nor `cfourDefTriple`.  The
   theorem the docstring describes has **no** docstring.  §3.1(a).
2. **`NuSeeds.lean` cites a declaration that does not exist and claims a construction it does not
   perform**, in one sentence.  This is the module that spent seven days outside every green
   build, and it is the only file in scope whose prose had never been read by anyone.  §3.2(a).
3. **A nine-field structure is called ten-field in three places**, one Lean and two docs, and the
   same paragraph that says "ten" then breaks it down as six plus three.  §3.1(c).

The single highest-risk category came up **clean and machine-verified**: `NuSeeds.lean`'s "everything
prints std-3, census 11" is **true**, checked by `mirror.sh` on all eight declarations, four of
which carry no pin.

Nothing in this lane changes a statement.  The ten module files touched are comment-only, which I
verified mechanically rather than by eye (see the verification record), and all ten are
`mirror.sh check`-clean.

---

## Ticket 1: round 9's findings, verified and applied

Each row was checked against the Lean before being applied; the "verified" column says what I
confirmed, not what round 9 asserted.  All findings are prose-only unless marked.

### 1.1  §2.2, the wave-71 modules

| # | site | verified | applied |
| --- | --- | --- | --- |
| (a) | `GradedClassFourKnob.lean:51-53`, `:242-244` | `cfour_sqRelWord` has exactly one fourth power, `m 1 ^ 4`; `sqArbBase_one` gives `m 1 = x₀`.  `σ⁴` occurs nowhere | yes, both sites, plus the reciprocal in `w71-cfour-note.md` |
| (b) | `GradedClassFourKnob.lean:93-96` | `cfourKnob_leftover_eq` has five factors; `cfourKnob_pair_correction` delivers `A⁴` and the triple bracket only, so `⁅A, x₀⁆²` and `⁅⁅A, x₁⁆, A⁆` are undelivered | yes, as a three-item list, with a pointer to wave 72 |
| (c) | `GradedClassFourKnob.lean:18-19`, `:92-93` | `:79-81` and `:467` both disclaim the residue; only the headline does not | yes, both sites, plus `w71-cfour-note.md:26` |
| (d) | `GradedGammaFourFive.lean:40-42` | no declaration states it; `gFourFive_hcentral_iff`'s RHS is about left-normed fourfold brackets, and `gFourFive_jacobi`'s factors have a `Y`-element in the near slot, not a bracket | yes, clause deleted |
| (e) | `GradedGammaFourFive.lean:189`, `:29-30` | `gFourFive_ad_right`'s `T`-element is the **right** entry of `commP`; `GradedGammaThreeFour.lean:115-117` fixes near = left, far = right | yes, both sites |
| (f) | `GradedGammaFourFive.lean:12-13` | `GradedGammaThreeFour.lean` has **14** declarations and 14 pins; "three" is that file's "three **forms** a class-four run consumes" (`:16`) | yes, "three" → "fourteen" |
| (g) | `GradedGammaFourFive.lean:40`, `:105`, `:278`, `:281` | `gFourFive_hcentral_iff` quantifies over `⁅⁅⁅p,q⁆,r⁆,t⁆` only | yes, "left-normed" inserted at four sites |
| (h) | `GradedGammaFourFive.lean:28`, `:155`, `:436` | `gFourFive_drop_right`, `gFourFive_sq_dress`, `gFourFive_sq_zLayer_dress` run on `cfive_commP_zLayer_left` / `gFourFive_commP_zLayer_right` and never cite `gFourFive_commP_vanish` | yes; `:436`'s "by §1" softened rather than deleted, §1 containing the centrality lemmas too |
| (i) | `GradedClassFourKnob.lean:123`, `:128` | statements are the implications for the trivial row; the doubling is the proof.  **Round 9's fix text fits `:123` only**: `:128` has no "In particular" sentence | yes, both, rewritten separately |
| (j) | `GradedClassFourKnob.lean:30-32` | `cfourKnob_dressSq_admissible` binds `hsigma : ν'(σ) = 1` and `hx0 : ν'(x₀) = 0`; `:158-160` is accurate, the header is not | yes |

### 1.2  §2.3, the wave-70 modules

| # | site | verified | applied |
| --- | --- | --- | --- |
| (a) | `GradedRelatorBase.lean:13-14` | `grep -rn 'should replay' GQ2/ docs/` still returns only this line and round 9's own report of it.  The sourced quote is real and is in wave 69's **§4 header** (`GradedClassFour.lean:556`), not its closing analysis (the `ANALYSIS, NOT COMMITTED` block, `:105-131`) | yes.  Second quotation withdrawn, first repointed at §4 |
| (b) | `GradedRelatorBase.lean:53-54`, `:92-94`, `:105-107` | `cfour_commP_mul_right`, `cfour_comm_self`, `cfour_one_comm` are all in `GradedClassFour.lean`'s `section FreeIdentities` (`:153-192`) under `variable {Q : Type*} [Group Q]`.  By hand, `commP c (c·w) = c⁻¹w⁻¹cw = commP c w`.  `GradedClassFive.lean` §5 names only the fourth-power factor, so it had this right | yes, all three sites |
| (c) | `GradedClassFourIdentity.lean:524-528` | `cfourId_zLayer_le` still binds `hsq`, `hcomm` (both unrestricted universals) and needs `S` a subgroup; §4's inventory (`:65-75`) reaches `commP c g` only at frame letters and `c²` only bundled | yes; headline retitled and the gap written out |
| (d) | `GradedClassFourIdentity.lean:191` | §2 holds `cfourId_twoCentral_le_index_two` and `cfourId_modTwoIndep_mul`, neither mentioning `nuLam` or `nu'`; `:38` says the opposite of the header | yes, "on the rows and" deleted |
| (e) | `GradedClassFive.lean:11-17`, `:269-270` | `GradedClassFour.lean` mentions class five on **one** line (`:860`); `w69-class4-note.md` has **zero** occurrences of "class five", "γ₅" or "bookkeeping".  "reorder at will" *is* wave 69's | yes; attribution note added, the accurate quotation kept |
| (f) | `GradedClassFive.lean:78-79` | nothing proves `γ₄ ⊄ γ₅`; over the file's binders it is false | yes, replaced by the membership statement |
| (g) | `GradedClassFourIdentity.lean:513`, `:107` | statement is `DiscreteTopology (levelQuot (DSq h) 4)`, level four | **partly.**  Round 9's preferred fix (generalise to `(k : ℕ)`) is a STATEMENT change: **not made**, reported in §3.  Docstring scoped to level four instead |
| (h) | `GradedClassFourIdentity.lean:266-268` | `cfourId_supply_of_reach : H → SqClassClearingSupply h 4`, sufficiency only | yes, with the scope stated as `relBase_defectDies_iff_trivial` does |
| (i) | `GradedRelatorBase.lean:45-46` | `twoCentralSeries_normal` is a global instance and is cited at `:32`; `relBase_relator_base_of_commuting` targets a bare `[Group Q]` | yes |
| (j) | `GradedRelatorBase.lean:70-72`, `:354-356` | `bridgeDefect` is defined, central, of order dividing two and evaluated; nothing shows it `≠ 1` | yes, both |
| (k) | `GradedRelatorBase.lean:115-116`, `:254-255`; `GradedClassFive.lean:53-54`; `GradedClassFourIdentity.lean:79` | `relBase_map_commP` used **six** times (`:319`×2, `:323`×2, `:331`×2); `relBase_relator_base_mem_iff` binds and uses `[hN : N.Normal]`; the scope note names lemmas outside "the whole inventory"; wave 69's §5 is its `ANALYSIS` block | yes, all four |

### 1.3  §2.4b, the `Instances` and `MarkedCore` modules

| # | site | verified | applied |
| --- | --- | --- | --- |
| (a) | `EvenStratumPoint.lean:371-372` | **machine-verified.**  `mirror.sh check` prints `hilbertSymbol_normCriterion_finiteDyadic` + `tateDualityAt` on the §4/§7 refutations and `tateDualityAt` + `Foundations.absGalQ2_localEulerCharacteristic` on §6.  The module header's "Axiom scope (measured)" is right | yes; §8 now states the header's per-section breakdown |
| (b) | `EvenStratumPoint.lean:70-71`, `:311-316` | `nonempty_orientedEquivN_evenDegree_of_forwardGeneratorData` has **four** hypotheses; `hev` is still bound at `:320` | yes, three sites |
| (c) | `EvenStratumPoint.lean:63-65` | `evenUnram_isEmpty_orientedN` (`EvenUnramified.lean:340-346`) denies it at every `α ≥ 3`, `a`, `h` | yes, scoped to the depth-2 point, with the wave-69 theorem named |
| (e) | `EvenStratumPoint.lean:17-18`, `:25-26` | `w69-unram-note.md:112-117` prices **three** items and its first is the **abelianization** torsion; `NFrameAlphaOne.lean:108-110` states it correctly | yes; the finding (two different objects) kept, the attribution fixed |
| (f) | `EvenStratumPoint.lean:85`, `:155` | §2 holds exactly one theorem, the single value at the twisted index | yes, both |
| (g) | `EvenStratumPoint.lean:145-146` | `(hα : 1 ≤ α)` is consumed by the `omega` | yes |
| (d) | `NFrameAlphaOne.lean:27-28` | §8 (`:611-617`) opens "The invariant package ... is **not** here" | yes |
| (h) | `NFrameAlphaOne.lean:93-95` | `EvenDemushkin.lean:252-260` now says the opposite and cites `nFrame4_demushkinQ_DN_one` | yes, past tense + the reciprocal state noted |
| (k) | `NFrameAlphaOne.lean:11-12`; `EvenAlphaOne.lean:703-704` | `evenAlphaOne_isDemushkin_DM` (`:598`) is the `M` half; `evenAlphaOne_card_H2_DN`/`_DM` are §7's (`:521`, `:543`), §6 being the inverse Grams | yes, both |
| (l) | `NFrameAlphaOne.lean:625-626` | `nZ4Hom = abLiftG (nLiftHom 1 h _ (coreMark (ofAdd 1) 1 1 1) _)` and `nFourTHom = nCoordHom 1 h _ (coreMark (ofAdd 1) 1 1 1) _`, where `nCoordHom` *is* `abLiftG (nLiftHom …)`.  Same hom, same marking | yes |
| (i) | `NFrameAlphaOneInvariants.lean:89` | no `EvenModel.lean` exists; `demushkinRank_DN` is `EvenModelH2.lean:482` | yes |
| (j) | `EvenAlphaOne.lean:110`, `:124` | `MarkedCore/Cores.lean`: `diagCoeff` at `:1215`, `mWord_centLift_fib` at `:1392`, `nWord_centLift_fib` at `:1411`.  All three off by exactly 3 | yes |

### 1.4  The "half a fix" rule, applied to my own edits

Round 9's own recommendation for round 10 is that a claim fixed in one file is often half a fix.
Applied to ticket 1, it produced **three** reciprocal edits that round 9 did not list:

* **`GradedClassFour.lean:841` carried the very overreach that `GradedClassFourIdentity.lean` §1
  criticises it for**: "So the entire class-four obligation is the single `Q₄`-identity
  `cfourEichDefect nu' j = 1`", on `cfour_supply_of_eichDefect`, which is `H → SqClassClearingSupply
  h 4`.  Found by grepping `entire class-four obligation` while fixing §2.3(h).  Corrected, with
  wave 70's sharper reading attached.
* **`w71-cfour-note.md:16-18`** carried §2.2(a)'s `σ⁴` sentence and **`:26`** carried §2.2(c)'s
  unqualified "reachable".  Both corrected.  That note's §4 already had the three-item list right.

**And one reciprocal that came up clean, worth recording because a null result is the point of
the rule:** `EvenAlphaOne.lean:702` carries the *same sentence* as the false census claim of
§2.4b(a), "Every declaration is expected std-3".  There it is **TRUE**: `mirror.sh check` prints
19 pins, every one `[propext, Classical.choice, Quot.sound]`.  Only `EvenStratumPoint.lean`'s copy
was false.

---

## Ticket 2: the axiom-ledger gate

### 2.1  What was built

`scripts/check_ledger.sh`, new, and a **D6** block in `scripts/check_dyadic.sh`.

`ax1-proposal.md:489` prescribes `lake env lean GQ2/AxiomLedger.lean` as a merge gate.  It was in
no script.  The new script runs it and turns its report into pass/fail:

* **L1** the command's own exit code.  `AxiomLedger.lean`'s terminal certificate `throwError`s, so
  a nonzero exit already means a capstone rests on `sorryAx`, on a non-census axiom, or has stopped
  printing identically to its `Γ_A` twin.
* **L2** gap map empty.
* **L3** ALARM empty.
* **L4** terminal violations `= 0`, **read back from the printed count**.  Redundant with L1 by
  construction, and kept so that a future refactor turning the `throwError` into a warning cannot
  silently disarm the gate.

A **missing** report line is a FAILURE, not a pass.  If `AxiomLedger.lean`'s output format moves,
the gate says so rather than quietly auditing nothing.  The scanned and std-3 counts are printed
and never asserted: they move with every landing, and a gate pinning them would fail every wave.

### 2.2  How the lane/orchestrator separation is done

D6 is **off by default**.  The default path of `check_dyadic.sh` is unchanged, and prints

```text
SKIP: axiom-ledger gate - off by default because it runs `lake` and lanes must not.
      The orchestrator runs it at a merge with:
          GQ2_LEDGER_GATE=1 bash scripts/check_dyadic.sh
      or standalone:  bash scripts/check_ledger.sh
```

so the gate is discoverable from a default run without being triggered by one.  Either
`GQ2_LEDGER_GATE=1` in the environment or `--ledger` on the command line turns it on; any other
argument exits 2 before anything runs.

### 2.3  What I could not verify, said plainly

**I did not run the gate, because running it means running `lake`.**  Therefore:

* **The `lake env lean GQ2/AxiomLedger.lean` invocation is unverified.**  I have not seen it
  succeed, fail, or produce output from this worktree.
* **The real output's exact shape is unverified.**  My four `sed` extractors quote
  `AxiomLedger.lean`'s own `s!`-interpolated format strings (`:97`, `:107`, `:111`, `:173`)
  character for character, but I have matched them only against fixtures I wrote by hand from
  those format strings.  If Lean's `run_cmd` output is wrapped, prefixed, or interleaved with
  anything, L2/L3/L4 will report "line absent" and FAIL.  That is the safe direction, but the
  orchestrator's first run may need one adjustment.
* **Whether the ledger passes today is unverified by me.**  The orchestrator's manual wave-72 run
  is the last evidence (31954 declarations, 0 terminal violations, 0 on `sorryAx`).

**What I did verify:**

| check | result |
| --- | --- |
| `bash -n scripts/check_ledger.sh` | clean |
| `bash -n scripts/check_dyadic.sh` | clean |
| parser on a passing fixture | exit 0, all four lines `OK`/`INFO` |
| parser on a fixture with gap map 2, ALARM 1, terminal 3 | exit 1, all three named correctly |
| parser on a fixture with the gap-map line mangled | exit 1, "no `--- gap map: N …` line in the output" |
| `bash scripts/check_dyadic.sh --nope` | exits 2 with a message, nothing else runs |

`GQ2_LEDGER_FIXTURE` is the documented hook that made that testing possible without a toolchain.
It is explicit about what it does: it marks L1 **skipped** in the output, so it can never be used
to make the gate appear to pass.

### 2.4  The protocol finding

Repeating it from the headline because it is the part an orchestrator should act on:
**`check_dyadic.sh`'s default path already runs `lake env lean` twice**, in `check_axioms.sh`
check 5 (`:280`) and check 5b (`:363`).  Those blocks skip only when
`.lake/build/lib/lean/GQ2/Roe/Main.olean` and `.lake/build/lib/lean/GQ2.olean` are missing.  Both
are present in this worktree.  D6 is opt-in and does not add to that exposure, but the existing
exposure is real and is not something this lane should change unasked.

---

## Ticket 3: watch round 10

Scope: the wave-72 landings (`GradedClassFourDefect.lean`, `GradedClassFiveKnob.lean`,
`EvenStratumFrame.lean`, `NuSeeds.lean`) and the four wave-72 lane notes.  Every finding below was
verified against the Lean; the two I relay from parallel audits and re-checked myself are marked.

### 3.1  The graded-class landings

**(a) HIGH.  A ⭐⭐⭐ docstring is attached to the wrong theorem, and the theorem it describes has
none.**  `GQ2/Dyadic/SqCore/GradedClassFourDefect.lean:435-455`, on `cfourDef_relator_step`
(`:456`).  *(Re-verified here.)*

> "⭐⭐⭐ **The wave-68 leftover, reduced to the two defects.**  One admissible correction of wave
> 68's class-three witness ... turns the class-four relator into `cfourDefCore nu' j ·
> (cfourDefTriple nu' j · ⁅⁅x₀, x₁⁆, A⁆)`."

That display is verbatim the right-hand side of **`cfourDef_leftover_reduce`** (`:485-492`).
`cfourDef_relator_step` concludes `cfourIdLeftover nu' j * (commP … * commP … * (… ^ 2 * commP …))`:
it pushes the correction through `cfourId_dress_core` and rewrites by `cfourId_leftover_eq`, and it
evaluates nothing, produces neither `cfourDefCore` nor `cfourDefTriple`, and never calls
`cfourDef_assemble`, which the docstring cites as the reason five factors annihilate.
`cfourDef_leftover_reduce`, which is exactly what the docstring states, carries **no docstring**.
Both landed in the same commit (`32ead642`).  Correction: move the docstring down onto
`cfourDef_leftover_reduce` and give `cfourDef_relator_step` its own, naming what it actually does.

**(b) MEDIUM.  "Five of the leftover's factors": three are the leftover's; the other two
cancellations are internal to the knob.**  `GradedClassFourDefect.lean:53` (module header) and
`:443`.

> "Five of the leftover's factors annihilate against the knob (`cfourDef_assemble`)"

By `cfourKnob_leftover_eq` the leftover is `⁅σA,x₀A⁆ · ⁅σ,x₀⁆⁻¹ · cfourEichDefect · (A⁴ · ⁅A,x₀⁆²)
· ⁅x₁,⁅x₁,A⁆⁆`.  Against `cfourDef_assemble`'s pattern, `A⁴`, `⁅A,x₀⁆²` and `⁅x₁,⁅x₁,A⁆⁆` are the
leftover's three; `⁅⁅A,x₁⁆,A⁆` and `⁅⁅x₁,A⁆,x₀⁆` each occur **twice inside the knob** and are not
factors of the leftover at all.  The file has this right in two other places:
`cfourDef_assemble`'s own docstring (`:360`) says "Five of the **eight factors of the corrected
relator**", and `cfourDef_defect_mem_zLayer`'s (`:286`) says the leftover's "other **three**
factors".  Correction: "Five factors of the corrected relator occur twice and annihilate: three of
the leftover's, and two pairs internal to the knob."

**(c) HIGH.  A nine-field structure called ten-field, in one Lean file and two docs.**  *(Field
count re-verified here: `NForwardGeneratorData`, `EvenForwardRouteSkeleton.lean:122-142`, has
`generators`, `relation`, `topGen`, `x0`, `x1`, `sigma`, `x2`, `handleU`, `handleV` = **nine**.)*

* `GQ2/Dyadic/Instances/EvenStratumFrame.lean:339`: "That `Prop` is a *structure* with ten fields"
* `EvenStratumFrame.lean:342`: "Of the ten fields, the six row fields ... are the"
* `docs/dyadic/w72-stratum-note.md:78-79`: "That `Prop` is a **structure with ten fields**"
* `docs/dyadic/owner-items-2026-08-05.md:25`: "a ten-field structure rather than a single
  condition; six fields are already free"

The text refutes itself: six row fields plus "the other three fields" (`EvenStratumFrame.lean:346`)
is nine.  Correction: "nine" at all four sites.

**(d) MEDIUM.  "the five frame letters" is false for `h ≥ 2`, and at that set the hypothesis is
unsatisfiable.**  `GQ2/Dyadic/SqCore/GradedClassFiveKnob.lean:74-77`.

> "the knobs of the inventory have their far slots fixed to the five frame letters"

`sqRank h = 3 + 2h`.  There are five knob **families**, but their far slots are `m 0`, `m 1`,
`m 2` and the two handle slots **at every `j' : Fin h`**, i.e. all `3 + 2h` letters.  This is the
round's own item 1 (satisfiability, not binder generality): `cfiveSpan_ad_far_of_gens` (`:522`)
takes `hX : (Subgroup.closure X).topologicalClosure = ⊤`, and at "the five letters" that
hypothesis is **false** as soon as `h ≥ 2`.  The theorem is fine; the prose names a set that does
not close the gap.

**(e) MEDIUM.  `cfiveSpan_zLayer_le_dsq`'s third family is wider than "the fourfold brackets".**
`GradedClassFiveKnob.lean:763-765`.  The hypothesis (`:769`) is
`hJ : ∀ y ∈ lambdaImage (DSq h) 2 5, ∀ r q, commP (commP y r) q ∈ S`, indexed by **all** of `Y`,
which contains squares as well as brackets.  The file reserves "the fourfold bracket" for
`commP (commP (commP a b) r) q` (`:65-66`, `:717-718`), and `cfiveSpan_zLayer_le_gens` separates
`hJ2` from `hJ4` correctly.  As written the sentence advertises a strictly narrower sufficient
condition than the theorem proves.

**(f) MEDIUM-LOW.  Two ⭐⭐⭐ relations-half headlines drop closedness side conditions.**
`GradedClassFiveKnob.lean:564-571` (`cfiveSpan_zLayer_le_rel` also needs
`hT : IsClosed (lambdaImage G 3 5)`, `:583`) and `:711-720` (`cfiveSpan_zLayer_le_gens` needs both
`hT`, `:727`, and `hY`, `:728`).  The module header (`:71-72`) says "the closedness side
conditions", plural, so the file knows; only the headlines overstate.

**(g) MEDIUM-LOW.  "only needs a topological generating set", but it also needs `S` closed.**
`GradedClassFiveKnob.lean:518-521`.  `cfiveSpan_ad_far_of_gens` takes `hS : IsClosed S` (`:523`)
and the proof uses it (`hS.preimage hcont` into `Subgroup.topologicalClosure_minimal`).

**(h) MEDIUM-LOW, intra-wave.  `cfourDefCore` is called "the wave-72 residue"; the wave's residual
has two factors.**  `GradedClassFourDefect.lean:240-241`, written at `dfd25ad1`, before the
reduction and the residual landed.  In the final state `CfourDefResidual` (`:766`, added at
`75f8b7ad`) is about `cfourDefCore nu' j · ⁅⁅σ, A⁆ · ⁅A, x₀⁆ · ⁅x₀, x₁⁆, A⁆`, and the module header
(`:59`) uses "the residue" for that two-factor product, "`x₁`-free **apart from the near slot
`⁅x₀, x₁⁆`**".  So `cfourDefCore` is the residual's `x₁`-free *first* factor.  The `x₁`-freeness
claim about `cfourDefCore` itself is correct.

**(i) MEDIUM-LOW.  "Those three brackets are the knob expressions" is contradicted eight lines
later by the same commit.**  `GradedClassFourDefect.lean:692-693` versus
`cfourDef_core_knob_pair`'s docstring at `:715-717` (both `ccdb647c`): "`cfourId_dress_core`
**does** compose those two slots, so this one is available as a correction and not only as an
expression."  Also "the frame's remaining slots" is off: the pivot bracket comes from a correction
on core slots 0 **and** 1, and slot 0 already carries `cfourDefCorr`'s `⁅x₁, A⁆`.

**(j) LOW.**  `GradedClassFiveKnob.lean:571-573` "every family here is indexed by `Y` with one or
two free slots of `Q₅`": `hfour` (`:584`) has **zero** free slots.

**(k) LOW.**  `GradedClassFiveKnob.lean:101-103`, `:206-207` attribute all three repair facts to
§1; the square fact is `gFourFive_sq_zLayer_dress`, imported from `GradedGammaFourFive.lean:510`.

**(l) LOW.**  `GradedClassFourDefect.lean:360-364` names `p` "the `x₀`-slot bracket", but
`cfourDefCorr` puts `1` on the `x₀`-slot (`cfourDefCorr_one`, `:399`) and §6's own docstring
(`:447`) calls `p` the Jacobi residue.  The RHS is `c * (tri * n)`, so the core `c` survives too.

**(m) LOW.**  `GradedClassFiveKnob.lean:60`, `:439` attribute the `T`-indexed statement to
`gFourFive_zLayer_le_gen`, which is stated at free `k`; the `T`-indexed one is
`gFourFive_zLayer_le` (`GradedGammaFourFive.lean:424`), which is what the proof consumes (`:611`).
`:67-68`'s separate citation of `_gen` is correct and should stay.

**(n) LOW.**  `GradedClassFiveKnob.lean:127` "the `h` brackets `⁅u j, v j⁆`": the statement binds
`{n : ℕ}` with tuples `Fin n → Q`, and `h` is the genus elsewhere in the file.

### 3.2  `NuSeeds.lean`, the module that was never in a green build

This file landed 2026-08-05 and was registered only at `a515b437`, wave 72.  Its prose had
therefore never been read against the tree, and it is where round 10's yield is highest per line.

**(a) HIGH.  One sentence with three defects: a nonexistent declaration, a misspelled one, and a
construction the file does not perform.**  `GQ2/Dyadic/SqCore/NuSeeds.lean:37-38`.  *(Both name
failures re-verified here.)*

> "`sqNuAdmissible` below builds that family — one marking per `t ∈ ℤ₂` — and `nu_rho_sub_nu`
> extracts the `ū`-coordinate condition from a seed by differencing two members of the family."

`nu_rho_sub_nu` occurs **nowhere else in the repository**; the declarations meant are
`SqNuSeed.toAdd_nu_rho_eq` (`:140`) and `SqNuSeed.toAdd_nu_rho_eq_of_two` (`:147`).
`sqNuAdmissible` is not a name either: the `def` at `:112` is `SqNuAdmissible`.  And nothing
"builds that family": `SqNuAdmissible` is a `Prop`-valued predicate **on** markings, and the only
marking exhibited anywhere in the file is `nuSq h`, via `sqNuAdmissible_nuSq` (`:133`).  No
declaration in `NuSeeds.lean`, `ChiFreeClearing.lean` or `EichlerSeeds.lean` constructs an
admissible marking with prescribed `ν'(u_j) = t`.

**(b) HIGH.  "exact" / "pinned exactly" is stronger than anything in the file, and the frame it
describes was superseded 85 minutes after the file landed.**  `NuSeeds.lean:10` (title), `:28`
(§2 heading), `:31-33`.

> "the derivation shows the recipe is not merely *sufficient* but **exact**"

§2's four declarations are a definition, `ν'(x₁) = 0`, "`nuSq h` is admissible", and two
unbundlings of `nu_rho`.  None is a necessity claim; none mentions a `σ̄`- or `ū`-coordinate.
Separately, `GQ2/Dyadic/SqCore/NuSeedWide.lean` (`5a802bee`, 23:56, against `NuSeeds.lean`'s
`dd2d689b` at 22:31 the same day) says the four-slot scaffold "fixes the `v_j`-slot **literally**
... a restriction of the *search*, not of the target", adds a fifth slot with its own `ν`-field
`SqNuSeedW.nu_rhoV`, and records that "The class-4 obstruction is an artifact of the
linearization, not an invariant of the group."  `NuSeeds.lean` never mentions it.  This is the
round's intra-wave item at a seven-day range.

**(c) MEDIUM.  The "precisely" marking list omits every handle other than `j`.**
`NuSeeds.lean:34-36`.  `SqNuAdmissible h j nu'` (`:112-115`) constrains
`nu' (sqGen h (sqHandleIdxV j))` at the **single** index `j`; for `i ≠ j` both `ν'(u_i)` and
`ν'(v_i)` are as free as `ν'(u_j)`.  A list introduced by "precisely" that shows `ν'(v_j) = 0` and
only `ν'(u_j)` free misstates the family at `h ≥ 2`.

**(d) MEDIUM.  "Differencing" describes an operation the proofs do not perform.**
`NuSeeds.lean:101-103`, `:136-139`.  `toAdd_nu_rho_eq` is hypothesis unbundling;
`toAdd_nu_rho_eq_of_two` is transitivity through the constant `k`.  No difference is formed and no
coordinate condition is produced anywhere in the file.

**(e) MEDIUM.  A "so" that needs a fact the file never establishes.**  `NuSeeds.lean:145-146`:
that two admissible markings agree on `ρ` gives "the `ū`-coordinate of `ρ̄` is invisible" only if
the family contains two markings differing in `ν'(u_j)`.  That is asserted at `:139` and never
proved; the only admissible marking exhibited is `nuSq h`.

**(f) MEDIUM.  `docs/dyadic/chifree-clearing-note.md` is stale in the other direction.**  Single
commit `49d869c6`, predating both `NuSeeds.lean` and `NuSeedWide.lean`.  It still presents the
retargeted search as a proposal (`:100` "Target `SqNuSeed 1 0 1` first"; `:114` "On failure with
the widened family ..."), and its status ledger's last row still reads "**open** — the retargeted
seed search".  The search has been run and its result re-read since.  This is the same defect
round 9 flagged as a secondary finding in §1(a) and left as an owner call; it is still open, and
it now has a second unreferenced module.

**(g) MEDIUM-LOW.**  `NuSeeds.lean:13-14` "Two independent contributions, both from the retargeted
machine search": contribution 1 is not, and the file says so at `:18-20` (it is
`EichlerSeeds.lean:94`'s scaffold lemma, which predates the retargeting).

**(h) MEDIUM-LOW.**  `NuSeeds.lean:25-26` "the `t̄`-freedom `λ` is exactly the kernel of every
`ℤ₂`-marking": the substance is defensible, but nothing in the file states it, and as written a
scalar "is a kernel".

**(i) LOW.**  `NuSeeds.lean:46-47` "Everything here prints **std-3** ... §3 commits the prints."
The claim is **true** (see §3.4) but §3 pins **four** of the eight declarations.  Either pin the
other four or say "four of the eight".

### 3.3  `EvenStratumFrame.lean`

**(a) HIGH.  "so that it is no longer prose" is false for half of §7; the arithmetic has been a
committed theorem since wave 69.**  `GQ2/Dyadic/Instances/EvenStratumFrame.lean:470-475`.
*(The wave-69 theorem re-verified here.)*

> "Wave 69's queue item 4 and wave 71's queue item 4 both record, in prose, that `q ≥ 8` is out of
> reach ... Two statements, so that it is no longer prose."

`evenUnram_head_eq_two_pow_iff` (`EvenUnramified.lean:274`) has said `2 + 2^a = 2^b ↔ (a = 1 ∧ b = 2)`
since wave 69, under the docstring "**The head exponent is a power of two at exactly one
parameter**", which is the sentence §7 reuses.  It is pinned, and cited by name at
`NFrameAlphaOne.lean:102` and in two places in `w69-unram-note.md`.  Both cited queue items call it
a **theorem**, not prose.  Consequently `evenStratum_two_add_two_pow_eq_two_pow` (`:486-517`, some
32 lines of proof) is the `mp` direction of that theorem, and `evenStratum_pAlpha_eq_pow_two_iff`
(`:521-526`) is it verbatim modulo unfolding `pAlpha`.  **The de-duplication would be a statement
change and is not proposed**; the prose correction is to say the arithmetic half is already
committed and that §7 supplies the *invariant* half.

**(b) MEDIUM-LOW.  §6.x subsection numbers that do not exist, in an order the file contradicts.**
`EvenStratumFrame.lean:345`, `:352`, `:358`.  `section Reduction` (`:362-466`) has no `§6.x`
headers.  "§6.1" maps to `evenStratum_vN_one_mem_range` (`:399`) and "§6.2" to the two defs at
`:368` and `:385`, so §6.1 comes *after* §6.2 in the source.

**(c) LOW.**  `:41-43` cites `frattiniFrameEval_characterClass` for a step running class →
character; that lemma runs character → class and is never used in the file.  The step is the
file's own `evenStratumFrame_exists_character` (`:128`).

**(d) LOW.**  `:471-472` "Two statements": §7 has four theorems.  `:483`'s headline "**`2 + 2^a` is
a power of two exactly at `a = 1`**" sits on a one-direction theorem.  `:395`'s "**The six row
fields of the datum are free**" is qualified correctly by the next sentence and by the module
header, so it is a bold-headline-only overreach.

### 3.4  What came up clean

Said in detail, because a round that reports only hits is not a check.

* **Census and axiom claims: clean, machine-verified, and this is the strongest positive result of
  the round.**  `NuSeeds.lean:46-47`'s "Everything here prints std-3 ... census unchanged at 11" is
  **true**: `mirror.sh check` on a copy carrying four extra pins printed all **eight** declarations
  at exactly `[propext, Classical.choice, Quot.sound]`, including the four the file never pins,
  and `GQ2/Foundations/Axioms.lean` holds exactly 11 `axiom` declarations.  Given seven days
  outside every green build, this was the round's highest-risk claim.  `w72-defects-note.md` §6's
  "34 declarations, 34 pins, every one std-3" is exact, including its parenthetical naming the
  four unpinned (`cfourDefCore`, `cfourDefTriple`, `cfourDefCorr`, `CfourDefResidual`).
  `w72-five-note.md` §6's "41 declarations, 41 pins, all std-3 except `cfiveRow_handleWord_congr`,
  which is `[propext, Quot.sound]`" is exact.  `EvenStratumFrame.lean` makes no axiom claim and
  pins all 23 of its own declarations plus three external ones.
* **The refutation headline, which was the flagged risk, is exact.**
  `evenStratum_no_cupAdaptedFrame` negates the full existential at **every** row table, under
  exactly its two named hypotheses, with no reciprocity bundle and no ramification binder; the
  claim that nondegeneracy is unused is right; and `IsCupAdapted` really is what both committed
  producers deliver.  There is no contradiction with
  `evenDegreeNCyclotomicFrattiniFrameSupply_holds`, which carries
  `cyclotomicModFourClassKTwo ≠ 0`, precisely what fails on the third stratum.
* **Cross-reference *names*: clean apart from §3.2(a).**  Roughly seventy cited declarations across
  the four files resolve and say what the citing prose says, checked formula by formula where a
  formula is quoted (`bridgeDress`, `sqEichU`/`sqEichV`, `bridge_comm_common_dress`,
  `cfour_dress_two`, `bridge_frame_zero/one/two`, `cfourId_dress_core`/`_handleU`/`_handleV`,
  `gThreeFour_commP_sq_left`, `bridge_row_image`, `evenFrameGram_expand`, `Frame.levelTwoGen`,
  `card_H1_zmodTwo_maxProTwoGalK`, and the rest).  No dangling **file** citation in either graded
  file.  `NuSeeds.lean`'s two verbatim quotations from `chifree-clearing-note.md` are exact.
* **Intra-wave staleness: clean for `EvenStratumFrame.lean`**, which is the one that had five
  commits and an explicitly blocked route.  Every "blocked/not proved here" sentence survives to
  the final state: `evenClimb_defectReachable` does have exactly three inputs, all three are
  supplied on the `N` row only under `2 ≤ α`, and `StageAbstractionEvenRawSpan.lean:65` does say
  verbatim "the coordinate-`0` row is false at `α = 1`".  The two graded siblings falsify nothing
  in it.  Hits were confined to §3.1(h) and §3.2(b).
* **What a hypothesis is doing: clean.**  `cfiveSpan_commP_sq_left`'s `hy`, and
  `cfourDefCorr_admissible`'s use of `hsigma`/`hx0` through `cfourKnob_dressSq_admissible` only, are
  both exactly as described; `cfourDef_leftover_reduce_merged` genuinely carries no marking
  hypothesis, so "the relator identity itself needs **no** hypothesis on the marking" is correct.
  `evenStratumFrame_pairing_self`'s "this holds at every field" is right, it carrying no range
  hypothesis.
* **Hypothesis satisfiability: clean apart from §3.1(d), and `EvenStratumFrame.lean` is careful in
  exactly the place round 9's defects appeared**: it does not claim the climb is reusable at
  `α = 1`, it says the opposite and names why.  `cfiveRow_handleWord_congr` is genuinely reusable
  (one pointwise hypothesis, discharged at the use site); the four `section Involutions` lemmas are
  genuinely layer-free; `cfiveSpan_lambdaImage_le`'s two unrestricted universals are discharged at
  **both** of its use sites.
* **Counts: clean apart from §3.1(b), (c), (d), (j), (n) and §3.2(i).**  Verified by counting:
  `cfourDef_common_dress`'s "five factors"; `gFourFive_sqRelWord`'s "five factors"; "three
  families"/"six families" (exactly 3 and 6 hypotheses); `cfourDef_assemble`'s "eight factors, five
  occur twice"; `coreRank h = 4 + 2h` against `card_H1_zmodTwo_maxProTwoGalK`; "the five committed
  rows are `±2, 5, ±10`"; `SqNuSeed`'s three ν-fields; `StageGeneric.Frame`'s three fields; prefix
  discipline 38/38 and 41/41.
* **Notes-versus-Lean:** covered in §3.5.

---

## Verification record

* Base `6a8fbc90`, lane branch `claude/w73-house`, shared cache at `a515b437`.
* `scripts/mirror.sh sweep` (5833 artifacts) once at lane start.  **No `lake` command was run**,
  and `scripts/check_dyadic.sh` was deliberately **not** run end to end, for the reason in §2.4.
* `scripts/mirror.sh check` **OK** on all ten edited modules:
  `GQ2/Dyadic/SqCore/GradedClassFourKnob.lean`, `GradedGammaFourFive.lean`,
  `GradedRelatorBase.lean`, `GradedClassFourIdentity.lean`, `GradedClassFour.lean`,
  `GradedClassFive.lean`; `GQ2/Dyadic/Instances/EvenStratumPoint.lean`, `EvenAlphaOne.lean`,
  `NFrameAlphaOneInvariants.lean`; `GQ2/Dyadic/MarkedCore/NFrameAlphaOne.lean`.
* **Every module edit is comment-only, verified mechanically, not by eye.**  I stripped comments
  from the `6a8fbc90` version and from the working version of each of the ten files, with the
  nesting-aware `/- … -/` + `--` scan that `check_dyadic.sh`'s `STRIP_PROLOGUE` uses, and diffed.
  All ten are byte-identical after stripping.  No statement, binder, hypothesis or proof was
  touched anywhere in this lane.
* `mirror.sh check` also run as **evidence** rather than as a post-edit check on
  `EvenStratumPoint.lean` (the census claim: it prints `hilbertSymbol_normCriterion_finiteDyadic`,
  `tateDualityAt` and `Foundations.absGalQ2_localEulerCharacteristic`, refuting "every declaration
  is expected std-3") and on `EvenAlphaOne.lean` (19 pins, all std-3, confirming that file's copy
  of the same sentence is true).
* No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth` introduced.
  No file created under `GQ2/Dyadic/SqCore/` or `GQ2/Dyadic/Instances/`.
* `GQ2.lean` **not edited**.  `GQ2/Roe/*` **not edited**, per plan A6.

## Files edited

| file | what |
| --- | --- |
| `GQ2/Dyadic/SqCore/GradedClassFourKnob.lean` | §2.2 (a), (b), (c), (i), (j) |
| `GQ2/Dyadic/SqCore/GradedGammaFourFive.lean` | §2.2 (d), (e), (f), (g), (h) |
| `GQ2/Dyadic/SqCore/GradedRelatorBase.lean` | §2.3 (a), (b), (i), (j), (k) |
| `GQ2/Dyadic/SqCore/GradedClassFourIdentity.lean` | §2.3 (c), (d), (g partly), (h), (k) |
| `GQ2/Dyadic/SqCore/GradedClassFive.lean` | §2.3 (e), (f), (k) |
| `GQ2/Dyadic/SqCore/GradedClassFour.lean` | reciprocal of §2.3(h), found by grep |
| `GQ2/Dyadic/Instances/EvenStratumPoint.lean` | §2.4b (a), (b), (c), (e), (f), (g) |
| `GQ2/Dyadic/MarkedCore/NFrameAlphaOne.lean` | §2.4b (d), (h), (k), (l) |
| `GQ2/Dyadic/Instances/EvenAlphaOne.lean` | §2.4b (j), (k) |
| `GQ2/Dyadic/Instances/NFrameAlphaOneInvariants.lean` | §2.4b (i) |
| `docs/dyadic/w71-cfour-note.md` | reciprocals of §2.2(a) and §2.2(c) |
| `scripts/check_ledger.sh` | new, ticket 2 |
| `scripts/check_dyadic.sh` | D6, opt-in, ticket 2 |

## For the wave-74 queue

1. **Run the ledger gate**: `GQ2_LEDGER_GATE=1 bash scripts/check_dyadic.sh`.  Its `lake`
   invocation and the real output's shape are the two things this lane could not verify (§2.3).  A
   first run either passes or reports a missing report line, which is the safe direction.
2. **Decide on `check_axioms.sh` check 5's `lake env lean`** (§2.4).  Either lanes may run
   `check_dyadic.sh` and the "no `lake`" rule needs restating, or check 5 needs the same opt-in
   treatment D6 got.  This is an owner call, not a lane's.
3. **`GradedClassFourDefect.lean:435-455`'s misplaced docstring** (§3.1(a)) is the round's top
   item and is a two-minute move, but it touches a wave-72 landing and should go to the lane that
   owns that file, or to a house lane once it is quiet.
4. **`NuSeeds.lean`'s prose has never been audited before this round** (§3.2).  Six findings in
   192 lines, two of them HIGH.  The registration at `a515b437` is what made it visible; the prose
   should be brought up to the tree it now sits in, together with the `chifree-clearing-note.md`
   staleness of §3.2(f), which round 9 also flagged and which is an owner call.
5. **The two `GQ2/Roe/` R6 hazards remain live** (round 9's queue item 2): four docstrings citing
   the nonexistent `GQ2/Roe/DRH2.lean`, and `TwoCentralTower.lean:65-66` announcing `sorry`s in a
   sorry-free file.  Still frozen by plan A6, still needing an owner nod.  Unchanged this wave.
6. **Round 11 should keep all three checklist items.**  Item 3 (a claim fixed in one file is often
   half a fix) earned its place immediately: it produced three reciprocal edits inside ticket 1
   alone, one of which, `GradedClassFour.lean:841`, is a module carrying the exact overreach that a
   *later* module criticises it for.  It also produced a **null** result worth keeping visible, the
   `EvenAlphaOne.lean` census sentence that turned out to be true.  A fourth item to consider:
   **a docstring can be attached to the wrong declaration**, which §3.1(a) is and which no previous
   round has looked for; the check is cheap, and is to read each `⭐` display against the statement
   immediately below it rather than against the section.
