# W81-HOUSE: the supersession sweep, watch round 18, and the endgame board

**Lane W81-HOUSE, branch `claude/w81-house`, base `6f2916f3`.**  Standing verification lane.
Comment-only throughout: no statement anywhere in the tree was changed, no theorem was added or
removed, no `sorry`, no axiom, no import.

Verification of record: `scripts/mirror.sh sweep` at lane start, then `check` on every edited
module, all green with zero errors and zero warnings.  `scripts/mirror.sh check
GQ2/AxiomLedger.lean` green, exit `0`.  No `lake` command was run.

## Headline

**The odd closure survives the near-miss check exactly.**  `gOdd_markTransitivity` really does
prove `SqLamMarkTransitivity h` at every `h`, on the nose, with no hidden binder and on the
standard three axioms.  I elaborated the statement rather than reading it, and also elaborated
the raw unfolded quantifier against the theorem; both typecheck.  The campaign's biggest claim
is what it says it is.

**Everything wrong that I found is prose, and the pattern is one pattern**: the wave-80 lanes
ran blind to each other and to their own base, so the corpus is now full of remains-lists whose
items are theorems.  The worst instance is the wave-80 lesson repeating verbatim: W80-UNIFORM
listed `GJoinSeparationAll h` as "the last graded-side interface" that W81 would need, when
that lane's own base commit already carried `gExt_separationAll` proving it unconditionally.

**One distinction the corpus was blurring, now marked everywhere**: `GTowerKnobRealizable h` is
neither a theorem nor a refutation.  It is unproved AS QUANTIFIED (a route failure, wave 79) and
was BYPASSED by the `x₁`-free re-run, not discharged.  Three separate documents were describing
it as "the residual"; one in-tree docstring came close to calling it false.

---

# Ticket 1: the supersession sweep

One as-of-hash annotation at each interface `Prop` and each composite family, in the wave-78
discipline (each annotation says what IS and what IS NOT settled).  Files touched:
`GradedDepthThree`, `GradedUniformGen`, `GradedUniformJoin`, `GradedUniformTower`,
`GradedAbsorption`, `GradedXFree`, `GradedJoinBase`, `GradedOddClose`.

## 1.1 The census: every `GXf`/`GDeep`/`GJoin`/`GAbs`/`GDecide`/`GTower`-prefixed `Prop`

Complete.  The grep is `^def \(GXf\|GDeep\|GJoin\|GAbs\|GDecide\|GTower\)` over
`GQ2/Dyadic/SqCore/`; it returns eighteen declarations, of which one (`GDecideQ`) is a `Type`
and not a `Prop`.  All seventeen `Prop`s are accounted for below.

### THEOREM (8)

| `Prop` | defined | discharged by | reach |
|---|---|---|---|
| `GDeepKillAt h k` | `GradedDepthThree.lean:937` | `gGen_killAt`, `GradedUniformGen.lean:946` | every `k ≥ 2`, every `h` |
| `GJoinSeparationAll h` | `GradedUniformJoin.lean:1004` | `gExt_separationAll`, `GradedExtraction.lean:519` | every `h` |
| `GJoinTowerSeparation h ν' k` | `GradedUniformJoin.lean:882` | `gExt_towerSeparation`, `GradedExtraction.lean:497` | every `h`, `ν'`, `k` |
| `GJoinDefectVanishing h` | `GradedUniformJoin.lean:191` | `gOdd_defectVanishing`, `GradedOddClose.lean:127` | every `h` |
| `GAbsVanishingTwo h` | `GradedAbsorption.lean:1347` | `gAbs_vanishingTwo_of_sep (fun _ => gExt_towerSeparation)` | every `h` |
| `GDeepVanishingThree h` | `GradedDepthThree.lean:985` | `gDeep_vanishingThree_of_sep (fun _ => gExt_towerSeparation)` | every `h` |
| `GXfChiSupply h k` | `GradedXFree.lean:900` | `gOdd_chiSupply`, `GradedOddClose.lean:131` | every `h`, `k` |
| `GXfKillResidual h` | `GradedXFree.lean:1024` | `gOdd_killResidual`, `GradedOddClose.lean:75` | every `h` |

Two footnotes on that table.  `GAbsVanishingTwo` and `GDeepVanishingThree` have no
*standalone* unconditional theorem in the tree; they are theorems in the sense that their sole
hypothesis is `gExt_towerSeparation`, and that is how `GradedXFree`'s `gXf_chiSupply_four` and
`gXf_chiSupply_five` actually consume them.  `GXfKnobRealizable h` (`GradedXFree.lean:880`) is
also a theorem (`gXf_knobRealizable`, `:894`) but is listed separately below because its whole
point is the contrast with `GTowerKnobRealizable`.

### THEOREM, derivable in one step (1)

| `Prop` | defined | route |
|---|---|---|
| `GJoinChiSupply h k` | `GradedUniformJoin.lean:209` | `gXf_chiSupply_le (gOdd_chiSupply h k)` |

No unconditional `gJoin_chiSupply` is recorded in the tree.  Flagged rather than added: adding
it would be a statement change, which this lane may not make.

### REFUTED (3)

| `Prop` | defined | refuted by |
|---|---|---|
| `GTowerLayerReach h ν' k`, `k ≥ 2` | `GradedUniformTower.lean:1139` | `gDeep_not_layerReach`, every depth and marking |
| `GDecideBaseThree h` | `GradedBaseDecide.lean:595` | `gDeep_not_baseThree`, every `h` |
| `GJoinBase h` | `GradedUniformJoin.lean:1014` | `gDecide_not_joinBase`, every `h` |

All three already carried correct refutation markers before this lane; I added only the note
that the target they were aiming at is now reached by another route.  (`GBaseResidual h`,
`GradedJoinBase.lean:648`, is a fourth refutation - `gDecide_not_baseResidual` - outside the
six prefixes but in the same family, and likewise already marked.)

### OPEN AND LIVE (0)

**None.**  This is the finding.  No `Prop` in the census is both unproved and still needed.

### OPEN, NOT NEEDED (1)

| `Prop` | defined | status |
|---|---|---|
| `GTowerDefectVanishing h` | `GradedUniformTower.lean:1706` | neither proved nor refuted; strictly stronger than the proved `GJoinDefectVanishing h`, and nothing consumes it |

### SUPERSEDED, AND NEITHER PROVED NOR REFUTED (1)

| `Prop` | defined | status |
|---|---|---|
| `GTowerKnobRealizable h` | `GradedUniformTower.lean:1723` | unproved AS QUANTIFIED (wave 79: a route failure, not a counterexample); BYPASSED by `GXfKnobRealizable h`, which is a theorem |

This is the one that needed the most careful annotation; see §2.3.

### AUXILIARY PREDICATES, not interfaces (4)

`GXfFree h a` (`GradedXFree.lean:78`), `GDecideGoodMark m` (`GradedBaseDecide.lean:300`),
`GTowerAdm ν' k` (`GradedUniformTower.lean:887`), `GJoinChiAdm ν' …`
(`GradedUniformJoin.lean:95`).  These are conditions on a dressing, a mark, or an element,
quantified inside the interfaces above rather than asserted; there is nothing to discharge and
they carry no annotation.

Total: 8 + 1 + 3 + 0 + 1 + 1 + 4 = 18, minus `GDecideQ` (a `Type`) = 17 `Prop`s, all accounted.

## 1.2 What the annotations say

Fourteen annotations landed, at commits `9c30921e` and `1bcec7cd`.  The three that carry real
information rather than bookkeeping:

**(a) `GradedDepthThree.lean:934` and `:919`** - the `GDeepKillAt` docstring read "TRUE at
`k = 2, 3`, open at `k ≥ 4`" and §8's header said the residual "re-cuts onto the ladder at
`k ≥ 4` plus the two wave-75 interfaces".  Both were false at the merge: `gGen_killAt` proves
every rung.  Annotated affirmatively, with the note that the defect restriction remains
essential because the unrestricted `GTowerLayerReach` is still refuted.

**(b) `GradedUniformTower.lean:1723`** - the `GTowerKnobRealizable` annotation now states the
route-failure-versus-refutation distinction explicitly, names the bypass, and says "do not
restart this `Prop` as a lane target".

**(c) `GradedUniformJoin.lean` §8 header** - the "two further inputs … needs a third" framing
is annotated with the status of each of the three separately, because they are now in three
different states (refuted / theorem / bypassed) and the header treated them as one kind.

---

# Ticket 2: watch round 18

## 2.1 (a) The near-miss check on the campaign's biggest claim: PASSES

I did not read these statements off; I elaborated them, against the swept mirror, with the
verification flags of record (`-DautoImplicit=false -DrelaxedAutoImplicit=false`).

```
gOdd_markTransitivity : ∀ (h : ℕ), SqLamMarkTransitivity h
gOdd_supply           : ∀ (h k : ℕ), SqClassClearingSupply h k
@gGen_killAt          : ∀ {h : ℕ} (k : ℕ), 2 ≤ k → GDeepKillAt h k
@gXf_markTransitivity_of_residual : ∀ {h : ℕ}, GXfKillResidual h → SqLamMarkTransitivity h
gExt_separationAll    : ∀ (h : ℕ), GJoinSeparationAll h
```

with

```
'GQ2.Dyadic.SqCore.gOdd_markTransitivity' depends on axioms: [propext, Classical.choice, Quot.sound]
'GQ2.Dyadic.SqCore.gOdd_supply'           depends on axioms: [propext, Classical.choice, Quot.sound]
```

Four things were checked that a reading would not catch, and all four hold:

1. **No hidden section hypothesis.**  `gXf_markTransitivity_of_residual` sits in
   `GradedXFree`'s `section Chain`, whose only variable is `variable {h : ℕ}`; `gGen_killAt`
   sits in `GradedUniformGen`'s `section Ladder`, likewise.  Neither picks up a `0 < h`.  The
   elaborated types above confirm it: no positivity binder, no instance binder.
2. **The unfolded statement is the claimed statement.**  I typechecked the headline against the
   raw quantifier written out by hand:
   `∀ (h) (ν'), ν'(σ) = ofAdd 1 → ν'(x₀) = ofAdd 0 → ∃ Ψ, (∀ x, nuLam h (Ψ x) = nuLam h x) ∧
   ∀ x, ν' (Ψ x) = nuSq h x := gOdd_markTransitivity`.  Accepted.  So the definition
   `SqLamMarkTransitivity` is not hiding a weaker body than its docstring advertises.
3. **The binders really do meet.**  `GDeepKillAt h k` (`GradedDepthThree.lean:937`) quantifies
   `ν'` and `g` internally and mentions no handle index; `gGen_killAt`'s `k ≥ 2` does contain
   `GXfKillResidual`'s `k ≥ 4`; the `h` is the same implicit in both.  `GradedOddClose.lean`'s
   §Compose prose asserting exactly this is accurate in every clause.
4. **No `sorryAx`, no census axiom.**  Standard three only.

**Ledger.**  `scripts/mirror.sh check GQ2/AxiomLedger.lean` exits `0`: gap map `0`, ALARM `0`,
terminal violations `0`, and the five capstones each certified against their Γ_A twins at 12
axioms.  The census is clean *with* the new modules: all four wave-80 landings are registered
in `GQ2.lean` (`:782` `GradedXFree`, `:783` `GradedUniformGen`, `:784` `GradedOddClose`,
`:870` `MpcRowData`), so the ledger's `import GQ2` walk covers them rather than silently
skipping them.  That registration check matters here - wave 72 found `NuSeeds.lean` had never
been in any green build - and it passes.

## 2.2 (b) The uniform note's stale remains-list: CONFIRMED STALE, CORRECTED

Not corrected before this lane.  It is the wave-80 lesson repeating.

**`docs/dyadic/w80-uniform-note.md:137`, verbatim:**

> 1. **`GJoinSeparationAll h`** for `h >= 1`: the last graded-side interface, wave 75
>    Section 7's ordered-product bookkeeping, now consumed at every depth `k >= 2` by the
>    closed ladder.  Vacuous at `h = 0`.

**Wrong, and wrong when written.**  That note's own first line gives its base as `4f30776b`.
`git show 4f30776b:GQ2/Dyadic/SqCore/GradedExtraction.lean` contains, at line 514:

```
theorem gExt_separationAll (h : ℕ) : GJoinSeparationAll h :=
```

unconditional, at every `h`, proved by wave 79 - in the lane's own base.  It was never "the
last graded-side interface" and W81 never needed it.

**`docs/dyadic/w80-uniform-note.md:140`, verbatim:**

> 2. **`GTowerKnobRealizable h`**: the extraction, the wave-73 multi-handle bookkeeping,
>    unchanged, now THE residual at `h = 0`.

**Wrong in status.**  It is not the residual anywhere, because the route no longer passes
through it; see §2.3.

Both corrected in place, under a `### CORRECTION [W81-HOUSE, watch round 18, as of 6f2916f3]`
heading that retracts items 1 and 2 and records that item 3 stands and understates the result.
The same two errors were in the module docstring, `GradedUniformGen.lean` §7 (`:935-939`),
verbatim:

> what now stands between the tree and `SqLamMarkTransitivity h` is exactly the two wave-75
> interfaces: the separation bookkeeping `GJoinSeparationAll h` (vacuous at `h = 0`) and the
> extraction `GTowerKnobRealizable h`.

annotated there in the same pass.

## 2.3 The `GTowerKnobRealizable` conflation: a correction to `GradedOddClose` itself

`GQ2/Dyadic/SqCore/GradedOddClose.lean:17-18`, verbatim:

> the extraction, which wave 79 showed does **not** hold as quantified in
> `GTowerKnobRealizable h`, is replaced by …

"does not hold" reads as refuted.  The sibling module that did the work states it correctly.
`GradedXFree.lean:878-879`, verbatim:

> Unlike `GTowerKnobRealizable h`, which wave 79 showed the route does not prove as quantified,
> this one is a **theorem**.

"the route does not prove" and "does not hold" are different claims, and the corpus contains no
counterexample to `GTowerKnobRealizable`.  This matters because the tree's genuine refutations
(`GTowerLayerReach`, `GDecideBaseThree`, `GJoinBase`, `GBaseResidual`) all carry counterexamples
and all say so; blurring the boundary makes the refutation record less trustworthy, not more.

## 2.4 (c) Headline-versus-statement across `GradedOddClose.lean`: two drifts, both minor

I checked all fifteen theorems and every docstring in the file against its statement.
**Thirteen are exact.**  In particular the three ⭐⭐⭐ claims all hold as written:
`gOdd_markTransitivity`'s "with no hypothesis of any kind" (verified by elaboration),
`gOdd_handleMix`'s "at every `h` and every unit exponent" (the `h = 0` branch really does go
through `sqHandleMixFixesCore_zero`, so the `0 < h` of
`sqHandleMixFixesCore_of_lamMarkTransitivity` is not silently inherited), and
`gOdd_certificate`'s own docstring, which lists its binders correctly.

The two that drift:

**(i) `:190-192`, §4 section prose, verbatim:**

> the marked-core certificate for the odd row costs exactly an oriented identification and the
> two `ν`-normalizations, and no correction-stratum hypothesis at all

`gOdd_certificate` also binds `hcont : Continuous fun x : (DSq h : Type) => nuG (f x)`.  Four
binders, not three.  The theorem's own docstring twenty lines later gets it right ("the
oriented identification `f`, its continuity data, and the two selected core rows"), so this is
the header being loose, not the theorem overclaiming.  Annotated.

**(ii) `:104-105`, `gOdd_supply` docstring, verbatim:**

> Wave 79 had this at `k ≤ 5` only (`gXf_supply_five`); the classes `k ≥ 6` were the open part.

Misattributed by one wave.  `gXf_supply_five` is in `GradedXFree.lean`, whose module docstring
is headed `# W80-XFREE`, and whose own docstring says "Wave 79 discharged the separation
(`gExt_separationAll`); this file discharges the extraction".  Wave 79 had the *conditional*
`gDeep_supply_five (hsep) (HR)`.  The substance - that `k ≥ 6` was open - is right.  Annotated.

**Checked and found accurate**, so that the next round does not re-check them:
`gOdd_arbRelWord`'s contrast with `SqEichRelWord` (`not_sqEichRelWord {h} (hh : 0 < h)`,
`EichRefutation.lean:380`, so "refuted for `h ≥ 1`" is exact); `gOdd_clearingStep`'s
"one handle at a time, every other handle's rows left where they were" (matches
`SqClearingStep`, `LamFrames.lean:606-615`, clause by clause); `gOdd_markedMatching`'s
"preserves χ itself" (the statement carries `chiSq h (u x) = chiSq h x`); and the §Compose
binder analysis in full (§2.1 above).

One naming observation, not an error: `gXf_markTransitivity_of_vanishing`,
`gXf_markTransitivity_of_kills` and `gXf_markTransitivity_of_residual` are all described as
"the `h ≥ 1` residual" or "the `h ≥ 1` stratum", but none of them binds `0 < h` and all cover
`h = 0`.  The names understate rather than overstate; annotated on the last of them.

## 2.5 (d) The wave-80 merge messages: 36 commits, two defects

The range `4f30776b..6f2916f3` is 36 commits.  The narrative is on the whole careful and
matches the tree: declaration names, signatures, hypothesis lists and every structural count I
re-checked (four `GenAsmRowResidual` fields, nine sites across five files at `a08e046f`, seven
vacuous layer-step theorems, 56 pins at `e59a5600`, `B.r ≤ 1` at both procyclic rows,
`GGenRecord` at `j ≥ 1`) is accurate.  Two defects.

**(i) ⚠⚠ HIGH - `a0b7fa0e` (the W80-FINAL merge) calls `GTowerKnobRealizable` refuted.**
Verbatim, line 18 of the message:

> the generation lane's own composite still carried the extraction interface that wave 79
> refuted as quantified

It was not refuted.  `docs/dyadic/w79-extract-note.md:129`, verbatim:

> **This is not a refutation**: nothing here shows that such a frame satisfies

and the same note states elsewhere that the claim "`GTowerKnobRealizable h` is false" is not
made and is not supported.  There is no `¬ GTowerKnobRealizable` anywhere in the tree, whereas
the genuinely refuted `Prop`s all have one (`gDeep_not_layerReach`, `gDeep_not_baseThree`,
`gDecide_not_joinBase`, `gDecide_not_baseResidual`).  This is the merge message borrowing the
word that belongs to those four.  It matters because the merge messages are the campaign's
narrative record and this one is the closing merge of the odd route.

The same wave's own W80-XFREE merge (`75498b2b`) gets it exactly right - "the abstract
interface is **neither proved nor refuted**" - so this is a slip in one message, not a
misunderstanding in the wave.  It is the same slip as `GradedOddClose.lean:17` (§2.3), one
notch stronger.

**(ii) ⚠ LOW - `427c4819` (the W80-HOUSE merge) miscounts a list.**  Verbatim:

> marked once at the definition with the five statements it does not touch named

The list at `GradedUniformTower.lean:1135-1137` names **six**: `SqClassClearingSupply h k`,
`GTowerDefectVanishing h`, `GTowerKnobRealizable h`, `gTower_clear_step`,
`gTower_supply_of_vanishing`, `limFinal_markTransitivity_iff`.  The adjacent count in the same
sentence ("seven theorems") is right, so this is an isolated off-by-one.

**Worth recording as a positive.**  `540ad3f7`, the W80-UNIFORM merge, caught the separation
staleness at merge time and said so, verbatim:

> One staleness note for the record: the lane's list of what remains
> names separation at h >= 1 as open, but its own base carries
> gExt_separationAll at every h, a wave-79 theorem.

So the orchestrator did see it.  What did not happen is the follow-through: the note itself was
left uncorrected, and so was the module docstring that says the same thing.  That is the actual
process gap - not detection, but the absence of a step that writes a merge-time finding back
into the artifact it is about.  Both are corrected in this lane (§2.2).

---

# Ticket 3: the endgame board

Report-only.  Nothing in this section was acted on.

## 3.0 What the odd closure did and did not move

`gOdd_markTransitivity` closes the odd route's *graded* problem.  It discharges the `hMix`
binder wherever that binder appears, and **zero of `GenAsmRowResidual`'s four obligation
fields**: the odd residual feeds the selector one layer earlier than the obligation record, so
the two never meet.  `GQ2/Dyadic/GeneralAssembly.lean` still calls it "the odd route's residual"
at `:449`, `:530`, `:609`, `:618`; annotated at `:530` in this lane, comment-only.

## 3.1 (a) The general theorem at every odd-degree ramified-`i` `K`

Two things stand between the tree and it.

**The seam (`oddId`).**  There is no declaration named `oddId` in the tree and no
`Instances/OddIdentification.lean`; the seam is the binder

```
e : OrientedContinuousMulEquiv (SqCore.chiSq h) (chiCycKTwo (K := K))
```

in `genAsm_branch_of_oddSq` (`GeneralAssembly.lean:621-633`) and its canonical form
`genAsm_branch_of_oddSq_canonical` (`:650-658`).  This binder **is** the odd-degree
classification statement; no theorem in the tree produces it at an arbitrary ramified-`i` `K`.
The canonical form already discharges `nuP`, `hnuP`, `hnuIota` via `lNu h`, and `hMix` is now a
theorem, so what `genAsm_branch_of_oddSq_canonical` still binds is `hdeg`, `e`, `hsigma`, `hx0`
- of which only `e` is deep.

**[W82-HOUSE, as of `a45bc557`: "no theorem in the tree produces it at an arbitrary ramified-`i`
`K`" IS FALSE, and was false at this lane's own base `6f2916f3`.**
`LSquare.nonempty_orientedEquiv_oddDegree`
(`Instances/GammaLSylowPreimageFieldLabuteCubicNeutral.lean:249`, landed 2026-08-05, i.e. ten
days before this note) gives `Nonempty (OrientedContinuousMulEquiv (chiSq (([K : ℚ₂] - 1) / 2))
chiCycKTwo)` from `B : MarkedRecip Rec K` and `Odd [K : ℚ₂]` and nothing else, at census
{B1, B6, B7, B11a}, verified here by elaborating its re-indexed form `oddId_orientedEquiv`.
Ramifiedness at odd degree is free (the next paragraph in this section says so), so `e` is free
at every odd-degree ramified-`i` `K`.

**The ranking in the last clause is inverted.**  What is deep is not `e` but the PAIR
`hsigma`, `hx0` AT the equivalence: the transported pivot row's parity is an invariant of the
target (`SqCore/PivotClimb.lean` §9) and the rows do not follow from orientation
(`Instances/GammaLSylowPreimagePivotNu.lean` §5, a refutation).  The seam is
`LSquare.SqMarkedForwardSupply B h`, which packages exactly the triple, and
`oddId_supply_iff_certificate` shows it is interchangeable with the `L`-row marked-core
certificate with no side binder.  So: the odd residual is the ROWS, not the EQUIVALENCE.

Two things this correction does NOT say.  It does not say the odd row is closed: the seam at
`h ≥ 1` is open, and §3.1a's `L h` CAND gap is untouched.  And it does not fault the adjacent
sentence "there is no declaration named `oddId` in the tree": that was true of `dyadic` when
this lane merged (a8c8ade6 precedes 21d9a8c8), and the `e` claim is independent of it.

The diagnosis is worth keeping with the correction, because this note's own headline is that
the wave-80 lanes "ran blind to each other and to their own base".  This sentence is the same
error one wave later, from the lane auditing for it: own-base blindness (the theorem predates
the base) compounded by sibling blindness (W81-ODDID was building on that theorem, off this
same base, in this same wave).  The in-tree copy at `GeneralAssembly.lean` is corrected at its
site.]**

Ramifiedness itself is **free** at odd degree:
`not_hasEqualNormValueGroups_sqrt_neg_one_of_odd_finrank`
(`GQ2/Dyadic/OddDegreeRamifiedI.lean:60-63`) is a theorem needing only `Odd (finrank ℚ₂ K)`.
That is the odd side's structural advantage over the even side.

**The three obligation blocks.**  `GenAsmRowResidual` (`GeneralAssembly.lean:283-299`) has
four fields; wave 80 wired one away, so three remain:

| field | ledger | status |
|---|---|---|
| `exactLifting` | ASK field 3 | one named `Prop` (`askCStageVanishing`); the corrected bundle is closed - see the update below |
| `stokes` | ASK field 4 | **CLOSED** at general degree, `askC_stokes_galK` - see the update below |
| `determinant` | ASK field 6 | **dischargeable**, wave 80: `mpcRow_determinant_of_bridge` over `affineDeterminant_galK` (`GaussZ/FinalDK.lean`) |
| `cand` | CAND | open; per-row, see §3.1a |

The `determinant` field's own docstring already carried the wave-79 correction that it was "a
binder because nobody wired it, not because the rung is missing"; wave 80 wired it, and
`mpcRow_genAsmRowResidual_of_counting` builds the record with no `determinant` argument.  With
the W81-ASK landing below, **the general row residual costs one block, not three**.

**§3.1a The `L h` CAND field.**  At `h ≥ 1` there is **no producer**, at any `h`.  At `h = 0`
it is discharged (`genCert_wordCertificate_nonempty_L_zero`).  With `e` still open, this is the
odd row's only other campaign-side gap.

**Correction carried forward.**  `GeneralAssembly.lean:273-280`'s CAND coverage table is stale:
it is a W75-STATE table and `GeneralCertificates.lean` (wave 76) improved three of its five
rows, including `Npc α r η h`, which the table records as "none | none" but which
`genCertNpcWordCertificate` (`GeneralCertificates.lean:727`) covers at free `(α, r, h, q)`.
Flagged in `docs/dyadic/w76-house-note.md` and never absorbed.  Not annotated here: it is a
five-row table and rewriting it is more than a marker.

## 3.2 (b) The same at even degree

**The classification is a theorem**, and this is the even side's structural advantage:
`parityFinal_evenClassification` (`Instances/EvenParityModel.lean:156-168`) produces the
oriented equivalence - the analogue of `e` - as an existential over `alpha ≥ 2`, given
`hram : ¬ HasEqualNormValueGroups K deltaI` and `hev : finrank ℚ₂ K = 2 + 2h`.  Where the odd
side has an unproved `e`, the even side has a proved one.

**Its price is `hram`.**  At odd degree ramifiedness is derived; at even degree it is assumed.
That is the trade.

**The consumers.**  `genAsm_branch_of_evenN` (`:579-590`) and `genAsm_branch_of_evenM`
(`:594-605`) still bind a raw oriented equivalence `e` plus `hpair` (N-family) or
`hMix`/`hpivot` (M-family).  The M-family `hMix` is `MMixHypothesis`, **not** the `SqCore` one
the odd closure discharged, so wave 80 does not reach it.

**`Hfam` / `EvenFamParitySupply`.**  Unchanged by wave 80, and the W65 finding stands: it is
proved *equivalent in strength* to the even classification at the field's own depth
(`hfamFinal_parityN_iff_orientedEquiv`, `hfamFinal_parityM_iff_orientedEquiv`,
`Instances/EvenFamilyStatus.lean:389-422`).  So it can be neither refuted nor discharged by
soft means: any proof of it at `K` proves the classification at `K`.

**The branch identifications: five, not four.**  The ticket says four exist at the quadratic
fields; the tree has **all five**, each a theorem:

| field | theorem | file |
|---|---|---|
| ℚ₂(√−2) | `hrangeFinal_sqrtNegTwo` | `Instances/EvenRangeModelFields.lean:626` |
| ℚ₂(√2) | `hrangeFinal_sqrtTwo'` | `Instances/EvenRangePolish.lean:271` |
| ℚ₂(√5) | `fieldId_hrange_sqrtFive` | `Instances/FieldBranchIdentification.lean:429` |
| ℚ₂(√10) | `fieldId_hrange_sqrtTen` | `Instances/FieldBranchIdentification.lean:438` |
| ℚ₂(√−10) | `fieldId_hrange_sqrtNegTen` | `Instances/FieldBranchIdentification.lean:451` |

The "four" is most likely a crossed wire with a different fact -
`docs/dyadic/literature-axioms-dyadic.md:133`, four rows carrying literal instantiations that
print byte-identically to their parametrized parents - which is about byte-identity, not branch
identification.

What is **three of five**, not five, is the full branch *datum* `GenAsmBranch` being
unconditional: √−2, √2 and √5 carry it outright, while √10 and √−10 carry it only over
`MpcRowData_sqrt{Ten,NegTen}`.

**[W82-HOUSE, as of `a45bc557`: FOUR of five, not three.**  W81-NORMS landed
`mpcNorm_genAsmBranch_sqrtTen` (`Instances/MpcNormValues.lean:1215`) unconditionally, at
exactly the axiom set of `mpcRow_genAsmBranch_sqrtTen` (both measured here: B1, B6, B7, B11a,
`peripheralCyclotomicAction`).  Only √−10 still carries a clause, and it is the `ε = true`
pivot alone (`mpcNorm_genAsmBranch_sqrtNegTen_of_pivot`), the level and all three congruences
having become theorems.  This lane merged before that one, so the count is a dated fact rather
than an error; recorded because the endgame board is read forward.]**

## 3.3 (c) The quadratic flagship unconditional at all five rows

The five per-row obligation structures are `ResidualSqrtNegTwo` (`Main.lean:352-381`),
`ResidualSqrtTwo` (`:391-429`), `ResidualSqrtFive` (`:435-473`), `ResidualSqrtTen`
(`:480-519`), `ResidualSqrtNegTen` (`:524-564`), bundled by `RowResidual` (`:569-574`).

**The norm values (rows 4 and 5).**  Wave 80 broke the two opaque `Prop`s
`MpcRowData_sqrt{Ten,NegTen}` into named arithmetic, and proved the level's upper half
outright:

* `B.r ≤ 1` at both fields: **theorem**, `mpcRow_level_le_one_sqrtTen` /
  `_sqrtNegTen` (`Instances/MpcRowData.lean:214,218`), by the scalar-`2` witness.
* `B.r = 1`: needs `MpcNoUnitKerChi B` (`:436-437`), **still a binder**.
* the `λ` clauses `MpcLambdaOne B (−1) p` and `MpcLambdaOne B (mUnit 2) 1` (`:442-443`):
  **still binders**.
* the pivot: **still a raw binder**, and the one conjunct with no equivalence-free form.

What remains is arithmetic, not classification: four values of the norm-group character, a
mod-8 congruence on norms of units plus one descent, and (for the pivot) freeness of `ℤ₂ˣ` as
`⟨−1⟩ × 5^{ℤ₂}`, of which the tree has only generation.

**The two ASK bundles.**  ASK appears in two shapes, and the asymmetry is real:

1. **bundled** - `structure KSupply` (`Instances/KSupply.lean:309-333`), carried as one field
   `KS` by the four M-family rows (`Main.lean:427-429`, `:471-473`, `:517-519`, `:562-564`);
2. **unbundled** - the pilot row spells only `hexact`/`hstokes` directly
   (`Main.lean:368-373`).  **The pilot record carries no `G_K`-side `determinant` field at
   all**, where `KSupply` and `GenAsmRowResidual` both do.

`exactLifting`/`stokes` were open struct-level binders at all five rows - ticket ASK, queued
and never done.  `determinant` became dischargeable at wave 80, and the ASK block moved again
during this lane; see the commit-time update below.

**`hdet`.**  `ResidualSqrtNegTwo.hdet : SqrtNeg2.PilotDet …` (`Main.lean:381`), **still open**,
and it is a *different* obligation from `KSupply.determinant`: `hdet` is the **candidate**-side
Gauss-`Z` clause, only at the pilot row, feeding `sqrtNegTwoWordCertificate`.  Its own docstring
(`Instances/SqrtNeg2.lean:880-885`) records that the two Gauss-`Z` clauses have no
candidate-side supplier in the repository.  Wave 80 left a fully worked, dispatchable brief for
it (`docs/dyadic/w80-house-note.md` Ticket 2) whose acceptance test is that
`ResidualSqrtNegTwo` loses its `hdet` field.  **Not taken as of this tree.**  The pilot's three
sibling candidate-side binders `PilotHsimp`, `PilotStageSep`, `PilotStageZ` are likewise open.

**The CAND row.**  Per-row producers exist for M0, Mpc, N0 and Npc (the last three improved by
`GeneralCertificates.lean` beyond what `GeneralAssembly.lean`'s table records, §3.1); none is
unconditional - all still take the four analytic clauses as hypotheses.  `L h` at `h ≥ 1` has
no producer at all.

**Summary of the flagship board.**  To get all five rows unconditional the tree needs: the one
surviving ASK clause `askCStageVanishing` (§3.4, down from three); `hdet` plus three siblings
at the pilot; the norm-value arithmetic at rows 4 and 5; and a CAND producer that does not
re-bind the analytic clauses.  The odd closure moved none of these, and never claimed to -
`GradedOddClose.lean:45-48` says so explicitly, and that disclaimer is accurate.

## 3.4 COMMIT-TIME UPDATE: W81-ASK landed mid-lane and moved the ASK block

Caught by the standing re-check of status words at commit time.  `dyadic` advanced past this
lane's base `6f2916f3` while the lane was running: `091ea7f0` (merge of `claude/w81-ask`) and
`5a55cb57` (registration), adding `GQ2/Dyadic/Instances/AskCounting.lean`, 481 lines.  I read
the module rather than the merge message, per §2.5's own discipline.  The claims hold:

* **`stokes` is CLOSED at general degree.**  `askC_stokes_galK` (`AskCounting.lean:101`) proves
  `StokesDualityCertificate (galKProfinite K) n (qOf K FF) P nuP (standardNumerics n)
  (smulZmod2GalK K)` from `hdeg : finrank ℚ₂ K = n` alone, in the exact spelling
  `KSupply.stokes` and `GenAsmRowResidual.stokes` are written at.  All four clauses.
* **The half-torsor existential is owned.**  `askC_halfTorsor_galK` (`:112`) - the conjunct
  `KSupply.lean` §4 calls "the `K` analogue of `RadicalEdgeLocal.exists_good_twist`, unowned".
  It was owned: `Count.exists_nonzero_varCoc_of_tateDualityG` plus `Count.lem86N`.
* **The corrected exact-lifting bundle is closed at every degree.**
  `askC_exactLiftingRN_galK` (`:121`) gives `ExactLiftingSemanticsRN` at every degree; only the
  *frozen* bundle's third conjunct is open, and it is measured, not hand-waved, by the named
  `askCStageVanishing` (`:184`) with `askC_exactLifting_iff_stageVanishing` (`:259`) an
  equivalence at the campaign's degree.
* **The record consequence.**  `askCKSupply_of_markedCore` (`:372`) builds a whole `KSupply` at
  general degree taking `hvan` and no `stokes` or `determinant` argument.

**So §3.1's and §3.3's "the two ASK analytic clauses are unowned" is wrong as of `091ea7f0`,
and the general row residual costs ONE block, not three.**  I am recording this rather than
quietly rewriting the sections above, because the shape of the error is the one this whole
lane is about: I wrote a remains-list, and a sibling had already closed two of its items.
The difference from the wave-80 instances in §2.2 is only that this one was caught before
merge, by the re-check the protocol mandates and not by luck.

Two further consequences the sibling reports and I did not re-derive: the recommended repair
(restating the rows against the degree-free bundle) is a **statement change**, reported and not
made; and the sharp finding that carrying the frozen field at degree two asserts the Galois
group admits no boundary-framed surjection onto any marked target with nontrivial Frattini
block.  Both belong to that lane's note, `docs/dyadic/w81-ask-note.md`.

## 3.5 One staleness correction owed elsewhere

`docs/dyadic/w80-rowdata-note.md` §7 items 3 and 4 are both stale as of this tree: item 3 asks
for `MpcRowData.lean` to be registered in `GQ2.lean`, which `GQ2.lean:870` already does; item 4
says `fieldUni_TwoIsUniformizer KSqrtFive` "is still open (row 3)", but
`fieldFive_twoIsUniformizer` (`Instances/FieldSqrtFiveUnramified.lean:209`) proves it with no
hypotheses, landed wave 79.  Left uncorrected here only because that note is a sibling lane's
record from a different ticket; flagged for the orchestrator.

---

# Owner items

Carried forward, unchanged by this lane.

1. **The A6 freeze** - `GQ2/Roe/*` frozen, now **eight** review rounds without motion (seven at
   the wave-80 round, per `docs/dyadic/owner-items-2026-08-05.md`).  Nothing in this lane
   touched `GQ2/Roe/` or `GQ2.lean`.  It remains the only owner item with no motion across the
   whole run.
2. **Line length** - the corpus has lines over 100 *bytes* but none over 100 *codepoints*;
   the two measures differ because of `⭐ ⚠ ≥ ₂ γ ν`.  Every file this lane touched is at
   zero over-100-codepoint lines, verified.  If the owner's linter counts bytes, that is a
   standing pre-existing divergence and not a wave-81 regression.

   **[W82-HOUSE, as of `a45bc557`: the per-file half is right, the corpus half is wrong.**
   Counting codepoints, `GQ2/` carries **707** lines over 100 in **250** files, not zero.  The
   worst single line in the ASK chain was `Instances/KSupply.lean:275` at **135** codepoints
   (fixed in passing this round, since the sentence on it was also stale).  Wave 81 did
   regress the measure: `Instances/AskCounting.lean` lands **6** over-100-codepoint lines
   (`:20` at 121, `:21` at 112, `:22` at 109, `:23` at 104, `:442` at 101, `:450` at 129), all
   of them markdown table rows inside docstrings.  The other two wave-81 modules are clean
   (`OddIdentification.lean` 0, `MpcNormValues.lean` 0), so the claim held for the files this
   lane checked and was over-generalized to the corpus.]**
3. **Pilot record** - unchanged.
