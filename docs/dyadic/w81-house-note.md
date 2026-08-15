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

## 2.5 (d) The wave-80 merge messages

Reported separately below once the spot-check completes.

---

# Ticket 3: the endgame board

Reported below.

---

# Owner items

Carried forward, unchanged by this lane.

1. **The A6 freeze** - `GQ2/Roe/*` frozen. Round count carried; nothing in this lane touched
   `GQ2/Roe/` or `GQ2.lean`.
2. **Line length** - the corpus has lines over 100 *bytes* but none over 100 *codepoints*;
   the two measures differ because of `⭐ ⚠ ≥ ₂ γ ν`.  Every file this lane touched is at
   zero over-100-codepoint lines, verified.  If the owner's linter counts bytes, that is a
   standing pre-existing divergence and not a wave-81 regression.
3. **Pilot record** - unchanged.
