# W80-FINAL: the odd route closes

**Lane W80-FINAL, branch `claude/w80-final`, base `97f1cc0c`** (the merge point carrying BOTH
wave-80 sibling modules).  One new module, `GQ2/Dyadic/SqCore/GradedOddClose.lean` (prefix
`gOdd`), 245 lines, 15 declarations, 15 `#print axioms`, every one
`[propext, Classical.choice, Quot.sound]`.  No edits to any existing file, no `sorry`, no new
axiom, no `native_decide`, no heartbeat or recursion-depth options.  New leaf module, `GQ2.lean`
untouched per protocol.

Commit: `7d78e2e5`.

Verification of record: `scripts/mirror.sh sweep` at lane start (5923 artifacts), then
`gen GQ2.Dyadic.SqCore.GradedXFree` and `gen GQ2.Dyadic.SqCore.GradedUniformGen` to put the two
sibling oleans into the mirror ahead of the cache, then `check` and `gen` on this module.  Zero
errors, zero warnings, zero sorries.  The module compiled on the first attempt; no statement was
weakened and no bridge lemma was needed.

---

## Headline

**`SqLamMarkTransitivity h` is a theorem at every `h`, with no hypothesis of any kind.**  The odd
route's residual, which has been the odd-degree row's open input since wave 44 and the graded
campaign's target since wave 51, is closed.

```
gOdd_killResidual   : GXfKillResidual h                       (the weakening, 2 <= k  ->  4 <= k)
gOdd_markTransitivity : SqLamMarkTransitivity h               ⭐⭐⭐ UNCONDITIONAL, every h
gOdd_supply         : SqClassClearingSupply h k, every h, k   (wave 67 read-back)
gOdd_arbRelWord     : SqArbRelWord h                          (the word form)
gOdd_clearingStep   : SqClearingStep h                        (the clearing scheme)
gOdd_handleMix      : IsUnit c -> SqHandleMixFixesCore h c    ⭐⭐⭐ the K-facing binder
gOdd_pivotFix       : SqHandleMixFixesCore h sqPivotExp       (the canonical spelling)
gOdd_markedMatching : chi-preserving correction onto nu_sq    (at every selected marking)
gOdd_nuClear        : SqNuClearHypothesis h                   (the chi-free target)
gOdd_certificate    : MarkedCoreCertificateSq, no handle binder  (furthest committed)
```

The composition is two lines of Lean.  All of the mathematics is in the two sibling modules; this
lane's job was to check that their binders meet, and they do, exactly.

---

## 1. The binder check

This was the one thing that could have failed, so it is recorded in full.

### 1.1 What each side says

`GradedXFree.lean:1024` (prefix `gXf`):

```
def GXfKillResidual : Prop := ∀ k, 4 ≤ k → GDeepKillAt h k

theorem gXf_markTransitivity_of_residual (H : GXfKillResidual h) : SqLamMarkTransitivity h
```

`GradedUniformGen.lean:946` (prefix `gGen`):

```
theorem gGen_killAt : ∀ k, 2 ≤ k → GDeepKillAt h k
```

Both sit in a section with `variable {h : ℕ}`, so the `h` is the same implicit natural number in
both, with no side condition on it (no `0 < h`, no parity, no bound).

### 1.2 The subject they share

`GDeepKillAt` (`GradedDepthThree.lean:937`) is a `def ... : Prop` of **two** explicit arguments,
`h` and `k`, and nothing else:

```
def GDeepKillAt (k : ℕ) : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
    ∀ g ∈ twoCentralSeries (DSq h : Type) (k + 1), nuLam h g = 1 → nu' g = 1 →
      (∀ c : Fin (sqRank h) → ℤ_[2], gDelta h c g = 0) →
      levelMk (DSq h : Type) (k + 2) g ∈ gTowerReach h nu' k
```

Three things worth stating explicitly, because each is a place a mismatch could have hidden:

* **The marking `ν'` is quantified INSIDE the definition**, universally, with its two selected
  core rows as hypotheses.  Neither side carries a `ν'` in its own binder list, so there is no
  question of one lane proving the ladder at a marking the other lane does not use.
* **There is no handle parameter at all.**  `GDeepKillAt` never mentions `Fin h` or a handle
  index; the handle enters only further downstream, in `GJoinDefectVanishing` and
  `SqClassClearingSupply`, where both lanes route through the same committed
  `gDeep_defectVanishing_of_kills`.  So there is no marking/handle scope mismatch to bridge.
* **The `k`-indexing convention is one and the same**, because it is literally the same `def`:
  the element sits in `γ_{k+1}` and the conclusion reads at level `k + 2` into
  `gTowerReach h nu' k`.  Neither lane re-indexed it.

### 1.3 The composition

`gGen_killAt` proves the family on `k ≥ 2`; `GXfKillResidual h` asks for it on `k ≥ 4`.  The only
step is the weakening:

```
theorem gOdd_killResidual : GXfKillResidual h := fun k hk => gGen_killAt k (by omega)
theorem gOdd_markTransitivity : SqLamMarkTransitivity h := gXf_markTransitivity_of_residual
                                                              (gOdd_killResidual h)
```

**No binder mismatch was found.**  Nothing had to be re-quantified, re-indexed, generalized or
specialized; there is no bridge lemma in the module because none was needed.

### 1.4 Why neither lane could have written this itself

Worth recording, since it is the reason the composition is momentous rather than clerical.

* `GradedUniformGen`'s own composite `gGen_markTransitivity` still carries **two** hypotheses,
  `GJoinSeparationAll h` and `GTowerKnobRealizable h`, because that lane routed through
  `gDeep_markTransitivity_of_kills`, which takes them.  The first is wave 79's
  `gExt_separationAll` and is discharged; the second is the extraction, and wave 79 proved it
  does **not** hold as quantified.  So the uniform lane, alone, ends at a statement whose second
  hypothesis is not available.
* `GradedXFree` is exactly the repair of that second hypothesis: it replaces
  `GTowerKnobRealizable h` by the `x₁`-free form `GXfKnobRealizable h`, which is a theorem
  (`gXf_knobRealizable`), threads the freeness clause through the supply recursion, and
  internalizes `gExt_separationAll`.  That is why `gXf_markTransitivity_of_residual` has exactly
  **one** hypothesis where `gDeep_markTransitivity_of_kills` has three.  But that lane could only
  get the ladder at `k = 2, 3` from the tree, so it stopped at `GXfKillResidual`.

Each lane removed precisely what the other could not.

---

## 2. The read-backs inside the graded route (§2 of the module)

Wave 67 proved `SqLamMarkTransitivity h ↔ ∀ k, SqClassClearingSupply h k`
(`limFinal_markTransitivity_iff`) and the wave-51 era proved
`SqArbRelWord h ↔ SqLamMarkTransitivity h` (`sqArbRelWord_iff_lamMarkTransitivity`).  Those
equivalences were stated when the left-hand side was open; they now have a proved left-hand side,
so the whole equivalence class collapses to theorems.  The module takes the read-backs through
wave 67's `iff` rather than re-running the direct chain, which makes the dependence on the
compactness assembly explicit.

* `gOdd_supply (h k : ℕ) : SqClassClearingSupply h k`.  Wave 79 had this at `k ≤ 5` only
  (`gXf_supply_five`); classes `k ≥ 6` were the open part, and they are now closed.
* `gOdd_limFinalResidual : LimFinalResidual h`, wave 67's own residual statement, discharged.
* `gOdd_arbRelWord : SqArbRelWord h`.  This is the word-level statement: at every selected
  marking and every handle there is a `λ`-trivial, `ν'`-trivial dressing whose frame spans `H₁`
  and kills the relator outright.  Note the contrast with `SqEichRelWord`, `SqEichRelWordT`,
  `SqEichRelWordMix` and `SqEichRelWordUV`, all four of which are **refuted** for `h ≥ 1`
  (`EichRefutation.lean`).  The arbitrary-dressing widening was the right one.
* `gOdd_clearingStep : SqClearingStep h`, the family-agnostic clearing scheme.
* `gOdd_defectVanishing : GJoinDefectVanishing h` and `gOdd_chiSupply : GXfChiSupply h k`, the
  two wave-75/wave-80 interface shapes, recorded because several earlier modules quote them as
  inputs.

---

## 3. The `K`-facing read-backs (§3 and §4 of the module)

`SqLamMarkTransitivity h` is the hypothesis-free form.  What the certificate machinery actually
consumes is the handle stratum `SqHandleMixFixesCore h c`.  The passage
(`sqHandleMixFixesCore_of_lamMarkTransitivity`) costs `0 < h` and `IsUnit c`; `h = 0` is
separately a theorem (`sqHandleMixFixesCore_zero`, for every `c`).  So:

```
gOdd_handleMix (h : ℕ) {c : ℤ_[2]} (hc : IsUnit c) : SqHandleMixFixesCore h c
```

holds at **every** `h`, by a two-case split.  Specialized at the canonical exponent
(`isUnit_sqPivotExp`) this is `gOdd_pivotFix : SqHandleMixFixesCore h sqPivotExp`, which is the
spelling the `L`-row producers and `SqCore/PivotClimb.lean` use for their `hfix` binder.

From there the module records, in increasing strength:

* `gOdd_handleMixHypothesis`: MC5's weaker `SqHandleMixHypothesis h c`, a fortiori.
* `gOdd_markedMatching`: at every selected marking there is a **χ-preserving** continuous
  automorphism carrying it to `ν_sq`.  This is a genuinely different clause from §1's, which
  preserves the χ-**exponent functional** `λ`; the certificate consumes the χ-preserving form.
* `gOdd_nuClear : SqNuClearHypothesis h`, the χ-free target, which is what
  `MarkedCoreRealization (DSq h) (lNu h)` consumes and nothing more.
* `gOdd_lamNuClear : SqLamNuClearHypothesis h`, the same statement under its clearing-condition
  name.

**The furthest committed consequence** (module §4) is
`marked_matching_certificate_sq_of_fixesCore` with its handle binder discharged:

```
gOdd_certificate {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ℕ) (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2])
    (f : ContinuousMulEquiv (DSq h : Type) G)
    (horient : ∀ x, chiG (f x) = chiSq h x) (hcont : Continuous fun x => nuG (f x))
    (hsigma : nuG (f (dsqSigma h)) = ofAdd (1 : ℤ_[2]))
    (hx0 : nuG (f (dsqX0 h)) = ofAdd (0 : ℤ_[2])) :
    Nonempty (MarkedCoreCertificateSq h chiG nuG)
```

On an abstract slot, the odd row's marked-core certificate now costs exactly an oriented
identification, its continuity data, and the two selected core rows.  **No correction-stratum
hypothesis remains in it.**

This is as far as `SqCore` can carry the result without importing downstream.  Turning the
abstract slot into `G_K(2)` is `LabuteInterface.lean`'s
`marked_matching_certificate_KTwoSq_of_fixesCore`, and then `GeneralAssembly.lean`'s
`genAsm_branch_of_oddSq` / `genAsm_branch_of_oddSq_canonical`.  Neither is imported here, so the
statement of what happens there is prose, in §4 below, not Lean.

---

## 4. What this does and does NOT close

The single sentence to carry forward: **the odd route's residual is closed; the odd row's branch
datum is not, and the general assembly's obligation record is untouched.**

### 4.1 What becomes dischargeable

Exactly one named binder in the downstream tree, and its clones:

| binder | where | status now |
| --- | --- | --- |
| `hMix : SqCore.SqHandleMixFixesCore h c` | `GeneralAssembly.lean:627` (`genAsm_branch_of_oddSq`, at `:621`) | **theorem** at every `h`, every unit `c` |
| the same, canonical form | `GeneralAssembly.lean:653` (`genAsm_branch_of_oddSq_canonical`, at `:650`) | **theorem** |
| `hMix` | `LabuteInterface.lean:167` (`marked_matching_certificate_KTwoSq_of_fixesCore`) | **theorem** |
| `H` | `Certificate.lean:533` (`marked_matching_certificate_sq_of_fixesCore`, at `:528`) | **theorem**, recorded as `gOdd_certificate` |
| `hfix : SqHandleMixFixesCore h sqPivotExp` | `PivotClimb.lean:806`, `:835` | **theorem** (`gOdd_pivotFix`) |

`genAsm_oddResidual_gives_mix` (`GeneralAssembly.lean:613`) is the statement that reads the mix
off the residual; its hypothesis `H : SqCore.SqLamMarkTransitivity h` is now a theorem, so that
implication can be applied unconditionally.  A one-line downstream restatement is available to
whoever wires it; this lane wrote no downstream edit.

⚠ **`PivotClimb.lean:806/:835` is only half freed.**  `sqNuOrientedClearAtUnitPivot_of_pivotMoves`
takes `hfix` **and** the pivot-move family `hmv`.  Only `hfix` is discharged.  The pivot family is
untouched by anything in this lane.

### 4.2 `GenAsmRowResidual`: ZERO of the four fields become dischargeable

The record (`GeneralAssembly.lean:283`) has exactly four fields, and none of them is on the odd
route's residual path:

| field | block | dischargeable by this lane? |
| --- | --- | --- |
| `exactLifting` | ASK, ledger field 3 at `G_K` | **no**, arithmetic counting pack, untouched |
| `stokes` | ASK, ledger field 4 at `G_K` | **no**, untouched |
| `determinant` | ASK, ledger field 6 at `G_K` | **no**; the `K` clone exists (`affineDeterminant_galK`, per W79-HOUSE) but the wiring is a separate ticket, unrelated to this one |
| `cand` | CAND, the `WordCertificate` over the row's own slot | **no**.  On the `L 0` row it is *already* discharged, independently, by `GeneralCertificates.lean`'s `genCert_wordCertificate_nonempty_L_zero`; on the `L h` row at `h ≥ 1` there is **no producer at all** |

The structural reason: `GenAsmRowResidual` is the *obligation surface* attached to a branch datum
that already exists.  The odd residual feeds the *selector*, i.e. it discharges an input to
`GenAsmBranch`'s producer, one layer earlier.  The two never meet.

### 4.3 The `L`-row branch datum is still not producible

Freeing `hMix` leaves `genAsm_branch_of_oddSq_canonical` asking for:

* `hdeg : Module.finrank ℚ_[2] K = (SelectedPresentation.L h).degree`, the degree pin (odd,
  `1 + 2h`);
* `e : OrientedContinuousMulEquiv (SqCore.chiSq h) (chiCycKTwo (K := K))`, **the odd-degree
  classification output**, which no theorem in this tree produces at an arbitrary ramified-`i`
  `K`;
* `hsigma`, `hx0`, the two `ν`-normalizations at `σ` and `x₀`.

So the honest phrasing is: *the marking-transitivity input to the odd row's certificate is now a
theorem at every `h`*.  It is **not** the case that the odd-degree classification is proved; `e`
is exactly the classification statement and it remains a hypothesis.  Do not read §1 as more than
it says.

### 4.4 Untouched entirely

* **The even route.**  `Hfam` and the exact-fibre parity supplies
  (`EvenFamParitySupply{N,M}`, `Instances/EvenFamilyStatus.lean`) are arithmetic at a field and
  have nothing to do with `D_sq`.  W65-HFAM's finding stands unchanged: `Hfam` can be neither
  refuted nor softly discharged.
* **The quadratic flagship's ASK/CAND obligations.**  All of them, on all five rows.
* **`GenAsmFieldInputs`.**  Six fields, none touched; `ramified` is the standing hypothesis that
  *selects* `K` and is never to be discharged.
* **The `M`, `N`, `Mpc`, `Npc` rows.**  `MMixHypothesis`, `hpivot`, `hpair` and the per-branch
  certificate producers are even-side and unaffected.

---

## 5. One correction to the sibling notes

`docs/dyadic/w80-uniform-note.md`'s headline says that after that lane "what now stands between
the tree and `SqLamMarkTransitivity h` is exactly the two wave-75 interfaces: `GJoinSeparationAll
h` and `GTowerKnobRealizable h`".  That was accurate as a reading of `gGen_markTransitivity` in
isolation, and it is the reading that would have left the wave stuck, since `GTowerKnobRealizable
h` is the statement wave 79 showed the route does not prove as quantified.  The sibling lane had
already removed it.  Neither note is wrong about its own module; the pair is what closes.

---

## 6. Queue

Nothing in `SqCore` is owed by the odd route any more.  The natural next items, none of them
taken here:

1. **Wire the mix downstream.**  `genAsm_oddResidual_gives_mix`'s hypothesis is a theorem; a
   hypothesis-free `L`-row restatement in `GeneralAssembly.lean` costs one line plus an import,
   and would make the odd row's remaining binder list visible in the tree rather than in this
   note.  Requires editing an existing file, so it is an owner decision.
2. **Annotate the superseded statements.**  Every `..._of_kills`, `..._of_residual`,
   `..._of_vanishing` and `..._of_baseThree` composite in `GradedAbsorption`, `GradedExtraction`,
   `GradedDepthThree`, `GradedUniformJoin`, `GradedUniformTower`, `GradedXFree` and
   `GradedUniformGen` now has an unconditional conclusion available.  They are not wrong and not
   vacuous, but a reader arriving at them will not know they are superseded.  This is a
   comment-only sweep of the same shape as W80-HOUSE's.
3. **The `L h` CAND field at `h ≥ 1`**, which has no producer and is now the odd row's only
   remaining *campaign-side* gap other than the classification output `e` itself.
4. **`PivotClimb`'s pivot-move family**, the other half of `sqNuOrientedClearAtUnitPivot_of_pivotMoves`.
