# W80-XFREE lane note

Branch `claude/w80-xfree`, based on `4f30776b`.  One new module,
`GQ2/Dyadic/SqCore/GradedXFree.lean` (prefix `gXf`).  No `sorry`, no new axiom, no
`native_decide`, no heartbeat or recursion-depth bump.  Every declaration carries a
`#print axioms` line in the file's own pin section; all report
`[propext, Classical.choice, Quot.sound]` except `gXf_ofFn_one` (`[propext, Quot.sound]`) and
`gXf_ne_of_val_ne` (no axioms).

Verification of record: `scripts/mirror.sh sweep` at lane start, then
`scripts/mirror.sh gen GQ2.Dyadic.SqCore.GradedXFree` after every edit.  Nothing in the tree
imports this module (registration in `GQ2.lean` is the orchestrator's), so there is no
dependent to re-check.

## Headline

**`SqClassClearingSupply h 5` is UNCONDITIONAL**, at every `h`, every selected marking and
every handle (`gXf_supply_five`).  Wave 79's `gDeep_supply_five` took two inputs; both are
gone.  The extraction is discharged in the form that survives wave 79's quantifier analysis,
and what remains of the whole graded `h >= 1` route is the kill ladder at `k >= 4`:

```
gXf_markTransitivity_of_residual : GXfKillResidual h -> SqLamMarkTransitivity h
GXfKillResidual h := forall k, 4 <= k -> GDeepKillAt h k
```

## T1: the invariant

`gXfSpan h := gTowerFar h ⊔ γ₂`, and `GXfFree h a := ∀ i, a i ∈ gXfSpan h`.

Taking the clause as membership in a **subgroup** is what makes it an invariant for free:

* **preservation** (`gXf_free_mul`, `gXf_free_mul_gamma`): a depth-`k` correction with `k ≥ 2`
  lies in `γ₂ ≤ gXfSpan h`, so `a · d` is `x₁`-free whenever `a` is.  No bracket computation is
  involved, unlike the "corrections are invisible to the brackets" phrasing of the wave-79
  note: that fact is used later, where the clause is *consumed*, not here.
* **base** (`gXf_bridgeTuple_free`, via `gXf_bridgeDress_far`): `bridgeDress` is
  `u_j^{ν'(v_j)}·v_j^{ν'(u_j)}·w^{-2ν'(u_j)ν'(v_j)}`, three `ℤ₂`-powers of far-span elements
  (`gBase_handleU_far`, `gBase_handleV_far`, `gAbs_pivot_far`), and the far span is closed
  (`gTower_zpow_mem`).  So the base dressing lies in `gTowerFar h` **outright**, with no `γ₂`
  slack; the `γ₂` summand of `gXfSpan` is there only for the corrections.

The shape chosen is the **weakened interface**, not a strengthened invariant threaded through
the committed recursion: the consumers (`gAbs_clear_step_two`, `gDeep_clear_step_three`,
`gJoin_clear_step`) take `GTowerKnobRealizable h` as a hypothesis quantified over *all*
admissible dressings, and no weakening composes with them without editing them.  §8 therefore
re-runs the same recursion carrying the clause (`GXfChiSupply`), which is 40 lines and costs
nothing: every other clause of the step is verbatim wave 75's.

## T2: what closes the extraction

### The missing fact, and how it is proved

Wave 79's paper argument was a dimension count in the Frattini quotient: the `2 + 2h` non-`x₁`
frame slots are independent, lie in the `x₁`-free hyperplane `W`, and `dim W = 2 + 2h`, so they
span `W`.  That needs `V = D_sq h / γ₂` as a finite `𝔽₂`-space with a known dimension, and
`W` as a hyperplane in it - none of which is in the tree.

The Lean proof does the same argument with **cosets instead of dimensions**, and needs no
vector-space structure at all.  The tool is `sqEps` (`DsqDemushkin.lean` §2), the characteristic
vector of the mod-two cup form, whose defining property is exactly what is wanted:
`toAdd_sqEps_gen i = if i = 2 then 1 else 0`, so `ε` reads the `x₁`-coordinate of a letter and
nothing else.  Then:

* `gXf_far_le_half`, `gXf_gammaTwo_le_half`, `gXf_xOne_notMem_half`: `ker ε` contains the far
  span and `γ₂` and misses `x₁`.  (`γ₂ ≤ ker ε` because the target is commutative of exponent
  two, so `twoCentralSucc ⊤`'s two generating families both die.)
* `gXf_eq_top_of_indep`: `SqModTwoIndep` read through the pro-`2` Frattini criterion at the
  **subgroup** rather than the endomorphism (`eq_top_of_forall_not_le_index_p`): a closed
  subgroup carrying every slot of a mod-two independent frame is `⊤`.
* ⭐⭐⭐ `gXf_far_le_of_slots`: let `K` be closed, carry `γ₂`, carry the `2 + 2h` non-`x₁`
  slots, have those slots inside `ker ε` and the `x₁`-slot outside.  Then `gTowerFar h ≤ K`.
  Proof: `S = K ⊓ ker ε` is closed and normal (it contains `γ₂`), `m₂² ∈ γ₂ ≤ S`, so
  `closure {m₂} ⊔ S` has underlying set exactly `S ∪ m₂·S` (`Subgroup.mul_normal` plus the
  even/odd split of the `zpow`), which is closed and carries every slot, hence is `⊤`.  A far
  element lies in `ker ε`, so it cannot lie in the coset `m₂·S`, so it lies in `S ≤ K`.

### The two scoped Lean steps the ticket named

* `gXf_move_mul`: **`gExtMove` is a homomorphism in the correction tuple**, for any frame, at
  `k ≥ 2`.  Per slot: `gXf_commP_left` (the correction term of `cfour_commP_mul_left` is a
  bracket against a top-layer element, killed by `cfive_commP_zLayer_left`), `gXf_commP_right`
  (same, plus one central swap; it needs no hypothesis on the second factor at all), and
  `gXf_sq_mul` (the `cfour_sq_mul` defect is a bracket of two `γ_k`-slots, killed by
  `gTower_commP_vanish`).  The blocks recombine by `gXf_shuffle4`, three applications of one
  two-block shuffle, because every knob value is central (`zLayer_le_center`).
* `gXf_commHom_far_span`: **`gTower_commHom_span` restricted to `gTowerFar`** - the same
  closure argument run against `gTowerFar`'s own generators, so a far bracket reduces to the
  `2 + 2h` non-`x₁` letter brackets and never asks for the `x₁` one.

  **Honesty marker.** This one turned out **not to be needed** for the composite: the coset
  route of `gXf_far_le_of_slots` places the whole far span inside the comap subgroup directly,
  so the reduction to letters is subsumed.  It is kept because it is a genuine strengthening of
  a committed lemma and is the natural tool if a later lane wants the letter-level statement.

### The extraction

* `gXfMove nu' hk m`: the **move subgroup** of a frame - the layer classes by which an
  admissible depth-`k` correction tuple multiplies the relator.  A subgroup precisely by
  `gXf_move_mul` (with `gXf_move_one` for the unit and the homomorphy for the inverse).
* `gXf_frame_mem_move`: `commP t (m i)` is a move for **every** `i ≠ 2`.  Slot `0` supplies the
  bracket against `m 1`, slot `1` the bracket against `m 0` on the other side (so its inverse),
  slot `u_j` the bracket against `m (v_j)`, slot `v_j` the bracket against `m (u_j)`.  That is
  the pairing wave 79's note described, and it is a bijection of the non-`x₁` slots.
* ⭐⭐⭐ `gXf_span_mem_move`: on an `x₁`-free frame, `commP t q` is a move for **every**
  `q ∈ gXfSpan h`.  The comap of `gXfMove` along `cfiveCommHom` is a closed subgroup carrying
  `γ₂` (brackets against `γ₂` die) and the non-`x₁` slots, so `gXf_far_le_of_slots` applies.
* ⭐⭐⭐ `gXf_knobSet_le_move`: **every knob generator is a move.**  The far knobs are the
  previous item.  The bundle knob `t²·[t, x₁]` is the `x₁`-slot move corrected by one far knob:
  the `x₁`-slot frame value is `x₁ · a₂` with `a₂` `x₁`-free, so the slot-2 move is
  `t²·[t, x₁]·[t, a₂]` and `[t, a₂]` is itself a move.
* ⭐⭐⭐ `gXf_realizable` / `gXf_knobRealizable`: **the extraction.**  On a mod-two independent
  frame with an `x₁`-free dressing, a knob-span defect class is killed by an admissible
  depth-`k` correction tuple.  The two marking hypotheses of `GTowerKnobRealizable` and the
  `γ_{k+1}`-membership of the relator are **not used** and are not in the statement.

## T3: the composite

`GXfChiSupply h k` is `GJoinChiSupply h k` with the clause.  `gXf_chiSupply_three` is the
committed `bridgeTuple` witness plus T1's base; `gXf_clear_step_of_knob` is wave 75's step with
`gXf_realizable` in place of the interface and `gXf_free_mul_gamma` for the new clause.  Then

* `gXf_chiSupply_four` from wave 78's `gAbs_vanishingTwo_of_sep`;
* `gXf_chiSupply_five` from wave 79's `gDeep_vanishingThree_of_sep`;
* ⭐⭐⭐ `gXf_supply_five (h : ℕ) : SqClassClearingSupply h 5`, **no hypotheses**, using wave
  79's `gExt_separationAll` for the separation;
* `gXf_supply_of_vanishing`, `gXf_markTransitivity_of_vanishing`: the supply at every class and
  the residual, from `GJoinDefectVanishing h` alone;
* ⭐⭐⭐ `gXf_markTransitivity_of_kills`: `(∀ k ≥ 2, GDeepKillAt h k) → SqLamMarkTransitivity h`,
  and hence `gXf_markTransitivity_of_residual` from the ladder at `k ≥ 4` only, since
  `gDeep_killAt_two` and `gDeep_killAt_three` are theorems.

### What remains, verified against the binders

`GDeepKillAt h k` (`GradedDepthThree.lean` §8) is

```
∀ ν' selected, ∀ g ∈ γ_{k+1} with λ(g) = ν'(g) = 1 and every gDelta-reading zero,
  levelMk (k+2) g ∈ gTowerReach h ν' k
```

`gDeep_defectVanishing_of_kills` consumes exactly `∀ k ≥ 2, GDeepKillAt h k` and
`GJoinSeparationAll h`; the latter is wave 79's theorem.  `gXf_markTransitivity_of_vanishing`
consumes exactly `GJoinDefectVanishing h`.  So after this lane the graded route's residual is
`GXfKillResidual h` and nothing else - the rungs `k = 2, 3` are `gDeep_killAt_two` and
`gDeep_killAt_three`.

## Honesty markers

* T1, T2 and T3 are theorems, unconditional, at every `h`.  `gXf_supply_five` takes only `h`.
* The extraction is proved **on `x₁`-free dressings**, which is what wave 79 scoped.  This
  lane does **not** prove `GTowerKnobRealizable h`, and does not refute it: the file says
  nothing about frames whose dressing carries an `x₁`-component.  The committed consumers that
  take `GTowerKnobRealizable h` as a hypothesis are untouched and still take it; §8's chain is
  a parallel re-derivation, not a rewiring of theirs.
* `gXf_commHom_far_span` landed but is unused by the composite (see the marker above).
* The `x₁`-freeness of `bridgeDress` is a proof here, not a reading: `gXf_bridgeDress_far`
  derives it from the far-span membership of the two handle letters and the pivot.  Wave 74's
  "unipotent mod-2 letter matrix" claim is neither used nor re-derived.
* Nothing in this lane touches `GDecideBaseThree h`; the odd route's `k ≥ 4` kill ladder and
  that base are separate obligations, and the composite above routes through the ladder.

## What W81 needs

1. **The kill ladder at `k ≥ 4`** (`GDeepKillAt h k`) is now the *only* open input of the
   graded `h ≥ 1` route.  It is the sibling lane's territory; the rungs at `k = 2, 3` are the
   pattern (`gAbs_zero_reader_reach`, `gDeep_zero_reader_reach`).
2. If a later lane wants the extraction at frames the recursion does **not** produce, the
   missing ingredient is exactly the `x₁`-slot bare bracket `[t, x₁]` unbundled from `t²`, and
   `gTower_comm_x1_split` is the committed way to manufacture it one level up.
3. `gXf_far_le_of_slots` is stated for an arbitrary closed subgroup `K` and is reusable
   wherever a "the non-`x₁` slots span the far half-space" step is needed.
