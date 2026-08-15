# W73: the composition lemma, the collapse, and the class-four relations half

Lane W73-KNOB.  New module `GQ2/Dyadic/SqCore/GradedClassFourCompose.lean`; no edits to existing
files.  Prefix `cfourCmp`.  Base `6a8fbc90`, lane branch `claude/w73-knob`.

## 0.  Headline

**`SqClassClearingSupply h 4` is NOT discharged, and it is NOT refuted.**  Both tickets landed.

1. The composition lemma exists (`cfourCmp_dress_all`), and with it wave 72's tail `⁅y, A⁆`
   becomes an actual correction.  ⭐⭐⭐ `cfourCmp_core_reduce`: **one admissible correction of
   wave 68's frame turns the class-four relator into `cfourDefCore nu' j` on the nose.**  That is
   the collapse wave 72 asked a wave-73 lane to commit.
2. Route (B) of ticket 2 landed.  ⭐⭐⭐ `cfourCmp_zLayer_le_gens` is the relations half of the
   graded decomposition of `Z = γ₃/γ₄` at class four, in the form wave 70 needed and never had:
   **three families indexed by `Q₄` alone**.  Consequently ⭐⭐⭐ `cfourCmp_residual_of_span`
   replaces "is `cfourDefCore` a knob" by three uniform questions that do not mention
   `cfourDefCore`, and ⭐⭐⭐ `cfourCmp_zLayer_le_triple` reduces those three to **one**: the
   triple brackets.

**Neither route (A) nor route (B) produced a negative.**  Nothing in this wave says that
`cfourDefCore` is not a knob, and nothing says it is.  What the wave produces is a replacement of
the question by a sharper one and one further named condition (§5).

> **[W75-HOUSE, wave-74 refutation: the sharper question was answered, and the answer is NO.**
> `gDelta_cfourCmp_span_hyp_false` (`GQ2/Dyadic/SqCore/GradedDeltaFunctionals.lean:1575`) proves
> the hypothesis of `cfourCmp_residual_of_span` **unsatisfiable at every `h ≥ 1`**.  So §4's
> payoff and §5's named condition are dead as a *route*, and this note's own honesty markers (§0
> "Scope, in the required words", §7 bullet 2) are exactly what came true: the failure is a
> statement about the knob subgroup of one inventory, and `SqClassClearingSupply h 4` is still
> neither discharged nor refuted.
>
> **The failing family is family 1, the fourth powers -- not family 3, the triple brackets this
> note expects to be the whole remaining obligation** (§4, §5).  Any subgroup satisfying the
> hypothesis must contain the sigma tower `(levelMk σ)⁴`; every correction of wave 70's
> `CfourIdReachable` route has `mod 8` chi-trivial slots and is therefore invisible at the layer
> bit to the twisted functionals `gDelta`, while the tower reads `4 · unit` there.  Moves do not
> span the layer; they span at most its functional-invisible part, which is Labute's Lemma 3, and
> the defect's tower components die by the functionals (his Theorem 5), not by being reached.
> Read `docs/dyadic/w74-func-note.md` §4.1 and §4.3 before using anything below as a target.]**

**Scope, in the required words.**  Everything below concerns ONE sufficient route, wave 70's
`CfourIdReachable`: `γ₂`-valued corrections of wave 68's frame.  Any negative reachable from this
material would be a negative about that route.  It would be a statement about the knob subgroup of
one inventory, it would NOT be "no dressing works", and it would NOT refute
`SqClassClearingSupply h 4`, which is what wave 67's `limFinal_markTransitivity_iff` is stated
against.

## 1.  Ticket 1: the composition lemma (§1 of the file)

⭐⭐⭐ `cfourCmp_dress_all`.  For `γ₂`-elements `c₀, c₁, c₂, c_U, c_V`,

```text
  m' = m dressed on slots 0, 1, 2 by c₀, c₁, c₂ and on the j'-th handle by c_U, c_V
    ⟹ sqRelWord m' = sqRelWord m ·
         (⁅c₀, m 1⁆ · ⁅m 0, c₁⁆ · (c₂² · ⁅c₂, m 2⁆) · (⁅c_U, m(v_{j'})⁆ · ⁅m(u_{j'}), c_V⁆))
```

with every knob read at the **undressed** frame.  Exactly the shape wave 72's note §4.1 specified.
The proof is three stages (`cfourId_dress_core`, then `cfourId_dress_handleU`, then
`cfourId_dress_handleV`) with two knob-transport steps; the only cross term is `⁅c_U, c_V⁆`, and
it dies by `cfour_commP_lambdaTwo`.  `cfourCmp_dress_handles` is the instance with the core slots
left alone, and `cfourCmp_handle_knob` packages it against an explicit correction tuple
`cfourCmpHandleCorr`.

## 2.  The tail, and a correction to wave 72's route (§3 of the file)

⭐⭐⭐ `cfourCmp_dress_reach`.  For **every** admissible `γ₂`-correction `c`,

```text
  ⁅c, A⁆ = ⁅a, V_j⁆ · ⁅U_j, b⁆ ,     a, b admissible ,
```

an exact identity, not a subgroup membership.  The mechanism is a two-way parity count.  Modulo
`γ₂` and modulo squares, which is all `⁅c, ·⁆` sees,

```text
  ν'(v_j)·U_j + ν'(u_j)·V_j = ν'(v_j)·u_j + ν'(u_j)·v_j - 2·ν'(u_j)·ν'(v_j)·w = A ,
```

the two pivot contributions cancelling because their total exponent is even.  `a` is `c` exactly
when `ν'(u_j)` is odd and `b` is `c` exactly when `ν'(v_j)` is odd; the four parity cases are the
four branches of the proof.

**[W75-HOUSE, round 11 §4.2(g) and §4.2(e).**  Two corrections to the display above.  `a, b ∈
{1, c}` was written as a side condition of the identity; the theorem concludes only that `a` and
`b` are **admissible**, and the `{1, c}` reading is a fact about the four parity branches that a
consumer cannot use.  Strengthening the conclusion would be a statement change, so the display is
what moved.  And the pivot coefficient is `- 2·ν'(u_j)·ν'(v_j)·w`, not `+`: `bridgeDress` is
`u_j^{ν'(v_j)}·v_j^{ν'(u_j)}·w^{-2·ν'(u_j)·ν'(v_j)}` (`GradedBridge.lean:337`) and the cleared
letters are `U_j = w^{-ν'(u_j)}·u_j`, `V_j = v_j·w^{-ν'(v_j)}` (`sqEichU`/`sqEichV`,
`LamFrames.lean:303`/`:295`).
The sign is invisible under this paragraph's own "modulo squares" hedge, which is why it survived;
it is **not** invisible in the module, where the same display carries only a "(mod γ₂)" tag.]**

**[W77-HOUSE, ticket 2(b): the citation in the paragraph above is repaired, and the wave-75
correction that produced it was wrong.**  Round 11 shipped `LamFrames.lean:301` and then amended
it to `:300`.  Both are wrong, and in opposite ways.  At `1d3d5a84`, `LamFrames.lean:300` is a
bare `variable (h) in` line, and `:301` is the **first** line of the cleared-`u` docstring, not
the second.  The consistent pairs are `:293`/`:301` if one wants the two docstrings and
`:295`/`:303` if one wants the two definitions, and note that `:293` is the cleared-**`v`**
docstring, so the original `:293`, `:300` was also mis-ordered against this sentence's own
`U_j`, `V_j` order.  Repaired above to the definitions, named, in the sentence's order:
`sqEichU` at `:303`, `sqEichV` at `:295`.  Same repair at the second shipped site,
`GradedClassFourCompose.lean:420`.  `w74-func-note.md:139` already had `295,303` right.]**

**Correction to wave 72 §3, and it is an improvement rather than a retraction.**  Wave 72 routed
`⁅y, A⁆` through the pivot (`cfourDef_comm_dress_frame_mem` needs `⁅y, w⁆`, and
`cfourDef_core_knob_pair` pays for it with the `σ`- and `x₀`-slot knobs at a common correction).
**The pivot is not needed.**  The two pivot brackets that the cleared letters `U_j` and `V_j`
carry cancel against each other in the combination that reconstructs `A`, so only the two handle
slots are spent and **the three core slots stay free**.  Wave 72's statements are correct as
stated; what is corrected is the reading that the core slots had to be spent on the tail.

## 3.  The collapse (§4 and §5 of the file)

⭐⭐⭐ `cfourCmp_core_reduce`: at every selected marking and every handle there is an admissible
correction `c` of wave 68's frame with

```text
  sqRelWord (fun i => levelMk 4 (sqArbFrame h nu' j (bridgeTuple nu' j) i * c i))
    = cfourDefCore nu' j .
```

The correction is wave 72's `cfourDefCorr` followed by the handle-pair correction of §2; the tail
`⁅y, A⁆` cancels itself, `Z` having exponent two.

`CfourCmpResidual h` names what is left of `CfourIdReachable h`: from *any* admissible correction
whose class-four relator is the core defect, a further admissible correction kills it.  Then

* ⭐⭐ `cfourCmp_reachable_of_residual : CfourCmpResidual h → CfourIdReachable h`,
* ⭐⭐ `cfourCmp_supply_of_residual : CfourCmpResidual h → SqClassClearingSupply h 4`,
* `cfourCmp_residual_of_core_vanish`, `cfourCmp_supply_of_core_vanish`: the class-four supply
  follows from `cfourDefCore nu' j = 1` alone.  Nothing here says it vanishes.

## 4.  Ticket 2, route (B): the relations half at class four (§6 of the file)

⭐⭐⭐ `cfourCmp_zLayer_le_gens`.  A subgroup of `Q₄` containing

| family | element | graded summand |
|---|---|---|
| 1 | `p⁴` | `V^{[4]}` |
| 2 | `⁅p, q⁆²` | `(Λ²V)^{[2]}` |
| 3 | `⁅⁅p, q⁆, r⁆` | `L₃(V)` |

contains the whole of `Z = γ₃/γ₄`.  Three families indexed by `Q₄` alone.

**The class-four analogue does follow from the class-five shape, and it is sharper.**  Wave 72's
`cfiveSpan_zLayer_le_gens` needs six families over `Q₅`, because at class five `Y` is not abelian
and the reduction has to be run twice, once from `T` to `Y` and once from `Y` to `Q₅`.  At class
four `Y` **is** abelian, so both maps of `cfourId_zLayer_le` are homomorphisms on `Y` outright
(`cfour_sq_mul_lambdaTwo`, `cfourId_comm_dress_left`), the test set `cfourCmpTest` is a subgroup
with no work, and one reduction reaches `Q₄`.  The `p²`-generator check is
`gThreeFour_commP_sq_left`, which turns `⁅p², q⁆` into a family-2 element times a family-3
element, so no fourth family is needed.

⭐⭐ `cfourCmp_zLayer_le_bundle` and ⭐⭐⭐ `cfourCmp_zLayer_le_triple` sharpen this against the
shape the inventory actually delivers.  The `x₁`-slot knob is `c² · ⁅c, x₁⁆` and never yields a
square on its own.  Modulo the triple brackets the bundle is as good as the square, so **families
1 and 2 cost nothing once family 3 is paid for**: `Z` is generated by the triple brackets together
with the two `x₁`-slot bundles (the bracket correction, and `cfourKnob_sq_knob_pair`'s paired
knob).

⭐⭐⭐ `cfourCmp_residual_of_span` / `cfourCmp_supply_of_span` are the payoff: the residual holds
as soon as there is a subgroup, all of whose elements are knobs, containing the three families.
**The statement no longer mentions `cfourDefCore`.**

> **[W75-HOUSE: both theorems stand and are unedited; their hypothesis is now known false at
> `h ≥ 1`** (`gDelta_cfourCmp_span_hyp_false`), **so neither is instantiable.**  Note which half
> of this paragraph did the damage: not "containing the three families" as a generation statement
> -- `cfourCmp_zLayer_le_gens` is untouched -- but "all of whose elements are knobs", which the
> fourth-power family cannot meet.]**

## 5.  What is left, exactly, and one named condition

The remaining obligation is family 3, the triple brackets `⁅⁅p, q⁆, r⁆`, as moves of the collapsed
frame.  Here is what is proved and what is analysis.

**Proved.**  Everything in §1 to §4 above.  A commutator `⁅p, q⁆` is an admissible correction on
the nose (`cfourKnob_comm_admissible`), so the near slot of a triple bracket is never the problem.

**Analysis, not proved anywhere in the tree.**  Read the far slots of the five knobs at the
collapsed frame: slot `σ` sees `x₀·A`, slot `x₀` sees `σ·A`, slot `x₁` sees `x₁` **bundled with a
square**, slot `u_j` sees `V_j`, slot `v_j` sees `U_j`.  Since `⁅c, ·⁆` kills `γ₂` and kills
squares, only the classes mod `γ₂` matter, and over `𝔽₂`

```text
  (x₀ + A) + (σ + A) = σ + x₀ = w ,   U_j = u_j + ν'(u_j)·w ,   V_j = v_j + ν'(v_j)·w ,
```

so `w`, then `u_j`, `v_j`, then `A`, then `x₀` and `σ` are all in the span.  **The far slots of
the four square-free knobs span every direction of `V` except `x₁`.**  The `x₁` direction is
available only through the bundle, and the bundle's square part is family 2, which by
`cfourCmp_zLayer_le_triple` is itself only available once the triple brackets are.  That is a
genuine circle, and it is the same `x₁`-slot bundle phenomenon wave 69 identified and wave 71
re-diagnosed.

**The named condition for wave 74.**

> For every admissible `γ₂`-element `y`, is `⁅y, x₁⁆` a move of the collapsed frame?
> Equivalently (given the four square-free slots) is `y²` a move?

Given that one condition, families 1, 2 and 3 all follow for `h = 1`, and
`cfourCmp_residual_of_span` closes the route.  This is one `𝔽₂`-linear condition on one layer, and
it is the whole of what is left along this route.

> **[W75-HOUSE, wave-74: this condition is dead, and the inference chain matters.**  What is
> *proved* is `¬ H` for `cfourCmp_residual_of_span`'s hypothesis at `h ≥ 1`
> (`gDelta_cfourCmp_span_hyp_false`).  The step from there to "the named condition is false" runs
> **backwards through the very implication displayed above** -- "given that one condition,
> families 1, 2 and 3 all follow for `h = 1`, and `cfourCmp_residual_of_span` closes the route" --
> which is this section's own analysis and is **not in the tree** (the paragraph above says so:
> "Analysis, not proved anywhere in the tree").  So: the condition is false at `h = 1` *granted
> this note's span argument*, and unconditionally the route it was meant to close is shut.  A lane
> wanting the condition refuted as a Lean statement in its own right does not have it yet.
>
> The owner memo (`owner-items-2026-08-05.md`, wave-74 status) states the short form, "wave 73's
> 'one condition' (the x1-bracket as a move) is unsatisfiable at the committed knob subgroup";
> that is the composite, not the committed theorem.  The committed theorem is about the span
> hypothesis.]**

**Two caveats on that reduction, both honest.**

* The span argument above uses the far slots of **one** handle.  For `h ≥ 2` the directions
  `u_{j'}, v_{j'}` with `j' ≠ j` are not reached by `cfourCmp_dress_all`, which composes the three
  core slots with a single handle pair.  A multi-handle version (the same argument with an
  induction over the handle index inside `cfour_handleWord_update`) would supply them, and it is
  the obvious next piece of tooling.  Nothing in this wave states it.
* The span argument is analysis.  Turning it into a theorem needs the knob subgroup itself as a
  `Subgroup`, which needs the observation that a `γ₂`-valued correction does not change any knob
  (all five knob entries are blind to a `γ₂`-factor of the frame, by `cfour_commP_lambdaTwo`).
  That observation is available from `cfourCmp_dress_all` but is not committed here.

## 6.  Route (A), and why it was not pursued to a verdict

Route (A) asks for an explicit presentation of `cfourDefCore = ⁅σ, A⁆ · ⁅A, x₀⁆ · cfourEichDefect`
as a `⁅y, g⁆` with `g` off the `x₁`-direction.  The obstruction to a *search* is structural rather
than computational: `cfourDefCore` is a product of three `Y`-elements whose `L₂`-images cancel, so
its value in `Z` is a secondary invariant, not readable off the degree-two data, and no expansion
of the three factors exhibits it as a single bracket.  Route (B) subsumes the question: if the
three families are moves then `cfourDefCore` is a move whatever its presentation, because it lies
in `Z` (`cfourDef_core_mem_zLayer`).  **No claim is made here that no presentation exists.**

## 7.  Honesty markers

* Nothing in this wave is evidence that **no** dressing works, and nothing in it bears on
  `SqClassClearingSupply h 4` except through wave 70's `CfourIdReachable`.  The only unconditional
  statements about the supply produced here are the sufficient conditions
  `cfourCmp_supply_of_residual`, `cfourCmp_supply_of_core_vanish` and `cfourCmp_supply_of_span`.
* `cfourCmp_residual_of_span`'s hypothesis is **not** claimed to hold, and §5 records precisely
  where it is delicate.  If it fails, that is a statement about the knob subgroup of one
  inventory, not a refutation of the residual.
  **[W75-HOUSE: it fails (wave 74), and this marker is why the failure cost nothing.  The one
  thing the marker got wrong is *where* it is delicate: §5 puts the delicacy at the `x₁`-slot
  triple brackets, and the refutation runs through the fourth powers.]**
* `cfourCmp_dress_all`, `cfourCmp_dress_handles` and `cfourCmp_z_pair` are stated over
  `levelQuot G 4` for an arbitrary topological group.  They are **class-four, not
  layer-agnostic**, and the hypotheses were checked for satisfiability rather than for general
  binders: `cfourCmp_dress_all` rests on `Y` being abelian, which is exactly what kills the
  `c_U`-`c_V` cross term, and one layer up that term survives, so the lemma would have six factors
  and not five.  The wave-70 §5 warning applies unchanged.
* The §6 results are stated at `D_sq h` only.  They consume discreteness of `Q₄` through
  `cfourId_isClosed`, which is what pays for the topological closure inside `twoCentralSucc`, and
  `cfourCmpTest` is a subgroup for the class-four reason above.  Their hypotheses are satisfiable
  and not merely generally bound: `cfourCmp_zLayer_le_gens` fires at `S = ⊤`, and it is consumed
  non-vacuously inside `cfourCmp_residual_of_span`.
* `cfourCmp_dress_reach` is an **identity**, not a membership.  Wave 72's
  `cfourDef_comm_dress_frame_mem` and `cfourDef_core_knob_pair` are about knob expressions and
  remain true; §2 does not retract them, it shows their pivot detour is avoidable.

## 8.  Verification record

* Base `6a8fbc90`, lane branch `claude/w73-knob`.  Four code commits plus this note, all
  path-limited.  Not pushed.  `GQ2.lean` not edited; no existing file edited; no docstring of any
  existing module touched.
* `scripts/mirror.sh sweep` at lane start (5833 artifacts), `scripts/mirror.sh check
  GQ2/Dyadic/SqCore/GradedClassFourCompose.lean` after every increment, and
  `scripts/mirror.sh gen GQ2.Dyadic.SqCore.GradedClassFourCompose` at the end.  Clean.  No name
  collisions: `grep -rl cfourCmp GQ2/ docs/` returns this module and this note only.
* One import, `GQ2.Dyadic.SqCore.GradedClassFourDefect`.  No `SqCore → Count` import.
* **35 declarations, 35 axiom pins, every one `[propext, Classical.choice, Quot.sound]`.**  No
  `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.

  `cfourCmp_dress_all`, `cfourCmp_dress_handles`, `cfourCmp_z_pair`, `cfourCmpHandleCorr`,
  `cfourCmpHandleCorr_handleU`, `cfourCmpHandleCorr_handleV`, `cfourCmpHandleCorr_handleU_ne`,
  `cfourCmpHandleCorr_handleV_ne`, `cfourCmpHandleCorr_zero`, `cfourCmpHandleCorr_one`,
  `cfourCmpHandleCorr_two`, `cfourCmpHandleCorr_admissible`, `cfourCmp_handle_knob`,
  `cfourCmp_comm_zpow_even`, `cfourCmp_comm_zpow_odd`, `cfourCmp_comm_dress_split`,
  `cfourCmp_comm_eichU`, `cfourCmp_comm_eichV`, `cfourCmp_dress_reach`, `cfourCmpTail`,
  `cfourCmpTail_admissible`, `cfourCmpTail_levelMk`, `cfourCmp_core_reduce`, `CfourCmpResidual`,
  `cfourCmp_reachable_of_residual`, `cfourCmp_supply_of_residual`,
  `cfourCmp_residual_of_core_vanish`, `cfourCmp_supply_of_core_vanish`, `cfourCmpTest`,
  `cfourCmp_mem_test`, `cfourCmp_zLayer_le_gens`, `cfourCmp_zLayer_le_bundle`,
  `cfourCmp_zLayer_le_triple`, `cfourCmp_residual_of_span`, `cfourCmp_supply_of_span`.
* `commP` is used throughout; the element bracket `⁅ , ⁆` appears nowhere in the code, only in
  prose.

## 9.  Wave-74 queue

1. ~~**The named condition of §5**: is `⁅y, x₁⁆` (equivalently `y²`) a move?  One `𝔽₂`-linear
   condition, and the whole of what is left along this route.~~  **[W75-HOUSE: OVERTAKEN at wave
   74.  The route this condition was to close is refuted at `h ≥ 1`
   (`gDelta_cfourCmp_span_hyp_false`), so the item is withdrawn as a target.  Its replacement is
   the Lemma 3 analogue of `w74-func-note.md` §4.3(2): the functional-invisible part of the layer
   is spanned by knobs.  See §5's annotation for what is and is not committed.]**
2. **The multi-handle composition lemma**: `cfourCmp_dress_all` with the handle pair replaced by a
   set of handles, so that the far-slot span argument of §5 covers `h ≥ 2`.  Same argument, one
   induction inside `cfour_handleWord_update`.
   **[W75-HOUSE: the *motive* is gone (the §5 span argument no longer leads anywhere), but the
   lemma is tooling and would still be needed by the Lemma 3 analogue, which also has to see every
   handle.  Re-scope rather than withdraw.]**
3. **The knob subgroup as a `Subgroup`**, so that §5's span argument becomes a theorem.  The
   ingredient is that a `γ₂`-valued correction is invisible to every knob entry, which follows
   from `cfour_commP_lambdaTwo` and `cfourCmp_dress_all`.
   **[W75-HOUSE: still wanted, and now for the opposite purpose.  Wave 74 refuted the span
   hypothesis without ever building the knob subgroup as an object -- it refuted the *existence*
   of any subgroup meeting the clauses.  A named knob `Subgroup` is what the Lemma 3 analogue
   (`w74-func-note.md` §4.3(2)) needs on its right-hand side, so the item survives its original
   motive.]**
4. ~~**Register the module.**  `GQ2/Dyadic/SqCore/GradedClassFourCompose.lean` is not wired into
   `GQ2.lean`; the orchestrator owns that file.  (Wave 72's `NuSeeds` finding is the standing
   reminder that an unregistered module has never been in a green build.)~~  **DISCHARGED at
   `5d7ce5c9`, 73 seconds after this note landed** (`0063dc8c` 19:01:12, `5d7ce5c9` 19:02:25).
   [W74-HOUSE, watch round 11: all three wave-73 lane notes carried this item and all three were
   discharged within about a minute, so the wave-72 `NuSeeds` lesson took at the lane level and
   at the orchestrator level; what is missing is only the annotation afterwards.  The tree has
   exactly one unreachable module today, `GQ2.AxiomLedger`, which is deliberately excluded.]
