# W77-DECIDE: the depth-two base is FALSE, at every `h`, by a group of order sixteen

**Lane W77-DECIDE, branch `claude/w77-decide`, base `1d3d5a84`.**  One new module,
`GQ2/Dyadic/SqCore/GradedBaseDecide.lean` (prefix `gDecide`), 62 declarations, all pinned on
`[propext, Classical.choice, Quot.sound]` or a subset.  No edits to existing files, no `sorry`,
no new axiom, no `native_decide`, no heartbeat or recursion-depth options.

Commits: `9fa93556` (module opened), `e79cdce4` (the witness group), `e9521128` (the marking,
the hom, `λ₄ = 1`), `3dea56c2` (the decision at `h = 0`), `3c453a7b` (the decision at every
`h`, plus the depth-`3` restart).

Verification of record: `scripts/mirror.sh sweep` at lane start, `scripts/mirror.sh gen
GQ2.Dyadic.SqCore.GradedBaseDecide` green after every commit, zero warnings, zero sorries.  New
leaf module, no dependents, `GQ2.lean` untouched per protocol.

## Headline

**Wave 76's §4 argument is now a theorem, at every `h`, and it needed no structure theorem.**

```
gDecide_not_baseResidual : ¬ GBaseResidual h
gDecide_not_layerReach   : ¬ GTowerLayerReach h (gDecideNu h) 2
gDecide_not_joinBase     : ¬ GJoinBase h
```

`GJoinBase h` is wave 75's first named input to `SqLamMarkTransitivity h`
(`gJoin_markTransitivity_of_base`).  It is false.  The odd route's depth-`2` base is dead as
stated, at every `h`, not conditionally and not only at `h = 0`.

Both residual classes fail, not one: `gDecide_x0_not_mem` and `gDecide_sigma_not_mem` are the
two classes `⁅⁅x₁, x₀⁆, x₁⁆` and `⁅⁅x₁, σ⁆, x₁⁆` that wave 76 singled out, and each is proved
outside `gTowerReach h ν' 2`.

## The witness

`Q₁₆ = ⟨X, Y | X⁸ = 1, Y² = X⁴, Y⁻¹XY = X⁻¹⟩`, the generalized quaternion group of order
sixteen, carried on `Bool × ZMod 8`.  (`Mathlib.GroupTheory.SpecificGroups.Quaternion` is not
in this project's import closure, so it is built in the file; every group law is a `decide`
over at most `16³` tuples.)  Two markings, both through the committed standard shape `sqMark`
so that `sqRelWord_sqMark` drops the handles:

| marking | `σ` | `x₀` | `x₁` | handles | relator | sees |
|---|---|---|---|---|---|---|
| `gDecideMarkX` | `1` | `X` | `Y` | `1` | `sqWord 1 X Y = X⁻⁴Y² = 1` | `⁅x₁, x₀⁆` |
| `gDecideMarkS` | `X` | `1` | `Y` | `1` | `sqWord X 1 Y = Y²·X⁴ = 1` | `⁅x₁, σ⁆` |

Why `Q₁₆` and not something smaller: at `σ ↦ 1` the relator collapses to `x₀⁻⁴·x₁²`, so any
receiving group needs `Y² = X⁴`; among the two-generator groups of order sixteen exactly the
generalized quaternion one has that, and it is the smallest group in which `⁅Y, X⁆² = X⁴ ≠ 1`.

The three collapses (§5 of the module), each a `decide` after one structural step:

* **knobs** `⁅t, q⁆`.  `gDecideHom` maps `γ₂(D_sq h)` into `λ₂(Q₁₆) = ⟨X²⟩`
  (`map_twoCentralSeries_le` plus `gDecide_lambdaTwo`) and maps the far span `gTowerFar h` into
  `⟨X⟩` (topological-closure minimality against the preimage of `⟨X⟩`, which is closed because
  `Q₁₆` is discrete).  `⟨X⟩` is abelian, so every knob is `1`.
* **bundles** `t²·⁅t, x₁⁆`.  For `t ↦ X^{2k}` this is `X^{4k}·X^{-4k} = 1`.  That is exactly
  the cancellation wave 76 calls the vacuous bundle, here as a finite check rather than a
  graded assertion.
* **towers** `x̃₁^{4a}` and the Eichler-cleared handle towers.  `x̃₁ = x₁x₀⁻² ↦ Y·(m x₀)⁻²`,
  which has order four for every `m x₀ ∈ ⟨X⟩`; and at the selected marking `gDecideNu h`, whose
  handle rows are zero, `sqEichU h ν' j` and `sqEichV h ν' j` are the plain handle letters,
  which go to `1`.

The target reads `commP (commP Y X) Y = X⁴ = Z ≠ 1`.  `λ₄(Q₁₆) = 1`
(`gDecide_lambdaFour`, via the explicit chain `λ₂ ≤ ⟨X²⟩`, `λ₃ ≤ ⟨X⁴⟩`, `λ₄ = 1`) is what lets
the hom descend to `Q₄ = levelQuot (D_sq h) 4`, where the reach lives.

## Scope, stated exactly

* This is a statement about **one inventory at one depth**: wave 74's `gTowerKnobSet` and
  `gTowerTowSet` at `k = 2`.  `SqClassClearingSupply h k` is untouched, and so is
  `limFinal_markTransitivity_iff`.  The same shape of finding as wave 74's
  `gDelta_cfourCmp_span_hyp_false`: a route's sufficient condition fails; the residual stands.
* The failing element really is inside what `GTowerLayerReach h ν' 2` quantifies over:
  `gDecide_triple_mem_three` puts it in `γ₃`, and `gBase_adm_commP` gives both rows exactly
  trivial.  Not a quantifier artefact.
* The refutation of `GTowerLayerReach` is at the specific marking `gDecideNu h` for `h ≥ 1`
  (the Eichler tower letters depend on `ν'`); at `h = 0` there are no handle letters and the
  two hypotheses on `ν'` are vacuous, so `gDecide_not_layerReach_zero` gives it at **every**
  marking.  Either way `GBaseResidual h` and `GJoinBase h`, which quantify over markings, are
  refuted at every `h`.
* Nothing here says the depth-`3` layer statement fails.  See §T2 below for why that is
  nevertheless not a free repair.

## The refutation is stronger than wave 76's argument

**`GTowerAdm`'s row conditions are never used.**  `gDecide_reach_le_ker` quantifies over every
`t ∈ γ₂(D_sq h)`, not only the exactly row-trivial ones; only `ht.1` is consumed.  So the
enlarged inventory, with admissibility dropped entirely, still misses both classes.

This corrects wave 76's §4 in one place.  The note writes the depth-`2` inventory as including
"towers `ξ²(v)`, **all** of `V^{[4]}`", and concludes that if the admissible corrections were
widened so that `W` grew to all of `V`, the gap would close.  The committed `gTowerTowSet h ν'
2` is not all of `V^{[4]}`: it is the `4`-divisible `ℤ₂`-powers of the **cleared** letters
only, which at `h = 0` is the single class `ξ²(x₁)`.  Redoing the wave-76 count with the
committed inventory and `W = V`:

```
reach  =  span{A1, A2, B1, B2, C2, P1, T1 + B3, T2 + C3}      (dimension 8 of 10)
```

in the basis `A1 = ⁅⁅x₀,σ⁆,σ⁆`, `A2 = ⁅⁅x₀,σ⁆,x₀⁆`, `B1 = ⁅⁅x₁,σ⁆,σ⁆`, `B2 = ⁅⁅x₁,σ⁆,x₀⁆`,
`B3 = ⁅⁅x₁,σ⁆,x₁⁆`, `C2 = ⁅⁅x₁,x₀⁆,x₀⁆`, `C3 = ⁅⁅x₁,x₀⁆,x₁⁆`, `P1 = ξ⁅x₀,σ⁆`, `T1 = ξ²σ`,
`T2 = ξ²x₀` of `gr₃(D_sq 0)`.  Modulo that span the two residual classes are `ξ⁅x₁,σ⁆ ≡ T1` and
`ξ⁅x₁,x₀⁆ ≡ T2`, i.e. `σ⁴` and `x₀⁴`.  That is precisely what the two markings of `Q₁₆` read:
in each of them the surviving central involution `Z = X⁴` is the image of a fourth power of a
far letter.  So the gap is two-dimensional even at the widest admissibility, and it is the
**tower** side of the inventory, not the row conditions, that is short.

## T2 second branch: the depth-three re-cut, assessed

Two findings, one positive and one negative.

**Positive.**  The engine really does restart from any base depth.
`gTower_layerReach_step` carries `hk : 2 ≤ k`, not `k = 2`, so the induction runs from any
`k₀ ≥ 2`.  The packaged `gTower_layerReach_of_base` is stated only at `k₀ = 2`, so a re-cut
needs a restatement; the module supplies it:

```
gDecide_layerReach_of_baseAt : 2 ≤ k₀ → GTowerLayerReach h ν' k₀ → ∀ k, k₀ ≤ k → GTowerLayerReach h ν' k
GDecideBaseThree h           : ∀ ν' selected, GTowerLayerReach h ν' 3
gDecide_tower_of_baseThree   : GDecideBaseThree h → ∀ k, 3 ≤ k → GTowerLayerReach h ν' k
```

**Negative, and this is the load-bearing half.**  A depth-`3` base is **not** enough for the
committed downstream chain.  `gJoin_supply_of_vanishing` proves `∀ K, GJoinChiSupply h (K + 3)`
by induction seeded at `K = 0` with the committed class-three witness `gJoin_chiSupply_three`,
and its successor step calls `gJoin_clear_step` at `k = K + 2`.  At `K = 0` that is `k = 2`.
So the very first step, class `3 → 4`, consumes `GJoinDefectVanishing h` at `k = 2`, which by
`gTower_defect_reach_of_base` needs the layer statement at `k = 2` - the statement this lane
has just refuted.  A depth-`3` base delivers the layer statement only for `k ≥ 3`, hence the
vanishing only for `k ≥ 3`, hence nothing that seeds the recursion.

**So the depth-`3` re-cut needs, in addition, a class-four supply witness**
(`GJoinChiSupply h 4`, or `SqClassClearingSupply h 4` with the `χ`-clause restored) to restart
the induction one class up.  That is exactly the class-four question waves 69 to 73 have been
chasing and left open.  Wave 76's item 2 is therefore not a free repair: it converts the
depth-`2` base into "depth-`3` base **and** class four".

Inventory of what a depth-`3` discharge would need, if that seed were available.  The four
ingredients of `GradedJoinBase` all reappear one level up, with `Q₅ = levelQuot (D_sq h) 5` in
place of `Q₄`: letter generation (`gBase_letters_mem` is a `gTower_discrete`/`dsq_topGen`
argument, level-agnostic), the triple brackets, the bracket squares, the fourth powers.  What
changes is the row-trivial set: at depth `3` the admissible corrections' square parts range
over the row-trivial part of `γ₂`, which is far larger than `W ⊆ V`.  What the tree does **not**
have one level up is `cfourCmp_zLayer_le_gens` at level `5`; the `GradedClassFour*` files are
written against `Q₄` throughout, and that is the bulk of the porting work.

## T3: widening admissibility to row-trivial mod `2` (report only)

**Answer: it cannot close the depth-`2` gap, and it is a statement change to the committed
supply.**

* *It does not help on its own.*  Any widened correction is still a `γ₂`-element, and
  `gDecide_reach_le_ker` kills `gTowerReach` for **all** `γ₂`-corrections.  So no widening of
  `GTowerAdm`'s row clauses reaches the two classes.  The linear-algebra reason is in the
  display above: with `W = V` the residual is still two-dimensional, spanned by `ξ²σ` and
  `ξ²x₀`, and the shortfall is on the tower side.  Only widening **and** enlarging the tower set
  to the uncleared letters would close it, which is two statement changes rather than one.
* *Which clauses change, and is it a statement change.*  Yes, and to the committed supply
  itself.  `SqClassClearingSupply h k` (`GradedLimit.lean:236`) carries `∀ i, nuLam h (a i) = 1`
  and `∀ i, nu' (a i) = 1` **exactly**; `GJoinChiSupply h k` adds `∀ i, chiSq h (a i) = 1`.
  Relaxing to a mod-`2` condition rewrites the `Prop` that `limFinal_markTransitivity_iff` is
  stated against, so it is not a refinement of the route but a different endgame statement.
* *Would the vanishing side survive.*  Probably not, and for a concrete reason.  The brief
  names `gDelta_chiSq_of_gammaTwo`; the actual committed lemma is
  **`gDelta_chiSq_of_nuLam`** (`GradedUniformJoin.lean:113`), and it is exact-`nuLam`-triviality
  that forces `χ_sq(a i) = ±1`.  The `-1` branch is then killed by `-1 ≢ 1 (mod 8)` together
  with `gDelta_chi_gammaTwo_dvd` (`GradedUniformJoin.lean:137`).  A mod-`2` row would leave
  `χ_sq(a i)` free in `1 + 2ℤ₂`, and the mod-`8` reading that discharges `GJoinDefectVanishing`
  breaks there.  Since the widening also fails to close the gap, this was not pursued further.

## Corrections to the brief and to the wave-76 note

1. **`gDelta_chiSq_of_gammaTwo` does not exist.**  The lemma is `gDelta_chiSq_of_nuLam`
   (`GradedUniformJoin.lean:113`), with `gDelta_chiSq_sq_of_nuLam` beside it.
2. **`gTowerTowSet` at depth `2` is not all of `V^{[4]}`.**  Wave 76 §4's inventory line
   "towers `ξ²(v)`, all of `V^{[4]}` (this part of the note's §T2 is right)" is wrong for the
   committed set, which is the `2^k`-divisible powers of the **cleared** letters only.  This
   is what makes the gap survive the widening of item 3 of wave 76's "What W77 needs".
3. **The gap is not two-dimensional for the reason wave 76 gives.**  Wave 76 attributes it to
   `W ∩ F` being small (`W = ⟨x₁⟩` at `h = 0`, so `W ∩ F = 0`).  With the committed tower set
   the gap is two-dimensional even when `W = V`; the row conditions are not what makes it work.
4. **`gTower_layerReach_of_base` is stated only at `k₀ = 2`.**  The ENGINE note's "the
   induction restarts from any `k ≥ 2`" is true of `gTower_layerReach_step`, not of the
   packaged corollary.  `gDecide_layerReach_of_baseAt` supplies the general form.
5. **A finite-model refutation did not need the graded structure theorem.**  Wave 76 expected
   "an explicit finite class-`4` quotient of `D_sq 0`" of order `2^18`.  What is actually
   needed is far smaller: any finite `2`-group of class `3` receiving `D_sq h` in which the
   reach collapses.  `Q₁₆` is the answer, and the reason the collapse is so cheap is that both
   the correction slot and the far slot land in one cyclic subgroup.
6. **`Mathlib.GroupTheory.SpecificGroups.Quaternion` is not in the import closure.**  Anyone
   reaching for a named finite group in this tree must build it; the `Bool × ZMod n` carrier
   with `decide`d group axioms is cheap and worked first time.

## What is open

1. **The residual itself.**  `SqClassClearingSupply h k` is exactly where wave 67 left it.
   This lane removed a route to it, not the target.
2. **The re-cut, now costed.**  Depth `3` alone does not restart the chain (§T2).  Either a
   class-four supply witness must be produced, or `gJoin_supply_of_vanishing` must be reseeded
   at a class where a depth-`3` base does reach.
3. **The other two named inputs.**  `GJoinSeparationAll h` (T3 of wave 75) and
   `GTowerKnobRealizable h` (T4) are untouched here, and are now moot for this route unless the
   base is repaired.
4. **A different inventory.**  The lever this lane did not test is enlarging `gTowerTowSet`.
   Two separate remarks, and they must not be conflated.

   *Not the full reach.*  Adding the non-admissible towers is not a repair.  In the graded
   model, `gTowerFullReach 0 ν' 2` is `span{A1, A2, B1, B2, C2, P1, T1, T2}`, and `B3`, `C3`
   are outside it too; consistently, `gTower_cut` cannot manufacture the classes from
   `gTowerFullReach` even though they are exactly row-trivial.  (That count is a graded-model
   remark, **not** formalized here: the `Q₁₆` witness sees `gTowerTowXW` as nontrivial, so it
   proves nothing about the full reach.)

   *The real lever.*  With admissibility widened to all of `γ₂` the residual becomes
   `span{T1, T2} = span{σ⁴, x₀⁴}` exactly, so a tower set containing the `4`-divisible powers
   of the **uncleared** letters would close the depth-`2` gap - but only in combination with
   the widening, and both changes rewrite committed statements (§T3).  Whether the clearing
   recursion genuinely needs the corrections to be admissible, or only their **defect** to be,
   is the sharpest question this lane leaves.
