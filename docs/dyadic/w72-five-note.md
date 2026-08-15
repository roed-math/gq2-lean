# W72: the row repair at `γ₃`, and the relations half of `γ₄/γ₅`

Lane W72-FIVE.  New module `GQ2/Dyadic/SqCore/GradedClassFiveKnob.lean`; no edits to existing
files.  Prefixes `cfiveRow` / `cfiveSpan`.  Base `e2e8917a`, lane branch `claude/w72-five`.

## 0.  Headline

**Both of wave 71's named next steps landed, and neither is a refutation.**  Nothing here
discharges `SqClassClearingSupply h k` at any `k`, and nothing here refutes it.

1. The row repair at `γ₃` exists, and wave 71's framing of the obstacle was slightly off:
   `bridge_row_image` was never restricted to `γ₂`, it is stated at a **free** index.  What
   actually moves one class up is the index, from `m = 2` to `m = 3`, so the repairable rows are
   `8ℤ₂` and not `4ℤ₂`.  The reason is exactly the one thing a repair factor has to be, namely
   invisible, and at `Q₅` only a `γ₄`-element is.
2. The relations half of the graded decomposition of `γ₄/γ₅` is proved, in two forms: three
   families indexed by `Y` with free `Q₅`-slots, and then six families indexed by `Q₅` alone.
3. The pairing that wave 71 used to remove the square from the `x₁`-slot knob transfers, but
   **both of its ingredients change**, and one of them changes the range of applicability: the
   class-five pairing runs only at a near slot in `Y`, where wave 71's ran at an arbitrary group
   element.

## 1.  The row repair (module §§1-4)

> ⭐⭐ `cfiveRow_repair`: at a selected marking, a `γ₃`-element whose two rows lie in `8ℤ₂` may be
> replaced by a `γ₃`-element with **exactly** trivial rows differing from it by a `γ₄`-factor.

`cfiveRow_repair_knob` is wave 70's shape (same bracket against every slot of `Q₅`, same square),
derived from it.  The `γ₄`-form is the primary statement because it is stronger than the knob
form: it also gives blindness of the relator, which the knob form does not.

**Which step fails at `m = 2`, precisely.**  Invisibility, and nothing else.
`cfiveRow_comm_zLayer_dress` is the invisibility of a `Z`-factor, and
`cfiveRow_comm_lambdaThree_dress` is the exact cost of a `T`-factor:

```text
  commP (p · t) q = commP p q · commP t q      for t ∈ T = lambdaImage G 3 5 .
```

The defect `commP t q` is a `Z`-element, and the class-five calculus supplies no reason for it to
vanish.  One class down the same factor was central and the defect was absent, which is why wave
70 could stop at `m = 2`.  This is a statement about the two committed identities, not a claim
that no `4ℤ₂`-repair exists by some other route.

> ⭐⭐ `cfiveRow_relator_blind`: the class-five relator is blind to a `Z`-valued correction of
> **every** slot at once.

Each of the five factors of `gFourFive_sqRelWord` is a bracket, a square, a fourth power or a
conjugation, and a central factor of exponent two survives none of them; the handle word is
handled by the pointwise congruence `cfiveRow_handleWord_congr`, which is an identity in any
group.  So the repair is free at the level of the **relator**, not merely of the knob, and that
is what makes the weakened obligation work.

> ⭐⭐ `cfiveRow_supply_of_reachable`: `CfiveRowReachable h → SqClassClearingSupply h 5`.

`CfiveRowReachable` is `cfiveKnob_supply_of_reach`'s hypothesis with "exactly row-trivial
correction" weakened to "correction whose two rows lie in `8ℤ₂`".  This is the named `Prop` the
ticket asked for, with the implication committed.

**And in the cases that arise, no repair is needed at all** (module §3, following wave 71's
class-four lane).  A square of an exactly row-trivial `γ₂`-element is an exactly row-trivial
`γ₃`-correction (`cfiveRow_sq_admissible`), and so is a bracket with a `γ₂`-slot
(`cfiveRow_comm_admissible`), because the two rows are homomorphisms into an abelian group and
kill every commutator.  `cfiveRow_mul_admissible` closes the family under products.  So
`cfiveKnob_supply_of_reach` is consumable with no row arithmetic whatever; the repair is the
fallback for corrections that arrive with rows.

## 2.  The pairing, with both ingredients re-established (module §5)

Wave 71 recorded that the pairing needs two inputs per class, and that the second must be
re-established rather than transported.  Both turned out to move.

* ⭐ `cfiveSpan_commP_sq_left` carries a hypothesis that `gThreeFour_commP_sq_left` does not.
  The Hall-Petrescu step reorders three factors, and the reordering needs `commP (commP y q) y`
  central.  At `Q₄` a triple bracket is always central; at `Q₅` it is central only when the
  innermost slot is a `Y`-element, since `commP y q` then lies in `T` and a bracket with a
  `T`-slot lands in `Z`.  So the near slot must be in `Y`.
* ⭐ The fourth-power cancellation is carried by `T`, not by `Y`
  (`cfiveSpan_pow_four_lambdaThree`).  Wave 70's §5 warning is exactly what bites: the class-four
  proof puts the square of a `Y`-element in the top layer, and one class up that square only
  reaches `T`.  What a `Y`-element has at class five is a trivial **eighth** power
  (`cfiveSpan_pow_eight_lambdaTwo`), its fourth power lying in `Z`
  (`cfiveSpan_pow_four_lambdaTwo_mem`).  **Nothing here says that fourth power is nontrivial.**

> ⭐⭐ `cfiveSpan_sq_knob_pair`: for `y ∈ Y` and any `q`, the product of the two `x₁`-slot knobs
> at the corrections `y²` and `⁅y, q⁆` is `y⁴ · ⁅⁅y, q⁆, y⁆ · ⁅⁅y, q⁆, q⁆`, a fourth power times
> two **pure** iterated brackets with no square attached.

`cfiveSpan_dress_two_mul` makes it one move: `cfiveSpan_pair_correction` exhibits the single
`T`-correction `c = y² · ⁅y, q⁆` with that knob.

**The narrowing is real and the next lane must know it.**  Wave 71's `cfourKnob_sq_knob_pair` is
stated at arbitrary `p ∈ Q₄`, and both corrections `p²` and `⁅p, q⁆` are legal there because
class-four corrections are `γ₂`-valued and every square and every commutator is a `γ₂`-element.
At class five the corrections must be `γ₃`-valued, so `p²` is legal only when `p` is already a
`γ₂`-element.  The restriction is forced by the depth of the correction layer, not by the proof.

> ANALYSIS, NOT COMMITTED.  Wave 71 instantiated its pairing at `p = A = bridgeDress nu' j` and
> reached the leftover's `A⁴`.  `A` is a product of generator powers and is not committed to lie
> in `γ₂`, so that instantiation has no class-five counterpart at the same element.  The
> available one is `y = A²`, which is a `γ₂`-element by `cfourKnob_sq_mem`, and it would deliver
> `A⁸` rather than `A⁴`.  No class-five leftover is evaluated in this wave, so nothing here says
> `A⁸` is what a class-five leftover carries.

## 3.  The relations half (module §§6-7)

`gFourFive_zLayer_le_gen` gives generation only, and its two families are indexed by `T`, which
is opaque: it is the image of `γ₃`, not a family indexed by `Q₅`.  The relations half replaces it.

> ⭐⭐⭐ `cfiveSpan_zLayer_le_rel`: a closed subgroup of `Q₅` containing `(y²)²`, `⁅y, r⁆²` and
> `⁅⁅y, r⁆, q⁆` for every `y ∈ Y` and all `r, q ∈ Q₅` contains all of `Z = γ₄/γ₅`.

Two relations pay for it.  Both `t ↦ t²` and `t ↦ ⁅t, q⁆` are **homomorphisms** on `T`
(`cfiveSpan_sq_mul_lambdaThree`, `gFourFive_ad_left`), so each `T`-indexed family need only be
checked on generators of `T`; and the generators of `T` are the squares and the brackets of `Y`.
The generation statement is applied at `T` inside `Q₅`, which needs the target level freed from
the class: `cfiveSpan_lambdaImage_le` is `gFourFive_zLayer_le_gen` with `n` in place of `k + 2`,
and nothing in wave 71's proof was about the level.  On a square generator the check is §2's
Hall-Petrescu step, which is the one place the third family is consumed with `q` in its
innermost slot.

The same reduction applies again, from `Y` down to the generators of `Y`.  The three families are
homomorphic in their `Y`-slot; the fourth power only because the outer square kills the
`Z`-defect that the class-four proof killed by abelianness
(`cfiveSpan_pow_four_lambdaTwo_mul`, `cfiveSpan_ad_lambdaTwo_left`, `cfiveSpan_ad_lambdaTwo_inv`).

> ⭐⭐⭐ `cfiveSpan_zLayer_le_gens`: six families indexed by `Q₅` alone, namely `g^8`, `⁅a, b⁆^4`,
> `⁅g², r⁆²`, `⁅⁅a, b⁆, r⁆²`, `⁅⁅g², r⁆, q⁆` and `⁅⁅⁅a, b⁆, r⁆, q⁆`.

The last is the fourfold bracket, and it is exactly the family `gFourFive_jacobi_iter` is a
relation on; `cfiveSpan_jacobi_iter_rewrite` solves that relation for one member, with no
hypothesis, inside the exponent-two abelian `Z`.  `cfiveSpan_zLayer_le_dsq` and
`cfiveSpan_zLayer_le_gens_dsq` are the two forms at `D_sq h`, where `Q₅` is discrete
(`cfiveSpan_discreteTopology`) and the closedness side conditions are free.

**One further bridge.**  The knobs of wave 71's inventory have their far slots fixed to the five
frame letters, while the six families range over all of `Q₅`.

> ⭐ `cfiveSpan_ad_far_of_gens`: for `t ∈ T`, `q ↦ ⁅t, q⁆` is a homomorphism, so a check against
> a set whose closed span is `Q₅` is a check against every `q`.

## 4.  What this is NOT

**`K ⊇ L₄(V)` is not established.**  The relations half says what a subgroup must contain in
order to contain the layer; it says nothing about whether the knob subgroup contains any of the
six families.  Wave 71 proved wave 70's argument for `K ⊇ L₃(V)` unsound, and that argument is
not reused anywhere here.  What §2 supplies towards the class-five analogue is the pairing, which
delivers pure iterated brackets with no square attached; what §3 supplies is the list of families
that would have to be delivered.  Joining them is the next step, not this one.

**No supply instance, and no refutation.**  `SqClassClearingSupply h 4` and
`SqClassClearingSupply h 5` are both untouched.  Nothing in this wave is evidence that no
dressing works: everything above concerns sufficient routes, and a failure of a route would not
touch the supply, which is what wave 67's equivalence is stated against.

## 5.  What a class-five run now has, and what it still lacks

Has: the layer calculus and Jacobi (wave 71), the knob inventory (wave 71), the obligation (wave
71) now consumable with corrections that need no repair and, when they do, a repair at `8ℤ₂`
(§1); the pairing with both ingredients at the right layer (§2); and the graded decomposition in
six explicit families over `Q₅` together with the far-slot bridge (§3).

Lacks, as named next steps:

1. **The knob subgroup against the six families.**  For each of `cfiveSpan_zLayer_le_gens`'s six
   families, is it inside the subgroup generated by the five knobs of wave 71's table at
   `γ₃`-valued corrections?  The pairing settles the shape of the `x₁`-slot contribution; what is
   missing is a term-by-term reading, in the shape of wave 71's `cfourKnob_leftover_eq` but for
   the knob subgroup rather than the leftover.
   **[W75-HOUSE: wave 73 reduced all six families to one (`w73-five-note.md` §2), and wave 74
   answered the class-four analogue of that one **negatively**, as a theorem
   (`gDelta_cfourCmp_span_hyp_false`, `GradedDeltaFunctionals.lean:1575`).  The class-five answer
   is argued but not committed (`w74-func-note.md` §4.2, needing the mod-16 kit).  Expect "no" on
   the square families: the towers they contain are functional-visible and the knobs are not.]**
2. **A class-five leftover in closed form.**  Wave 71's class-four lane evaluated the leftover
   (`cfourKnob_leftover_eq`) and found that its hard terms were not the ones the analysis had
   predicted.  No class-five analogue exists, and `cfiveKnob_supply_of_reach` deliberately
   existentially quantifies its base frame, so there is nothing yet to evaluate against.
3. **Class four itself**, ~~unchanged from wave 71's list~~.  **[W74-HOUSE: "unchanged" was
   falsified the same wave, 8 minutes after this note.]**  The *lack* survives:
   `SqClassClearingSupply h 4` is still neither discharged nor refuted, and no class-four-clearing
   frame is committed, which is what `w71-five-note.md`'s item 3 actually says.  But all three of
   wave 71's class-four leftover sub-items moved in wave 72, per `w72-defects-note.md`'s
   disposition table: item 1 (the two defects) **expanded and split** by `cfourDef_defect_eq`,
   item 2 (`⁅A, x₀⁆²`) **committed** by `cfourDef_commSq_correction`, and item 3 (the pairing
   residue `⁅⁅A, x₁⁆, A⁆`) **committed**, cancelling against the `σ`-slot knob of `⁅x₁, A⁆`.
   Read the two notes together: this one was committed at `74739c37` (16:01:55), the defects note
   at `e6f2f9bf` (16:10:15), parallel lanes.

## 6.  Verification record

* Base `e2e8917a`, lane branch `claude/w72-five`, cache at `6db3ee88`.
* Harness: `scripts/mirror.sh sweep` (5813 artifacts) at lane start, then `scripts/mirror.sh
  check` on the source file after every increment, then `scripts/mirror.sh gen
  GQ2.Dyadic.SqCore.GradedClassFiveKnob`.  Clean, no name collisions.  No dependents to check:
  the module is new and nothing imports it.
* 41 declarations, 41 `#print axioms` pins.  Every one is
  `[propext, Classical.choice, Quot.sound]` except `cfiveRow_handleWord_congr`, which is
  `[propext, Quot.sound]`.
* No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`, no linter
  warnings.  Whole-file elaboration is about 6 seconds.
* Imports added: `GQ2.Dyadic.SqCore.GradedClassFourKnob` and
  `GQ2.Dyadic.SqCore.GradedGammaFourFive`.  The first is taken for `cfourKnob_comm_row`,
  `cfourKnob_sq_nuLam` and `cfourKnob_sq_nu` in §3, and it carries `GradedClassFourIdentity`
  and `GradedBridge` (hence `bridge_row_image`) with it.  No `SqCore → Count` import was taken;
  the owner item is untouched.  `GQ2.lean` not edited, per the lane.
* Independent restatement check (scratch, not committed), nine items, all typecheck: Hall-Petrescu
  and the pairing written out with no `commP`; the `T`-fourth-power and the `Y`-eighth-power with
  `twoCentralSeries` and `map` instead of `lambdaImage`; the Jacobi rewriting raw; the six-family
  decomposition with `zLayer` and `lambdaImage` spelled as `map`, and its six hypotheses as raw
  words; the relator blindness with the correction's membership written upstairs; the row repair
  with its knob clause raw; and `cfiveRow_supply_of_reachable` consumed against a fully
  spelled-out `SqClassClearingSupply h 5`.
* The element bracket `⁅ , ⁆` is avoided throughout, as in wave 71; everything is written in
  `commP`, and `gFourFive_levelMk_commutator` (wave 71's, reused) is the one place the level map
  meets mathlib's bracket.  The claim in some older notes that the bracket "does not elaborate in
  SqCore" is false and was not repeated.
