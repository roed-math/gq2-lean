# W73: the join, and the single defect the whole class-five route now turns on

Lane W73-FIVE.  New module `GQ2/Dyadic/SqCore/GradedClassFiveJoin.lean`; no edits to existing
files.  Prefix `cfiveJoin`.  Base `6a8fbc90`, lane branch `claude/w73-five`.

## 0.  Headline

**The join closes, as an equivalence, onto exactly one open input.**

> ⭐⭐⭐ `cfiveJoin_zLayer_le_iff`: for a closed `S ≤ Q₅` holding every bracket knob
> (`commP c w`, `c ∈ T`, `w ∈ X`) and every `x₁`-slot knob (`c² · commP c x`, `c ∈ T`), with
> `insert x X` topologically generating `Q₅`,
>
> ```text
>   zLayer G 4 ≤ S   ↔   ∀ c ∈ T, commP c x ∈ S .
> ```

It is an **iff**, in both directions, so the join has no slack left in it: the knob subgroup
contains the whole graded piece `γ₄/γ₅` exactly when it contains the one x₁-free defect, and no
rearrangement of the five knobs can do better.  With `cfiveJoin_knobSub_le` (every knob is in
`Z`) the containment upgrades to an equality of subgroups, `cfiveJoinKnobSub X x = zLayer G 4`
(`cfiveJoin_knobSub_eq_of_defect`).

So the honest form of the ticket's `K ⊇ L₄(V)` is: **`K = γ₄/γ₅`, the whole layer and not merely
its Lie part, conditionally on `∀ c ∈ γ₃, ⁅c, x₁⁆ ∈ K`, and unconditionally not without it.**
That defect is neither proved nor refuted here.

> **[W75-HOUSE, wave-74 update, with the qualifier that matters.**  One class down, the analogous
> route is **refuted as a theorem**: `gDelta_cfourCmp_span_hyp_false`
> (`GQ2/Dyadic/SqCore/GradedDeltaFunctionals.lean:1575`) kills the class-four span hypothesis at
> every `h ≥ 1`, because the committed corrections cannot reach the Frobenius towers that the
> twisted functionals detect.  `w74-func-note.md` §4.2 argues the same mechanism here, one level
> up: `zLayer 4` contains the tower class `σ^{2^3}`, while class-five knob readings sit in
> `2^4 ℤ₂`, so by this note's own equivalence read contrapositively the defect fails along the
> committed route.
>
> **That class-five half is analysis, not a theorem.**  Wave 74 committed the mod-8 congruence
> kit, which class four consumes; the mod-16 variant this paragraph needs was **not** committed
> (`w74-func-note.md` §4.4, third bullet, carries it as a W75 gap).  So the sentence above stays
> literally true -- the defect is still neither proved nor refuted in the tree -- and the honest
> reading is that the route is expected dead rather than known dead.  Everything this note proves
> is about arbitrary subgroups `S` and stands unchanged.]**

**Nothing is discharged and nothing is refuted.**  `SqClassClearingSupply h 4` and
`SqClassClearingSupply h 5` are untouched.  A failure of this join would be a statement about
this route: `cfiveKnob_supply_of_reach` quantifies its base frame existentially, and class five
is conditional on class four in any case.

## 1.  Why the join is one question and not six (module §4)

The generation half `gFourFive_zLayer_le` asks for exactly two things, both indexed by `T`: the
squares `c²` and the brackets `commP c q` at every `q`.  Read against wave 71's table:

* the four **bracket** knobs supply `commP c w` at every frame letter **except** `x₁`, and
  `q ↦ commP c q` is a homomorphism killing `Y` (`cfiveJoin_far_lambdaTwo_mul`), so the far slots
  they reach are exactly the closed span of `X ∪ Y`, and the only far-slot direction they can
  miss is `x₁`'s.  (Whether they miss it is the defect: they do not, for instance, if the frame
  letters are dependent in `Q₅/Y`.  No claim either way is made here.)
* the one **square** knob supplies `c²` only bundled as `c² · commP c x`.

Both gaps are the same element.  ⭐ `cfiveJoin_defect_pt_iff`: the `x₁`-slot knob is the product
of the two, so a subgroup holding it holds `c²` iff it holds `commP c x`.  Fill in that one
family and the generation half closes; leave it out and neither half of the generation input is
available.  That is the whole of §4.

**Wave 70's `L₃(V)` argument is not reused, and the trap it fell into is closed off by the
statement's shape.**  Wave 71 refuted that argument for reading a triple bracket off a knob that
is the bracket *times a square*.  Here the square is never dropped: `cfiveJoin_defect_pt_iff` is
an equivalence, not a one-way reading, and every use of it carries the knob as a hypothesis.

## 2.  The six families, one at a time (module §6)

Every family of `cfiveSpan_zLayer_le_gens` reduces to a member of the last two with the free far
slots put at `x = x₁`.

| # | family | status |
| --- | --- | --- |
| 1 | `g ^ 8` | **iff** `⁅⁅g², x₁⁆, x₁⁆` (`cfiveJoin_family_one_iff`) |
| 2 | `⁅a, b⁆ ^ 4` | **iff** `⁅⁅⁅a,b⁆, x₁⁆, x₁⁆` (`cfiveJoin_family_two_iff`) |
| 3 | `⁅g², r⁆ ^ 2` | **iff** `⁅⁅g², r⁆, x₁⁆` (`cfiveJoin_family_three_iff`) |
| 4 | `⁅⁅a,b⁆, r⁆ ^ 2` | **iff** `⁅⁅⁅a,b⁆, r⁆, x₁⁆` (`cfiveJoin_family_four_iff`) |
| 5 | `⁅⁅g², r⁆, q⁆` | **reached unconditionally** for `q` in the closed span of `X ∪ Y`; open at `q ≡ x₁` |
| 6 | `⁅⁅⁅a,b⁆, r⁆, q⁆` | the same (`cfiveJoin_family_six_of_span`) |

Rows 5 and 6 are the part of the join that closes outright, with no hypothesis on the defect:
`cfiveJoin_family_five_of_span` and `cfiveJoin_family_six_of_span`.  Rows 3 and 4 are the
`x₁`-slot knob read at a single correction.  Rows 1 and 2 are where **wave 72's pairing is
consumed**: ⭐⭐ `cfiveJoin_pow_four_iff` runs the pairing at the single `T`-correction
`y² · ⁅y, x₁⁆` and finds its knob to be `y⁴ · ⁅⁅y, x₁⁆, x₁⁆`, so the fourth power and the
doubled bracket differ by a knob and neither is reached without the other.

⭐⭐ `cfiveJoin_zLayer_le_via_gens` runs the join through all six families into
`cfiveSpan_zLayer_le_gens`, reaching the same conclusion as §1's generation-half route at the
cost of two more closedness hypotheses.  Both routes close on the same defect.

**On the "no reached family" reading.**  It is worth being precise about what rows 1 to 4 say:
this route does not reach them, and the reason is exactly identified (the square is available
only in the `x₁`-bundle).  Nothing here says no dressing reaches them.  A model exhibiting the
failure is not committed anywhere, and none is claimed.

## 3.  Wave 72's uncommitted analysis, checked (module §5)

The ticket flagged wave 72's `A⁸` paragraph as analysis, not result.  It checks out, and it is
one term shorter than wave 72 thought.

> ⭐ `cfiveJoin_commP_self_lambdaTwo`: `commP (commP y q) y = 1` for `y ∈ Y`, because
> `commP y q ∈ T` and `⁅T, Y⁆` is trivial.

Wave 72's statements are true as written; this evaluates a factor inside them.  Two consequences:

* ⭐ `cfiveJoin_commP_sq_lambdaTwo`: `commP (y²) q = (commP y q)²` for `y ∈ Y` and **every** `q`,
  with no trailing bracket.  `cfiveSpan_commP_sq_left` carries one.
* ⭐ `cfiveJoin_pair_correction`: the pairing's leftover is `y⁴ · ⁅⁅y, q⁆, q⁆`, **one** pure
  iterated bracket and not two.

Instantiated at `y = A²` with `A = bridgeDress nu' j`, which is legal since `g² ∈ Y` for
every `g` (`cfiveSpan_sq_mem_lambdaTwo`), this delivers `A⁸ · ⁅⁅A², x₁⁆, x₁⁆`, confirming wave 72's
reading of the fourth power as `A⁸`.  And `A⁸` is precisely family one at `g = A`, so the
class-five leftover's fourth-power term and the table's row 1 are the same object.

## 4.  The join at the real inventory (module §8)

The abstract statement takes `X`, `x` and a density hypothesis.  All three are supplied by the
frame the class-five obligation already carries.

* ⭐ `cfiveJoin_topGen_of_modTwoIndep`: a mod-2 independent frame topologically generates `Q₅`.
  The pro-2 Frattini criterion (`eq_top_of_forall_not_le_index_p`) gives it in `D_sq h`, and the
  level map is a continuous surjection, so the preimage of the closed span swallows everything.
  **The density hypothesis is therefore `SqModTwoIndep`, a clause already in the obligation.**
* `cfiveJoin_farSlot_cases`: the four bracket knobs' far slots are `m 1`, `m 0`,
  `m (sqHandleIdxV j)` and `m (sqHandleIdxU j)`, which by `sqIdx_cases` are exactly the frame
  slots other than `m 2`.  So `X` is `{m i : i ≠ 2}` and `x` is `m 2`, on the nose.
* `cfiveSpan_isClosed` makes every closedness condition free, `Q₅` being discrete.

> ⭐⭐⭐ `cfiveJoin_zLayer_le_iff_frame`: at any mod-2 independent frame of `D_sq h`,
> `zLayer 4 ≤ S ↔ ∀ c ∈ T, commP c (levelMk 5 (m 2)) ∈ S`, given the five knob clauses.

## 5.  The defect, reduced as far as this wave takes it (module §7)

Neither reduction is a discharge; both move the question.

* ⭐⭐ `cfiveJoin_defect_of_two_families`: `t ↦ commP t x` is a homomorphism on `T`, and `T` is
  topologically generated by the squares and brackets of `Y`, so the defect follows from two
  families indexed by `Y`: `(commP y x)²` and `commP (commP y r) x`.  The first is
  `commP (y²) x` evaluated by §3.
* ⭐ `cfiveJoin_defect_jacobi`: on a bracket generator `commP y w` with `w` an x₁-free far slot,
  Jacobi gives `commP (commP y w) x = commP (commP w x) y · commP (commP x y) w`, and the second
  factor is a bracket knob because `commP x y ∈ T`.  So that instance of the defect costs exactly
  `⁅⁅w, x₁⁆, y⁆`, a bracket with **both** slots in `Y`.

That residual bracket vanishes as soon as either slot lies in `T`
(`gFourFive_commP_vanish` and `gFourFive_commP_vanish'`), so it only ever sees its two arguments
modulo `T`.  Whether it is a knob is not settled here, and no bi-additivity for it is committed.

## 6.  What a class-five run now has, and what it still lacks

Has: the layer calculus, Jacobi, the knob inventory and the obligation (wave 71); the row repair,
the admissible corrections, the pairing and the six-family decomposition (wave 72); and now the
join, as an equivalence, at the real frame, with the six families read one at a time.

Lacks, as named next steps:

1. **The defect `∀ c ∈ γ₃, ⁅c, x₁⁆ ∈ K`**, in either of its two equivalent forms.  This is now
   the *only* thing between the knob inventory and `K = γ₄/γ₅`.  Sharpest sub-question: is the
   `⁅Y, Y⁆` pairing of §5 a knob?
   **[W75-HOUSE: still the only thing, and now expected to fail rather than to be supplied.  Wave
   74's tower obstruction refutes the class-four analogue outright and argues this one; the
   cheapest way to settle it is the mod-16 congruence kit of `w74-func-note.md` §4.4, one
   congruence pass over the same coefficient bounds.  A lane that goes looking for the defect as
   a *positive* should read `w74-func-note.md` §4.2 first.]**
2. **A class-five leftover in closed form**, unchanged from wave 72's list.  §3 identifies its
   fourth-power term with family one, but no leftover is evaluated.
3. **Class four itself**, ~~unchanged~~.  **[W74-HOUSE, watch round 11: the same defect the
   wave-72 five note carried, one wave later, and falsified 4 minutes 41 seconds after this note
   landed.]**  The *lack* survives: `SqClassClearingSupply h 4` is still neither discharged nor
   refuted.  But class four did move, in this very wave, in the parallel W73-KNOB lane
   (`56db0e02` 18:56:31 here, `0063dc8c` 19:01:12 there): `cfourCmp_core_reduce` turns the
   class-four relator into `cfourDefCore nu' j` on the nose with one admissible correction, and
   `cfourCmp_zLayer_le_triple` reduces the three uniform questions to one.  See
   `w73-knob-note.md` §0 and §5.

The class-four lane's wave-72 finding ("class four reduced to ONE x1-free defect") and this
lane's are the same shape one class apart.  Whether they are the same obstruction is not
investigated here and should not be assumed.  **[W74-HOUSE: the caution is right about this
lane, and the wave answered the question elsewhere.]**  The owner's wave-73 status
(`owner-items-2026-08-05.md`, "the wave's result is a convergence") records that both graded
classes reduce to the same condition, reached independently by the two lanes: this note's
"is the `⁅Y, Y⁆` pairing of §5 a knob?" and `w73-knob-note.md` §9's "is `⁅y, x₁⁆` (equivalently
`y²`) a move?".  Read the two together before quoting either "should not be assumed" or the
convergence alone.

**[W75-HOUSE, and this is the third reading the paragraph has needed.**  Wave 74 settled the
question the caution was about: the two are the same obstruction, and it is the tower obstruction.
The class-four half is a theorem (`gDelta_cfourCmp_span_hyp_false`); the class-five half is
argued but uncommitted (`w74-func-note.md` §4.2, needing the mod-16 kit).  So the convergence the
owner recorded is real, and what both classes converged on is a **dead end**, not a target: the
condition fails at the committed knob subgroup because granting it would force functional-visible
Frobenius towers into the move image.  Quote the convergence with that ending attached.]**

## 7.  Verification record

* Base `6a8fbc90`, lane branch `claude/w73-five`, cache at `a515b437`.
* Harness: `scripts/mirror.sh sweep` (5833 artifacts) at lane start, then `scripts/mirror.sh
  check` on the source file after every increment, then `scripts/mirror.sh gen
  GQ2.Dyadic.SqCore.GradedClassFiveJoin`.  Clean, no name collisions.  No dependents to check:
  the module is new and nothing imports it.  (Registered at `959e22aa`, 69 seconds after this
  note; `GQ2.lean` imports it now.  [W74-HOUSE, watch round 11.])
* 33 declarations, 33 `#print axioms` pins.  Every one is
  `[propext, Classical.choice, Quot.sound]`.
* No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`, no linter
  warnings.  Whole-file elaboration is about 6 seconds.
* One import added, `GQ2.Dyadic.SqCore.GradedClassFiveKnob`, which carries
  `GradedGammaFourFive`, `GradedClassFourKnob` and `Certificate` (hence `sqIdx_cases`) with it.
  No `SqCore → Count` import was taken; the owner item is untouched.  `GQ2.lean` not edited, per
  the lane.
* Independent restatement check (scratch, not committed), twelve items, all typecheck: the join
  and its square form with `commP` expanded to its word and `lambdaImage` / `zLayer` expanded to
  `Subgroup.map (levelMk _ _) (twoCentralSeries _ _)`; the Hall-Petrescu simplification and the
  pairing raw; family one's equivalence and family six's unconditional case raw; the knob
  subgroup equality at `D_sq h`; the frame form consumed at `sqArbFrame h nu' j a`; the
  two-family reduction raw; a satisfiability check that the knob subgroup itself meets both knob
  clauses (so the equivalence is not vacuously quantified); a round trip at `S = Z`, where the
  knob clauses hold outright and the forward direction must and does return the defect clause;
  and the six-family route discharged against raw hypotheses.
  One earlier item was **discarded as vacuous**: comparing the two routes' proof terms with
  `rfl` succeeds for any two proofs of a `Prop` by proof irrelevance and checks nothing.
* The element bracket `⁅ , ⁆` is avoided throughout, as in waves 71 and 72; everything is written
  in `commP`.
