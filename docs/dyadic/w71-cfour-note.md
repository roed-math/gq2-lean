# W71: the class-four leftover, evaluated; the wave-70 obstruction analysis withdrawn

Lane W71-CFOUR.  New module `GQ2/Dyadic/SqCore/GradedClassFourKnob.lean`; no edits to existing
files.  Prefix `cfourKnob`.  Base `ad0f7788`, lane branch `claude/w71-cfour`.

## 0.  Headline

**`SqClassClearingSupply h 4` is NOT discharged, and it is NOT refuted.**  What changed is the
diagnosis.  Wave 70's note, §4, recorded as uncommitted analysis that the knob subgroup has
codimension exactly two in `Z = γ₃/γ₄`, missing the fourth powers `σ^{[4]}` and `x₀^{[4]}`, and
that a `w⁴` cancellation would close the gap.  **Both halves of that analysis are withdrawn, in
the optimistic direction.**

1. **The missing directions are not directions the leftover has.**  `cfourKnob_leftover_eq`
   evaluates the leftover, and its **only** fourth power is `A⁴`, `A = bridgeDress nu' j` being
   wave 68's dressing.  The generator fourth power `x₀⁴` occurs in the dressed frame's relator
   and in the generator relation alike, and cancels; `σ⁴` occurs in **neither**, `cfour_sqRelWord`
   carrying exactly one fourth power and that one being the `x₀`-slot's.  (Corrected at wave 73:
   this line originally named both generators as cancelling, which is right about the conclusion
   and wrong about the reason.)  No `w⁴` cancellation is needed anywhere, and wave 69's
   `A⁴`-computation, which §4 leaned on, is not used.
2. **`A⁴` is a knob outright.**  Admissibility of a square knob `c = d²` was measured in §4 by a
   codimension-two condition on the rows of `c`, repaired inside `γ₃` by `cfourId_row_repair`.
   That measurement is sound but does not govern the terms that occur: if `d` is **exactly**
   row-trivial then so is `d²` (`cfourKnob_sq_admissible`), with no repair.  Wave 68 built `A`
   to be exactly row-trivial - that is what the pivot factor `w^{-2ν'(u)ν'(v)}` is for - so `A²`
   is a legal correction and `A⁴` is its square knob (`cfourKnob_dressSq_admissible`).
   Likewise every commutator is exactly row-trivial (`cfourKnob_comm_admissible`).
3. **The `ad(x₁)²`-direction is reachable modulo the uncommitted residue `⁅⁅A, x₁⁆, A⁆`, and
   §4's argument for it is unsound.**  See §3 below, and §4 item 3 for the residue.

So the wave-71 ticket's question - does the leftover lie in the knob subgroup - is answered
`yes` for the two terms that were believed to be the obstruction, and remains open for one
factor that §4 did not identify as hard at all.

## 1.  The leftover in closed form

⭐⭐⭐ `cfourKnob_leftover_eq`.  Wave 68's tuple dresses the `σ`- and `x₀`-slots by `A` and
nothing else, so against the **undressed** frame - whose class-four relator is exactly wave 69's
`cfourEichDefect nu' j` (`cfour_relator_base`) - only three of the five factors of
`cfour_sqRelWord` move.  The `x₁`-square and the handle word are untouched, and

```text
  LEFTOVER = ⁅σA, x₀A⁆ · ⁅σ, x₀⁆⁻¹ · cfourEichDefect nu' j · (A⁴ · ⁅A, x₀⁆²) · ⁅x₁, ⁅x₁, A⁆⁆ .
```

The fourth-power factor is `cfour_pow_four_mul`; the triple-bracket factor is
`cfourKnob_triple_right_hom`, the statement that `ad(p)²` is additive in its far slot, which is
new here.  The last two factors are `Z`-elements, hence central, which is why they may be listed
at the end.

This is the closed form in the marking data: `A = u_j^{ν'(v_j)} · v_j^{ν'(u_j)} ·
w^{-2ν'(u_j)ν'(v_j)}` is explicit in the two handle rows, and every other letter is a generator.

## 2.  The fourth-power question, answered

Read off §1: the leftover's fourth-power content is `A⁴` and nothing else.  `A²` is an
admissible correction (§0.2), and the `x₁`-slot knob of `cfour_dress_two` at `c = A²` has square
part `(A²)² = A⁴` (`cfourKnob_sq_knob`, `cfourKnob_dressSq_knob`).

Two things follow for the record.

* §4's "the missing part of `Z` sits in `V^{[4]}`, represented by `σ^{[4]}` and `x₀^{[4]}`" is
  not wrong as a statement about the knob subgroup - it is simply not about the leftover, which
  has no component there.
* §4's proposed closure, wave 69's `w⁴`-cancellation, is not needed.  It should not be carried
  forward as a pending sub-step.

## 3.  The `ad(x₁)²`-direction: §4's argument has a real gap, and the gap is closable

§4's second bullet argues `K ⊇ L₃(V)` and finishes the case `⁅⁅a, x₁⁆, x₁⁆` by saying "that is
`[x₁^{[2]}, a]`, the knob of §3".  **The knob of §3 is not that element.**  Wave 70's own
committed `cfourId_x1_sq_direction` reads

```text
  commP (x₁²) q = (commP x₁ q)² · commP (commP x₁ q) x₁ ,
```

an iterated bracket **times a square**.  The identification drops the square, and the square
cannot be supplied separately: `cfour_dress_two`'s own docstring records that the `x₁`-slot
bundle is the only knob in the inventory that produces a square, because `m 2 ^ 2` is the only
square in `cfour_sqRelWord`.  So `K ⊇ L₃(V)` is **not established** by that argument.  (Whether
it is true is open; nothing here decides it.)

The gap is closable by pairing two knobs instead of reading one.  ⭐⭐⭐
`cfourKnob_sq_knob_pair`: run the `x₁`-slot knob `c ↦ c² · ⁅c, q⁆` at `c = p²` and at
`c = ⁅p, q⁆` and multiply.  Each contributes `⁅p, q⁆²`; the two cancel, because `⁅p, q⁆` is a
`Y`-element and a `Y`-element has trivial fourth power (`cfourKnob_pow_four_lambdaTwo`).  What
survives is

```text
  p⁴ · ⁅⁅p, q⁆, p⁆ · ⁅⁅p, q⁆, q⁆ ,
```

a fourth power and two **pure** iterated brackets, no square attached.

At `p = A`, `q = x₁` both corrections are admissible (§0.2), and `cfourKnob_triple_swap` -
`⁅⁅q, p⁆, p⁆ = ⁅p, ⁅p, q⁆⁆` in `Z` - makes the last factor literally the leftover's triple
bracket.  Since the `x₁`-slot knob is multiplicative in its correction
(`cfourKnob_dress_two_mul`), this is one move, not two: ⭐⭐ `cfourKnob_pair_correction`
exhibits the single `γ₂`-element

```text
  c = A² · ⁅A, x₁⁆ ,
```

exactly row-trivial, whose `x₁`-slot knob is `A⁴ · ⁅⁅A, x₁⁆, A⁆ · ⁅x₁, ⁅x₁, A⁆⁆`.

## 4.  What is actually left

Against §1, the correction of §3 moves the leftover's fourth power and its triple bracket.  What
remains, and what a wave-72 run should target, is:

1. **`⁅σA, x₀A⁆ · ⁅σ, x₀⁆⁻¹ · cfourEichDefect nu' j`** - the two class-four defects, core and
   handle, whose class-three images are both `bridgeDefect nu' j` and cancel there.  Their
   product lies in `Z` (that is `cfourId_leftover_mem_zLayer` read through §1) and it is
   `x₁`-free: every letter in it is `σ`, `x₀`, a handle letter or the pivot.  This factor was
   not identified as an obstacle by §4 at all, and it is now the main one.
2. **`⁅A, x₀⁆²`** - a square of a commutator class.  The commutator `⁅A, x₀⁆` is exactly
   row-trivial (`cfourKnob_comm_admissible`), so it is a legal `x₁`-slot correction, and its
   knob is `⁅A, x₀⁆² · ⁅⁅A, x₀⁆, x₁⁆`; the residue has outer slot `x₁`, where `gThreeFour_jacobi`
   rewrites it into two brackets with outer slots `A` and `x₀`.  This looks routine but is not
   committed.
3. **`⁅⁅A, x₁⁆, A⁆`** - the residue of §3, a pure bracket with outer slot `A`.  Reaching it
   needs the far slot of a knob moved from a handle letter to `A`: bilinearity in the far slot
   plus the `zpow` bookkeeping of `bridgeDress`.  Not committed.

None of 1-3 is claimed here to be reachable, and none is claimed to be unreachable.

**Honesty marker.**  Nothing in this wave is evidence that no dressing works.  Everything above
concerns one sufficient route - `γ₂`-valued corrections of wave 68's frame, wave 70's
`CfourIdReachable` - and a failure of that route would not touch `SqClassClearingSupply h 4`,
which is what wave 67's equivalence is stated against.  A genuine per-class failure would have
to be a statement about the supply itself, and this wave produces no such statement.

## 5.  Information for route A (`GradedRelatorBase.lean`)

§1 gives the two routes a common object.  The leftover is `cfourEichDefect nu' j` **times three
explicit factors coming from wave 68's dressing**, so:

* at any marking where route A's clause `cfourEichDefect nu' j = 1` holds, route B's remaining
  obligation is only `⁅σA, x₀A⁆ · ⁅σ, x₀⁆⁻¹ · (A⁴ · ⁅A, x₀⁆²) · ⁅x₁, ⁅x₁, A⁆⁆`, of which §3
  already moves two factors;
* conversely the wave-70 measurement of route A's strength (its clause forces
  `bridgeDefect nu' j = 1`) is unaffected by anything here.

There is also a transferable observation for route A itself: `relBase_supply_of_eichDefect k`
is about the **trivial** dressing, and §0.2 says the trivial dressing is not the only free one -
squares of exactly row-trivial elements and commutators are free corrections at **every** class,
by statements (`cfourKnob_sq_admissible`, `cfourKnob_comm_admissible`, `cfourKnob_comm_row`)
that mention no level at all.

## 6.  Is the method class-generic?

Partly, and the split is clean.

* **Level-free, transfers verbatim.**  `cfourKnob_sq_mem`, `cfourKnob_sq_nuLam`,
  `cfourKnob_sq_nu`, `cfourKnob_sq_admissible`, `cfourKnob_comm_row`,
  `cfourKnob_comm_admissible`, `cfourKnob_mul_admissible`, `cfourKnob_levelMk_commP`.  These are
  statements about `D_sq h` and its two rows; no level, no class.
* **Class-four in proof, generic in shape.**  `cfourKnob_sq_knob_pair` and
  `cfourKnob_dress_two_mul`.  The pairing idea - pair the `p²`-knob with the `⁅p, q⁆`-knob so
  that the two copies of `⁅p, q⁆²` cancel - needs exactly two inputs per class: a Hall-Petrescu
  step in the shape of `gThreeFour_commP_sq_left`, and "a `Y`-element has trivial fourth power".
  The second is where wave 70's §5 warning bites: one layer up `Y` is no longer abelian, so that
  fact must be re-established rather than transported.  `GradedGammaFourFive.lean` (merged this
  wave) is the natural home for both at `γ₄/γ₅`.
* **Class-four throughout.**  `cfourKnob_triple_right_hom`, `cfourKnob_triple_swap`,
  `cfourKnob_push_two`, `cfourKnob_push_four`, `cfourKnob_leftover_eq` - the last unavoidably
  so, being an evaluation of a class-four object.

## 7.  Corrections to the wave-70 note, itemised

* §4, "the missing part of `Z` sits in `V^{[4]}`, represented by `σ^{[4]}` and `x₀^{[4]}`":
  true or not of the knob subgroup, it does not describe the leftover, which has no `V^{[4]}`
  component other than `A⁴` (`cfourKnob_leftover_eq`).
* §4, "Wave 69's other analysis point answers it in the negative: its `A⁴` term contributes
  ... which cancel because `w⁴` has order two":  withdrawn as unnecessary.  `A⁴` needs no
  cancellation; it is the square knob of the admissible correction `A²`.
* §4, "`K ⊇ L₃(V)` ... the only surviving case is `⁅⁅a, x₁⁆, x₁⁆`, and that is `[x₁^{[2]}, a]`,
  the knob of §3":  the knob of §3 is that bracket **times `(commP x₁ a)²`**, by wave 70's own
  `cfourId_x1_sq_direction`.  The bullet does not establish `K ⊇ L₃(V)`.
* §4's framing of admissibility as a codimension-two condition:  correct as stated, but it is
  not the binding constraint on the corrections that arise, all of which are exactly row-trivial
  on the nose.

Nothing committed by wave 70 is affected: all four items are about its §4, which that note
marked ANALYSIS NOT COMMITTED.  Its Lean statements are untouched and are used here.

## 8.  Verification record

* Base `ad0f7788`, lane branch `claude/w71-cfour`.  The shared cache had advanced past the base
  (three sibling merges) and was being rewritten by a concurrent umbrella build during the first
  sweep, which produced a spurious missing-olean error; the sweep was repeated after the build
  finished.
* `scripts/mirror.sh sweep` (5808 artifacts), then `scripts/mirror.sh check` on the module after
  every increment, then `scripts/mirror.sh gen GQ2.Dyadic.SqCore.GradedClassFourKnob`.  Clean, no
  name collisions.
* 21 declarations, 21 axiom pins, **every one** `[propext, Classical.choice, Quot.sound]`.  No
  `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.
* One import, `GQ2.Dyadic.SqCore.GradedClassFourIdentity`.  No `SqCore → Count` import; the
  owner item is untouched.  `GQ2.lean` not edited, per the lane.
* The element bracket `⁅ , ⁆` is again avoided throughout; everything is written in `commP`, and
  `cfourKnob_levelMk_commP` is the one place the level map meets it.
