# W71: the graded layer `γ₄/γ₅`, and a correction to wave 70's tooling record

Lane W71-FIVE.  New module `GQ2/Dyadic/SqCore/GradedGammaFourFive.lean`; no edits to existing
files.  Prefixes `gFourFive` / `cfiveKnob`.

## 0.  Headline

**The layer-agnostic tooling held by half, and wave 70's record needs correcting.**

`gThreeFour_hallWitt` is genuinely layer-agnostic and was reused unchanged.  `gThreeFour_jacobi_of`
is **not**: it quantifies its two reductions over the whole ambient group, and at `γ₄/γ₅` neither
is available at unrestricted arguments.  The obstruction is exactly the one the class-five map
already recorded for brackets.  At `γ₃/γ₄` a triple bracket is in the top layer, so wave 70's
`hcentral` is free; at `γ₄/γ₅` a triple bracket is in `T = lambdaImage G 3 5`
(`cfive_commP_lambdaTwo_mem_lambdaThree`), one layer short of the central `Z = zLayer G 4`.

> ⭐ `gFourFive_hcentral_iff`: wave 70's `hcentral`, read in `Q₅`, is **equivalent** to the
> vanishing of every fourfold bracket in `Q₅`.

That is a measurement, not a refutation.  No witness for the failure of that vanishing is
committed anywhere in the tree, and none is claimed here.  What is committed is that the
class-five calculus does not supply it, and that if it did then `gFourFive_jacobi` below would be
an identity between three trivial elements.

**The repair keeps the tooling.**  ⭐⭐ `gFourFive_jacobi_of` is the passage over an arbitrary
group taking the six pointwise equations the Hall-Witt reduction actually rewrites, instead of two
universals.  It strictly subsumes wave 70's version, and `gFourFive_jacobi_of_forall` re-derives
that version from it as the check.  **A later wave should reach for the pointwise form**, since
the ∀-form is usable only at the layer where the top of the quotient is two steps up.

## 1.  Jacobi at `γ₄/γ₅` (module §2)

> ⭐⭐ `gFourFive_jacobi`: in `Q₅`, for `p ∈ Y = lambdaImage G 2 5` and **arbitrary** `q, r`,
> `commP (commP p q) r * commP (commP q r) p * commP (commP r p) q = 1`.

The side condition is weight bookkeeping, not weakness: all three rotations then lie in `Z`
(`gFourFive_triple_mem_one` and its two companions), so this is the Jacobi identity of the layer
`γ₄/γ₅` at weights `2 + 1 + 1`, which is the only shape a weight-4 identity can have with three
entries.  The three reductions are §1's vanishing plus wave 70's pattern:

* `gFourFive_inv_mid_one` is wave 70's proof with `Y` moved to `T`;
* `gFourFive_inv_mid_two` picks up an extra term wave 70 did not have, a bracket of a `T`-element
  against a `Y`-element, killed by `gFourFive_commP_vanish`;
* `gFourFive_inv_mid_three` is **shorter** than wave 70's, because the correction term of
  `cfour_commP_mul_right` dies outright, so the inner bracket is exactly inverted.

Since a bracket of two `Q₅`-elements lies in `Y`, the fourfold form ⭐⭐ `gFourFive_jacobi_iter`
carries **no hypothesis at all**.  That is the form a spanning argument for the fourfold-bracket
part of `γ₄/γ₅` consumes, and it is the class-five analogue of the `L₃(V)` step in wave 70's §4.

## 2.  The vanishing that runs the layer (module §1)

> ⭐ `gFourFive_commP_vanish`: in `Q₅`, `commP z y = 1` for `z ∈ T` and `y ∈ Y`.

This is `cfive_commutator_lambdaTwo` at `k = 3` read downstairs, i.e. `⁅γ₃, γ₂⁆ ≤ γ₅`.  It is what
kills every correction term in §§2 and 4, and it has no class-four analogue: one class down the
corresponding statement is `⁅γ₂, γ₂⁆ ≤ γ₄`, which is `Y` being abelian, and that is exactly the
fact class five loses.  So the class-five layer is not run by an abelianness but by a vanishing one
layer lower down, and that turns out to be enough.

## 3.  Generation (module §3)

> ⭐⭐ `gFourFive_zLayer_le_gen`: for `1 ≤ k`, a **closed** subgroup of `Q_{k+2}` holding `y ^ 2`
> and `commP y q` for every `y ∈ lambdaImage G k (k + 2)` and every `q` holds `zLayer G (k + 1)`.

Wave 70's `gThreeFour_zLayer_le` is the case `k = 2`.  The class-five instance is `k = 3`
(`gFourFive_zLayer_le`), where the side condition sits on `T` and not on `Y`, exactly as the
class-five map predicts.  The statement was generalised rather than replayed because nothing in
wave 70's proof was about the number three: it is the recursion `γ_{k+1} = twoCentralSucc γ_k`
pulled back along `levelMk`, and `1 ≤ k` is what makes that recursion available.
`gFourFive_levelMk_commutator` is likewise stated at a free level.

## 4.  The knob inventory at class five (module §4)

Wave 70 recorded that "a class-five knob inventory must be redone from `relBase_sqWord_free`",
because `cfour_sqRelWord` is class-four-only.  Done, through `gFourFive_sqRelWord`.  **With the
correction moved from `γ₂` to `γ₃`, all five slots buy exactly the class-four expressions.**

| slot | knob | name |
| --- | --- | --- |
| `σ` | `commP c (m 1)` | `cfiveKnob_dress_zero` |
| `x₀` | `commP (m 0) c` | `cfiveKnob_dress_one` |
| `x₁` | `c² · commP c (m 2)` | `cfiveKnob_dress_two` |
| `u_{j'}` | `commP c (m (sqHandleIdxV j'))` | `cfiveKnob_dress_handleU` |
| `v_{j'}` | `commP (m (sqHandleIdxU j')) c` | `cfiveKnob_dress_handleV` |

`cfiveKnob_dress_core` composes the three core knobs.  Every knob lands in `Z = γ₄/γ₅` and is
central of exponent two, so the chaining is free, as at class four.

**The stability of the table is a result, not a restatement: two entries are not the class-four
proof one class up.**

* The `x₀`-slot's fourth power is blind for a **different reason**
  (`gFourFive_pow_four_dress`).  The class-four proof runs through `cfour_pow_four_mul`, which
  needs `Y` abelian.  Here the inner square already collects the whole correction into `Z`
  (`gFourFive_sq_dress`: `(p·c)² = p²·(c²·commP c p)`) and the **outer** square kills it, since
  `Z` has exponent two.
* The `x₁`-slot's `conjP` factor, which at class four had already been collapsed to a triple
  bracket before any knob was computed, is live here.  It contributes
  `commP (m 2) c · commP c (conjP (m 2) (m 0))`; the second term reduces to `commP c (m 2)`
  because `conjP (m 2) (m 0)` differs from `m 2` by a `Y`-element and `⁅T, Y⁆` is trivial, and the
  two are then mutually inverse in an exponent-two layer.  `gFourFive_dress_two_conj_factor`
  isolates the cancellation, and it is stated for arbitrary `p, s`, not only for the frame letters.

So the `x₁`-slot remains the only source of squares, and `c²` remains available only bundled with
a bracket against `m 2`.  Wave 70's asymmetry survives the class jump verbatim.

## 5.  The class-five obligation (module §5)

> ⭐⭐ `cfiveKnob_supply_of_reach`: `SqClassClearingSupply h 5` follows as soon as, at every
> selected marking and handle, some exactly row-trivial, mod-2 independent frame admits a
> `γ₃`-valued, exactly row-trivial correction killing the relator in `Q₅`.

This is wave 70's `cfourId_supply_of_reach` one class up, with two deliberate differences.  The
correction is inside `γ₃` rather than `γ₂`, which is what puts every knob in `γ₄/γ₅`.  And the
base dressing is **existentially quantified** rather than being wave 68's tuple, because class
four is open and no frame clearing it is committed; a later wave supplies whatever frame its
class-four argument produces.  Rows multiply, mod-2 independence is blind to a `γ₂`-factor and
`γ₃ ≤ γ₂` (`cfourId_modTwoIndep_mul`), and the relator clause is the membership read in `Q₅`.

`cfiveKnob_kills` is the identity form: if the core-slot knob product is inverse to the base
relator value, the corrected relator is trivial in `Q₅`.

**Nothing is discharged and nothing is refuted.**  No instance of `SqClassClearingSupply` is
proved here, at class four or at class five.

## 6.  What a class-five run now has, and what it still lacks

Has: the layer calculus (§1), Jacobi in both the weight-`(2,1,1)` and the fourfold form (§2), the
generation half of the graded decomposition (§3), the full knob inventory (§4), and the obligation
in the shape wave 70 reached (§5).

Lacks, and these are the named next steps:

1. The **relations** half of the graded decomposition of `γ₄/γ₅`, as at class four.
   `gFourFive_zLayer_le` gives generation only, and wave 70's §4 already recorded that the
   `L₃(V)` spanning claim needs the relations half.  The same gap is one layer up.
2. A **row-repair at `γ₃`**: wave 68's `bridge_row_image` supplies exactly row-trivial corrections
   inside `γ₂`, and `cfiveKnob_supply_of_reach` asks for them inside `γ₃`.  Wave 70's
   `cfourId_row_repair` is the class-four shape of what is wanted.
3. Class four itself.  `cfiveKnob_supply_of_reach` is conditional on a frame that clears class
   four, and no such frame is committed.

## 7.  Verification record

* Base `ad0f7788`, lane branch `claude/w71-five`, cache at `1cc0535c`.
* Harness: `scripts/mirror.sh sweep` (5798 artifacts), then
  `scripts/mirror.sh gen GQ2.Dyadic.SqCore.GradedGammaFourFive`, then `scripts/mirror.sh check`
  on the source file.  Clean, no name collisions.
* Axiom pins: 49 `#print axioms`, one per declaration (49 declarations, 49 pins).  Every one is
  `[propext, Classical.choice, Quot.sound]` except `gFourFive_conj_iff`,
  `gFourFive_conj_mul_right`, `gFourFive_conj_mul_left` and `gFourFive_conj_eq`, which are
  `[propext]` only.
* No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`, no linter
  warnings.  Whole-file elaboration is about 4 seconds.
* Imports added: `GQ2.Dyadic.SqCore.GradedClassFive` and
  `GQ2.Dyadic.SqCore.GradedClassFourIdentity`.  The second is taken for `cfourId_modTwoIndep_mul`
  in §5 and it carries `GradedGammaThreeFour` (hence `gThreeFour_hallWitt`) with it, so no third
  import is needed.  No `SqCore → Count` import was taken; the owner item is untouched.
* Independent restatement check (scratch, not committed), nine items, all typecheck: Jacobi and
  its fourfold form written out with no `commP`; the generation statement with `map` and
  `twoCentralSeries` instead of `zLayer` and `lambdaImage`; the §1 vanishing as elementwise
  commutation of the two images in `Q₅`; `gFourFive_hcentral_iff` with both sides spelled out as
  raw words; the `σ`- and `x₁`-slot knobs raw; wave 70's two-hypothesis passage discharged by the
  pointwise one; and a fully spelled-out `SqClassClearingSupply h 5` discharged by
  `cfiveKnob_supply_of_reach`.
* The element bracket `⁅ , ⁆` still does not elaborate inside `GQ2.Dyadic.SqCore` (wave 69's
  finding).  Everything is written in `commP`, and `gFourFive_levelMk_commutator` is the one place
  that meets mathlib's bracket, through `commutatorElement_def` with the word spelled out.
