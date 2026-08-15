# W76-BASE: the depth-two base, reduced to two layer classes (and the case that it is false)

**Lane W76-BASE, branch `claude/w76-base`, base `97d51e93`.**  One new module,
`GQ2/Dyadic/SqCore/GradedJoinBase.lean` (prefix `gBase`), 48 declarations, all 48 pinned on
`[propext, Classical.choice, Quot.sound]`.  No edits to existing files, no `sorry`, no new
axiom, no `native_decide`, no heartbeat or recursion-depth options.

Commits: `f25f420f` (module opened), `ee8f3ac4` (T1), `88b66ea4` (T2 triples and bracket
squares), `64845fa1` (T2 fourth powers and the base), `64dfe4a6` (the residual in its two
forms).

Verification of record: `scripts/mirror.sh sweep` at lane start, `scripts/mirror.sh gen
GQ2.Dyadic.SqCore.GradedJoinBase` green after every commit, zero warnings, zero sorries.  New
leaf module, no dependents, `GQ2.lean` untouched per protocol.

## Headline

**`GJoinBase h` is now one atomic family of `3 + 2h` layer classes, and the argument of §4 says
that family is false.**

```
gBase_joinBase_of_residual : GBaseResidual h → GJoinBase h
```

where `GBaseResidual h` is: at every selected marking `ν'` and every letter `xᵢ`,

```
⁅⁅x₁, xᵢ⁆, x₁⁆ ∈ gTowerReach h ν' 2 ,
```

equivalently (`gBase_residual_iff`, at every `c ∈ Q₄` not merely at letters)

```
⁅x₁, c⁆² ∈ gTowerReach h ν' 2 .
```

So the depth-two base is missing exactly the `(Λ²V)^{[2]}`-classes at the `x₁` slot, and
nothing else.  T3 and T4 were not attempted; T5 is stated conditionally
(`gBase_markTransitivity_of_residual`, `gBase_supply_of_residual`).

## T1: the relator's degree-three consequence, with a correction to the wave-75 note

`gBase_relator_bracket`: for every `c ∈ Q₄`,

```
⁅⁅σ, x₀⁆, c⁆ · (⁅x₁, c⁆² · ⁅⁅x₁, c⁆, x₁⁆) · ⁅H, c⁆ = 1
```

(`H` the handle word), and its solved form `gBase_xOne_triple`.  The proof is one bracket of
`cfour_sqRelWord` against `dsq_relation`: every factor of the relator lies in `Y`, so
bracketing is additive by `gThreeFour_ad_left`; the `x₀`-fourth power and the `x₁`/`σ` triple
bracket are already central and drop out; the `x₁`-square contributes through
`gThreeFour_commP_sq_left`.

**The wave-75 join note's §T2 predicted `⁅⁅c, x₁⁆, x₁⁆ = ⁅⁅x₀, σ⁆, c⁆ + Σⱼ ⁅⁅uⱼ, vⱼ⁆, c⁆`.
That is wrong: there is a third term, the bracket square `⁅x₁, c⁆².**  The reason is a grading
subtlety worth recording, because it is the whole content of this lane.  The campaign's
filtration is the lower `2`-central series, whose restriction map `ξ` raises degree by **one**
(`gr₃ = L₃(V) ⊕ (Λ²V)^{[2]} ⊕ V^{[4]}` with `V^{[4]} = ξ²(V)`), not the Zassenhaus filtration,
where it multiplies degree by `p`.  In that grading the restricted-algebra slogan
`ad (x^{[2]}) = (ad x)²` is **false**; the correct identity, forced by the group identity
`⁅p², q⁆ = ⁅p, q⁆² · ⁅⁅p, q⁆, p⁆`, is

```
ad (ξ x) = ξ ∘ ad x + (ad x)²   on degree-one elements.
```

The note dropped the `ξ ∘ ad x` term.  It is not a harmless bookkeeping term: §4 shows it is
the entire obstruction.

## T2: the base from the residual

Four ingredients, all new here.

1. **Letter generation in `Q₄`** (`gBase_letters_mem`).  `Q₄` is discrete
   (`gTower_discrete`), so every subgroup is closed, and `dsq_topGen` transfers to "contains
   every letter class, hence is everything".  Cheap, and the workhorse: it is what lets a
   statement over all of `Q₄` be checked on the `3 + 2h` letters.
2. **The triple brackets** `⁅⁅p, q⁆, r⁆` (`gBase_triple`).  The outer slot reduces to the
   letters by the committed `gTower_commHom_span`; a non-`x₁` letter there makes the class a
   far-span bracket knob, because **every bracket is an admissible depth-`2` correction**
   (`gBase_adm_commP`: both rows are characters, so they kill commutators outright).  For the
   `x₁` letter, both inner slots reduce to letters as well, the triple bracket being additive
   in each of them (`gBase_triple_mul_left`, `gBase_triple_mul_right`, and the two test
   subgroups); Jacobi discharges every letter pair with no `x₁` in it
   (`gBase_jacobi_xOne`), the pair `(x₁, x₁)` is trivial, and the pairs with exactly one `x₁`
   are the residual.
3. **The bracket squares** `⁅p, q⁆²` (`gBase_bracketSq`): the `x₁`-slot bundle knob at the
   correction `⁅a, b⁆` divided by the triple bracket of (2).
4. **The fourth powers** `p⁴` (`gBase_pow_four`).  This one turned out to be cheap, contrary
   to the note's expectation that it would need the pivot and Eichler letter identifications:
   `p⁴ = (p²)²` and `p²` is a `γ₂`-class, so it is enough that the square of any `γ₂`-element
   lands in the full reach.  `gTower_decomp` splits a `γ₂`-element into an admissible part
   `d`, whose square is the bundle knob divided by `⁅d, x₁⁆` (`gBase_comm_xOne`, itself a
   closure induction over the squares and commutators generating `γ₂`), and a two-tower part,
   whose square is a complement tower.  **No letter-by-letter identification is needed
   anywhere in this file**, so the `σ⁴` and `x₁⁴` bookkeeping the note scoped never arises.

Then `cfourCmp_zLayer_le_gens` gives `zLayer (D_sq h) 3 ≤ gTowerFullReach h ν' 2` and
`gTower_cut` pulls the exactly row-trivial part back into `gTowerReach`.

## The residual in its two forms

`gBase_residual_iff`: at every `c ∈ Q₄`,

```
⁅⁅x₁, c⁆, x₁⁆ ∈ gTowerReach h ν' 2   ↔   ⁅x₁, c⁆² ∈ gTowerReach h ν' 2 .
```

The two knob terms of T1 reach **unconditionally**: `⁅⁅σ, x₀⁆, c⁆` and each `⁅⁅uⱼ, vⱼ⁆, c⁆`
have two far elements inside, so `gBase_triple_far_inner` (Jacobi plus the far-span knobs)
discharges them at every outer slot.  So T1 does not discharge the residual; it identifies the
`L₃(V)` half of it with the `(Λ²V)^{[2]}` half.

## §4 The case that `GJoinBase h` is FALSE

**This is an argument, not a theorem.**  It uses the structure of `gr(D_sq h)` as the free
restricted Lie algebra on `V` modulo the restricted ideal generated by the relator's leading
form, which is Labute's theorem and is **not formalized in the tree**.  Everything in the Lean
file is a reduction and is neutral about the answer.

Write `V = gr₁`, `F = span{σ, x₀, uⱼ, vⱼ} ⊆ V` for the far span's image, and
`W = ker λ̄ ∩ ker ν̄' ⊆ V` for the image of the exactly-row-trivial subgroup, where `λ̄, ν̄'` are
the mod-`2` reductions of the two rows.  The relator's leading form is
`R = ξ(x₁) + ⁅x₀, σ⁆ + Σⱼ ⁅uⱼ, vⱼ⁆`.

**The inventory, in `gr₃`.**  The depth-`2` reach is spanned by:

* bracket knobs `⁅y, f⁆` for `y ∈ gr₂` row-trivial and `f ∈ F`;
* bundles `ξ(y) + ⁅y, x₁⁆` for the same `y`;
* towers `ξ²(v)`, all of `V^{[4]}` (this part of the note's §T2 is right).

The row-trivial `y` are exactly `Λ²V + ξ(W)`: the row of a `γ₂`-element is `2λ(c)` for the
square part `c`, so exact triviality forces `c̄ ∈ W`.

**Where `ξ(⁅x₁, f⁆)` comes from, and where it does not.**  For `f ∈ F`:

* the bundle at `y = ⁅x₁, f⁆` gives `ξ(⁅x₁, f⁆) + ⁅⁅x₁, f⁆, x₁⁆`, and T1 says exactly
  `⁅⁅x₁, f⁆, x₁⁆ = ξ(⁅x₁, f⁆) + (knobs)`.  The two cancel: **the bundle is vacuous there**.
  This is the degeneracy the campaign kept hitting from wave 71 on;
* the knob `⁅ξ(x₁), f⁆ = ξ(⁅x₁, f⁆) + ⁅⁅x₁, f⁆, x₁⁆` is the same expression, also vacuous;
* the bundle at `y = ξ(w)` for `w ∈ W` gives `ξ²(w) + ξ(⁅w, x₁⁆) + ⁅⁅w, x₁⁆, w⁆`.  The first
  term is a tower and the third is a bracket knob **when `w ∈ F`**.  So this generator, and
  only this one, delivers `ξ(⁅x₁, w⁆)` for `w ∈ W ∩ F`.

Hence the map `Ψ : V → gr₃/(reach)`, `f ↦ ξ(⁅x₁, f⁆)`, kills `x₁` and all of `W ∩ F`, and the
residual is `V / (⟨x₁⟩ + (W ∩ F))`.

**That quotient is two-dimensional.**  `λ̄(σ) = λ̄(x₀) = 1` and `λ̄` kills the other letters
(`PivotClimb.lean:322-347`); `ν̄'(σ) = 1` and `ν̄'(x₀) = 0` at a selected marking.  So on `F`
the two functionals are independent, `W ∩ F` has dimension `2h`, and it is spanned by the
Eichler-cleared classes `Ũⱼ = uⱼ + ν̄'(uⱼ)·w̄`, `Ṽⱼ = vⱼ + ν̄'(vⱼ)·w̄` with `w̄ = σ + c·x₀` the
pivot class (`sqEichU`/`sqEichV`, `LamFrames.lean:295-306`).  Adding `x₁` gives dimension
`1 + 2h` out of `3 + 2h`.

**So the residual is at most two-dimensional, spanned by `ξ(⁅x₁, σ⁆)` and `ξ(⁅x₁, x₀⁆)`.**  A
coefficient functional `φ` on `gr₃(free)` that reads the `ξ(⁅x₁, x₀⁆)` coordinate together with
the Hall coordinate of `⁅⁅x₁, x₀⁆, x₁⁆`, and vanishes on `L₃(V)` elsewhere and on `ξ²(V)`,
kills `⁅R, c⁆` for every `c`, kills `ξ(R)`, and kills every generator listed above; it is
nonzero on `ξ(⁅x₁, x₀⁆)`.  The one generator that could have hit it, the bundle at `y = ξ(x₀)`,
needs `x₀ ∈ W`, and `λ̄(x₀) = 1` forbids that.  **If Labute's structure theorem holds for
`D_sq h`, the residual is exactly two-dimensional and non-zero, so `GTowerLayerReach h ν' 2` is
false and `GJoinBase h` with it, at every `h ≥ 0`.**

**Honesty markers.**

* This is a statement about **one inventory**, wave 74's `gTowerKnobSet`/`gTowerTowSet` at
  depth `2`.  It is **not** evidence about `SqClassClearingSupply h k`, which is what wave
  67's `limFinal_markTransitivity_iff` is stated against.  It is the same kind of finding as
  wave 74's `gDelta_cfourCmp_span_hyp_false`: a route's sufficient condition fails, the
  residual is untouched.
* The element in question, `⁅x₁, x₀⁆²`, **is** exactly row-trivial and **does** lie in `γ₃`,
  so it really is inside what `GTowerLayerReach h ν' 2` quantifies over.  The failure is not a
  quantifier artefact.
* The `δ` functionals cannot see it.  `⁅x₁, x₀⁆` reads with `v₂ ≥ 2` (its far factor is
  `χ(x₀) - 1 = 4`), so its square reads `8`-divisibly, exactly like the knobs
  (`gJoin_knob_dvd`).  A wave-74-style functional refutation is therefore **not** available,
  and a Lean refutation needs the graded structure theorem, which the tree does not have.
* Nothing above says the depth-`3` layer statement fails.  At depth `3` the admissible
  corrections' square parts range over the row-trivial part of `γ₂`, which is far larger than
  `W`, and the counting that produces the two-dimensional gap at depth `2` does not repeat.
  The wave-74 induction `gTower_layerReach_step` runs from **any** base `k ≥ 2`, so a depth-`3`
  base would restart it.

## What W77 needs

1. **Decide the residual.**  Two layer classes, `⁅x₁, σ⁆²` and `⁅x₁, x₀⁆²`, in
   `gTowerReach h ν' 2`.  Either produce them as knob combinations (which would refute §4) or
   refute them.  A refutation needs a graded model: the cheapest formalizable one is probably
   an explicit finite class-`4` quotient of `D_sq 0` rather than the general structure theorem.
2. **If the residual is false, re-cut the base to depth `3`.**  `gTower_layerReach_of_base`
   only needs a base at some `k ≥ 2`, and the counting argument of §4 does not obstruct
   `k = 3`.  The depth-`3` version of this file's §§1-4 should go through with the same four
   ingredients, the only change being which `y ∈ gr₃` are row-trivial.
3. **Enlarge the inventory instead.**  The bundle is `t² · ⁅t, x₁⁆` for `t` an exactly
   row-trivial `γ₂`-element.  If the clearing recursion admits corrections whose square part
   is only row-trivial *modulo 2* (rather than exactly), `W` grows to all of `V` and the gap
   closes.  Whether that is legitimate is a question about `sqArbFrame`'s dressing clauses,
   not about the layer.
4. T3 (`GJoinSeparationAll`) and T4 (`GTowerKnobRealizable`) are untouched by this lane and
   are still open exactly as wave 75 left them.
