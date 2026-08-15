# W78-ABSORB: Labute's Theorem 5 absorption, formalized; the class-4 seed recovered

**Lane W78-ABSORB, branch `claude/w78-absorb`, base `e6bbd2b9`.**  One new module,
`GQ2/Dyadic/SqCore/GradedAbsorption.lean` (prefix `gAbs`), 103 declarations, 103
`#print axioms`, every one `[propext, Classical.choice, Quot.sound]` or a subset
(`gAbs_pow_combine` drops `Classical.choice`).  No edits to existing files, no `sorry`, no
new axiom, no `native_decide`, no heartbeat or recursion-depth options.  New leaf module, no
dependents, `GQ2.lean` untouched per protocol.

Commits: `aa9412fc` (module opened), `920cab92` (corrected rows, reach in their layer
kernel, coker readings), `2f0aecb8` (the widened reach absorbs the triple family),
`69b82716` (T1, the normal form), `6c0ef904` (T2 the kill, T3 the re-seeded recursion, and
the functional re-proof of the wave-77 refutation).

Verification of record: `scripts/mirror.sh sweep` green at lane start, `scripts/mirror.sh
gen GQ2.Dyadic.SqCore.GradedAbsorption` green after every commit, zero errors, zero
warnings, zero sorries.

## Headline

**Wave 77 refuted the route's statement, not Labute's argument.  His Theorem 5 mechanism is
now formalized: the two unreachable classes are absorbed as explicit `𝔽₂`-coefficients that
the Δ-functionals kill on every actual defect, and the class-3-to-4 clearing step goes
through WITHOUT the refuted full-generation statement.**

```
gAbs_layer_wide          : row-trivial γ₃ ⟶ gAbsWide = gTowerReach ⊔ ⟨B, C⟩   (T1, unconditional)
gAbs_leftover_decomp     : g = p · B^{e₁} · C^{e₂},  mk p ∈ reach,  e ∈ 𝔽₂     (T1, unconditional)
gAbs_zero_reader_reach   : all readings zero ⟶ e₁ = e₂ = 0 ⟶ mk g ∈ reach     (T2, unconditional)
gAbs_vanishingTwo_of_sep : depth-2 separation ⟶ GAbsVanishingTwo h            (the k = 2 vanishing)
gAbs_supply_four         : GAbsVanishingTwo h → GTowerKnobRealizable h → SqClassClearingSupply h 4
gAbs_markTransitivity_of_baseThree :
  GDecideBaseThree h → GJoinSeparationAll h → GTowerKnobRealizable h → SqLamMarkTransitivity h
```

with `B = commP (commP x₁ σ) x₁` and `C = commP (commP x₁ x₀) x₁` (`gAbsB`, `gAbsC`), the
two classes of `gDecide_sigma_not_mem`/`gDecide_x0_not_mem`.  At `h = 0` the separation is
vacuous, so `GAbsVanishingTwo 0` is a theorem outright (`gAbs_vanishingTwo_handleFree`).

Wave 77's costing is discharged: "the depth-3 re-cut needs, in addition, a class-four supply
witness".  The witness is `gAbs_supply_four`, produced by the absorption mechanism from the
separation input the route already carried.  The endgame is back to the wave-75 three-input
shape with the REFUTED input replaced by an OPEN one: `GJoinBase h` (false) is replaced by
`GDecideBaseThree h` (open, and wave 77 proved the `Q₁₆` witness says nothing against it).

## The mechanism, checked against the source

Labute p. 126, proof of Theorem 5: the level-`j` leftover is
`ε_j = Σ_{i≠2} aᵢ π^{j-1}ξᵢ + δ_{j-1}(τ)`, and `0 = Δᵢ(ε_j) = aᵢ π^j` kills every
coefficient, so the leftover is a move.  Campaign translation, all proved:

* **The coker basis.**  His coker classes are the towers `π^{j-1}ξᵢ` of the letters his
  inventory excludes at that stage; the committed inventory is row-restricted, so its
  depth-2 coker appears in the equivalent spelling `B, C` (triple brackets, equivalently the
  bracket squares by `gBase_residual_iff`; equivalently `σ⁴, x₀⁴` mod the full reach, wave
  77's display).  T1 (`gAbs_leftover_decomp`) is his `ε_j`-decomposition at `j = 2`: the
  wide chain re-runs wave 76's base argument with the two classes adjoined, the handle
  instances reduced through the Eichler bracket squares, which reach unconditionally
  (`gAbs_eich_bracketSq_mem`: the bundle at the admissible correction `U²`, his
  `w ∈ W ∩ F` generator; the pivot is a `σ,x₀`-word, so its `ℤ₂`-powers ride the closed
  test subgroup).
* **The diagonal reading.**  His Lemma 4(3), `Δᵢ(π^{j-1}ξ_k) = π^j δ_{ik}`, becomes: the
  corrected `σ`-row reads `B` as `2²·unit` and `C` as `0`; the corrected `x₀`-row reads `C`
  as `2²·unit` and `B` as `0` (`gAbs_delta_B_rowS`, `gAbs_delta_C_rowS`,
  `gAbs_delta_C_rowX`, `gAbs_delta_B_rowX`).  The two rows are the plain core rows with a
  handle correction `c(u_j-slot) = ν'(u_j)·Δ(w)` that zeroes every Eichler-cleared letter
  (`gAbs_delta_eichU/V`), his "crossed homomorphism vanishing on the other generators".
* **The moves are one bit deeper.**  The whole depth-2 reach reads `8`-divisibly at both
  corrected rows (`gAbs_reach_le_layerDvd_rowS/X`): knobs and bundles by wave 75's
  invisibility bounds, the Eichler towers by the correction (readings exactly zero), the
  `x̃₁`-tower because `χ(x̃₁) ≡ -1 (mod 8)` collapses the norm sum at exponent 4
  (`gAbs_xOne_tower_dvd`, in fact `16`-divisible).
* **The kill.**  A defect reads zero at every row (`gDeltaDefectVanishing`, wave 74's
  theorem).  Reading the normal form at the two corrected rows mod `8` forces
  `e₁ = e₂ = 0` (`gAbs_kill_mid`, `gAbs_kill_last`, `gAbs_zero_reader_reach`): his
  `0 = Δᵢ(ε_j) = aᵢπ^j` at the two coordinates.  The refuted layer statement is recovered
  exactly on the all-rows-zero elements, which is all the argument ever needed of it.

Theorem 3's other regime (no character pinned; leftover absorbed into `λ ∈ 4ℤ₂` exponents
of the generators, iterated to the limit) is not formalized here: the campaign is in the
pinned regime, and the brief's assignment of that half was contingency.

## The brief's caveat, resolved: the functionals DO see the two classes

The brief warned the coker classes might be invisible at the layer bit (readings
`8`-divisible), in which case a finer `mod 2^{j+1}` reading would be needed.  That is
false, and the wave-76 honesty marker it descends from is wrong:

* `w76-base-note.md` §4 marker: "`⁅x₁, x₀⁆` reads with `v₂ ≥ 2` (its far factor is
  `χ(x₀) − 1 = 4`), so its square reads `8`-divisibly, exactly like the knobs.  A
  wave-74-style functional refutation is therefore not available."  The computation took
  only the `Dx₁`-term of `gDelta_commP`.  The `Dx₀`-term is
  `χ(x₀)⁻¹(1 − χ(x₁)⁻¹)·Dx₀` with `v₂(1 − Y⁻¹) = 1` **exactly** (`Y − 1 = −(X² + 1)`,
  `gDelta_rootX_sq_add_one`), so at the `x₀`-row the bracket reads `2·unit` and the
  square/triple reads `2²·unit`: at the layer bit, visible.
* Consequence, formalized: `gAbs_B_notMem_reach`, `gAbs_C_notMem_reach` re-prove wave 77's
  two non-membership statements purely functionally, with no `Q₁₆` and **at every marking
  with no selection hypotheses** (wave 77's `gDecide_not_layerReach` needed the specific
  marking `gDecideNu h` for `h ≥ 1`).  The finite witness remains the stronger artifact in
  other directions (it kills the enlarged, admissibility-free inventory too); the
  functional route is the one that generalizes to the kill.

One more correction while auditing: wave 76 §4's inventory line "towers `ξ²(v)`, all of
`V^{[4]}` (this part of the note's §T2 is right)" was already corrected by wave 77 item 2;
this lane's `gAbs_eichU_four_mem` shows the committed set does contain the Eichler fourth
powers `U⁴, V⁴` as `2²`-divisible zpowers of cleared letters, so the committed tower set at
depth 2 is `x̃₁, U_j, V_j` exactly, as wave 77 stated.

## What is open, stated exactly

1. **`GDecideBaseThree h`** (the depth-3 base): `∀ ν'` selected, `GTowerLayerReach h ν' 3`.
   Open.  Wave 77 proved the depth-2 analogue false and its witness silent at depth 3; this
   lane makes it the sole layer-side input.  Note what this lane's method says about it:
   the depth-3 coker of the SAME mechanism would be the classes `ξ⁅x₁,σ⁆²`-style one level
   up, and the corrected rows read one bit deeper there too; a W79 lane could attempt
   either the direct discharge (wave 77's §T2 inventory: the port of
   `cfourCmp_zLayer_le_gens` to level 5 is the bulk) or the absorption at depth 3
   (normal form + kill again, avoiding the port's hardest part the same way).
2. **`GJoinSeparationAll h`** (wave 75 T3): unchanged, consumed at every depth `k ≥ 2`;
   only its depth-2 instance feeds the seed.  Vacuous at `h = 0`.
3. **`GTowerKnobRealizable h`** (wave 75 T4): unchanged, the extraction interface.
4. The per-class residual `SqClassClearingSupply h k` and
   `limFinal_markTransitivity_iff` are untouched, as always.

## What W79 needs

1. **The depth-3 base by absorption** (recommended): repeat T1+T2 one level up.  The
   ingredients that made depth 2 work all have depth-3 analogues in the tree
   (`gTower_decomp` is level-free, `gJoin_knob_dvd`/`gJoin_bundle_dvd` are depth-general,
   the corrected rows are depth-free); the new work is the level-5 analogue of
   `cfourCmp_zLayer_le_gens` and the `γ₃`-analogues of the `gThreeFour_*` identities.  If
   the depth-3 coker again lands in the functionals' sight, `GDecideBaseThree` follows and
   the residual reduces to separation + extraction outright.

   > ⚠⚠ **[W79-HOUSE, watch round 16, as of `527adf51`: the umbrella claim in that paragraph is
   > FALSE, and this item is the one a wave-79 lane is being asked to act on, so the correction
   > is recorded here rather than only in the house note.]**
   >
   > The three ingredients **named** all check out, individually: `gTower_decomp`
   > (`GradedUniformTower.lean:340`) is universally quantified in `k` with only `hk : 1 ≤ k`;
   > `gJoin_knob_dvd` (`GradedUniformJoin.lean:509`) and `gJoin_bundle_dvd` (`:523`) carry no
   > depth literal and at `k := 1` give the `2^4` bound depth 3 wants; and the corrected-row
   > *objects* (`gAbsRowS`, `gAbsRowX`, `gAbs_delta_eichU/V`, `gAbs_rowS_pivot`, ...) carry no
   > depth index.
   >
   > What is false is "**all**".  Every ingredient carrying **T2, the kill** is hardcoded at
   > depth 2 and has no depth-3 analogue anywhere in the tree.  Four of them:
   >
   > 1. `gAbs_reach_le_layerDvd` (`GradedAbsorption.lean:332`) and its two row instances
   >    (`:351`, `:355`) are stated at the literal `2` in both indices, and are the only three
   >    `gTowerReach _ ≤ gJoinLayerDvd _` statements in the tree.
   > 2. `gAbs_xOne_tower_dvd` (`:308`) **exports `2^3`, one bit too weak**.  Depth 3 uses
   >    exponent `2^3 * a` and `gJoinLayerDvd _ 3` demands `2^4`; instantiating the exported
   >    lemma at `a := 2*a` still gives only `2^3`.  The `2^4` **is** proved, but only as the
   >    internal `have hall` at `:311-326`, never exported.  `gJoin_delta_zpow` is no escape:
   >    it wants `chiSq h x = 1`, and `χ(x̃₁) ≡ -1 (mod 8)` (`gAbs_chi_xOne_add_one`, `:263`).
   >    **This is the one concrete blocker, and it is a ~15-line hoist, not a re-instantiation.**
   > 3. `gAbs_kill_mid` (`:1224`) / `gAbs_kill_last` (`:1246`) bake in `2^3 ∣ ·` and
   >    `2^2 * unit`; depth 3 needs `2^4` and `2^3 * unit`.  Same for `gAbs_unit_mul_dvd`
   >    (`:1202`) and `gAbs_four_unit_not_dvd` (`:1211`).
   > 4. The coker readings (`gAbs_delta_B_rowS` `:440`, `_B_rowX` `:449`, `_C_rowX` `:456`,
   >    `_C_rowS` `:465`) read the depth-2 elements `gAbsB`/`gAbsC` (`:376`, `:380`).  The
   >    depth-3 coker this note posits at line 116 has no reading lemma at all.
   >
   > So the "new work" list above covers only **T1's wide chain**.  T2 additionally needs a
   > depth-3 `gAbs_reach_le_layerDvd`, a `2^4`-strength `x̃₁`-tower lemma, depth-3 kill
   > arithmetic, and depth-3 coker readings.
   >
   > Two things are **better** than the paragraph says, and a lane should use them: the knob
   > half is already packaged depth-generally as `gJoin_knob_le_layerDvd`
   > (`GradedUniformJoin.lean:596`), which is what to reach for rather than the raw
   > `gJoin_knob_dvd`/`gJoin_bundle_dvd`; and the Eichler-tower half genuinely is depth-free
   > via `gJoin_zpow_vanish` (`:327`) from `gAbs_rowS_eichU/V` (`:232`-`:246`).
   >
   > Separately, ⚠ **line 72's "in fact `16`-divisible"** (and the module's own `:306`) is true
   > of the proof and **not** of the exported statement, which is `2^3`.  That is item 2 above,
   > seen from the note's side.
2. **Separation at depth 2** (`GJoinTowerSeparation h ν' 2` for `h ≥ 1`): wave 75 §7
   scoped it as ordered-product bookkeeping; it is now on the critical path twice over
   (the seed and the tower).
3. **The extraction** (`GTowerKnobRealizable`): the wave-73 multi-handle bookkeeping,
   unchanged, now the only interface between the vanishing and the supply.
