# W79-EXTRACT lane note

Branch `claude/w79-extract`, based on `527adf51`.  One new module,
`GQ2/Dyadic/SqCore/GradedExtraction.lean` (prefix `gExt`), 756 lines, no `sorry`, no new
axiom, no `native_decide`, no heartbeat or recursion-depth bump.  Every declaration carries
a `#print axioms` line in the file's own pin section; all of them report
`[propext, Classical.choice, Quot.sound]`, except `gExt_ofFn_single`, which reports
`[propext, Quot.sound]`.

Verification of record: `scripts/mirror.sh sweep` at lane start, then
`scripts/mirror.sh gen GQ2.Dyadic.SqCore.GradedExtraction` after every edit.  Nothing in the
tree imports this module yet (registration in `GQ2.lean` is the orchestrator's, and a sibling
lane owns the housekeeping), so there is no dependent to re-check.

## Headline

**`GJoinSeparationAll h` is discharged, at every handle count and every depth.**  Wave 78's
repaired reduction took three inputs; it now takes two.

```
gExt_markTransitivity_of_baseThree :
  GDecideBaseThree h -> GTowerKnobRealizable h -> SqLamMarkTransitivity h
```

The third input, `GTowerKnobRealizable h`, is not discharged.  What this lane adds towards it
is the multi-slot dressing composition (wave 74's item (i), unconditional and `h`-uniform) and
a precise account of why wave 74's item (ii) does not close the interface **as stated**.  See
"T2" below; that account is the sharpest thing this lane found and it is what W80 should act
on.

## T1: the separation, proved

`gExt_towerSeparation : GJoinTowerSeparation h nu' k` at **every** `h`, **every** marking and
**every** `k` (no `2 <= k` needed, though the consumer only uses `k >= 2`), and
`gExt_separationAll (h : ℕ) : GJoinSeparationAll h`.

Wave 75 had this at `h = 0` only (`gJoin_towerSeparation_handleFree`, vacuously), and scoped
two routes.  This lane took the first, the ordered `List.ofFn` product in `Q_{k+2}`.  The
cheap route the ticket asked to check first (the w77/w78 corrected-row functionals separating
the towers outright, making the normal form unnecessary) does **not** exist: the readings
`gJoin_rowU_eichU` and friends separate the *generators*, but `GJoinTowerSeparation` is a
statement about the *span*, and a hypothesis about the readings of an element of the span says
nothing until the element has been written in terms of the generators.  The normal form is the
statement, not an implementation detail of it.

The chain, in file order:

* `gExt_ofFn_center`, `gExt_ofFn_mul`, `gExt_ofFn_mul'`, `gExt_ofFn_single` (arbitrary group):
  an ordered `List.ofFn` product of central factors is central; two such products of the same
  length multiply slotwise when either family is central; a product all but one of whose
  factors is trivial is that factor.  This is the whole of wave 75's "friction is that the
  layer sits inside a non-commutative quotient".
* `gExtWordU/V/gExtWord`: the words `prod_j U_j^{2^k f_j} · prod_j V_j^{2^k g_j}` at
  `Z_2`-exponent vectors.
* `gExt_delta_prod`: `gDelta` is additive along a list of `chi`-trivial factors (the crossed
  term of `gDelta_mul` carries `chi_sq`, which is `1` on the cleared handle letters and hence
  on their towers, `gJoin_chiSq_zpow`).  Hence `gExt_rowU_word`/`gExt_rowV_word`: the
  `u_{j0}`-row of a word reads `2^k f_{j0}` and the `v_{j0}`-row reads `2^k g_{j0}`, on the
  nose.
* `gExtSpan` and `gExt_mem_span`: the words form a subgroup of `Q_{k+2}` (the tower classes
  are central, being images of `gamma_{k+1}`-elements, so §1 applies), and it contains the
  generators as single-slot words, so the whole span consists of words.
* `gExt_towerSeparation`: rows `2^{k+1}`-divisible forces every exponent even
  (`gExt_even_of_dvd`), an even exponent puts each tower in `gamma_{k+2}`
  (`gExt_wordU_mem_of_even`), and the class is trivial.

No vacuity: `gJoin_eichU_tower_notMem` (wave 75) puts an odd-exponent handle tower outside the
layer kernel, so the hypothesis of `GJoinTowerSeparation` has content at every `h >= 1`.

## T3, in the form the lane could reach

`gExt_defectVanishing_of_baseThree`, `gExt_supply_of_baseThree`,
`gExt_markTransitivity_of_baseThree`: wave 78's three-input reduction with the middle input
removed.  The full collapse the ticket asked for (`GDecideBaseThree h -> SqLamMarkTransitivity h`)
needs T2, which did not land.

## T2: what landed, and where it stopped

Wave 74's engine note lists two missing pieces for the extraction
(`docs/dyadic/w74-engine-note.md`, "Where wave 73's `h >= 2` flag actually lives"):
(i) the multi-slot composition across all `2h + 3` slots, and (ii) the far-slot change of
basis from the letters to the accumulated frame values.

### (i) landed, unconditionally

* `gExt_comm_dress`: dressing both letters of one handle by corrections one layer down moves
  that handle's bracket by the two knobs, the cross term dying in
  `[gamma_k, gamma_k] <= [gamma_2, gamma_k] <= gamma_{k+2}`.
* `gExt_handleWord_dress` (arbitrary group): the handle word moves by the ordered product of
  the per-handle knobs.
* `gExt_dress_handles`: the `2h` handle slots dressed at once, with the core held fixed.  This
  is the multi-handle composition lemma wave 73 flagged and wave 74 queued.
* `gExt_dress_full`: the whole frame dressed at once, core plus handles.  The two blocks
  compose with **no** cross-term bookkeeping, because the core move
  (`gTower_dress_core`) reads only `m 0, m 1, m 2` while the handle block leaves those alone,
  and the handle move reads only the handle values while the core block leaves those alone.
* `gExtMove`, `gExt_dress_move`, `gExt_frame_move`: the move named, and the dressing identity
  stated at `sqArbFrame` in the vocabulary of `GTowerKnobRealizable`.  What an extraction has
  to produce is an admissible `d` whose move inverts the defect; `gExt_frame_move` is that
  reduction, and it is where the next lane should start.

### (ii) does not close the interface as stated

Write `V = D_sq h / gamma_2` for the Frattini quotient, an `F_2`-space of dimension
`sqRank h = 3 + 2h` with basis the letter classes `e_sigma, e_{x_0}, e_{x_1}, e_{u_j},
e_{v_j}`.  For an admissible `t` (a `gamma_k`-element, both rows trivial) the bracket class
`q |-> [t, q]` in `Q_{k+2}` kills `gamma_2` (`gTower_commP_vanish`), so it factors through `V`
and is `F_2`-linear; write it `beta_t`.  Then, with `m` the current frame values:

* the knob span is generated by `beta_t(W)` for the hyperplane `W = span{e_l : l /= x_1}`
  (that is `gTowerFar` mod `gamma_2`), together with the bundles `t^2 + beta_t(e_{x_1})`;
* the move span, by `gExt_dress_full`, is generated by `beta_c(m_l)` for `l /= 2` together
  with the bundles `c^2 + beta_c(m_2)`.  (The slot-to-partner pairing is a bijection of the
  non-`x_1` slots: slot 0 pairs with `m 1`, slot 1 with `m 0`, slot `u_j` with `m (v_j)`, slot
  `v_j` with `m (u_j)`.  Orientation costs nothing, since `[a,b]^{-1} = [b,a]` exactly and the
  layer has exponent two.)

`SqModTwoIndep` says the `m_l` topologically generate, hence their classes are a **basis** of
`V`; it does **not** say the basis is triangular against the letters.  If some far letter
`e_l` has a nonzero `m_2`-coordinate in that basis, then `beta_t(e_l)` needs `beta_t(m_2)`,
which the moves supply only bundled with `t^2`, and `t^2` alone is a *tower* class, exactly
the thing the moves do not produce.  So the knob span is not contained in the move span for a
general frame.

The hypotheses of `GTowerKnobRealizable` do not exclude such a frame.  Row-triviality does not
exclude an `x_1`-component in a dressing: the cleared letter `x_1~ = x_1 x_0^{-2}` is exactly
row-trivial (`gTower_xOne_nuLam`, `gTower_xOne_nu`) and its Frattini class is `e_{x_1}`, so
`a_0 = x_1~` is an admissible dressing whose frame slot `m 0 = sigma · x_1~` sits off the
hyperplane `W`.  **This is not a refutation**: nothing here shows that such a frame satisfies
the interface's remaining hypothesis (relator in `gamma_{k+1}`), and nothing here shows the
defect of such a frame is unrealizable.  What it shows is that the route of the engine note
does not prove the interface **as quantified**, and that no amount of composition bookkeeping
will repair that.

### What repairs it, and it is cheap

The frames the recursion actually produces are `x_1`-free mod `gamma_2`:

* the class-3 witness dresses with `bridgeTuple` (`GradedBridge.lean`), whose only nontrivial
  entries are `bridgeDress = u_j^{nu'(v_j)} v_j^{nu'(u_j)} w^{-2 nu'nu'}`, a product of handle
  letters and the pivot, with no `x_1`;
* every later correction is a `gamma_k`-element with `k >= 2`, hence lies in `gamma_2` and is
  invisible to every `beta_t`.

With `x_1`-freeness of the dressing, the `2 + 2h` classes `m_l` (`l /= 2`) are independent and
lie in `W`, which has dimension `2 + 2h`, so they **span** `W` exactly, the change of basis is
triangular, and both halves match: the far brackets come from the non-`x_1` slots and the
bundle at slot 2 matches the knob set's bundle modulo far brackets.  The route closes.

So the W80 shape is: carry an `x_1`-freeness clause on the dressing through
`SqClassClearingSupply` (it is preserved by `gTower_clear_step`, whose correction is a
`gamma_k`-element, and it holds at the class-3 base), weaken `GTowerKnobRealizable` by that
clause, and then run the extraction on `gExt_frame_move` with the four slot families.  The
remaining Lean work after that is the homomorphy of `gExtMove` in the correction tuple (each
slot separately: `cfour_commP_mul_left/right` with the correction term killed by
`cfive_commP_zLayer_left`, and `cfour_sq_mul` with `[gamma_k, gamma_k]` killed for the
bundle), which makes the move set a subgroup, plus the far-slot reduction
(`gTower_commHom_span` restricted to `gTowerFar`).

## Honesty markers

* T1 is a theorem, unconditional, at every `h` and `k`.  `gExt_separationAll` is not
  conditional on anything and its pins are in the file.
* T2 (i) is a theorem, unconditional.  T2 (ii) is **not** a theorem and **not** a refutation:
  it is an analysis of the interface's quantifier, supported by one explicit admissible
  dressing (`x_1~` at slot 0) that breaks the triangularity the route needs.  The claim
  "`GTowerKnobRealizable h` is false" is *not* made anywhere and is not supported.
* The dimension count in "what repairs it" is an argument on paper, not a Lean proof.  The
  `x_1`-freeness of `bridgeDress` is read off its definition
  (`GradedBridge.lean:340`); the claim that it has "unipotent mod-2 letter matrix" is wave
  74's, not re-derived here, and it is not needed for the dimension count above.
* Nothing in this lane touches the depth-3 base `GDecideBaseThree h`, which remains the other
  open input.
