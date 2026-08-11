# W66-PARITY: the even route's last statement, discharged

Wave 66, Opus lane, against `01b1b426`.  Working tree `claude/w66-parity`.  The ticket was the
campaign's number-one item: `EvenFamParitySupply`, the even route's single remaining statement
after wave 65, at the three model fields.

New modules: `GQ2/Dyadic/Instances/EvenParityKummer.lean` (307 lines) and
`GQ2/Dyadic/Instances/EvenParityModel.lean` (349 lines).  No committed file was edited.

## Verdict, in one sentence

`EvenFamParitySupply` is **a theorem at every field of even degree over `Q_2`**, at every level
`k >= 3`, for every stage tuple of every even word datum, on both branches, at the odd route's
own axiom set element for element; consequently `Hfam` is a theorem at every even-degree field,
the even oriented equivalence follows from the cyclotomic range identity and the degree with no
supply, and the **even classification holds at every even-degree field with `K(i)/K` ramified
over a marked reciprocity bundle**, in particular at `Q_2(sqrt -2)` and at `Q_2(sqrt 2)`, the
first even fields the campaign has closed.

## 1. Route taken, and why the memo's quarry was the wrong one

Route A, but not at the model fields: generically, at every even-degree field at once.

Wave 65's successor note pointed at `FiniteTwoLocalReciprocityHigherKummer*` and observed that
nothing there is in the required binder shape.  That was correct and it was the wrong quarry.
The right quarry was the **odd route's own parity proof**,
`GammaLSylowPreimageFieldLabuteStageKummerParity.lean`, whose every step is agnostic to the
degree parity.  It closes a numerical gap:

* the committed Demushkin count `|H^1(G_K(2), F_2)| = 2^([K : Q_2] + 2)`
  (`card_H1_zmodTwo_maxProTwoGalK`, no degree hypothesis, no parity hypothesis); against
* the odd core rank `sqRank h = 3 + 2h`, which at odd degree `2h + 1` is `[K : Q_2] + 2`.

The even bookkeeping closes the *same* gap on the complementary parity: `coreRank h = 4 + 2h`,
and at even degree `[K : Q_2] = 2 + 2h` that is again `[K : Q_2] + 2`.  So the pigeonhole runs
verbatim: evaluation of the mod-2 character group of `G_K(2)` at the exact-fibre lifts of a
stage tuple is injective (a character kills the second two-central term, hence `lambda_k` for
`k >= 2`, and the tuple's generators generate the level), between two sets of the same finite
cardinality, hence bijective.  Every Kronecker pattern on the lifts is realized by a character.
Mod-2 Kummer surjectivity (`kummerClassK_surjective`, committed) turns that character into an
`a` in `K^x`, and the committed chi-twisted higher Kummer cocycle of `a` at a `2^(k+1)`-th root
of unity has exactly the prescribed parities at the lifts.

Nothing in this wave is new arithmetic.  What was missing for twelve waves was the observation
that the even rank bookkeeping and the odd rank bookkeeping close the same numerical gap.

## 2. What landed (`EvenParityKummer.lean`)

* `evenParity_exists_lifts`: exact-fibre lifts of a generic stage tuple, from the tuple's own
  `rows` field.  Generic in the ambient group.
* `evenParity_card_characters (h) (hev : finrank = 2 + 2h)`: the even character count.
* `evenParity_characters_ext (hk : 3 <= k) (T) (hlvl)`: characters are determined at the lifts.
  Generic in the word datum, the value table, and the orientation character.
* `evenParity_exists_dual_character (hev) (hk) (T) (hlvl) (i0)`: the Kronecker dual character.
* **`evenParity_paritySupply_of_finrank (hev : finrank = 2 + 2h) (hk : 3 <= k) (T) :
  EvenFamParitySupply T`**, generic in `W` and `v`, so both branches at once.  The ticket.
* `evenParity_paritySupply_evenDegree`: the same on `Even (finrank)` with `h = (n - 2)/2`.

The proof is uniform enough that it also discharges the twisted slot `i0 = 1`, which
`EvenFamParitySupply` does not ask for.

## 3. What landed (`EvenParityModel.lean`)

* **`evenParity_hfam{N,M}_of_finrank (halpha : 1 <= alpha) (hev : finrank = 2 + 2h)`**: `Hfam`
  at every even-degree field, both branches, every level, every tuple.  No range identity, no
  ramification binder, no reciprocity bundle.  By wave 65 this is the strongest possible form,
  since `Hfam` at a field *is* the even classification there.
* **`parityFinal_orientedEquiv{N,M}_of_range (halpha : 2 <= alpha) (hrange) (hev)`**: the even
  oriented equivalence at a field from the range identity and the degree.  No supply.
* **`parityFinal_evenClassification (B : MarkedRecip R K) (deltaI) (hdeltaI) (hram) (hev)`**:
  `exists alpha, 2 <= alpha and (Nonempty (OrientedContinuousMulEquiv (chiM alpha h) chiCyc) or
  Nonempty (OrientedContinuousMulEquiv (chiN alpha h) chiCyc))`.  The even classification.
* `parityFinal_evenClassification_evenDegree`: the same on `Even (finrank)`.
* `parityFinal_classification_sqrtNegTwo (B)` and `parityFinal_classification_sqrtTwo (B)`: the
  classification at the two quadratic model fields, over the bundle and the standing instance
  binders and nothing else.  The ramification binder is discharged by the committed
  `not_hasEqualNormValueGroups_KSqrtNegTwo` and `..._KSqrtTwo`.
* `parityFinal_orientedEquivN_sqrtNegTwo (hrange = imChiN 2)`,
  `parityFinal_orientedEquivM_sqrtTwo (hrange = imChiM 3)`,
  `parityFinal_orientedEquivN_quartic (hrange = imChiN 3)`: the branch-pinned endpoints at the
  three model fields at the depths wave 56 measured, each over `hrange` and nothing else.
* `parityFinal_carried{N,M}_of_range` and `parityFinal_carried_evenClassification`: the wave-58
  artefacts `EvenRouteFinalCarried{N,M}`, now carried.

The bundle `B` is parametrized, not instantiated, so no lane statement carries `markedRecipAt`.
That is the odd route's own convention (`nonempty_orientedEquiv_oddDegree_of_bracketSquare`).

## 4. The exact residual now

Not cocycles.  Two things remain, both about `chi_cyc` and neither about the even route's
machinery:

1. **The branch label and the depth value.**  `parityFinal_evenClassification` delivers
   `exists alpha >= 2` and a disjunction of the two branches.  Pinning *which* branch and
   *which* `alpha` at a named field is `hrange`, which is local class field theory at that
   field; the campaign has always measured it (wave-56 census, `scripts/w57_model/`) and no
   statement in the tree computes it.  Every lane statement whose conclusion names a specific
   `alpha` and branch carries `hrange` honestly.
2. **Even fields with `K(i)/K` unramified.**  The committed range identity
   `evenRange_range_eq` needs `hram`, so those fields are outside §3.  `Hfam` and the parity
   supply hold there regardless (§1 and `EvenParityKummer.lean` carry no ramification binder),
   so for such a field only the range identity is missing, not the route.

The wave-65 memo's sentence that the even route's remaining content is the even classification
itself remains true, and is now the reason the wave closes: proving the supply proved the
classification.

## 5. Axiom discipline

Seven pins in `EvenParityKummer.lean` (six lane names and the odd analogue) and eighteen in
`EvenParityModel.lean` (fourteen lane names and four committed endpoints), all printed in real
runs against a full-mirror link of every build artifact.

* `evenParity_paritySupply_of_finrank` prints
  `[propext, Classical.choice, tateDualityAt, Quot.sound,
  Foundations.absGalQ2_localEulerCharacteristic]`, which is **element for element** the print of
  the committed odd analogue `sqStageTwistedCocycleParitySupply_of_finrank`, run side by side in
  the same elaboration.
* every lane endpoint (`parityFinal_*`) prints the seven-element committed even endpoint set,
  element for element identical to `evenRouteFinal_orientedEquiv{N,M}_atDepth` and
  `hfamFinal_carriedN_iff_orientedEquiv`, run side by side.
* `evenRange_range_eq`, the range identity, is std-3.
* No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `markedRecipAt`.

## 6. What a successor wave should do

1. **Register the two modules in `GQ2.lean`** (after `EvenFamilyStatus` and
   `EvenCyclotomicRange`).  This lane may not edit `GQ2.lean`; verification of record was the
   full-mirror harness.
2. **`hrange` at a named even field.**  This is now the whole even route.  It is local class
   field theory: compute the image of the cyclotomic character on `G_K(2)` at `Q_2(sqrt -2)`.
   The wave-56 census measured it; turning the measurement into a theorem is the ticket.
3. **The unramified-`K(i)` even fields**, if the campaign wants the even classification without
   the `hram` binder: extend `evenRange_range_eq`, not anything in the even route proper.
4. **Re-audit the odd route for the same trick.**  This wave found a twelve-wave gap closed by
   noticing that a committed odd-route theorem was degree-parity-agnostic.  Other odd-route
   arguments may be equally generic; the ones in `StageKummerParity.lean` were.
