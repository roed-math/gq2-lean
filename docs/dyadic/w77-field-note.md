# W77-FIELD: the branch identification at the five quadratic model fields

Lane W77-FIELD, ticket `docs/dyadic/w74-critical-path.md` §3 item 1.  Produced against tree
`1d3d5a84`, shared cache at the wave-76 umbrella (4346 jobs).  Verification of record:
`scripts/mirror.sh` (sweep, gen, check).  **No `lake` command was run.**

One new module: `GQ2/Dyadic/Instances/FieldBranchIdentification.lean`, declaration prefix
`fieldId`.  Nothing else was touched.

---

## 1.  The headline

**The branch identification is closed at all five committed quadratic model fields, and closed
unconditionally at each: over the field's own marked reciprocity bundle and the standing profinite
instance binders, with nothing carried.**

| row | field | asked for | status |
| --- | --- | --- | --- |
| `sqrtNegTwo` | `ℚ₂(√−2)` | `range χ = imChiN 2` | already in tree (wave 67) |
| `sqrtTwo` | `ℚ₂(√2)` | `range χ = imChiM 3` | already in tree (wave 68) |
| `sqrtFive` | `ℚ₂(√5)` | `range χ = imChiM 2` | **`fieldId_hrange_sqrtFive`** |
| `sqrtTen` | `ℚ₂(√10)` | `range χ = imChiM 2` | **`fieldId_hrange_sqrtTen`** |
| `sqrtNegTen` | `ℚ₂(√−10)` | `range χ = imChiM 2` | **`fieldId_hrange_sqrtNegTen`** |

The memo priced this item as "the smallest genuinely-open item and it gates all five rows".  Two
corrections to that pricing follow.

## 2.  Correction 1: the item was already discharged on two of the five rows

The memo (produced at `4fff1592`) lists the branch identification as open, and
`GeneralAssembly.lean:542`'s `genAsm_evenRoute_output` docstring still says, in a committed
module, "⚠ What the route does **not** supply is the `alpha` pin ... and it stays open."  That
sentence and the memo's item A1 were **already partly false when written**:

* `EvenRangeModel.hrangeFinal_sqrtNegTwo` (`EvenRangeModelFields.lean:626`, wave 67) proves
  `range χ = imChiN 2` at `ℚ₂(√−2)` over the bundle alone;
* `EvenRangePolish.hrangeFinal_sqrtTwo'` (`EvenRangePolish.lean:271`, wave 68) proves
  `range χ = imChiM 3` at `ℚ₂(√2)` over the bundle alone.

Both are re-exported as `fieldId_hrange_sqrtNegTwo` / `fieldId_hrange_sqrtTwo` so the five rows
read in one place.  The genuinely open part of item A1 was the three `DM 2 0` rows only.

`GeneralAssembly.lean`'s sentence is now false outright and should be superseded at the merge, the
way `EvenRouteModel.lean` §4's "no statement in the tree computes the cyclotomic range at a named
field" was superseded at the wave-67 merge.  This lane, being new-files-only, did not edit it.

## 3.  Correction 2: the three open rows all want the same thing, and it is surjectivity

`Main.lean:216`-`220` puts `sqrtFive`, `sqrtTen` and `sqrtNegTen` all on `isProP_DM 2 0`.  So all
three ask for `imChiM 2`, and `imChiM 2 = ⊤` (a `2`-adic unit is `≡ ±1 mod 4` always).  The
content of the last three rows is therefore: **`χ_cyc` is surjective on `G_K(2)` at `ℚ₂(√5)`,
`ℚ₂(√10)` and `ℚ₂(√−10)`.**  That is the correct arithmetic statement, and it is true because
`K ∩ ℚ₂(μ_{2^∞}) = ℚ₂` at each: `5`, `10` and `−10` are square classes distinct from `−1`, `2`
and `−2`, the three classes inside the cyclotomic `2`-tower.

## 4.  The argument that landed, and why it is cheaper than the two committed ones

The committed classification (`evenRange_range_eq`) gives `range = imChiM α` or `imChiN α` with
`α ≥ 2`; wave 67's degree bound (`evenRangeF_imChi{M,N}_depth_le` at `e = m = 1`) caps `α` at `3`
on `M` and at `2` on `N`.  So **at a quadratic field the range is one of exactly three
subgroups**: `imChiN 2`, `imChiM 3`, `imChiM 2`.  Modulo `8` the first two are `{1, 3}` and
`{1, 7}`, so:

> **One cyclotomic value `≡ 5 (mod 8)` pins the range at `imChiM 2`.**
> (`fieldId_range_eq_imChiM_two_of_classify`)

This is one membership where wave 67's and wave 68's routes each needed two (`−1 ∈ range` plus
`5 ∉ range` on the `M` branch; `−1 ∉ range` on the `N` branch).

The value comes from the bundle: `χ_K(rec_K x) = N_{K/ℚ₂}(x)⁻¹` on the unit part, with
`χ(rec 2) = 1` at the uniformizer, so an element of norm `2^e · u` carries the value `u⁻¹`
(`fieldId_inv_mem_range_of_norm`).  Inverting is invisible modulo `8` (`5⁻¹ ≡ 5`).  The three
witnesses:

| field | `x` | `N(x)` | value | mod `8` |
| --- | --- | --- | --- | --- |
| `ℚ₂(√5)` | `1 + 2√5` | `−19` | `(−19)⁻¹` | `5` |
| `ℚ₂(√10)` | `2 + √10` | `−6 = 2 · (−3)` | `(−3)⁻¹` | `5` |
| `ℚ₂(√−10)` | `√−10` | `10 = 2 · 5` | `5⁻¹` | `5` |

### Two findings inside the argument

**(a) The uniformizer clause is load-bearing, not decoration.**  Wave 68's `ℚ₂(√2)` route used an
element of *unit* norm (`1 + √2`, norm `−1`).  No such element works at `ℚ₂(√10)` or `ℚ₂(√−10)`:
the unit norms there are exactly the units `≡ ±1 (mod 8)` (Hilbert symbol `(u, ±10)₂ =
(−1)^{ω(u)}`), all of which lie in `imChiM 3` and so exclude nothing.  The residue-`5` value at
those two fields necessarily comes from an element of **odd valuation**, and `χ(rec 2) = 1`
(`LocalReciprocity.chiCyc_recip_uniformizer`) is what converts its norm into a cyclotomic value.
The tree's earlier uses of that clause are at `⊥ = ℚ₂` (`MarkedRecipBundle.lean:949`) and inside
the `ℚ₂`-side assembly (`PropOneOneAssembly.lean:248`); this is its first use to produce a value
at a proper extension.  The Hilbert-symbol computation of the unit-norm group is a hand
computation used to motivate the choice of witness; **nothing in the Lean depends on it**, since
the witnesses are exhibited outright.

**(b) `ℚ₂(√5)` cannot use the ramified entry, and does not need to.**  It is the one unramified
row (`Fields.lean:243`, `q_K = 4`), and the tree's only ramification supplier
`Fields.not_hasEqualNormValueGroups_quadField` has the hypothesis `Odd a.valuation`, false at
`a = 5`; there is no `not_hasEqualNormValueGroups_KSqrtFive` in the tree.  So `evenRange_range_eq`
is unavailable there.  The *other* committed entry, `evenRange_range_eq_imChiM`, takes
`−1 ∈ range χ` instead of any ramification binder, and `N(2 + √5) = 4 − 5 = −1` supplies it from
the same bundle clause.  **The `ℚ₂(√5)` row costs one extra element, not one extra binder**, and
nothing is carried there either (`fieldId_range_eq_imChiM_two_of_negOne`).

## 5.  What landed, with names

**The identities** (`§5` of the module), each over `B : MarkedRecip R K` and the standing
instance binders:

* `fieldId_hrange_sqrtFive`, `fieldId_hrange_sqrtTen`, `fieldId_hrange_sqrtNegTen`.

**The oriented endpoints**, composing with `EvenParity.parityFinal_orientedEquivM_of_range`:

* `fieldId_orientedEquivM_sqrtFive`, `_sqrtTen`, `_sqrtNegTen`, each giving
  `Nonempty (OrientedContinuousMulEquiv (chiM 2 0) (chiCycKTwo (K := ...)))`.

**The producer composition** (`§6`, `§7`): the memo's §1.5 point is that the even route's output
*is* the `(f, horient)` pair the `KTwoM`/`KTwoN` producers consume, and
`GeneralAssembly.genAsm_branch_of_even{M,N}` already packages it.  Three of the remaining inputs
are discharged here:

* `hdeg`, per field;
* `hMix`, from `MarkedCore.mMixHypothesis` (unconditional at `α ≥ 2`);
* the marking triple `nuP`/`hnuP`/`hnuIota`.  The tree carried `SelectedCoreLeavesRN.nNuZtwo` for
  the `N` core and `LSquareCore.lNu` for the `L` core but **no `M` counterpart**;
  `fieldId_mNuZtwo` builds it (three lines: `nuM` through the `ztwoIota` seam, onto because
  `nuM(C₀) = 1`).

leaving `fieldId_genAsmBranch_{sqrtNegTwo,sqrtTwo,sqrtFive,sqrtTen,sqrtNegTen}`, each producing
`∃ G : GenAsmBranch K B, G.pres = ...` over **exactly one remaining clause**: `hpivot` on the four
`M` rows (`ν_ur` a unit at the image of `C₀`), `hpair` on the pilot (at the image of `σ` or `x₂`).

## 6.  Axiom pins

All recorded in the module's §8, printed beside the committed statements they inherit from.

* The **range identities** and everything under them: `propext, Classical.choice, Quot.sound`.
  So the branch identification costs no arithmetic axiom at any of the five fields.
* The **oriented endpoints**: the even route's endpoint set, standard three plus
  `hilbertSymbol_normCriterion_finiteDyadic`, `tateDualityAt`,
  `Foundations.absGalQ2_isTopologicallyFinitelyGenerated`,
  `Foundations.absGalQ2_localEulerCharacteristic`.  Exactly the set of
  `EvenParity.parityFinal_orientedEquivM_of_range`; nothing added.
* The **`M`-row branch data** additionally carry `peripheralCyclotomicAction`, from one place:
  `MarkedCore.mMixHypothesis`, whose own set is the standard three plus that axiom.  The pilot's
  `N` branch datum does not carry it (the `N` producer has no `hMix`).

No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.

## 7.  What this changes on the critical path, and what is next

Group **A** of the memo's closing set is now empty of open mathematics:

* **A1** (the branch identification per field) is closed at all five rows.
* **A2** (the `KTwoN`/`KTwoM` adapter) was already a restatement; §6/§7 perform it, and the
  reduction is per-row to one unimodularity clause.

**[W78-HOUSE, ticket 3(b): A1 confirmed; A2 is BYPASSED, not discharged, and §6/§7 do not
perform it.**  Checked against `w74-critical-path.md` §3's Group A and §1.5.

**A1: confirmed.**  All five `fieldId_hrange_*` are equalities over the field's own bundle and
the standing binders, and the range identities print std-3.  Nothing carried.

**A2: the record this lane produces is not one of the two A2 names.**  A2 is the adapter into
`Main.lean`'s record spellings, and §1.5's test is "until it is done the even route's output does
not typecheck into either record".  §6/§7 here produce `∃ G : GenAsmBranch K B`, and
`GenAsmBranch` is `GeneralAssembly.lean`'s record, introduced in **wave 76**; `GenAsmBranch`
occurs in exactly two files in the tree, `GeneralAssembly.lean` and this one.  `Main.lean:352`'s
`ResidualSqrtNegTwo` is untouched and still carries `fLab`, `piAb`, `hpiAb`, `hpiNu` and
`horient : ∀ x, chiCycKAb K (piAb (fLab x)) = chiN 2 0 x`, i.e. the abelianization spelling the
memo says the even route does **not** produce.  What performs the adapter into `KSupply` is
`KSupply.ofMarkedCoreRealization`, consumed by `genAsm_candidate_equiv_galK`
(`GeneralAssembly.lean`) and mapped field by field in that module's §4.2; both are wave 76's, not
this lane's.  This lane's §6/§7 *inhabit* that record, which is a different and also useful thing.

So the accurate sentence is: **Group A is empty of open mathematics on the general-record path.
On `Main.lean`'s committed path A2 is untouched, and the memo's own typecheck test still fails
there.**  Which of the two paths ships is an owner call.]**

The nearest remaining item this lane touched is therefore **not** classification at all.  It is:

1. **`hpivot`/`hpair`, the marked-data pair unimodularity**, one clause per row, at the *chosen*
   oriented equivalence.  This is arithmetic about `K` and the bundle (`ν_ur` a unit at a
   specific image), and the tree has a stronger route that avoids it altogether:
   `marked_matching_certificate_KTwo{M,N}_of_level_zero` (`LabuteInterface.lean:81`, `:123`)
   replaces both `hpivot` and `hMix` by `B.r = 0` plus a `MDecomposition`/`NDecomposition`.  A
   follow-up lane should check whether `B.r = 0` is provable at these five fields, in which case
   the last classification-side clause disappears too.  Note `genAsm_branch_of_even{M,N}` route
   through the *non*-level-zero producers, so this would need a new `GenAsmBranch` producer.
2. Groups **B** and **C** of the memo (the `G_K`-side counting pack, the candidate-side clause
   layer, the `nuP` construction ticket AS3-b) are untouched by this lane and remain as priced.
   In particular the memo's sharpest item, `hdet` / the LG5 ⇒ `GaussZResidueK` bridge, is
   unaffected.

## 8.  One docstring to supersede at the merge

`GQ2/Dyadic/GeneralAssembly.lean:542`, `genAsm_evenRoute_output`:

> "⚠ What the route does **not** supply is the `alpha` pin: it produces an existential
> `∃ alpha ≥ 2`, and the branch datum asks for the row.  That is the critical-path memo's item A1,
> the branch identification `range chiCycKTwo = imChiN alpha` per field, and it stays open."

False at every one of the five frozen quadratic rows as of this lane, and false at two of them
since wave 68.

**[W78-HOUSE, ticket 3(c): DONE.**  Superseded in place, comment-only, with the as-of-hash
convention: the sentence is kept (it states correctly what `parityFinal_evenClassification`
itself supplies) and the closing clause "and it stays open" is annotated as false as of
`e6bbd2b9`, naming the five suppliers, the two wave-67/68 ones and the three from this lane.
The docstring now says the pin is supplied elsewhere, per field.  One citation note: the quoted
sentence is at `:539-541`, not `:542`; `:542` is `theorem genAsm_evenRoute_output` itself, the
declaration the docstring sits on.  Both readings are the same at `1d3d5a84` and at `e6bbd2b9`,
so this is an off-by-one and not drift.]**
