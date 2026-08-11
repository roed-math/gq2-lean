# W64-PSI4: the four gap markings, closed, and the parity line refuted at all four

**Verdict: PROVED, on route 1 (closed form).**  W63-FOUR's remaining identity is discharged,
the four conditional forcing theorems become unconditional, and the refutation of the parity
line at the same four markings comes with it.  Wave 61's strictness measurement is now a
theorem in both halves.

Everything is in `GQ2/Dyadic/SqCore/GradedStageFourClosed.lean` and `scripts/w64_psi4/`.
`GradedStageFour.lean` is untouched.

## 1  What was left, and what it cost

W63-FOUR proved the exact lattice bound at all four markings and reduced the forcing to

> `psiOne (gaThreeShift h (gapOneMark h j) z) = 0` for every `z` all of whose slots lie in
> `gapKOne`, and the `psiTwo` analogue at `gap-2`.

Its section 4 offered two routes.  Route 1 (closed form) went through with no surprises and is
what landed; route 2 (generators, via `gaThreeShift_mul` and `Finset.univ_prod_mulSingle`) was
not attempted, because route 1 finished in one pass.  The cost was three steps, of which only
the middle one is about the markings:

1. **the block terms die, at every marking.**  `gaThreeShiftO` carries two central collection
   terms, each a frame quantity times a Frobenius weight `-4 x + 2 y`.  Both certificates read
   the class-five row multiplied by `4`, and `4 * (-4 x + 2 y) = 8 * (-2 x + y)` vanishes over
   `Z/8`.  `psiOne_gaThreeShift` and `psiTwo_gaThreeShift` state the consequence at ANY marking
   and any handle count: the certificate never sees the handle block's class-two rows.
2. **the dead handles die, at every `fiveTuple` marking.**  `gaThreeHandle 1 1 z w = 1`
   (`gaThreeHandle_one_one`), over any commutative ring, so `handleShiftSum` collapses the
   handle sums to their single live term.  Neither step reads a letter.
3. **the rest is `Z/8`-linear in the thirty dressing coordinates**, and the target is by
   construction the joint kernel of the five slot pullbacks of the certificate.  So the identity
   is an exact combination of the target's own defining conditions:

   | marking | slot | pullback | combination |
   |---|---|---|---|
   | `gap-1` | `sigma` | `0` | - |
   | `gap-1` | `x0` | `6k + 4m + 4n` | `3 * (2k + 4m + 4n)` |
   | `gap-1` | `x1` | `2l + 4n` | `2l + 4n` |
   | `gap-1` | `U` | `6k + 2l + 4m` | `3 * (2k + 4m + 4n) + (2l + 4n)` |
   | `gap-1` | `V` | `0` | - |
   | `gap-2` | `sigma` | `0` | - |
   | `gap-2` | `x0` | `5k + 4n` | `5 * (k + 4n)` |
   | `gap-2` | `x1` | `2m` | `2m` |
   | `gap-2` | `U` | `4l` | `4l` |
   | `gap-2` | `V` | `6k + 4l` | `6 * (k + 4n) + 4l` |

   The pullbacks are exactly the ones `scripts/w63_four/results/certify.txt` measured.

⚠ **`ring` does not close it**, as W63-FOUR predicted: `ring` normalises numerals as integers
and does not reduce them modulo `8`.  The closer is `linear_combination` against the conditions
above plus `W * gr8c` with `gr8c : (8 : gr3R) = 0` and `W` the explicit integer form
`(LHS - combination) / 8`, `13` non-zero coefficients at `gap-1` and `9` at `gap-2`.
`scripts/w64_psi4/derive.py` computes `W` by reimplementing `gaThreeCore`, `gaThreeCorr`,
`gaThreePair` and `gaThreeHandle` over the integers, reading the letters, the targets and the
certificates OUT OF the Lean source, and cross-checks the resulting form, all `30` coefficients
at each of the four markings, against wave 61's `sharp4lib.slot_matrix`.

## 2  The second half: the parity line really does fail

Wave 61's diagram has three implications, and it proved the strictness of the first two and
measured the strictness of the third at exactly these four markings.  That last one is now a
theorem: `not_stageOrth_gapOneMark` and its three siblings, at every handle count and every
handle, and `gapOneA_gap` and its siblings package admissibility, the forcing and the parity
failure together.

The refuting dressings are the markings' own arithmetic, which is what makes achievability free:

* `gapOneW = ⁅⁅sigma, V⁆, V⁆ = <k=4, l=6, m=1, n=1, o=6>`, carried on the live handle's
  `U`-slot, moves the class-five row by `7` and the second class-four row by `2`;
* `gapTwoW = ⁅⁅sigma, V⁆, sigma⁆ = <k=4, m=4, n=5, o=4>`, carried on the `x0`-slot, moves the
  class-five row by `5` and the first class-four row by `4`.

Both are weight-three brackets of two letters of their marking, so membership in
`forceLcs (closure (range m)) 2` is three applications of
`Subgroup.commutator_mem_commutator`.  The class-four movement is the whole phenomenon: these
dressings pair oddly and still kill nothing, which is precisely why the parity line is not the
sharp line.

The closed forms `gaThreeShiftO_fiveTuple_handleU` and `gaThreeShiftO_fiveTuple_x0` are what
make the computation a numeral: with the other four slots undressed, the core term, the dead
handles and both block terms all vanish, so the whole class-five row is one `gaThreeHandle` or
one `gaThreeCore`.  The `x0` version additionally needs the dressing's own class-three rows to
vanish, which `gapTwoW` satisfies.

## 3  ⚠ A convention gap in W63-FOUR's certification, found and closed

`scripts/w63_four/certify.py` runs its `216` weight-three bracket census with
`u6mat.commP`, which is the **paper** convention `[x, y] = x⁻¹ y⁻¹ x y`.  The Lean file's
`gapOneABr`, the generator reduction `le_of_gens_three` and everything downstream use **mathlib's**
`⁅x, y⁆ = x y x⁻¹ y⁻¹`.  These are different families of elements, so W63's census was not a
check of the arithmetic input that its own `decide` closes.

Both statements are true.  `scripts/w64_psi4/close.py` part D re-runs the census in the mathlib
convention at all four markings: `0` violations of `864`.  So the finding costs nothing, but it
would have cost a wave if the two families had disagreed, and it did cost this lane one
compile: the first attempt asserted the `gap-1` odd dressing pairs to `3`, which is its value in
the paper convention, and `decide` correctly refuted it.  The mathlib value is `7`.

⚠ **For the next wave**: any script that certifies a bracket claim of a Lean file has to use
mathlib's convention.  `certify.py`'s claim survives, but the check it printed was not the check
it advertised.

## 4  Honesty

* The four **forcing** statements and the four **parity failures** are proved, unconditionally,
  at every handle count and every handle.
* **Not proved here, and not claimed**: that the sharp line `StageCentral` holds at the four
  (measured in `certify.txt`; it follows from `stageForces_iff_stageCentral` at an admissible
  marking, but that composition is not carried out in this file); that these are the ONLY four
  such markings among wave 61's 1650 (measured in `sweep_sharp4.txt`); and the honest lattice
  cardinalities `1024` and `256`, against which the Lean targets keep index-`16` slack.
  Nothing in the Lean file says the targets are the lattices.
* **Doctrine rule 3.**  The four theorems discharged here are conditional, so a subtly wrong
  identity would have promoted four conditional theorems into false unconditional ones.  Three
  independent checks: Lean's own elaboration of `stageForces_gapOneA_of_psi psiOne_gapOneMark`,
  which only succeeds if the statements agree; a textual comparison of the four `hpsi` binders
  against the four proved statements, re-assembled as Pi-types (`close.py` part A, `9` checks);
  and an independent re-derivation of the CONCLUSION on the honest `6 x 6` matrices, with no
  Lean formula consulted (`close.py` part C, `12` checks).  All agree.
* The identity is verified beyond the exhaustive single-slot sweep W63 ran: `close.py` part B
  evaluates the certificate on `4000` genuine five-slot tuples drawn from the target at each
  marking, through the honest relator computation rather than through the linearised slot
  matrices, `0` failures.

## 5  What the next wave should do

1. **Compose the four with `stageForces_iff_stageCentral`** to get `StageCentral` at the four as
   a theorem, closing the last measured entry of wave 61's table.
2. **Decide whether the four are the only four.**  The census is a measurement over 1650
   markings; the four are now proved, but "exactly four" is not.  A Lean statement would need a
   finite classification, which the tree does not have.
3. **`le_of_gens_three` deserves the generalisation `w64-verify` is doing.**  This lane consumed
   it as it stands, as instructed, and it was the whole reason route 1 was cheap.
4. **Audit the tree's other certification scripts for the bracket convention gap in section 3.**
   `scripts/w62_separate/` and `scripts/w61_sharp4/` both compute brackets with `commP`; where
   they certify a Lean `decide` about `⁅·, ·⁆`, the check is off by a convention.
