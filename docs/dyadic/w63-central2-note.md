# W63: the `gamma_2` centrality line, and the kill that closes the widening

**Wave W63, worker W63-CENTRAL2 (lead lane).**  Lean:
`GQ2/Dyadic/SqCore/GradedGammaTwoCentral.lean` (committed, 47 prints, all std-3 or a subset,
zero sorries, no new axiom, no `native_decide`).  Off-Lean: `scripts/w63_central2/` (plain
Python, exact integer arithmetic on the honest `6 x 6` engine of
`scripts/w59_force5/u6mat.py`).  Settles the question `GradedStageFrame` recorded as open and
wave 62 left conditional.

---

## 0.  Headline

| question | answer |
|---|---|
| does wave 62's conditional widening become unconditional when restated on centrality? | **No, and not by any restatement.**  At wave 60's own binder point the conclusion is FALSE: an achievable `gamma_2`-dressing KILLS the dressed frame. |
| what is the killing dressing? | ⭐⭐⭐ `gaTwoCenKill = <m = 3>` on the **sigma slot**, `1` on every other slot.  `sqRelWord_stageWit_cenKill`, at every handle count and every handle. |
| is it achievable? | **Yes**, and by an explicit certificate: `commP (sigma x0)^{-1} u_j ^ 2 * commP x1 (x0 u_j)`, a product of two honest commutators of the point's own letters (`gaTwoCenKill_comm_form`, `cenSigDress_cenKill_mem`). |
| does anything committed break? | **No.**  The killer is not achievable at stage four: `GradedFiveStageFour.forceLcs_two_le_stageN3` forces an EVEN class-four coordinate and this one is `3` (`gaTwoCenKill_not_stageFour_achievable`).  Wave 60's and wave 62's theorems both stand verbatim. |
| what is the mechanism? | ⭐ `gaThreePair z L` pairs a sigma-slot dressing's class-four coordinate against `L.e`, and wave 60's point needs `stageX.e = 5` ODD - that is the channel its own residue runs on.  A unit coefficient on a coordinate the wider lattice leaves free reaches every residue including `0`. |
| does the centrality line buy anything? | **Yes, two things.**  `gaTwoForces_of_gaTwoCentral` transposes wave 61's sufficient half one filtration step wider, so the refutation propagates through it; and `gaTwoCentral_iff_chan` identifies the line exactly - it is wave 62's channel condition asked of the central tuples only. |
| does the `ZMod 8` mechanism of wave 62's separation lane reproduce? | **Yes**, at four coordinates instead of three (`gaTwoCentral_x1_f_even` and siblings) - and ⚠ it is silent at this point, because every letter there has `L.j = 0`. |

---

## 1.  The three lines, one filtration step wider

`GradedStageNecessity` names three properties of a marking at stage four.  Their `gamma_2`
transpositions are

```
   GaTwoForces   every achievable gamma_2-dressing that kills leaves an even residue
   GaTwoOrth     every achievable gamma_2-dressing moves the class-five row evenly
   GaTwoCentral  every achievable gamma_2-dressing acting CENTRALLY does
```

with `forceLcs H 2` replaced by `forceLcs H 1` and `gaThreeShift` by `SqU6.gaTwoShift`.  Two of
wave 61's three implications transpose without cost:

```
   GaTwoOrth  =>  GaTwoCentral  =>  GaTwoForces
```

the first free (a central shift's class-five row IS its translation amount) and the second at
any marking whose relator is a central translation, on the strength of
`SqU6.sqRelWord_gaTwoDress` alone.

**The third does not transpose, and this is worth recording.**  Wave 61's
`stageCentral_of_stageForces` runs a POWER argument: a central shift with an odd class-five row
is a unit in `ZMod 8`, so a power of the dressing hits the residue exactly and kills.  That
argument needs `gaThreeShift_pow`, and one filtration step wider there is no such lemma: the
`gamma_2` shift is **not** a homomorphism of the dressing tuple.  Measured
(`results/derive.txt` section 7): multiplicativity fails at 192 of 200 random achievable
five-slot pairs, and at 77 to 185 of 200 per slot.  The reason is structural - the shift reads
the letters' class-two and class-three columns, which a `gamma_2`-dressing MOVES, where a
`gamma_3`-dressing does not.  So no `gamma_2` characterisation is claimed, only the sufficient
half.

## 2.  Centrality is the channel condition, restricted

`gaTwoCentral_iff_chan`: inside the family where wave 61's transport applies (every letter in
`stageN1`), `GaTwoCentral m` says exactly that every achievable dressing acting centrally has
an even three-channel functional.  This settles the lane's second question in the sharpest
form.  Centrality does not escape wave 62's collision - the collision is about the functional,
and centrality asks about the same functional - it only shrinks the set of dressings the
condition is asked of.  What that buys is genuine but limited: at wave 60's point the two lines
are separated, because wave 62's own odd-channel witness `[x0, x1]` on the `x1` slot moves two
lower rows and is not central (`stageWit_gaTwoSlotTwo_not_central`; the dressed relator is
`<j = 4, l = 6, o = 6>`).  So the refutation could not be read off wave 62's witness and needed
a new dressing.  The one section 4 produces IS central, with shift `SqU6.liftO 7`.

## 3.  The `ZMod 8` sharpening

`GradedStageSeparate` found that at stage four a central shift forces the `x1`-slot dressing's
class-three coordinates even, because `2 b = 4 a` in `ZMod 8` forces `b` even while mod `2` the
equation is vacuous.  The same reading one filtration step wider is stronger by one coordinate:
the `gamma_2` shift has FOUR class-two rows, all of them pure Frobenius
(`SqU6.gaTwoShift_f/_g/_h` here, `_i` committed), so centrality forces `(z 2).f`, `(z 2).g`,
`(z 2).h`, `(z 2).i` all even.  Two of the four (`g` and `i`) are not even on the achievable
lattice, so the sharpening is not empty, and `i` is one of the three channels.

⚠ **And it is not what decides wave 60's point.**  Every letter there has `L.j = 0`, so the
`i`-channel `z.i * L.j` is silent whatever `z` is.  The honest verdict is that the `ZMod 8`
mechanism reproduces, is a real theorem, and is orthogonal to the question the wave was set.

## 4.  The kill

The sigma slot is special: dressing it reparametrises the point.  `cenSigDress_stageWit`,
over any commutative ring,

```
   conFiveDress (stageWit h j v) (cenSigDress h w)  =  stageWit h j (v * w)
```

so a sigma-slot dressing needs no transport at all to evaluate.  Wave 60's exclusion is stated
at `v = stageX`, where the relator is `SqU6.liftO 1`; the undressed member `v = 1` kills.  The
question is therefore whether `stageX * w` can be pushed back onto a killing parameter with `w`
in the honest `gamma_2` of the image, and it can.

The achievable lattice, computed by an exact polycyclic sift (`centrallib.py`; `derive.txt`
section 1), is

```
   forceLcs (stageImage h j stageX) 1  =  { z gamma_2-shaped : f, g, h, j even }
```

exactly, of order `2^26 = 67108864` - the same count `GradedStageFrame` reports for `gamma_2`
of the same image by an unrelated coset decomposition.  Its class-four coordinate `m` is
**unrestricted**.  `forceLcs H 2` is `2^13`, contains `<m = 2>` and does not contain `<m = 1>`.
The class-five row of a slot-`0` dressing by `<m = t>` is `5 t` (measured for `t = 0, ..., 7`),
so `t = 3` reaches `7` and kills.

The exhaustive sigma-slot sweep (`results/sweep_sigma.txt`) shows the kill is not a
coincidence of one element.  The sigma-slot shift ignores the dressing's `i`, `j` and `o`
coordinates (checked at 3000 random pairs), which makes an exhaustive sweep of the remaining
seven possible: of `262144` dressings, `4096` act centrally, `2048` of those move the
class-five row oddly, and `512` kill outright - exactly one eighth of the central ones, which
is what equidistribution of the translation amount over `ZMod 8` predicts.  Scaled back over
the three ignored coordinates, `131072` of the `67108864` achievable dressings kill.

## 5.  What this does and does not refute

* **Refuted**: the widening of wave 60's exclusion from `forceLcs (stageImage) 2` to
  `forceLcs (stageImage) 1` at wave 60's own binder point.  `GradedStageFrame`'s scope note -
  "one filtration step wider again, `gamma_2`-dressings, is neither proved nor refuted, here or
  anywhere in the tree" - is now decided, in the negative.
* **Not refuted**: `GradedFiveStageFour.sqRelWord_stageWit_diag_ne_one`,
  `GradedStageFrame.sqArbFrame_stage_diag_ne_one_cleared` and
  `GradedGammaTwoPoint.sqRelWord_stageWit_diag_gaTwo_ne_one`.  All three carry hypotheses that
  the killing dressing fails, and this file proves it fails them:
  `gaTwoCenKill_not_stageFour_achievable` and `cenKill_chan_odd`.
* **Not claimed**: that every binder point is killable.  The mechanism reads `x0.e` odd plus an
  odd class-four coordinate in the achievable `gamma_2` lattice, and both hold at wave 60's
  point for reasons intrinsic to how it was built; but no census over other points was run.
* **Not reached**: the hom layer.  The certificate's two factors are commutators of letters
  that are `stageFrameHom`-images of `sigma * x0`, `x0`, `x1`, `u_j`, so the killing dressing is
  the image of an explicit element of the commutator subgroup of the frame; assembling that
  into a statement about `sqArbFrame` is bookkeeping and is left for the next wave.

## 6.  What the next wave should do

1. **Lift the refutation to the hom layer.**  `stageFrameHom h j` applied to
   `commP ((sigma x0)^{-1}) u_j ^ 2 * commP x1 (x0 u_j)` is `gaTwoCenKill` by
   multiplicativity; the statement to land is that the `x0`-dressed arbitrary-dressing frame
   admits a `gamma_2`-refinement killing the relator image.  That is the form the campaign's
   endgame quotes.
2. **Decide whether ANY binder point survives at `gamma_2`.**  The mechanism above is a
   criterion, not a census: a point survives only if the achievable `gamma_2` lattice has an
   even class-four coordinate at the sigma slot, or `x0.e` is even - and an even `x0.e` kills
   the class-five separation itself (wave 58's form).  If those two demands are incompatible,
   the `gamma_2` route is dead at every point and that is a theorem worth having.  This is the
   single highest-value follow-up.
3. **Do not spend another wave on the channel functional.**  Wave 62 closed the parity route by
   a collision and this wave closed the centrality route by a counterexample; the functional is
   not where the remaining content is.
