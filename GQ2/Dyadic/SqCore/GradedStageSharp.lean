/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedStageNecessity
import GQ2.Dyadic.SqCore.GradedStageFrame

/-!
# W62-MIGRATE4: the committed STAGE-FOUR catalogue, moved onto the CENTRALITY line

`GradedStageNecessity` (wave 61) proved that `GradedFiveStageFour`'s stage-four soundness chain
is **merely sufficient**, and characterised the sharp line in both directions
(`stageForces_iff_stageCentral`): at a marking whose relator is a central translation with an
odd residue, the stage-four forcing holds **exactly** when every achievable stage-four dressing
whose shift is **central** moves the class-five row evenly.  It recorded the migration and named
two statements.  This file performs the migration, finds that the list was **two of fourteen**,
and reports per statement what is actually traded.

## ⭐⭐⭐ Headline 1: the migration table

```text
committed statement                            wave  carried                  now needed
stageWit_sigma_forced                          W60   v.a, v.c even  =>  every  StageCentral
                                                     achievable dressing in    + relator central
                                                     stageN3 (j, l, m even)
sqRelWord_stageWit_diag_ne_one                 W60   the same, discharged      StageCentral alone
                                                     at v = stageX             (and EXACTLY that)
stageWit_sigma_forced_sharp                    W61   v.a even, z in stageN3    stageN3-centrality
                                                                               + relator central
stageFrame_sigma_forced_sharp                  W61   z in stageN3, two rows    stageN3-centrality
                                                                               (no row hypothesis)
stageFrame_sigma_forced                        W61   achievable at the POINT   StageCentral at the
                                                     + the chain + two rows    FRAME
sqRelWord_stageFrame_diag_ne_one_sharp         W61   z in stageN3              stageN3-centrality
sqRelWord_stageFrame_diag_ne_one               W61   achievable at the POINT   StageCentral at the
                                                                               FRAME (EXACTLY)
sqRelWord_stageFrame_stageLegal_ne_one         W61   z in stageN3              StageCentral
                                                                               (EXACTLY)
⚠ sqRelWord_stageFrame_legal_ne_one            W61   z in stageN3              StageOrth: the
                                                                               PARITY line, not
                                                                               the sharp one
sqArbFrame_stage_sigma_forced_cleared          W61   z in stageN3              stageN3-centrality
sqArbFrame_stage_sigma_forced_cleared_lattice  W61   achievable at the POINT   StageCentral
sqArbFrame_stage_diag_ne_one_cleared           W61   z in stageN3              stageN3-centrality
sqArbFrame_stage_diag_ne_one_cleared_lattice   W61   achievable at the POINT   StageCentral
                                                                               (EXACTLY)
sqArbFrame_stage_legal_ne_one_cleared          W61   z in stageN3              StageCentral
```

The two `sqArbFrame_stage_sigma_forced_cleared` rows are the only ones with no dedicated
corollary, and deliberately: the migrated forcing carries **no row hypothesis at all**
(Headline 1's second warning), so `stageFrame_sigma_forced_sharp_central` and
`stageFrame_sigma_forced_central` at `nu' = nuSel h j 0 0` *are* the named-row statements.

"EXACTLY" marks the four points where the new hypothesis is proved to be the **weakest** one, by
an equivalence rather than an implication: `stageWit_stageForces_iff_stageCentral`,
`stageWit_forcesN3_iff_centralN3`, `stageFrame_stageForces_iff_stageCentral` and
`sqArbFrame_stage_stageForces_iff_stageCentral`.  Elsewhere the migrated hypothesis is proved
sufficient and its necessity is not available, because the relator there is not a central
translation with an odd residue and the characterisation's converse half does not apply.

⚠ **The trade is not free, and the honest column is the last one.**  Wave 60's condition is a
statement about the **letters**; the centrality line is a statement about the **dressings** and
it comes with an extra hypothesis wave 60 did not carry - that the relator is a central
translation.  At the committed dressings that hypothesis is discharged outright
(`sqRelWord_stageWit_diag`, `sqRelWord_stageFrame_diag`, `sqRelWord_stageFrame_stageLegal`), and
at a general even-column sigma dressing `v` it is a real restriction.  Section 4 says which of
the two migrated lines each committed statement lands on and why.

## ⭐⭐⭐ Headline 2: wave 61's apparatus carried a hypothesis it never used

⭐⭐ `stageForces_of_stageOrth_free`.  `GradedStageNecessity.stageForces_of_stageOrth` and
`stageForces_of_le_stageN1` both take `hres : sqRelWord m = SqU6.liftO c`, because that wave
routed the parity line through the centrality line.  **The parity line forces at every marking
whatsoever**, with no hypothesis on the relator at all: three quantities carry the argument and
each is even outright - the relator's `(1,2)`-column (`SqU6.sqRelWord_a`), the shift's outer
class-three row (`gaThreeShift_l`), and by hypothesis the shift's class-five row.  This is
`GradedFiveStageFour.stageWit_sigma_forced`'s own argument, stated once and in general.

It is not a cosmetic gain.  It is what migrates the one committed exclusion whose relator is
**not** central (Headline 4), and it is what gives ⭐⭐⭐ `stageFrame_stageForces`: at every
handle count, every handle, every cleared row and **every** dressing element `g`, the stage-four
forcing holds at the frame, in one statement covering all three committed verdicts.

## ⭐⭐ Headline 3: what the reduction buys at the committed point, exhibited

`stageWit_achievable_not_central`.  The triple commutator `[[x0, U], V]` of the committed
point's own letters is an achievable stage-four dressing (`stageWit_gap_mem`); wave 60's
condition constrains it in all three coordinates (`stageWit_gap_mem_stageN3`: `j`, `l`, `m` are
`4`, `6`, `4`); and on the handle-`U` slot **its shift moves the first class-four row by `4`**,
so it is not central and the sharp line reads nothing off it at all.

⭐ The size of the move is the whole point, and it is wave 61's `MODLOW` finding made concrete:
`4` is invisible modulo `2`, so no mod-`2` covector condition could have separated this dressing
from a central one, and the reduction lives over `Z/8` rather than over `Z/2`.

## ⭐⭐ Headline 4: one committed exclusion does NOT migrate, and the reason is structural

`sqRelWord_stageWit_legal_not_central`.  At the single-commutator legal dressing
`fiveLegalDress h j = [x1, u_j]` the relator image is `<m = 4, n = 2, o = 5>`, whose class-four
row is `4`: **not** a central translation.  So the characterisation is unavailable in either
direction there, and `sqRelWord_stageFrame_legal_ne_one` keeps the stronger hypothesis - it
migrates onto the **parity** line and no further (`sqRelWord_stageFrame_legal_ne_one_orth`).

⭐ One fact, two consequences.  Wave 61 recorded the non-centrality of that residue as the
reason `[x1, u_j]` fails to be class-four blind at the new point
(`GradedStageFrame.stageFrame_legal_not_class_four_blind`).  It is the same fact that puts the
statement outside the centrality line: a residue the class-four machinery can see is a residue
the centrality characterisation cannot reach.  The two-commutator repair
`stageLegalDress h j = [x1, v_j] * [x1, u_j]⁻¹` has the central residue `liftO 5` and migrates
in both directions, which is a second reason to prefer it.

## ⭐⭐⭐ Headline 5: the line PREDICTS the tree's stage-four refutation

⭐⭐⭐ `orthFive_not_stageCentral`.  At wave 60's class-five orthogonal point the achievable
stage-four dressing `[[V, sigma], x0]^5` shifts the relator by exactly `liftO 7`
(`gaThreeShift_orthStageDress`): central, and odd.  So the sharp line **fails** there, read off
the centrality condition directly, and `GradedStageNecessity.orthFive_stageForces_false` is
**recovered** from the migration rather than merely being consistent with it
(`orthFive_stageForces_false_of_sharp`).  This is
`GradedFourSharp.oddLive_not_frameOrth` at stage four.

## ⭐⭐⭐ The certified negative: achievability is load-bearing for the sharp line

`stageWit_unrestricted_stageCentral_false`.  Read over **all** `gamma_3`-shaped tuples rather
than the achievable ones, the centrality condition is FALSE at the committed stage-four point:
`GradedFiveStageFour`'s own unrestricted move `<m = 1, n = 3>` on the sigma slot shifts the
relator by `liftO 7` (`gaThreeShift_stageWit_unrestricted`), central and odd, and it does kill
(`sqRelWord_stageWit_unrestricted_kill`, met from the shift side against the committed
`stageWit_unrestricted_kill`).  So `StageCentral` is not a condition on the marking alone, and
its achievability quantifier cannot be dropped - the exact stage-four analogue of
`GradedFourSharp.clrFour_unrestricted_sigma_forced_false`.

## Was wave 61's migration list complete?

**No.**  `GradedStageNecessity` section 7 names `GradedFiveStageFour.stageWit_sigma_forced` and
`sqRelWord_stageWit_diag_ne_one`.  `GradedStageFrame`, which landed in the **same wave**, carries
wave 60's condition in **twelve** further public forcing or exclusion statements (the table
above) and in three supply statements (`stageFrameHom_mem_stageN1`,
`stageFrameHom_columns_even`, `forceLcs_stageFrameHom_le_stageN3`), which are not migrated
because they are lattice facts rather than forcings.  The same is true of
`forceLcs_two_le_stageN3` and `gaThreeShiftO_even` themselves: they are the engine that
discharges a line, not statements of one, and there is nothing in them to migrate.

## Did any committed statement rely on more than it stated?

**Yes, in one mild and mechanical way, and once in the opposite direction.**

* ⚠ The hom-level exclusions of `GradedStageFrame` quantify the refinement over
  `forceLcs (stageImage h j (stageFrameHom h j g)) 2`, the achievable lattice of the **point**,
  while their docstrings describe the achievable lattice of the **frame's image** ("no
  achievable five-slot `gamma_3`-refinement of the frame's image kills the relator image").  The
  two agree by `stageImage_eq_frame_closure`, which is proved in that file, at the same two row
  hypotheses, and is cited by none of the statements that need it for their stated reading.  The
  migrated statements here quantify over the frame's own lattice - that is what `StageForces` and
  `StageCentral` mean at the frame marking - so the reliance is discharged in the statement
  rather than in the prose.  This is the analogue of `GradedFourSharp`'s
  `covectors_pivot_invariant`, and it is milder: the missing fact was already a theorem.
* The opposite direction is Headline 2: wave 61's `stageForces_of_stageOrth` and
  `stageForces_of_le_stageN1` **state** a hypothesis their mathematics does not use.

## The sweep against every refutation in the tree (doctrine iv)

* `GradedStageNecessity.orthFive_stage_kill` / `orthFive_stageForces_false` (the stage-four
  forcing FAILS at wave 60's class-five orthogonal point): swept, and **predicted** -
  `orthFive_not_stageCentral`, Headline 5.
* `GradedStageNecessity.mixStage_separates` (the forcing HOLDS where wave 60's hypothesis AND
  conclusion both fail): no conflict, by construction - every statement here reads
  `StageCentral` or `StageOrth`, and the mixed point satisfies both
  (`mixStage_stageOrth`).  Nothing in this file assumes wave 60's condition anywhere.
* `GradedFiveStageFour.stageWit_unrestricted_kill` / `stageWit_unrestricted_not_achievable` (an
  unachievable `gamma_4` move kills at the committed point): swept, and turned into this file's
  certified negative.  The move is central and odd, so it is exactly what the achievability
  quantifier of `StageCentral` excludes, and `stageWit_unrestricted_not_achievable` is why it
  may be excluded.
* `GradedFiveStageFour.fiveWit_gaThree_kill_not_stageN3` and
  `GradedFiveForce.fiveWit_gaThree_kill` (wave 59's point is killed by an achievable stage-four
  dressing): different point; that point fails `stageN1` at `forceU`, no statement here is about
  it, and the killing dressing's odd class-four coordinate is what puts it outside `stageN3`.
* `GradedStageFrame.stageFrame_legal_not_class_four_blind` (`[x1, u_j]` is visible to the
  class-four machinery at the new point): swept, and **explained** - Headline 4 shows it is the
  same non-centrality that blocks the migration of the exclusion at that word.
* `GradedStageFrame.stageFrame_fiveKillWord_no_kill` (wave 59's killing word does not kill at the
  new point, moving the residue from `1` to `7`): consistent and predicted - it moves the
  class-five row by an even amount, which is what `StageOrth` at that frame asserts.
* `GradedFiveNecessity.orthFive_no_kill`, `orthFive_pair_eq_zero`, `halfFive_unrestricted_kill`,
  `halfFive_unrestricted_forces_false`: class-FIVE statements about `gamma_4`-shaped
  refinements.  No conflict; `orthFive_not_stageCentral` is one filtration step wider and is the
  content of wave 61's Headline 4, not a contradiction of wave 60's.
* `GradedFiveFrame.fiveFrame_odd_sum_kill`, `fiveFrame_handleV_odd_kill` /
  `..._not_achievable`: kills from unachievable class-five moves at the old point; the same
  phenomenon as the certified negative here, one class down, and untouched.
* `GradedFrameNecessity` and `GradedFourSharp.oddLive_not_frameOrth` and the class-four
  catalogue: different class and different carrier (`SqU5`); untouched.
* `GradedFiveBlind.blindCex_not_handle_blind`, `GradedBlockRead.blindCexCore_not_relator_handleFree`,
  `GradedFive.sqRelWord_sigFive_not_handle_blind`: statements about blindness and the handle
  reading, not about the stage-four forcing; untouched.

## Docstrings repaired

* `GradedStageFrame` module docstring, the scope note: "`stageN3` … is the sharpest class the
  tree owns" is no longer true, the sharp line having been computed in the same wave and
  migrated onto here; and "strictly contains the achievable lattice **by**
  `forceLcs_two_le_stageN3`" attributes strictness to a lemma that proves containment - the
  strictness is measured, not proved anywhere in the tree.
* `GradedStageFrame.stageWit_sigma_forced_sharp`: the same two claims, in the same words.
* `GradedFiveStageFour` module docstring, "the soundness hypothesis … is the exact list of
  channels the frame does not already close": exact only relative to reading one letter column;
  `GradedStageNecessity.gaThreeShiftO_even_of_outer` closes the same row from three letter
  columns and one dressing coordinate, and `gaThreeShiftO_even_of_columns` from four letter
  columns and nothing.
* `GradedFiveStageFour.stageN3`: the same claim in miniature.
* `GradedStageNecessity.stageWit_stageForces_of_stageCentral`: "on the line it carries **only**
  that the centrally acting achievable dressings pair evenly" understates by one hypothesis -
  the statement also carries the relator's centrality, which the statement it supersedes does
  not need.
* `GradedStageNecessity.stageForces_of_stageOrth`: annotated with Headline 2, that the relator
  hypothesis it states is not used.
* `GradedFiveGammaTwo` scope note, "sufficient, not shown sharp, **exactly as at stage four**":
  the stage-four line is computed and its catalogue migrated, so the comparison as written is
  now wrong.

No committed statement or proof is modified anywhere.

## PROVED versus carried versus measured

**PROVED**: the two lines over an arbitrary sound class of `gamma_3`-shaped dressings, in both
directions; the parity line's sufficiency with no hypothesis on the relator; every statement of
the table, at every handle count, every handle and every cleared row; four of them as
equivalences; the achievable non-central dressing at the committed point; the certified negative;
the non-centrality of the single-commutator legal residue; the failure of the line at wave 60's
orthogonal point and the recovery of the committed refutation from it.

**Carried, and named**: the relator's centrality, wherever the centrality line is used - see the
warning under Headline 1.  Nothing else: no census, no achievability convention beyond the ones
the committed statements already name, no row hypothesis that is not forced.

**Measured, not proved**: nothing new.  This file adds no census.  It does **not** prove that
the centrality line is strictly weaker than the parity line at any marking; wave 61 measured
that separation at four of 1650 markings and it remains measured.  Nor does it prove that
`stageN3` strictly contains the achievable lattice; that too is measured.

## What this does NOT do

* It does not modify a committed statement or proof.  Every result is a new named corollary
  that supersedes one, plus the seven docstring repairs listed above.
* It does not decide the four measured markings separating the parity line from the centrality
  line.  That is a separate wave-62 item and nothing here bears on it.
* It defines **nothing**: forty-seven theorems and zero definitions, so it cannot collide with a
  sibling lane's names except at the theorem level, where every name carries a `_central`,
  `_orth`, `_free`, `On` or `_gap` marker absent from the tree at this tip.
* It says nothing one filtration step wider.  `GradedFiveGammaTwo`'s `gamma_2`-level soundness
  hypotheses are untouched, and its scope note is annotated rather than answered.

## Contents

* **1** ⭐⭐⭐ the two lines over an arbitrary sound class, and the composite check against
  wave 61; **2** ⭐⭐ what the parity line really costs; **3** the committed tuple-level
  statements, migrated, with the equivalence at the committed dressing; **4** ⭐⭐⭐ the
  committed hom-level statements, migrated, the one that does not migrate, and the named cleared
  row; **5** ⭐⭐ the reduction exhibited; **6** ⭐⭐⭐ the certified negative; **7** ⭐⭐⭐ the
  sweep and the prediction; **8** axiom pins, with the superseded statements printed alongside.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8`, `ZMod 2` or tuples
over them.  All **47** committed prints are **std-3** (`propext`, `Classical.choice`,
`Quot.sound`) or a subset: `44` std-3 and `3` `propext` + `Quot.sound`.  Each of the **23**
statements superseded or reduced is printed alongside, and every one of those is std-3, so
**the migration changes no axiom footprint anywhere**.

## Merge notes

**Nothing is defined and nothing is redefined.**  `StageForces`, `StageOrth`, `StageCentral`,
`stageForces_iff_stageCentral`, `stageForces_of_stageCentral`, `stageCentral_of_stageForces`,
`stageCentral_of_stageOrth`, `stageOrth_of_le_stageN1`, `forceLcs_two_le_gaThreeSub`,
`gaThreeShift_pow`, `orthStageDress`, `orthStageDress_mem`, `orthFive_stage_kill` and
`orthFive_stageForces_false` come from `GradedStageNecessity`; `stageWit`, `stageX`, `stageY`,
`stageU`, `stageV`, `stageImage`, `stageImage_le_stageN1`, `stageWit_a_even`, `stageN1`,
`stageN3`, `stageN3_isGaThree`, `stageN3_even`, `forceLcs_two_le_stageN3`, `gaThreeShift`,
`gaThreeShiftO`, `gaThreeShift_o`, `gaThreeShift_l`, `gaThreeShift_isGaThree`,
`gaThreeShiftO_even`, `sqRelWord_gaThreeDress`, `sqRelWord_stageWit_diag`,
`stageWit_unrestricted_kill`, `SqU6.IsGaThree` and `SqU6.isGaThree_one` come from
`GradedFiveStageFour`; `stageFrameHom`, `stageFrameHom_sqArbFrame`, `stageFrameHom_columns_even`,
`stageWit_one`, `stageWit_handleU`, `stageWit_handleV`, `sqRelWord_stageFrame_diag`,
`sqRelWord_stageFrame_legal`, `sqRelWord_stageFrame_stageLegal`, `sqRelWord_stageWit_legal`,
`stageFrameHom_fiveLegalDress`, `stageLegalDress` and `fiveLegalDress` come from
`GradedStageFrame` and `GradedFiveFrame`; `gaThreeSub`, `commP_mem_commSub`, `orthFiveMark` and
`sqRelWord_orthFiveMark` from `GradedFiveNecessity`; `SqU6.liftO`, `conFiveDress` and
`conFiveDress_apply` from `GradedFiveDefect`; `forceLcs` and `liftC6` from `GradedFiveForce`;
`sqArbFrame`, `sigArbDress` from `GradedFourHom`; `nuSel`, `nuSelClr_handleU`,
`nuSelClr_handleV` from `GradedFourCleared`; `selPar`, `selPar_two_mul`, `selPar_eq_zero_iff`
from `GradedSelect`.

⚠ **Collision watch for the merge** (doctrine v).  The names a sibling stage-four lane is most
likely to land independently are `stageN3_le_gaThreeSub`, `stageWit_stageOrth` and
`stageWit_stageCentral`, each of which is the one-line consequence a lane would reach for first;
any duplicate should be statement-identical, and the diff must still be run.  Import line for
`GQ2.lean`, after `GQ2.Dyadic.SqCore.GradedStageNecessity`:
`import GQ2.Dyadic.SqCore.GradedStageSharp`.
-/

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The two lines over an arbitrary sound class -/

section Engine

variable {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R}

/-- `stageN3` consists of `gamma_3`-shaped elements, so the stage-four translation identity
applies to a dressing drawn from it. -/
theorem stageN3_le_gaThreeSub : stageN3 ≤ gaThreeSub gr3R := fun _ hz => stageN3_isGaThree hz

/-- ⭐⭐⭐ **THE PARITY LINE FORCES WITH NO HYPOTHESIS ON THE RELATOR AT ALL.**  Over any class
`N` of `gamma_3`-shaped dressings, if every `N`-tuple moves the class-five row evenly then every
`N`-tuple that kills the relator leaves an even class-five residue - and the relator is
arbitrary.  Wave 61 routed this through `stageForces_of_stageCentral` and therefore carried the
relator's centrality; the argument does not need it.  Three quantities do the work and each is
even outright: the relator's `(1,2)`-column, the shift's outer class-three row, and (by
hypothesis) the shift's class-five row. -/
theorem stageForcesOn_of_orthOn {N : Subgroup (SqU6 gr3R)} (hN : N ≤ gaThreeSub gr3R)
    (hO : ∀ z : Fin (sqRank h) → SqU6 gr3R, (∀ i, z i ∈ N) → (2 : gr3R) ∣ gaThreeShiftO h m z)
    {z : Fin (sqRank h) → SqU6 gr3R} (hz : ∀ i, z i ∈ N)
    (hkill : sqRelWord (conFiveDress m z) = 1) :
    selPar (sqRelWord m).o = 0 := by
  have hga : ∀ i, (z i).IsGaThree := fun i => hN (hz i)
  rw [sqRelWord_gaThreeDress hga] at hkill
  have ho := congrArg SqU6.o hkill
  rw [SqU6.mul_o, SqU6.one_o] at ho
  have hsh := gaThreeShift_isGaThree (h := h) (m := m) (z := z)
  obtain ⟨ca, hca⟩ : (2 : gr3R) ∣ (sqRelWord m).a :=
    ⟨-2 * (m 1).a + (m 2).a, by rw [SqU6.sqRelWord_a]; ring⟩
  obtain ⟨cl, hcl⟩ : (2 : gr3R) ∣ (gaThreeShift h m z).l := by
    rw [gaThreeShift_l]
    exact ⟨-2 * (z 1).l + (z 2).l, by ring⟩
  obtain ⟨co, hco⟩ : (2 : gr3R) ∣ (gaThreeShift h m z).o := by
    rw [gaThreeShift_o]
    exact hO z hz
  rw [hca, hcl, hco, hsh.2.2.2.2.1, hsh.2.2.2.2.2.2.2.2] at ho
  have hfin : (sqRelWord m).o
      = 2 * (-(co + ca * (gaThreeShift h m z).n + (sqRelWord m).f * cl)) := by
    linear_combination ho
  rw [hfin, selPar_two_mul]

/-- ⭐⭐ **The centrality line suffices over any sound class**, at a central relator:
`GradedStageNecessity.stageForces_of_stageCentral` with the achievability convention replaced by
an arbitrary subgroup of `gamma_3`-shaped dressings. -/
theorem stageForcesOn_of_centralOn {N : Subgroup (SqU6 gr3R)} (hN : N ≤ gaThreeSub gr3R)
    {c : gr3R} (hres : sqRelWord m = SqU6.liftO c)
    (hC : ∀ (z : Fin (sqRank h) → SqU6 gr3R) (w : gr3R), (∀ i, z i ∈ N) →
      gaThreeShift h m z = SqU6.liftO w → (2 : gr3R) ∣ w)
    {z : Fin (sqRank h) → SqU6 gr3R} (hz : ∀ i, z i ∈ N)
    (hkill : sqRelWord (conFiveDress m z) = 1) :
    selPar (sqRelWord m).o = 0 := by
  have hga : ∀ i, (z i).IsGaThree := fun i => hN (hz i)
  rw [sqRelWord_gaThreeDress hga, hres] at hkill
  have hcen : gaThreeShift h m z = SqU6.liftO (-c) := by
    have h1 : SqU6.liftO c * gaThreeShift h m z = SqU6.liftO c * SqU6.liftO (-c) := by
      rw [hkill, SqU6.liftO_mul_liftO, add_neg_cancel]
      ext <;> simp [SqU6.liftO]
    exact mul_left_cancel h1
  obtain ⟨k, hk⟩ := hC z (-c) hz hcen
  rw [hres, SqU6.liftO_o, show c = 2 * (-k) from by linear_combination -hk, selPar_two_mul]

/-- ⭐⭐⭐ **…and it is NECESSARY over any sound class**, at a central relator with an odd
residue: `GradedStageNecessity.stageCentral_of_stageForces` with the same replacement.  The
engine is unchanged - the shift is a homomorphism of the tuple, an odd element of `ZMod 8` is a
unit, and the tuple's `k`-th power hits the residue exactly - and it needs of `N` only that it
is closed under powers, which a subgroup is. -/
theorem centralOn_of_stageForcesOn {N : Subgroup (SqU6 gr3R)} (hN : N ≤ gaThreeSub gr3R)
    {c : gr3R} (hres : sqRelWord m = SqU6.liftO c) (hc : selPar c = 1)
    (hF : ∀ z : Fin (sqRank h) → SqU6 gr3R, (∀ i, z i ∈ N) →
      sqRelWord (conFiveDress m z) = 1 → selPar (sqRelWord m).o = 0)
    {z : Fin (sqRank h) → SqU6 gr3R} {w : gr3R} (hz : ∀ i, z i ∈ N)
    (hcen : gaThreeShift h m z = SqU6.liftO w) : (2 : gr3R) ∣ w := by
  by_contra hodd
  have hw : selPar w = 1 := by
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (selPar w) with h0 | h1
    · obtain ⟨y, hy⟩ := (selPar_eq_zero_iff w).mp h0
      exact absurd ⟨y, hy⟩ hodd
    · exact h1
  have hunit : w * w = 1 := (by decide : ∀ x : gr3R, selPar x = 1 → x * x = 1) w hw
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ((k : ℕ) : gr3R) = -c * w :=
    ⟨(-c * w).val, by simp [ZMod.natCast_val, ZMod.cast_id]⟩
  have hga : ∀ i, (z i).IsGaThree := fun i => hN (hz i)
  have hpow : gaThreeShift h m (fun i => z i ^ k) = SqU6.liftO (-c) := by
    rw [gaThreeShift_pow hga, hcen, SqU6.liftO_pow, hk]
    refine congrArg SqU6.liftO ?_
    calc -c * w * w = -c * (w * w) := by ring
      _ = -c := by rw [hunit, mul_one]
  have hkill : sqRelWord (conFiveDress m (fun i => z i ^ k)) = 1 := by
    rw [sqRelWord_gaThreeDress (fun i => (hga i).pow k), hpow, hres,
      SqU6.liftO_mul_liftO, add_neg_cancel]
    ext <;> simp [SqU6.liftO]
  have hbit := hF (fun i => z i ^ k) (fun i => pow_mem (hz i) k) hkill
  rw [hres, SqU6.liftO_o, hc] at hbit
  exact absurd hbit (by decide)

/-- ⭐⭐⭐ **THE CHARACTERISATION OVER AN ARBITRARY SOUND CLASS.**  This is the engine of the
migration: `GradedStageNecessity.stageForces_iff_stageCentral` reads the achievable lattice, and
the committed statements of `GradedStageFrame` read the declared lattice `stageN3` instead, so
the migration needs the line over both. -/
theorem stageForcesOn_iff_centralOn {N : Subgroup (SqU6 gr3R)} (hN : N ≤ gaThreeSub gr3R)
    {c : gr3R} (hres : sqRelWord m = SqU6.liftO c) (hc : selPar c = 1) :
    (∀ z : Fin (sqRank h) → SqU6 gr3R, (∀ i, z i ∈ N) →
        sqRelWord (conFiveDress m z) = 1 → selPar (sqRelWord m).o = 0)
      ↔ ∀ (z : Fin (sqRank h) → SqU6 gr3R) (w : gr3R), (∀ i, z i ∈ N) →
        gaThreeShift h m z = SqU6.liftO w → (2 : gr3R) ∣ w :=
  ⟨fun hF _ _ hz hcen => centralOn_of_stageForcesOn hN hres hc hF hz hcen,
    fun hC _ hz hkill => stageForcesOn_of_centralOn hN hres hC hz hkill⟩

/-- **The composite check against wave 61** (doctrine iii): at the achievable lattice the
general form IS `GradedStageNecessity.stageForces_iff_stageCentral`, on the nose. -/
theorem stageForces_iff_stageCentral_on {c : gr3R} (hres : sqRelWord m = SqU6.liftO c)
    (hc : selPar c = 1) : StageForces m ↔ StageCentral m :=
  stageForcesOn_iff_centralOn (forceLcs_two_le_gaThreeSub _) hres hc

end Engine

/-! ## 2 What the parity line really costs -/

section Free

variable {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R}

/-- ⭐⭐ **The parity line gives the forcing at EVERY marking.**
`GradedStageNecessity.stageForces_of_stageOrth` carries `hres : sqRelWord m = SqU6.liftO c`; it
is not needed, and dropping it is what lets the migration reach the committed statements whose
relator is **not** a central translation (`GradedStageFrame.sqRelWord_stageWit_legal`, residue
`<m = 4, n = 2, o = 5>`). -/
theorem stageForces_of_stageOrth_free (hO : StageOrth m) : StageForces m :=
  fun _ hz hkill => stageForcesOn_of_orthOn (forceLcs_two_le_gaThreeSub _) hO hz hkill

/-- …so wave 60's soundness chain gives the forcing at every marking, with no hypothesis on the
relator: `GradedStageNecessity.stageForces_of_le_stageN1` without its `hres`. -/
theorem stageForces_of_le_stageN1_free (hle : Subgroup.closure (Set.range m) ≤ stageN1) :
    StageForces m :=
  stageForces_of_stageOrth_free (stageOrth_of_le_stageN1 hle)

/-- **The parity line over `stageN3`**, which is the class the committed `GradedStageFrame`
statements quantify over: wave 60's `gaThreeShiftO_even` read at the declared lattice. -/
theorem stageOrthN3_of_columns (ha : ∀ i, (2 : gr3R) ∣ (m i).a) :
    ∀ z : Fin (sqRank h) → SqU6 gr3R, (∀ i, z i ∈ stageN3) →
      (2 : gr3R) ∣ gaThreeShiftO h m z :=
  fun _ hz => gaThreeShiftO_even ha fun i => stageN3_even (hz i)

/-- …and the centrality line over `stageN3` follows from it, the sharp line being the parity
line read on the centrally acting tuples alone. -/
theorem stageCentralN3_of_columns (ha : ∀ i, (2 : gr3R) ∣ (m i).a) :
    ∀ (z : Fin (sqRank h) → SqU6 gr3R) (w : gr3R), (∀ i, z i ∈ stageN3) →
      gaThreeShift h m z = SqU6.liftO w → (2 : gr3R) ∣ w := by
  intro z w hz hcen
  have ho : gaThreeShiftO h m z = w := by
    rw [← gaThreeShift_o, hcen, SqU6.liftO_o]
  rw [← ho]
  exact stageOrthN3_of_columns ha z hz

end Free

/-! ## 3 The committed TUPLE-level statements, migrated -/

section TuplePoint

variable {h : ℕ} {j : Fin h}

/-- The committed stage-four point is on the parity line, at every sigma dressing whose two
columns are even: this is wave 60's chain, read as a statement about the shift. -/
theorem stageWit_stageOrth {v : SqU6 gr3R} (hv : (2 : gr3R) ∣ v.a ∧ (2 : gr3R) ∣ v.c) :
    StageOrth (stageWit h j v) :=
  stageOrth_of_le_stageN1 (stageImage_le_stageN1 hv)

/-- ⭐ **…hence on the sharp line.**  The centrality line is the parity line read on the
centrally acting tuples alone, so wave 60's condition still discharges it - and section 5 shows
the two are not the same demand at this point. -/
theorem stageWit_stageCentral {v : SqU6 gr3R} (hv : (2 : gr3R) ∣ v.a ∧ (2 : gr3R) ∣ v.c) :
    StageCentral (stageWit h j v) :=
  stageCentral_of_stageOrth (stageWit_stageOrth hv)

/-- ⭐⭐⭐ **`GradedFiveStageFour.stageWit_sigma_forced`, MIGRATED.**  Carried: `v.a` and `v.c`
even, which via `stageImage_le_stageN1` and `forceLcs_two_le_stageN3` forces `j`, `l` and `m`
even on **every** achievable stage-four dressing.  Now needed: only that the achievable
dressings acting **centrally** move the class-five row evenly - plus the relator being a
central translation, which the committed statement did not need and the characterisation does.
At the committed dressing `v = stageX` that extra hypothesis is free
(`sqRelWord_stageWit_diag`). -/
theorem stageWit_sigma_forced_central {v : SqU6 gr3R} {c : gr3R}
    (hres : sqRelWord (stageWit h j v) = SqU6.liftO c) (hC : StageCentral (stageWit h j v))
    {z : Fin (sqRank h) → SqU6 gr3R} (hz : ∀ i, z i ∈ forceLcs (stageImage h j v) 2)
    (hkill : sqRelWord (conFiveDress (stageWit h j v) z) = 1) :
    selPar (sqRelWord (stageWit h j v)).o = 0 :=
  stageForces_of_stageCentral hres hC z hz hkill

/-- ⭐⭐⭐ **THE COMMITTED POINT IS ON THE LINE, IN BOTH DIRECTIONS.**  At the `a0 = a1`
dressing the relator is the central translation `liftO 1` with an odd residue, so the stage-four
forcing there holds **exactly** when the sharp line does.  Wave 60's soundness condition is one
sufficient route to the right-hand side and nothing more. -/
theorem stageWit_stageForces_iff_stageCentral (h : ℕ) (j : Fin h) :
    StageForces (stageWit h j stageX) ↔ StageCentral (stageWit h j stageX) :=
  stageForces_iff_stageCentral (sqRelWord_stageWit_diag h j) (by decide)

/-- ⭐⭐ **`GradedFiveStageFour.sqRelWord_stageWit_diag_ne_one`, MIGRATED**: the exclusion from
the sharp line as a hypothesis, rather than from wave 60's chain.  `GradedStageNecessity`'s
`sqRelWord_stageWit_diag_ne_one_of_sharp` discharges the line at the committed point and so
states the exclusion outright; this is the form that says what the exclusion **consumes**. -/
theorem sqRelWord_stageWit_diag_ne_one_central (hC : StageCentral (stageWit h j stageX))
    {z : Fin (sqRank h) → SqU6 gr3R} (hz : ∀ i, z i ∈ forceLcs (stageImage h j stageX) 2) :
    sqRelWord (conFiveDress (stageWit h j stageX) z) ≠ 1 := by
  intro hc
  have hp := (stageWit_stageForces_iff_stageCentral h j).mpr hC z hz hc
  rw [sqRelWord_stageWit_diag, SqU6.liftO_o] at hp
  exact absurd hp (by decide)

/-- The centrality line over the **declared** lattice `stageN3`, at the committed point:
wave 60's even `(1,2)`-column is what supplies it, exactly as it supplies the parity line. -/
theorem stageWit_centralN3 {v : SqU6 gr3R} (hv : (2 : gr3R) ∣ v.a) :
    ∀ (z : Fin (sqRank h) → SqU6 gr3R) (w : gr3R), (∀ i, z i ∈ stageN3) →
      gaThreeShift h (stageWit h j v) z = SqU6.liftO w → (2 : gr3R) ∣ w :=
  stageCentralN3_of_columns (stageWit_a_even hv)

/-- ⭐⭐ **`GradedStageFrame.stageWit_sigma_forced_sharp`, MIGRATED.**  Carried: `v.a` even and
every dressing slot in `stageN3`, that is `j`, `l` and `m` even.  Now needed: only that the
`stageN3`-tuples acting centrally move the class-five row evenly.  The class quantified over is
unchanged, so this is a strictly weaker hypothesis on the same statement. -/
theorem stageWit_sigma_forced_sharp_central {v : SqU6 gr3R} {c : gr3R}
    (hres : sqRelWord (stageWit h j v) = SqU6.liftO c)
    (hC : ∀ (z : Fin (sqRank h) → SqU6 gr3R) (w : gr3R), (∀ i, z i ∈ stageN3) →
      gaThreeShift h (stageWit h j v) z = SqU6.liftO w → (2 : gr3R) ∣ w)
    {z : Fin (sqRank h) → SqU6 gr3R} (hz : ∀ i, z i ∈ stageN3)
    (hkill : sqRelWord (conFiveDress (stageWit h j v) z) = 1) :
    selPar (sqRelWord (stageWit h j v)).o = 0 :=
  stageForcesOn_of_centralOn stageN3_le_gaThreeSub hres hC hz hkill

/-- ⭐⭐⭐ **…and over `stageN3` too the line is sharp**, at the committed dressing: both
directions, at every handle count and every handle. -/
theorem stageWit_forcesN3_iff_centralN3 (h : ℕ) (j : Fin h) :
    (∀ z : Fin (sqRank h) → SqU6 gr3R, (∀ i, z i ∈ stageN3) →
        sqRelWord (conFiveDress (stageWit h j stageX) z) = 1 →
        selPar (sqRelWord (stageWit h j stageX)).o = 0)
      ↔ ∀ (z : Fin (sqRank h) → SqU6 gr3R) (w : gr3R), (∀ i, z i ∈ stageN3) →
        gaThreeShift h (stageWit h j stageX) z = SqU6.liftO w → (2 : gr3R) ∣ w :=
  stageForcesOn_iff_centralOn stageN3_le_gaThreeSub (sqRelWord_stageWit_diag h j) (by decide)

end TuplePoint

/-! ## 4 The committed HOM-level statements, migrated -/

section FramePoint

variable {h : ℕ} {j : Fin h}
variable {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])}

/-- **The frame is on the parity line at every dressing element**, with no hypothesis on `g`:
`stageFrameHom_columns_even` supplies both soundness columns for every element of `D_sq h`. -/
theorem stageFrame_stageOrth (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) (g : (DSq h : Type)) :
    StageOrth (fun i => stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i)) := by
  rw [stageFrameHom_sqArbFrame hu hv g]
  exact stageWit_stageOrth (stageFrameHom_columns_even g)

/-- ⭐ **…hence on the sharp line at every dressing element.** -/
theorem stageFrame_stageCentral (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) (g : (DSq h : Type)) :
    StageCentral (fun i => stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i)) :=
  stageCentral_of_stageOrth (stageFrame_stageOrth hu hv g)

/-- ⭐⭐⭐ **`GradedStageFrame.stageFrame_sigma_forced`, MIGRATED, and quantified over the
FRAME's own lattice.**  Carried: the achievability convention taken at the **point**
`stageImage h j (stageFrameHom h j g)`, plus wave 60's chain by way of
`forceLcs_stageFrameHom_le_stageN3`.  Now needed: the sharp line at the frame, and the relator
being a central translation.  ⚠ Note the quantifier: `StageCentral` and `StageForces` read
`gamma_3` of the subgroup generated by the **frame's** image slots, which is what the committed
docstrings describe and what the committed statements do not say; the two agree by
`stageImage_eq_frame_closure`, proved in the same file and cited by none of them.

⭐ The two row hypotheses are gone as well: the committed statement needs them to identify the
frame with the point, and this one states both the line and the residue at the frame itself.
They reappear, unavoidably, when the line is discharged (`stageFrame_stageCentral`). -/
theorem stageFrame_sigma_forced_central (g : (DSq h : Type)) {c : gr3R}
    (hres : sqRelWord (fun i =>
      stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i)) = SqU6.liftO c)
    (hC : StageCentral (fun i => stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i)))
    {z : Fin (sqRank h) → SqU6 gr3R}
    (hz : ∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range fun i =>
      stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i))) 2)
    (hkill : sqRelWord (conFiveDress
      (fun i => stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i)) z) = 1) :
    selPar (sqRelWord fun i =>
      stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i)).o = 0 :=
  stageForces_of_stageCentral hres hC z hz hkill

/-- ⭐⭐ **`GradedStageFrame.stageWit_sigma_forced_sharp`'s hom-level companion
`stageFrame_sigma_forced_sharp`, MIGRATED**, in the declared-lattice convention it uses. -/
theorem stageFrame_sigma_forced_sharp_central (g : (DSq h : Type)) {c : gr3R}
    (hres : sqRelWord (fun i =>
      stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i)) = SqU6.liftO c)
    (hC : ∀ (z : Fin (sqRank h) → SqU6 gr3R) (w : gr3R), (∀ i, z i ∈ stageN3) →
      gaThreeShift h (fun i => stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i)) z
        = SqU6.liftO w → (2 : gr3R) ∣ w)
    {z : Fin (sqRank h) → SqU6 gr3R} (hz : ∀ i, z i ∈ stageN3)
    (hkill : sqRelWord (conFiveDress
      (fun i => stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i)) z) = 1) :
    selPar (sqRelWord fun i =>
      stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i)).o = 0 :=
  stageForcesOn_of_centralOn stageN3_le_gaThreeSub hres hC hz hkill

/-- ⭐⭐⭐ **THE HOM-LEVEL FORCING IS ON THE SHARP LINE, IN BOTH DIRECTIONS.**  At the
`x0`-dressed frame the relator image is the central translation `liftO 1` with an odd residue,
so the stage-four forcing there holds **exactly** when every achievable stage-four refinement of
the frame's image that acts centrally moves the class-five row evenly.  This is
`GradedStageFrame.stageFrame_fiveForces_iff_fiveOrth` one filtration step wider, and it is the
statement wave 61's own scope note said was not computed. -/
theorem stageFrame_stageForces_iff_stageCentral (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    StageForces (fun i =>
        stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i))
      ↔ StageCentral (fun i =>
        stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i)) :=
  stageForces_iff_stageCentral (sqRelWord_stageFrame_diag hu hv) (by decide)

/-- ⭐⭐⭐ **`GradedStageFrame.sqRelWord_stageFrame_diag_ne_one`, MIGRATED**: the hom-level
exclusion from the sharp line alone, over the frame's own achievable lattice. -/
theorem sqRelWord_stageFrame_diag_ne_one_central (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1)
    (hC : StageCentral (fun i =>
      stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i)))
    {z : Fin (sqRank h) → SqU6 gr3R}
    (hz : ∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range fun i =>
      stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i))) 2) :
    sqRelWord (conFiveDress
      (fun i => stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i)) z) ≠ 1 := by
  intro hc
  have hp := (stageFrame_stageForces_iff_stageCentral hu hv).mpr hC z hz hc
  rw [sqRelWord_stageFrame_diag hu hv, SqU6.liftO_o] at hp
  exact absurd hp (by decide)

/-- ⭐⭐ **`GradedStageFrame.sqRelWord_stageFrame_diag_ne_one_sharp`, MIGRATED**: the same
exclusion over the declared lattice `stageN3`, from the centrality line read on that lattice. -/
theorem sqRelWord_stageFrame_diag_ne_one_sharp_central
    (hu : nu' (sqGen h (sqHandleIdxU j)) = 1) (hv : nu' (sqGen h (sqHandleIdxV j)) = 1)
    (hC : ∀ (z : Fin (sqRank h) → SqU6 gr3R) (w : gr3R), (∀ i, z i ∈ stageN3) →
      gaThreeShift h (fun i => stageFrameHom h j
        (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i)) z = SqU6.liftO w → (2 : gr3R) ∣ w)
    {z : Fin (sqRank h) → SqU6 gr3R} (hz : ∀ i, z i ∈ stageN3) :
    sqRelWord (conFiveDress
      (fun i => stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (dsqX0 h)) i)) z) ≠ 1 := by
  intro hc
  have hp := stageFrame_sigma_forced_sharp_central (dsqX0 h)
    (sqRelWord_stageFrame_diag hu hv) hC hz hc
  rw [sqRelWord_stageFrame_diag hu hv, SqU6.liftO_o] at hp
  exact absurd hp (by decide)

/-- ⭐⭐ **The repaired legal dressing is on the line too**, its residue `liftO 5` being central
and odd: `GradedStageFrame.sqRelWord_stageFrame_stageLegal_ne_one` migrated, in both
directions. -/
theorem stageFrame_stageLegal_stageForces_iff_stageCentral
    (hu : nu' (sqGen h (sqHandleIdxU j)) = 1) (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) :
    StageForces (fun i =>
        stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (stageLegalDress h j)) i))
      ↔ StageCentral (fun i =>
        stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (stageLegalDress h j)) i)) :=
  stageForces_iff_stageCentral (sqRelWord_stageFrame_stageLegal hu hv) (by decide)

theorem sqRelWord_stageFrame_stageLegal_ne_one_central
    (hu : nu' (sqGen h (sqHandleIdxU j)) = 1) (hv : nu' (sqGen h (sqHandleIdxV j)) = 1)
    (hC : StageCentral (fun i =>
      stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (stageLegalDress h j)) i)))
    {z : Fin (sqRank h) → SqU6 gr3R}
    (hz : ∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range fun i =>
      stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (stageLegalDress h j)) i))) 2) :
    sqRelWord (conFiveDress (fun i =>
      stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h (stageLegalDress h j)) i)) z) ≠ 1 := by
  intro hc
  have hp := (stageFrame_stageLegal_stageForces_iff_stageCentral hu hv).mpr hC z hz hc
  rw [sqRelWord_stageFrame_stageLegal hu hv, SqU6.liftO_o] at hp
  exact absurd hp (by decide)

/-- ⭐⭐⭐ **THE WHOLE HOM-LEVEL EXCLUSION IN ONE STATEMENT, AND IT CARRIES NOTHING.**  At every
handle count, every handle, every row cleared at the selected handle and **every** dressing
element `g`, the stage-four forcing holds at the frame: no achievable stage-four refinement of
the frame's own image kills the relator image without leaving an even class-five residue.  It
covers the three committed verdicts at once - `x0`, `[x1, u_j]` and
`[x1, v_j] * [x1, u_j]⁻¹` - **including the one whose residue is not central**, because
section 2 removed the relator hypothesis from the parity route. -/
theorem stageFrame_stageForces (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) (g : (DSq h : Type)) :
    StageForces (fun i => stageFrameHom h j (sqArbFrame h nu' j (sigArbDress h g) i)) :=
  stageForces_of_stageOrth_free (stageFrame_stageOrth hu hv g)

/-- ⚠ **The single-commutator legal dressing's relator is NOT a central translation**, so the
characterisation cannot reach it in either direction: its class-four row is `4`.  This is the
one committed exclusion of the stage-four catalogue that the centrality line does not migrate,
and saying so is the point. -/
theorem sqRelWord_stageWit_legal_not_central (h : ℕ) (j : Fin h) (c : gr3R) :
    sqRelWord (stageWit h j (commP stageY stageU)) ≠ SqU6.liftO c := by
  intro hc
  have hm := congrArg SqU6.m hc
  rw [sqRelWord_stageWit_legal] at hm
  have h0 : (SqU6.liftO c).m = 0 := rfl
  rw [h0] at hm
  exact absurd hm (by decide)

/-- …and the same at the frame. -/
theorem sqRelWord_stageFrame_legal_not_central (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1) (c : gr3R) :
    sqRelWord (fun i => stageFrameHom h j
      (sqArbFrame h nu' j (sigArbDress h (fiveLegalDress h j)) i)) ≠ SqU6.liftO c := by
  rw [stageFrameHom_sqArbFrame hu hv, stageFrameHom_fiveLegalDress]
  exact sqRelWord_stageWit_legal_not_central h j c

/-- ⭐⭐ **`GradedStageFrame.sqRelWord_stageFrame_legal_ne_one`, MIGRATED - onto the PARITY line,
because the centrality line does not reach it.**  Carried: every dressing slot in `stageN3`.
Now needed: that every achievable stage-four dressing of the frame's own image moves the
class-five row evenly.  ⚠ This is the parity line and not the sharp one; at a relator that is
not a central translation the sharp line says nothing, and the honest report is that this
statement keeps the stronger hypothesis. -/
theorem sqRelWord_stageFrame_legal_ne_one_orth (hu : nu' (sqGen h (sqHandleIdxU j)) = 1)
    (hv : nu' (sqGen h (sqHandleIdxV j)) = 1)
    (hO : StageOrth (fun i => stageFrameHom h j
      (sqArbFrame h nu' j (sigArbDress h (fiveLegalDress h j)) i)))
    {z : Fin (sqRank h) → SqU6 gr3R}
    (hz : ∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range fun i => stageFrameHom h j
      (sqArbFrame h nu' j (sigArbDress h (fiveLegalDress h j)) i))) 2) :
    sqRelWord (conFiveDress (fun i => stageFrameHom h j
      (sqArbFrame h nu' j (sigArbDress h (fiveLegalDress h j)) i)) z) ≠ 1 := by
  intro hc
  have hp := stageForces_of_stageOrth_free hO z hz hc
  rw [sqRelWord_stageFrame_legal hu hv] at hp
  exact absurd hp (by decide)

end FramePoint

/-! ### The named cleared row -/

section ClearedRow

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐⭐ **`GradedStageFrame.sqArbFrame_stage_diag_ne_one_cleared`, MIGRATED**: at the committed
cleared selected marking the hom-level exclusion holds **exactly** when the sharp line does. -/
theorem sqArbFrame_stage_stageForces_iff_stageCentral (h : ℕ) (j : Fin h) :
    StageForces (fun i => stageFrameHom h j
        (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h (dsqX0 h)) i))
      ↔ StageCentral (fun i => stageFrameHom h j
        (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h (dsqX0 h)) i)) :=
  stageFrame_stageForces_iff_stageCentral nuSelClr_handleU nuSelClr_handleV

/-- ⭐⭐ **`GradedStageFrame.sqArbFrame_stage_diag_ne_one_cleared`, MIGRATED**, in the declared
lattice convention it uses. -/
theorem sqArbFrame_stage_diag_ne_one_cleared_sharp_central
    (hC : ∀ (z : Fin (sqRank h) → SqU6 gr3R) (w : gr3R), (∀ i, z i ∈ stageN3) →
      gaThreeShift h (fun i => stageFrameHom h j
        (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h (dsqX0 h)) i)) z
        = SqU6.liftO w → (2 : gr3R) ∣ w)
    {z : Fin (sqRank h) → SqU6 gr3R} (hz : ∀ i, z i ∈ stageN3) :
    sqRelWord (conFiveDress (fun i => stageFrameHom h j
      (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h (dsqX0 h)) i)) z) ≠ 1 :=
  sqRelWord_stageFrame_diag_ne_one_sharp_central nuSelClr_handleU nuSelClr_handleV hC hz

/-- …and in the achievability convention. -/
theorem sqArbFrame_stage_diag_ne_one_cleared_central
    (hC : StageCentral (fun i => stageFrameHom h j
      (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h (dsqX0 h)) i)))
    {z : Fin (sqRank h) → SqU6 gr3R}
    (hz : ∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range fun i => stageFrameHom h j
      (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h (dsqX0 h)) i))) 2) :
    sqRelWord (conFiveDress (fun i => stageFrameHom h j
      (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h (dsqX0 h)) i)) z) ≠ 1 :=
  sqRelWord_stageFrame_diag_ne_one_central nuSelClr_handleU nuSelClr_handleV hC hz

/-- …and the same for the repaired legal dressing, which is what
`sqArbFrame_stage_legal_ne_one_cleared` states. -/
theorem sqArbFrame_stage_legal_ne_one_cleared_central
    (hC : StageCentral (fun i => stageFrameHom h j
      (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h (stageLegalDress h j)) i)))
    {z : Fin (sqRank h) → SqU6 gr3R}
    (hz : ∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range fun i => stageFrameHom h j
      (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h (stageLegalDress h j)) i))) 2) :
    sqRelWord (conFiveDress (fun i => stageFrameHom h j
      (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h (stageLegalDress h j)) i)) z) ≠ 1 :=
  sqRelWord_stageFrame_stageLegal_ne_one_central nuSelClr_handleU nuSelClr_handleV hC hz

/-- …and the line holds there, so the committed exclusions are recovered with nothing lost. -/
theorem sqArbFrame_stage_stageForces_cleared (g : (DSq h : Type)) :
    StageForces (fun i => stageFrameHom h j
      (sqArbFrame h (nuSel h j 0 0) j (sigArbDress h g) i)) :=
  stageFrame_stageForces nuSelClr_handleU nuSelClr_handleV g

end ClearedRow

/-! ## 5 The reduction, exhibited: an achievable dressing the sharp line does not read -/

section Reduction

variable {h : ℕ} {j : Fin h}

/-- The triple commutator `[[x0, U], V]` of the committed point's own letters is an **achievable**
stage-four dressing, at every handle count and every handle. -/
theorem stageWit_gap_mem :
    commP (commP stageX stageU) stageV ∈ forceLcs (stageImage h j stageX) 2 := by
  have hX : stageX ∈ stageImage h j stageX :=
    Subgroup.subset_closure ⟨1, stageWit_one stageX⟩
  have hU : stageU ∈ stageImage h j stageX :=
    Subgroup.subset_closure ⟨sqHandleIdxU j, stageWit_handleU stageX⟩
  have hV : stageV ∈ stageImage h j stageX :=
    Subgroup.subset_closure ⟨sqHandleIdxV j, stageWit_handleV stageX⟩
  exact commP_mem_commSub (commP_mem_commSub hX hU) hV

/-- …and wave 60's condition **does** constrain it: its `j`, `l` and `m` are `4`, `6` and `4`. -/
theorem stageWit_gap_mem_stageN3 : commP (commP stageX stageU) stageV ∈ stageN3 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩⟩

/-- The single-slot dressing it defines is achievable at every slot. -/
theorem stageWit_gap_dress_mem (i : Fin (sqRank 1)) :
    (if (i : ℕ) = 3 then commP (commP stageX stageU) stageV else 1)
      ∈ forceLcs (stageImage 1 0 stageX) 2 := by
  split_ifs
  · exact stageWit_gap_mem
  · exact one_mem _

/-- ⭐⭐ **THE REDUCTION IS REAL AT THE COMMITTED POINT.**  Dressing the handle-`U` slot by that
achievable triple commutator moves the relator's **first class-four row by `4`**, so the shift is
not central and the sharp line reads nothing off it - while wave 60's chain constrains all three
of its class-three and class-four coordinates.  ⭐ The size of the move is the point: `4` is
invisible modulo `2`, which is exactly why no mod-`2` covector condition can be the stage-four
line (`GradedStageNecessity`, `MODLOW`). -/
theorem stageWit_achievable_not_central :
    (∀ i, (fun i : Fin (sqRank 1) =>
        if (i : ℕ) = 3 then commP (commP stageX stageU) stageV else 1) i
      ∈ forceLcs (stageImage 1 0 stageX) 2)
      ∧ (gaThreeShift 1 (stageWit 1 0 stageX) (fun i =>
        if (i : ℕ) = 3 then commP (commP stageX stageU) stageV else 1)).m = 4
      ∧ ∀ w : gr3R, gaThreeShift 1 (stageWit 1 0 stageX) (fun i =>
        if (i : ℕ) = 3 then commP (commP stageX stageU) stageV else 1) ≠ SqU6.liftO w := by
  refine ⟨stageWit_gap_dress_mem, by decide, fun w hc => ?_⟩
  · have hm := congrArg SqU6.m hc
    rw [show (gaThreeShift 1 (stageWit 1 0 stageX) (fun i =>
      if (i : ℕ) = 3 then commP (commP stageX stageU) stageV else 1)).m = 4 from by decide,
      show (SqU6.liftO w).m = 0 from rfl] at hm
    exact absurd hm (by decide)

end Reduction

/-! ## 6 The certified negative: the sharp line's achievability quantifier is load-bearing -/

section Negative

/-- `GradedFiveStageFour.stageWit_unrestricted_kill`'s move, read in the `conFiveDress`
convention: the two tuples are the same. -/
theorem conFiveDress_stageWit_unrestricted :
    conFiveDress (stageWit 1 0 stageX)
        (fun i => if (i : ℕ) = 0
          then (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0⟩ : SqU6 gr3R) else 1)
      = fun i : Fin (sqRank 1) => if (i : ℕ) = 0
        then stageWit 1 0 stageX i * ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0⟩
        else stageWit 1 0 stageX i := by
  funext i
  rw [conFiveDress_apply]
  by_cases hi : (i : ℕ) = 0
  · rw [if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi, mul_one]

/-- ⭐ **The unrestricted move acts CENTRALLY with an odd class-five row.**  The
`gamma_4`-shaped `<m = 1, n = 3>` on the sigma slot shifts the relator by exactly `liftO 7`, so
it kills a relator whose residue is `1`. -/
theorem gaThreeShift_stageWit_unrestricted :
    gaThreeShift 1 (stageWit 1 0 stageX)
      (fun i => if (i : ℕ) = 0
        then (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0⟩ : SqU6 gr3R) else 1)
      = SqU6.liftO 7 := by decide

/-- ⭐⭐⭐ **THE ACHIEVABILITY QUANTIFIER CANNOT BE DROPPED FROM THE SHARP LINE.**  Read over
**all** `gamma_3`-shaped tuples rather than the achievable ones, the centrality condition is
FALSE at the committed stage-four point, at one handle: the move above is central and odd.  So
`StageCentral` is not a statement about the marking's covectors alone, and the certified
negative is the exact stage-four analogue of
`GradedFourSharp.clrFour_unrestricted_sigma_forced_false`.  ⭐ Note what it does **not** say:
that move is `GradedFiveStageFour.stageWit_unrestricted_not_achievable`, outside `stageN3`, so
nothing here touches the achievable line. -/
theorem stageWit_unrestricted_stageCentral_false :
    ¬ ∀ (z : Fin (sqRank 1) → SqU6 gr3R) (w : gr3R), (∀ i, (z i).IsGaThree) →
      gaThreeShift 1 (stageWit 1 0 stageX) z = SqU6.liftO w → (2 : gr3R) ∣ w := by
  intro hC
  have hga : ∀ i : Fin (sqRank 1), ((if (i : ℕ) = 0
      then (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0⟩ : SqU6 gr3R) else 1)).IsGaThree := by
    intro i
    split_ifs
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact SqU6.isGaThree_one
  obtain ⟨t, ht⟩ := hC _ 7 hga gaThreeShift_stageWit_unrestricted
  exact absurd ht (by revert t; decide)

/-- …and the kill really happens, which is what makes the negative a certificate rather than a
remark: this is the committed `stageWit_unrestricted_kill`, met from the shift side. -/
theorem sqRelWord_stageWit_unrestricted_kill :
    sqRelWord (conFiveDress (stageWit 1 0 stageX)
      (fun i => if (i : ℕ) = 0
        then (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0⟩ : SqU6 gr3R) else 1)) = 1 := by
  rw [conFiveDress_stageWit_unrestricted]
  exact stageWit_unrestricted_kill

end Negative

/-! ## 7 The sweep: the sharp line PREDICTS the tree's stage-four refutation -/

section Sweep

/-- ⭐ **The killing dressing at wave 60's class-five orthogonal point acts CENTRALLY**, with the
odd class-five row `7`.  `GradedStageNecessity` exhibits it as an achievable stage-four dressing
that kills; read through the shift it is exactly a violation of the sharp line. -/
theorem gaThreeShift_orthStageDress :
    gaThreeShift 1 (orthFiveMark 1 0) orthStageDress = SqU6.liftO 7 := by decide

/-- ⭐⭐⭐ **THE SHARP LINE FAILS AT WAVE 60's ORTHOGONAL POINT**, and this is read off the
covector-free centrality condition directly rather than inherited from the refutation. -/
theorem orthFive_not_stageCentral : ¬ StageCentral (orthFiveMark 1 0) := by
  intro hC
  obtain ⟨t, ht⟩ := hC orthStageDress 7 orthStageDress_mem gaThreeShift_orthStageDress
  exact absurd ht (by revert t; decide)

/-- ⭐⭐⭐ **…so `GradedStageNecessity.orthFive_stageForces_false` is RECOVERED from the
migration rather than contradicted by it**, exactly as `GradedFourSharp.oddLive_not_frameOrth`
recovers the class-four tree's single refutation.  The sweep of doctrine (iv) therefore closes
with a prediction rather than with a compatibility check. -/
theorem orthFive_stageForces_false_of_sharp : ¬ StageForces (orthFiveMark 1 0) := fun hF =>
  orthFive_not_stageCentral
    (stageCentral_of_stageForces sqRelWord_orthFiveMark (by decide) hF)

end Sweep

/-! ## 8 Axiom pins -/

section Pins

#print axioms stageN3_le_gaThreeSub
#print axioms stageForcesOn_of_orthOn
#print axioms stageForcesOn_of_centralOn
#print axioms centralOn_of_stageForcesOn
#print axioms stageForcesOn_iff_centralOn
#print axioms stageForces_iff_stageCentral_on
#print axioms stageForces_of_stageOrth_free
#print axioms stageForces_of_le_stageN1_free
#print axioms stageOrthN3_of_columns
#print axioms stageCentralN3_of_columns
#print axioms stageWit_stageOrth
#print axioms stageWit_stageCentral
#print axioms stageWit_sigma_forced_central
#print axioms stageWit_stageForces_iff_stageCentral
#print axioms sqRelWord_stageWit_diag_ne_one_central
#print axioms stageWit_centralN3
#print axioms stageWit_sigma_forced_sharp_central
#print axioms stageWit_forcesN3_iff_centralN3
#print axioms stageFrame_stageOrth
#print axioms stageFrame_stageCentral
#print axioms stageFrame_sigma_forced_central
#print axioms stageFrame_sigma_forced_sharp_central
#print axioms stageFrame_stageForces_iff_stageCentral
#print axioms sqRelWord_stageFrame_diag_ne_one_central
#print axioms sqRelWord_stageFrame_diag_ne_one_sharp_central
#print axioms stageFrame_stageLegal_stageForces_iff_stageCentral
#print axioms sqRelWord_stageFrame_stageLegal_ne_one_central
#print axioms stageFrame_stageForces
#print axioms sqRelWord_stageWit_legal_not_central
#print axioms sqRelWord_stageFrame_legal_not_central
#print axioms sqRelWord_stageFrame_legal_ne_one_orth
#print axioms sqArbFrame_stage_stageForces_iff_stageCentral
#print axioms sqArbFrame_stage_diag_ne_one_cleared_sharp_central
#print axioms sqArbFrame_stage_diag_ne_one_cleared_central
#print axioms sqArbFrame_stage_legal_ne_one_cleared_central
#print axioms sqArbFrame_stage_stageForces_cleared
#print axioms stageWit_gap_mem
#print axioms stageWit_gap_mem_stageN3
#print axioms stageWit_gap_dress_mem
#print axioms stageWit_achievable_not_central
#print axioms conFiveDress_stageWit_unrestricted
#print axioms gaThreeShift_stageWit_unrestricted
#print axioms stageWit_unrestricted_stageCentral_false
#print axioms sqRelWord_stageWit_unrestricted_kill
#print axioms gaThreeShift_orthStageDress
#print axioms orthFive_not_stageCentral
#print axioms orthFive_stageForces_false_of_sharp

/-! ### The superseded statements, for comparison

Every print below is a committed statement that one of the prints above supersedes, or an
apparatus statement whose hypothesis is reduced above.  The comparison is the point of the
section: **the migration changes no axiom footprint anywhere.** -/

#print axioms stageWit_sigma_forced
#print axioms sqRelWord_stageWit_diag_ne_one
#print axioms stageWit_sigma_forced_sharp
#print axioms stageFrame_sigma_forced_sharp
#print axioms stageFrame_sigma_forced
#print axioms sqRelWord_stageFrame_diag_ne_one_sharp
#print axioms sqRelWord_stageFrame_diag_ne_one
#print axioms sqRelWord_stageFrame_stageLegal_ne_one
#print axioms sqRelWord_stageFrame_legal_ne_one
#print axioms sqArbFrame_stage_sigma_forced_cleared
#print axioms sqArbFrame_stage_sigma_forced_cleared_lattice
#print axioms sqArbFrame_stage_diag_ne_one_cleared
#print axioms sqArbFrame_stage_diag_ne_one_cleared_lattice
#print axioms sqArbFrame_stage_legal_ne_one_cleared
#print axioms stageForces_of_stageOrth
#print axioms stageForces_of_le_stageN1
#print axioms stageForces_iff_stageCentral
#print axioms stageWit_stageForces_of_stageCentral
#print axioms sqRelWord_stageWit_diag_ne_one_of_sharp
#print axioms orthFive_stageForces_false
#print axioms stageWit_unrestricted_kill
#print axioms forceLcs_two_le_stageN3
#print axioms gaThreeShiftO_even

end Pins

end SqCore

end Dyadic

end GQ2
