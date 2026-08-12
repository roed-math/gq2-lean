/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFiveLive
import GQ2.Dyadic.SqCore.GradedGammaTwoCentral
import GQ2.Dyadic.SqCore.GradedGammaTwoCensus

/-!
# W64-VERIFY task B: W63-CENTRAL2's `gamma_2` kill DOES apply at W63-LIVE5's point

W63-LIVE5 built a fresh class-five binder point `liveBlkWit` whose block channel is live, and
reused the committed `GradedFiveStageFour.stageX` as its `x0` slot.  W63-CENTRAL2, at wave 60's
own binder point, killed the diagonally dressed frame with an achievable `gamma_2`-dressing and
recorded the mechanism as `cenKill_mechanism`: the sigma slot's class-four coordinate is paired
against `x0.e`, and at wave 60's point `stageX.e = 5` is a UNIT.

The two lanes ran in the same wave and neither resolved whether the kill transports.  It does,
and by the shared coordinate: **the two points have the SAME `x0` slot**, so they have the same
knob.

## ⭐⭐⭐ Headline: the live point inherits the whole `gamma_2` vulnerability

⭐⭐⭐ `gaTwoForces_liveBlkWit_false`, `gaTwoCentral_liveBlkWit_false`,
`gaTwoOrth_liveBlkWit_false`: at the live point's diagonal dressing, at **every** handle count
and **every** handle, all three `gamma_2` lines FAIL, with the very same killing element
`GradedGammaTwoCentral.gaTwoCenKill = <m = 3>` on the sigma slot.  The residue there is
`liftO 1` (`GradedFiveLive.sqRelWord_liveBlkWit_diag`), the shift is `liftO 7`
(`gaTwoShift_liveBlkWit_cenKill`), and `1 + 7 = 0`.

⭐⭐ `liveCenKill_comm_form`: at the live point the killer is a **single** honest commutator of
the point's own letters, `commP (liveBlkSig * stageX) (liveBlkV * liveBlkU⁻¹)`, where wave 60's
point needed a product of two.  ⚠ Since the fold below, this is a standalone record and not the
route to `cenSigDress_liveCenKill_mem`, which now takes the census's own certificate.

⭐ `liveCen_shared_x0`: the one-line reason.  `stageWit h j stageX 1 = liveBlkWit h j stageX 1`,
both `stageX`, so `GradedGammaTwoCentral.cenKill_mechanism` - `selPar stageX.e = 1` and
`stageX.e * gaTwoCenKill.m = 7` - is a statement about a slot the two points SHARE.  Moving the
sigma mark from `E_23` to `E_23 E_45` and re-solving the `x1` slot changes neither.  ⚠ Since the
fold below this is the HISTORICAL reason and not the route: the kill runs off the census's
ring-level identity, which reads the `x0` slot generically.

## ⚠ What this does and does not touch

**Nothing committed is contradicted.**  `GradedFiveLive` claims only the stage-four and
`gamma_3` exclusions at its point (`sqRelWord_liveBlkWit_diag_ne_one` and its siblings) and
never a `gamma_2` one, so this is not a refutation of anything published.  What it removes is
the hope that the new point is a fresh place for the class-five stack to stand one filtration
step wider: it is not.  ⭐ `liveCenKill_not_stageFour_achievable` marks the boundary exactly,
as at wave 60's point: the killer is NOT an achievable stage-four dressing, because
`GradedFiveStageFour.forceLcs_two_le_stageN3` forces those to have even class-four coordinate
and this one's is `3`.

## PROVED versus MEASURED

**PROVED** (this file and, since the fold below, `GradedGammaTwoCensus`; no `sorry`, no new
axiom, no `native_decide`): the single-commutator form of the killer; its achievability at
`gamma_2`; the kill; the central shift `liftO 7`; the failure of all three `gamma_2` lines; the
exclusion of the killer from the achievable stage-four lattice; and the shared `x0` slot.  All at
every handle count and every handle.

**MEASURED** (`scripts/w64_verify/task_b_live5_kill.py`, certified output in
`scripts/w64_verify/results/task_b.txt`): the achievable `gamma_2` lattice at the live point is
`2^26` and is EXACTLY the same box `{z gamma_2-shaped : f, g, h, j even}` that wave 63 measured
at its point, so the killer is not merely achievable but sits in a lattice of the same shape;
the exhaustive sigma-slot sweep, which counts how many achievable sigma dressings kill; and the
general form of the mechanism, which this file measured but did not prove -

✅ **the general form of the mechanism is now PROVED**, in
`GradedGammaTwoCensus.sqRelWord_fiveTuple_censKnob`: at every five-tuple
`fiveTuple R h j S X Y U V` over **any commutative ring**, dressing the sigma slot by `<m = t>`
multiplies the relator by `SqU6.liftO (X.e * t)`, with no hypothesis on `S`, `Y`, `U`, `V`, the
handle count or the handle.  Since `GradedGammaTwoCensus.censKnob_eq_gaTwoCenKill` identifies
`gaTwoCenKill` with `SqU6.censKnob 3` by `rfl`, this file's kill and wave 63's are both
corollaries of that identity, and the vulnerability is a property of the WITNESS STANDARD - which
demands an odd `x0.e` and an odd diagonal residue - rather than of two points.

## ⭐ Folded onto the census (W66-CONSOLEGAL, finished by W67-HOUSE)

Results proved twice - once here as a decide at this point, once in `GradedGammaTwoCensus` as a
corollary of the ring-level knob identity - now route through the census, which is the stronger
derivation, and this file imports it:

| here | now proved by |
|---|---|
| `gaTwoForces_liveBlkWit_false` | `GradedGammaTwoCensus.liveBlkWit_lines_false` `.1` |
| `gaTwoCentral_liveBlkWit_false` | the same, `.2.1` |
| `gaTwoOrth_liveBlkWit_false` | the same, `.2.2` |
| `sqRelWord_liveBlkWit_cenKill` | `GradedGammaTwoCensus.sqRelWord_liveBlkWit_censKnob` |
| `cenSigDress_liveCenKill_mem` | `GradedGammaTwoCensus.liveBlk_censKnob_mem` |
| `liveCenKill_not_stageFour_achievable` | `GradedGammaTwoCensus.censKnob_odd_not_mem_stageN3` |

⚠ **Every surviving name and every surviving statement is unchanged**; only proofs moved.  W66
left six results unfolded, with reasons; W67-HOUSE settled all six, one by folding, one by
retiring and four by keeping with the reason recorded on the declaration itself.

* **FOLDED (1).**  `liveCenKill_not_stageFour_achievable` read
  `GradedGammaTwoCentral.gaTwoCenKill_not_mem_stageN3`, a `decide` at this one killer.  The
  census's `censKnob_odd_not_mem_stageN3` proves the same for EVERY odd knob parameter, and
  `gaTwoCenKill` is the knob at `t = 3` by `rfl`, so the exclusion is now a corollary of the
  general statement, exactly as the other five are.
* **RETIRED (1).**  `cenSigDress_liveBlkWit` said that dressing the sigma slot of the live point
  moves the sigma parameter.  It was `GradedGammaTwoCentral.conFiveDress_fiveTuple_cenSigDress`
  plus `mul_assoc`; it was read by no proof in this file after the W66 fold and by nothing
  anywhere in the tree, this module's only importer being `GQ2.lean`.  The census reaches every
  reparametrisation it needs from the generic lemma directly, in `sqRelWord_cenSigDress_censKnob`,
  which is where the reparametrisation now lives.  Its old section 2 is gone and the sections
  below are renumbered.
* **KEPT (4)**, each with its own irreducibility note on the declaration: `liveCen_shared_x0` and
  `liveCen_knob` are the tree's only statements about the slot the two points share and about its
  two coordinate facts here, and since the fold they explain rather than carry;
  `gaTwoShift_liveBlkWit_cenKill` is the tree's only statement giving a `SqU6.gaTwoShift` a
  VALUE; and `liveCenKill_comm_form` is a genuinely different certificate from the census's
  `liveBlk_censKnob_comm_form`, though not a like-for-like one - see its docstring.

## Merge notes

⚠ This list is the names the file's CODE reads, re-derived at W67-HOUSE; the W66 list had seven
entries the fold had already made stale, and they are gone.

Reused: `liveBlkSig`, `liveBlkU`, `liveBlkV`, `liveBlkWit`, `liveBlkImage`,
`liveBlkImage_le_stageN1`, `sqRelWord_liveBlkWit_diag` (`GradedFiveLive`); `gaTwoCenKill`,
`gaTwoCenKill_isGaTwo`, `cenSigDress`, `GaTwoForces`, `GaTwoCentral`, `GaTwoOrth`,
`cenKill_mechanism` (`GradedGammaTwoCentral`); `stageX`, `stageWit`, `forceLcs_two_le_stageN3`
(`GradedFiveStageFour`); `censKnob_eq_gaTwoCenKill`, `cens_sigDress_mem_forceLcs`,
`liveBlk_censKnob_mem`, `liveBlkWit_lines_false`, `sqRelWord_liveBlkWit_censKnob`,
`censKnob_odd_not_mem_stageN3` (`GradedGammaTwoCensus`, the first five new with the
W66-CONSOLEGAL fold and the last with the W67-HOUSE fold); `commP` (`GradedFiveNecessity`);
`forceLcs` (`GradedFiveForce`); `fiveTuple_one`, `SqU6.liftO`, `SqU6.liftO_mul_liftO`,
`SqU6.isGaTwo_one`, `SqU6.sqRelWord_gaTwoDress`, `sqRelWord`, `selPar`, `sqRank`
(`GradedFive`, `Cores`).  New public names carry the `liveCen`
prefix except the five `_liveBlkWit_` theorems, which name the point they are about, and
`cenSigDress_liveCenKill_mem`, which is named for the dressing it applies.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8`, on tuples over it, or
on `ZMod 2` (`selPar` lands there, and the W67-HOUSE fold of
`liveCenKill_not_stageFour_achievable` onto the census's general odd-knob exclusion discharges its
oddness hypothesis that way).
-/

open scoped commutatorElement

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

/-! ## 1 The shared slot -/

section Shared

variable {h : ℕ} {j : Fin h}

/-- ⭐ **The two points share their `x0` slot.**  `GradedGammaTwoCentral.cenKill_mechanism`
reads `stageX.e`, and the live point's `x0` slot is `stageX` unchanged.

⚠ Since the W66 fold this EXPLAINS rather than carries.  The kill now runs off
`GradedGammaTwoCensus.sqRelWord_liveBlkWit_censKnob`, a corollary of a ring-level identity that
reads the `x0` slot's `e` coordinate generically and never asks whether two points share a slot.
KEPT as the tree's only statement of the coincidence; `liveCen_knob` reads it. -/
theorem liveCen_shared_x0 : stageWit h j stageX 1 = liveBlkWit h j stageX 1 := by
  rw [stageWit, liveBlkWit, fiveTuple_one, fiveTuple_one]

/-- …and the knob is the same unit.  Two coordinate facts about the shared `x0` slot: its `e`
coordinate is ODD, and `x0.e * gaTwoCenKill.m = 7`.  Both are ring identities about the slot; that
the sigma-slot dressing by `gaTwoCenKill` actually shifts the relator by `liftO 7` is the separate
`gaTwoShift_liveBlkWit_cenKill` in section 2.

⚠ KEPT with no consumer.  It is the numerical input to
`GradedGammaTwoCensus.sqRelWord_cenSigDress_censKnob` at this point: that identity multiplies the
relator by `liftO (X.e * t)`, and here `X.e * t = 5 * 3 = 7`, which is what makes the `liftO 7`
below a computation rather than a coincidence.  Stated nowhere else in the tree. -/
theorem liveCen_knob : selPar (liveBlkWit h j stageX 1).e = 1
    ∧ (liveBlkWit h j stageX 1).e * gaTwoCenKill.m = 7 := by
  rw [← liveCen_shared_x0, stageWit, fiveTuple_one]
  exact ⟨cenKill_mechanism.1, cenKill_mechanism.2.2⟩

end Shared

/-! ## 2 The killer, achievable at the live point -/

section Kill

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐ **The killer is a SINGLE commutator of elements of the live point's own image.**  Wave
60's point - the one `GradedGammaTwoCentral` works at - needed a product of two; here the moved
sigma mark and the new handle letters put it one commutator away.

⚠ Not a like-for-like comparison with the census's `liveBlk_censKnob_comm_form`, which is a
product of TWO commutators whose four arguments are all SLOTS of the tuple.  One argument here,
`liveBlkV * liveBlkU⁻¹`, is a product of two slots and not a slot, so this trades a commutator
for a longer argument.  Both land in the honest `gamma_2` of the image and either certifies
achievability.

⚠ KEPT with no consumer: a different statement from the census's, and the census's is what
`cenSigDress_liveCenKill_mem` now takes. -/
theorem liveCenKill_comm_form :
    gaTwoCenKill = commP (liveBlkSig * stageX) (liveBlkV * liveBlkU⁻¹) := by decide

/-- ⭐⭐ **The sigma-slot dressing by the killer is ACHIEVABLE at the live point**: every slot
lies in `forceLcs (liveBlkImage h j stageX) 1`, the honest `gamma_2` of the image.

Proved through `GradedGammaTwoCensus.liveBlk_censKnob_mem`, which puts the knob itself in the
`gamma_2` of the image, and `cens_sigDress_mem_forceLcs`, which spreads a sigma-slot element
across the slots.  ⚠ It no longer reads `liveCenKill_comm_form`; the census reaches the same
membership by its own two-commutator certificate. -/
theorem cenSigDress_liveCenKill_mem (i : Fin (sqRank h)) :
    cenSigDress h gaTwoCenKill i ∈ forceLcs (liveBlkImage h j stageX) 1 :=
  cens_sigDress_mem_forceLcs (by rw [censKnob_eq_gaTwoCenKill]; exact liveBlk_censKnob_mem) i

/-- ⭐⭐⭐ **THE KILL.**  At the live point's diagonal dressing, at every handle count and every
handle, the achievable `gamma_2`-dressing `gaTwoCenKill` on the sigma slot kills the dressed
frame outright.

Proved through `GradedGammaTwoCensus.sqRelWord_liveBlkWit_censKnob`, i.e. off the ring-level knob
identity, where this file originally decided it at the point. -/
theorem sqRelWord_liveBlkWit_cenKill (h : ℕ) (j : Fin h) :
    sqRelWord (conFiveDress (liveBlkWit h j stageX) (cenSigDress h gaTwoCenKill)) = 1 := by
  rw [censKnob_eq_gaTwoCenKill]
  exact sqRelWord_liveBlkWit_censKnob h j

/-- ⭐⭐⭐ **The `gamma_2` forcing FAILS at the live point**: the residue is odd and an
achievable `gamma_2`-dressing kills.  W63-LIVE5's point is NOT a fresh place to stand one
filtration step wider.

Proved through `GradedGammaTwoCensus.liveBlkWit_lines_false`, whose statement is exactly the
conjunction of this theorem and its two siblings below. -/
theorem gaTwoForces_liveBlkWit_false (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (liveBlkWit h j stageX) := (liveBlkWit_lines_false h j).1

/-- ⭐⭐ **The killing dressing acts CENTRALLY**, with the odd class-five row `7`, so it refutes
the centrality line and not merely the parity line.

⚠ KEPT: this is the tree's only statement giving a `SqU6.gaTwoShift` a VALUE.  The census and
`GradedGammaTwoCentral` carry shift facts only as hypotheses of the shape
`gaTwoShift h m z = SqU6.liftO w → …`, or existentially inside proofs, so there is nothing here
to fold onto. -/
theorem gaTwoShift_liveBlkWit_cenKill (h : ℕ) (j : Fin h) :
    SqU6.gaTwoShift h (liveBlkWit h j stageX) (cenSigDress h gaTwoCenKill) = SqU6.liftO 7 := by
  have hga : ∀ i, (cenSigDress h gaTwoCenKill i).IsGaTwo := by
    intro i
    by_cases hi : (i : ℕ) = 0
    · rw [cenSigDress, if_pos hi]
      exact gaTwoCenKill_isGaTwo
    · rw [cenSigDress, if_neg hi]
      exact SqU6.isGaTwo_one
  have hid := SqU6.sqRelWord_gaTwoDress (m := liveBlkWit h j stageX) hga
  rw [sqRelWord_liveBlkWit_cenKill, sqRelWord_liveBlkWit_diag] at hid
  refine mul_left_cancel (a := SqU6.liftO (1 : gr3R)) ?_
  rw [← hid, SqU6.liftO_mul_liftO]
  decide

/-- ⭐⭐⭐ **…so the CENTRALITY LINE FAILS at the live point too.**

Proved through `GradedGammaTwoCensus.liveBlkWit_lines_false`.  ⚠ The census route does not read
`gaTwoShift_liveBlkWit_cenKill`, so that theorem is no longer a step here; it survives as the
record of the shift's VALUE, `liftO 7`, which the census does not state. -/
theorem gaTwoCentral_liveBlkWit_false (h : ℕ) (j : Fin h) :
    ¬ GaTwoCentral (liveBlkWit h j stageX) := (liveBlkWit_lines_false h j).2.1

/-- ⭐⭐ …and so does the parity line, which the centrality line implies.  Proved through
`GradedGammaTwoCensus.liveBlkWit_lines_false`, which carries all three lines together. -/
theorem gaTwoOrth_liveBlkWit_false (h : ℕ) (j : Fin h) :
    ¬ GaTwoOrth (liveBlkWit h j stageX) := (liveBlkWit_lines_false h j).2.2

end Kill

/-! ## 3 The boundary: the stage-four exclusions are untouched -/

section Boundary

variable {h : ℕ} {j : Fin h}

/-- ⭐ **The killing element is NOT an achievable stage-four dressing at the live point.**
`GradedFiveLive.forceLcs_liveBlkHom_le_stageN3`'s chain forces every element of
`forceLcs (liveBlkImage h j stageX) 2` into `stageN3`, whose class-four coordinate is EVEN;
`gaTwoCenKill`'s is `3`.  So `GradedFiveLive`'s stage-four and `gamma_3` exclusions stand.

⭐ Folded onto the census (W67-HOUSE).  It read `GradedGammaTwoCentral.gaTwoCenKill_not_mem_stageN3`,
a `decide` at this one killer; `GradedGammaTwoCensus.censKnob_odd_not_mem_stageN3` proves the
same for EVERY odd knob parameter, and `gaTwoCenKill` is the knob at `t = 3`
(`censKnob_eq_gaTwoCenKill`, by `rfl`).  The statement is unchanged. -/
theorem liveCenKill_not_stageFour_achievable (h : ℕ) (j : Fin h) :
    gaTwoCenKill ∉ forceLcs (liveBlkImage h j stageX) 2 :=
  fun hz => censKnob_odd_not_mem_stageN3 (t := 3) (by decide)
    (forceLcs_two_le_stageN3 (liveBlkImage_le_stageN1 ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩) hz)

end Boundary

/-! ## 4 Axiom pins -/

section AxiomPins

#print axioms liveCen_shared_x0
#print axioms liveCen_knob
#print axioms liveCenKill_comm_form
#print axioms cenSigDress_liveCenKill_mem
#print axioms sqRelWord_liveBlkWit_cenKill
#print axioms gaTwoForces_liveBlkWit_false
#print axioms gaTwoShift_liveBlkWit_cenKill
#print axioms gaTwoCentral_liveBlkWit_false
#print axioms gaTwoOrth_liveBlkWit_false
#print axioms liveCenKill_not_stageFour_achievable

end AxiomPins

end SqCore

end Dyadic

end GQ2
