/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFiveLive
import GQ2.Dyadic.SqCore.GradedGammaTwoCentral

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

⭐⭐ `liveCenKill_comm_form`: at the live point the killer is achievable by a **single** honest
commutator of the point's own letters, `commP (liveBlkSig * stageX) (liveBlkV * liveBlkU⁻¹)`,
where wave 63's point needed a product of two.  `cenSigDress_liveCenKill_mem` turns that into
membership of `forceLcs (liveBlkImage h j stageX) 1`.

⭐ `liveCen_shared_x0`: the one-line reason.  `stageWit h j stageX 1 = liveBlkWit h j stageX 1`,
both `stageX`, so `GradedGammaTwoCentral.cenKill_mechanism` - `selPar stageX.e = 1` and
`stageX.e * gaTwoCenKill.m = 7` - is a statement about a slot the two points SHARE.  Moving the
sigma mark from `E_23` to `E_23 E_45` and re-solving the `x1` slot changes neither.

## ⚠ What this does and does not touch

**Nothing committed is contradicted.**  `GradedFiveLive` claims only the stage-four and
`gamma_3` exclusions at its point (`sqRelWord_liveBlkWit_diag_ne_one` and its siblings) and
never a `gamma_2` one, so this is not a refutation of anything published.  What it removes is
the hope that the new point is a fresh place for the class-five stack to stand one filtration
step wider: it is not.  ⭐ `liveCenKill_not_stageFour_achievable` marks the boundary exactly,
as at wave 63's point: the killer is NOT an achievable stage-four dressing, because
`GradedFiveStageFour.forceLcs_two_le_stageN3` forces those to have even class-four coordinate
and this one's is `3`.

## PROVED versus MEASURED

**PROVED** (this file, no `sorry`, no new axiom, no `native_decide`): the reparametrisation of
the live point by a sigma-slot dressing; the commutator form of the killer and hence its
achievability at `gamma_2`; the kill; the central shift `liftO 7`; the failure of all three
`gamma_2` lines; the exclusion of the killer from the achievable stage-four lattice; and the
shared `x0` slot.  All at every handle count and every handle.

**MEASURED** (`scripts/w64_verify/task_b_live5_kill.py`, certified output in
`scripts/w64_verify/results/task_b.txt`): the achievable `gamma_2` lattice at the live point is
`2^26` and is EXACTLY the same box `{z gamma_2-shaped : f, g, h, j even}` that wave 63 measured
at its point, so the killer is not merely achievable but sits in a lattice of the same shape;
the exhaustive sigma-slot sweep, which counts how many achievable sigma dressings kill; and one
general identity that is NOT proved here and is the natural target -

⚠ **the general form of the mechanism, MEASURED ONLY**: at every five-tuple
`fiveTuple R h j S X Y U V` over `ZMod 8`, dressing the sigma slot by `<m = t>` multiplies the
relator by `SqU6.liftO (t * X.e)`, with no hypothesis on `S`, `Y`, `U`, `V`, the handle count or
the handle (3000 random tuples, 0 failures).  If that were proved, both this file's kill and
wave 63's would be corollaries, and the vulnerability would be visibly a property of the WITNESS
STANDARD - which demands an odd `x0.e` and an odd diagonal residue - rather than of two points.

## Merge notes

Reused: `liveBlkSig`, `liveBlkU`, `liveBlkV`, `liveBlkWit`, `liveBlkWit_zero`,
`liveBlkWit_handleU`, `liveBlkWit_handleV`, `liveBlkImage`, `liveBlkImage_le_stageN1`,
`sqRelWord_liveBlkWit_diag` (`GradedFiveLive`); `gaTwoCenKill`, `gaTwoCenKill_isGaTwo`,
`gaTwoCenKill_not_mem_stageN3`, `cenSigDress`, `conFiveDress_fiveTuple_cenSigDress`,
`GaTwoForces`, `GaTwoCentral`, `GaTwoOrth`, `gaTwoCentral_of_gaTwoOrth`, `cenKill_mechanism`
(`GradedGammaTwoCentral`); `stageX`, `stageWit`, `forceLcs_two_le_stageN3`, `stageN3`
(`GradedFiveStageFour`); `commP`, `commP_mem_commSub` (`GradedFiveNecessity`); `forceLcs`
(`GradedFiveForce`); `fiveTuple`, `sqRelWord_fiveTuple`, `SqU6.liftO`, `selPar`
(`GradedFive`, `Cores`).  New public names all carry the `liveCen` prefix except the four
`_liveBlkWit_` theorems, which name the point they are about.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`; every `decide` is on `ZMod 8` or tuples over it.
-/

open scoped commutatorElement

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

/-! ## 1 The shared slot -/

section Shared

variable {h : ℕ} {j : Fin h}

/-- ⭐ **The two points share their `x0` slot.**  This is the whole reason wave 63's kill
transports: `GradedGammaTwoCentral.cenKill_mechanism` reads `stageX.e`, and the live point's
`x0` slot is `stageX` unchanged. -/
theorem liveCen_shared_x0 : stageWit h j stageX 1 = liveBlkWit h j stageX 1 := by
  rw [stageWit, liveBlkWit, fiveTuple_one, fiveTuple_one]

/-- …and the knob is the same unit: `stageX.e = 5` is odd and `stageX.e * gaTwoCenKill.m = 7`,
so the sigma-slot dressing by `gaTwoCenKill` moves the class-five row by `7`. -/
theorem liveCen_knob : selPar (liveBlkWit h j stageX 1).e = 1
    ∧ (liveBlkWit h j stageX 1).e * gaTwoCenKill.m = 7 := by
  rw [← liveCen_shared_x0, stageWit, fiveTuple_one]
  exact ⟨cenKill_mechanism.1, cenKill_mechanism.2.2⟩

end Shared

/-! ## 2 The sigma dressing reparametrises the live point -/

section Reparam

variable {h : ℕ} {j : Fin h}

/-- Dressing the sigma slot of the live point moves the sigma PARAMETER, exactly as
`GradedGammaTwoCentral.cenSigDress_stageWit` does at wave 60's point. -/
theorem cenSigDress_liveBlkWit (v w : SqU6 gr3R) :
    conFiveDress (liveBlkWit h j v) (cenSigDress h w) = liveBlkWit h j (v * w) := by
  rw [liveBlkWit, liveBlkWit, conFiveDress_fiveTuple_cenSigDress, mul_assoc]

end Reparam

/-! ## 3 The killer, achievable at the live point -/

section Kill

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐ **The killer is a SINGLE honest commutator of the live point's own letters.**  Wave
63's point needed a product of two; here the moved sigma mark and the new handle letters put it
one commutator away. -/
theorem liveCenKill_comm_form :
    gaTwoCenKill = commP (liveBlkSig * stageX) (liveBlkV * liveBlkU⁻¹) := by decide

/-- ⭐⭐ **…so the sigma-slot dressing by the killer is ACHIEVABLE at the live point**: every
slot lies in `forceLcs (liveBlkImage h j stageX) 1`, the honest `gamma_2` of the image. -/
theorem cenSigDress_liveCenKill_mem (i : Fin (sqRank h)) :
    cenSigDress h gaTwoCenKill i ∈ forceLcs (liveBlkImage h j stageX) 1 := by
  by_cases hi : (i : ℕ) = 0
  · rw [cenSigDress, if_pos hi]
    have hS : liveBlkSig * stageX ∈ liveBlkImage h j stageX :=
      Subgroup.subset_closure ⟨0, by rw [liveBlkWit_zero]⟩
    have hU : liveBlkU ∈ liveBlkImage h j stageX :=
      Subgroup.subset_closure ⟨sqHandleIdxU j, by rw [liveBlkWit_handleU]⟩
    have hV : liveBlkV ∈ liveBlkImage h j stageX :=
      Subgroup.subset_closure ⟨sqHandleIdxV j, by rw [liveBlkWit_handleV]⟩
    rw [liveCenKill_comm_form]
    exact commP_mem_commSub hS (mul_mem hV (inv_mem hU))
  · rw [cenSigDress, if_neg hi]
    exact one_mem _

/-- ⭐⭐⭐ **THE KILL.**  At the live point's diagonal dressing, at every handle count and every
handle, the achievable `gamma_2`-dressing `gaTwoCenKill` on the sigma slot kills the dressed
frame outright. -/
theorem sqRelWord_liveBlkWit_cenKill (h : ℕ) (j : Fin h) :
    sqRelWord (conFiveDress (liveBlkWit h j stageX) (cenSigDress h gaTwoCenKill)) = 1 := by
  rw [cenSigDress_liveBlkWit, liveBlkWit, sqRelWord_fiveTuple]
  decide

/-- ⭐⭐⭐ **The `gamma_2` forcing FAILS at the live point**: the residue is odd and an
achievable `gamma_2`-dressing kills.  W63-LIVE5's point is NOT a fresh place to stand one
filtration step wider. -/
theorem gaTwoForces_liveBlkWit_false (h : ℕ) (j : Fin h) :
    ¬ GaTwoForces (liveBlkWit h j stageX) := by
  intro hF
  have hb := hF (cenSigDress h gaTwoCenKill) (fun i => cenSigDress_liveCenKill_mem i)
    (sqRelWord_liveBlkWit_cenKill h j)
  rw [sqRelWord_liveBlkWit_diag, SqU6.liftO_o, selPar_one] at hb
  exact absurd hb (by decide)

/-- ⭐⭐ **The killing dressing acts CENTRALLY**, with the odd class-five row `7`, so it refutes
the centrality line and not merely the parity line. -/
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

/-- ⭐⭐⭐ **…so the CENTRALITY LINE FAILS at the live point too.** -/
theorem gaTwoCentral_liveBlkWit_false (h : ℕ) (j : Fin h) :
    ¬ GaTwoCentral (liveBlkWit h j stageX) := by
  intro hC
  obtain ⟨t, ht⟩ := hC (cenSigDress h gaTwoCenKill) 7 (fun i => cenSigDress_liveCenKill_mem i)
    (gaTwoShift_liveBlkWit_cenKill h j)
  exact (by decide : ∀ t : gr3R, (7 : gr3R) ≠ 2 * t) t ht

/-- ⭐⭐ …and so does the parity line, which the centrality line implies. -/
theorem gaTwoOrth_liveBlkWit_false (h : ℕ) (j : Fin h) :
    ¬ GaTwoOrth (liveBlkWit h j stageX) :=
  fun hO => gaTwoCentral_liveBlkWit_false h j (gaTwoCentral_of_gaTwoOrth hO)

end Kill

/-! ## 4 The boundary: the stage-four exclusions are untouched -/

section Boundary

variable {h : ℕ} {j : Fin h}

/-- ⭐ **The killing element is NOT an achievable stage-four dressing at the live point.**
`GradedFiveLive.forceLcs_liveBlkHom_le_stageN3`'s chain forces every element of
`forceLcs (liveBlkImage h j stageX) 2` into `stageN3`, whose class-four coordinate is EVEN;
`gaTwoCenKill`'s is `3`.  So `GradedFiveLive`'s stage-four and `gamma_3` exclusions stand. -/
theorem liveCenKill_not_stageFour_achievable (h : ℕ) (j : Fin h) :
    gaTwoCenKill ∉ forceLcs (liveBlkImage h j stageX) 2 :=
  fun hz => gaTwoCenKill_not_mem_stageN3
    (forceLcs_two_le_stageN3 (liveBlkImage_le_stageN1 ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩) hz)

end Boundary

/-! ## 5 Axiom pins -/

section AxiomPins

#print axioms liveCen_shared_x0
#print axioms liveCen_knob
#print axioms cenSigDress_liveBlkWit
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
