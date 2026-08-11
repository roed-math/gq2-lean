/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedGammaTwoPoint
import GQ2.Dyadic.SqCore.GradedStageNecessity

/-!
# W63-CENTRAL2: the `gamma_2` centrality line at class five, and the KILL that decides it

Two lanes pointed here.  `GradedStageNecessity` (wave 61) proved that at stage four the sharp
line is **centrality** rather than parity, and `GradedGammaTwoPoint` (wave 62) closed the parity
route one filtration step wider by a functional collision, leaving a **conditional** widening:
at wave 60's binder point no achievable `gamma_2`-dressing with an EVEN three-channel functional
kills the dressed frame.  The question both lanes left was whether restating that widening on
CENTRALITY - a `ZMod 8` condition, strictly finer than any mod-`2` reading - makes it
unconditional.

It does not, and the reason is not subtle.

## ⭐⭐⭐ Headline: WAVE 60's EXCLUSION DOES NOT SURVIVE ONE FILTRATION STEP WIDER

⭐⭐⭐ `sqRelWord_stageWit_cenKill`.  At wave 60's own binder point, at **every** handle count
and **every** handle, the achievable `gamma_2`-dressing carrying `gaTwoCenKill = <m = 3>` on the
**sigma slot** and `1` on every other slot **kills the dressed frame outright**.  Its dressing
is achievable - `cenSigDress_cenKill_mem` writes it as
`commP (sigma x0)^{-1} u_j ^ 2 * commP x1 (x0 u_j)`, the product of a SQUARED commutator and a
commutator of the point's own letters (the displayed `^ 2` is on the first factor) - and the
residue there is `1`, odd.  So

* ⭐⭐⭐ `gaTwoForces_stageWit_false`: the `gamma_2` forcing FAILS at wave 60's point;
* ⭐⭐⭐ `gaTwoCentral_stageWit_false`, `gaTwoOrth_stageWit_false`: so do the centrality line
  and the parity line, since each implies the forcing.

⚠ This is the question `GradedStageFrame` recorded as open in exactly these words - "one
filtration step wider again, `gamma_2`-dressings, is neither proved nor refuted, here or
anywhere in the tree" - and it is now **refuted at the MARKING-TUPLE level**.
⚠ `GradedStageFrame` records the question of its **frame/hom-level** composite, and everything
proved here is about tuples in `SqU6 gr3R`; the hom-level form of the question is therefore
refuted only modulo the lift the Scope section below leaves undone.

Wave 62's even-channel hypothesis is therefore **load-bearing** and cannot be removed by any
restatement: without it the conclusion is false.
⭐ `cenKill_chan_odd` closes the circle: the killing dressing's three-channel
functional is **odd**, exactly as wave 62's transport predicts of any kill at an odd residue.
⚠ Only its parity is proved; no theorem here names its value.  The `7` that does appear in this
file is `gaTwoShift_stageWit_cenKill`'s, the shift's `o`-row, which is a different quantity.

## ⭐⭐⭐ Nothing committed is contradicted, and the boundary is exact

`gaTwoCenKill_not_stageFour_achievable`: the killing element is **not** an achievable
stage-four dressing.  It is `gamma_3`-SHAPED (`gaTwoCenKill_isGaThree`), so what is new is not
its shape but its **provenance**: `GradedFiveStageFour.forceLcs_two_le_stageN3` forces every
achievable stage-four dressing to have an EVEN class-four coordinate `m`, and the honest
`gamma_2` of the image does not.  Wave 60's `sqRelWord_stageWit_diag_ne_one` and wave 62's
`sqRelWord_stageWit_diag_gaTwo_ne_one` both stand; what dies is the hope of dropping their
hypotheses.

⭐ **The mechanism, in one line.**  `GradedFiveStageFour.gaThreePair` pairs a sigma-slot
dressing's class-four coordinate against `x0.e`, and wave 60's point needs `stageX.e = 5` ODD -
that is the very channel its class-five residue runs on (`stageX_gauge`).  A unit coefficient on
a coordinate that the wider lattice leaves free is a knob that reaches every residue, `0`
included.  The point's separating feature and its killable feature are the same feature.

## ⭐⭐ What the centrality line still buys, and it is a real theorem

The three `gamma_2` lines are defined and the implications that transpose from stage four are
proved: `gaTwoCentral_of_gaTwoOrth` (free, no hypothesis at all) and
⭐⭐ `gaTwoForces_of_gaTwoCentral` (at a relator that is a central translation).  So the sharp
line is still SUFFICIENT one filtration step wider, and the refutation above propagates through
it rather than around it.

⭐⭐ `gaTwoCentral_iff_chan` answers the lane's second question exactly: inside the family where
wave 61's transport applies, `GaTwoCentral m` **is** the statement that every achievable
dressing acting centrally has an even three-channel functional.  Centrality is the parity line
read on the central tuples and nothing else, so wave 62's collision does apply to it - and
⭐⭐ `stageWit_gaTwoSlotTwo_not_central` shows the two lines are nonetheless SEPARATED at wave
60's point: wave 62's odd-channel witness `[x0, x1]` on the `x1` slot leaves a dressed RELATOR
`<j = 4, l = 6, o = 6>` that is not a central translation.  ⚠ Read the quantifier: `GaTwoCentral`
is a condition on the SHIFT `SqU6.gaTwoShift`, not on the dressed relator, and the bridge between
the two - `SqU6.sqRelWord_gaTwoDress` at a marking whose own relator is central - exists but is
not invoked in the theorem.  ⚠ And that this dressing is a counterexample to the PARITY line is
`GradedGammaTwoPoint`'s result, inherited, not reproved here; what is proved here is the
non-centrality alone.  The refutation genuinely needed a new dressing, and the one section 4
produces is central.

## ⭐⭐ The `ZMod 8` mechanism of `GradedStageSeparate` reproduces one filtration step wider

`gaTwoCentral_x1_f_even` and its `_g_`, `_h_`, `_i_` siblings: a `gamma_2` shift that is a
central translation forces the `x1`-slot dressing's own **class-two** coordinates `f`, `g`, `h`,
`i` to be EVEN, at every marking and with no achievability at all, because the shift's four
class-two rows are the Frobenius weights `-4 (z 1).x + 2 (z 2).x` and nothing else
(`SqU6.gaTwoShift_f`, `_g`, `_h`, and the committed `_i`), and `2 b = 4 a` in `ZMod 8` forces
`b` even.  Mod `2` the same equation is vacuous.  That is `GradedStageSeparate`'s
`stageCentral_x1_j_even` one class down, at FOUR coordinates instead of three, and **one** of
them (`i`) is not even on the achievable lattice, so the sharpening is not empty.

⚠ **An earlier reading of this sentence named `g` as well, and the file's own MEASURED block
below refutes it**: the achievable `gamma_2` lattice at the point is exactly
`{z gamma_2-shaped : f, g, h, j even}`, so `g` is already even there and the `g` half of the
sharpening is redundant.  (Re-measured independently at both class-five points in
`docs/dyadic/w64-verify-note.md` section 0.5: `<g=1>` is in neither lattice.)

⚠ **And it is not enough at wave 60's point**, which is worth recording precisely: the only
channel coordinate it reaches is `(z 2).i`, and at that point every letter has `L.j = 0`, so the
`i`-channel is silent there.  The `ZMod 8` sharpening is real and it is not what decides this
point.

## PROVED versus MEASURED

**PROVED** (this file, no `sorry`, no new axiom, no `native_decide`): the three lines and the
two implications; the `ZMod 8` sharpening over `ZMod 8`; the sigma-slot dressing as a
reparametrisation (`conFiveDress_fiveTuple_cenSigDress`, over any commutative ring;
`cenSigDress_stageWit` is its instance at the binder point and is `gr3R`-only); the
kill, its achievability certificate, its shift `SqU6.liftO 7`, its odd channel, and the failure
of all three lines, at every handle count and every handle; that the killing element is
`gamma_3`-shaped and NOT achievable at stage four; and the separation from wave 62's witness.

**MEASURED** (`scripts/w63_central2/`, certified output in `results/derive.txt`, **66** named
checks and **0** failures, on wave 59's honest `6 x 6` matrices with the shift read off the
relator rather than from any emitted form):

* the achievable `gamma_2` lattice at the point, by an exact polycyclic sift, is
  `67108864 = 2^26` elements and is EXACTLY `{z gamma_2-shaped : f, g, h, j even}` - the same
  count `GradedStageFrame` reports for `gamma_2` of the same image, by a different method;
* `forceLcs H 2` is `2^13` and contains `<m = 2>` but not `<m = 1>`, so the killer sits
  strictly between the two lattices;
* the `gamma_2` shift is **not** a homomorphism of the dressing tuple (it fails at `192` of
  `200` random achievable five-slot pairs, and at `77` to `185` of `200` per slot), which is why
  wave 61's `stageCentral_of_stageForces` engine - a power argument - does not transpose, so
  the CONVERSE `GaTwoForces -> GaTwoCentral` is not available here and is not claimed;
* the slot-`0` dressing by `<m = t>` has shift `SqU6.liftO (5 t)` for `t = 0, ..., 7`, so the
  sigma slot's class-four coordinate is a unit knob on the whole of `ZMod 8`;
* **the sigma slot exhaustively** (`results/sweep_sigma.txt`, `6` more named checks and `0`
  failures): the sigma-slot shift ignores the dressing's `i`, `j` and `o`, so the sweep over
  the remaining seven coordinates is exhaustive, and of its `262144` dressings `4096` act
  centrally, `2048` of those move the class-five row ODDLY and `512` KILL - one eighth of the
  central ones, exactly what equidistribution over `ZMod 8` predicts.  Scaled back, `131072` of
  the `67108864` achievable dressings kill.  The theorem below exhibits one of them; it is not
  a lucky one.

## Scope, honestly

* **Marking-tuple level, not hom level.**  Like `GradedFiveGammaTwo` and `GradedGammaTwoPoint`
  this file works with tuples in `SqU6 gr3R`; nothing here claims the killing dressing is the
  image of a continuous homomorphism on `D_sq h`.  ⭐ It is however the image of an explicit
  element of the commutator subgroup of the frame - the certificate's two factors are a SQUARED
  commutator and a commutator of the letters, which are `stageFrameHom`-images of `sigma * x0`,
  `x0`, `x1`, `u_j` - so a hom-level lift is a bookkeeping exercise and not a new mathematical
  step.  It is left undone here and named in the landing report.
* **What is refuted is the WIDENING, not wave 60.**  `sqRelWord_stageWit_diag_ne_one` quantifies
  over `forceLcs (stageImage) 2` and is untouched; this file exhibits a kill in
  `forceLcs (stageImage) 1`.
* **The converse of the characterisation is not proved and not refuted.**  At stage four wave 61
  had `stageForces_iff_stageCentral`; here only `gaTwoForces_of_gaTwoCentral` is available,
  because the shift is not multiplicative.  At wave 60's point the question is moot - all three
  lines are false - so no counterexample to the converse is offered either.
* **This is a refutation at ONE point.**  It is wave 60's own point, the one the committed
  exclusions are stated at, and the mechanism reads only `x0.e` odd plus an odd class-four
  coordinate in the achievable `gamma_2` lattice; but no census over other binder points was
  run, so "every binder point with an odd `x0.e` is killable" is a conjecture and is not
  claimed.

## The sweep against the tree's refutations

Doctrine rule 4, item by item.  ⭐ **The sharpest bound** (rule 1) is used where the file
concludes something SURVIVES: `gaTwoCenKill_not_stageFour_achievable` bounds the achievable
stage-four lattice by `stageN3`, which is the sharpest containment the tree owns, and the
measurement goes further and computes that lattice EXACTLY (`2^13` elements, `<m = 1>` absent),
so the conclusion does not rest on slack.  ⭐ **Composites** (rule 3) are checked:
`cenKill_decide_crosscheck` evaluates the same kill by kernel computation on the dressed tuple
rather than through the reparametrisation identity.

Nothing here quotes wave 56's retracted `EvenRouteCarriedDeep` structures; wave 60's
three-covector class-five line is not used as a criterion; wave 61's `gamma_2` affineness is
used only as a TRANSPORT (`SqU6.gaTwoShift_o_channel_even`, in section 1's two `iff` lemmas)
and never as an exclusion; wave 62's collision is not evaded but inherited, and
`gaTwoCentral_iff_chan` says so in as many words; wave 62's finding that the centrality
migration ADDS a relator-centrality hypothesis is respected, since
`gaTwoForces_of_gaTwoCentral` carries `sqRelWord m = SqU6.liftO c` explicitly and every
statement about wave 60's point is inside that family (`sqRelWord_stageWit_diag`).  No search
for a binder point with three even channels is made anywhere: wave 62 proved there is none.

## Contents

* **1** the three `gamma_2` lines and the implications that transpose;
* **2** ⭐⭐ the `ZMod 8` sharpening of centrality;
* **3** the sigma-slot dressing and its reparametrisation identity;
* **4** ⭐⭐⭐ the kill, its certificate, and the failure of all three lines;
* **5** the boundary against wave 60 and wave 62; **6** the separation from wave 62's witness;
* **7** axiom pins.

Companion memo: `docs/dyadic/w63-central2-note.md`.
-/

open scoped commutatorElement

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The three `gamma_2` lines -/

section Lines

variable {h : ℕ} {m : Fin (sqRank h) → SqU6 gr3R}

/-- **Every achievable `gamma_2`-dressing is `gamma_2`-shaped**, at every marking and with no
hypothesis: `GradedStageNecessity.forceLcs_two_le_gaThreeSub` one filtration step short. -/
theorem forceLcs_one_le_gaTwoSub (H : Subgroup (SqU6 gr3R)) : forceLcs H 1 ≤ gaTwoSub gr3R :=
  Subgroup.commutator_le.mpr fun p _ q _ => gaTwoSub_of_commutator p q

theorem isGaTwo_of_mem_forceLcs {H : Subgroup (SqU6 gr3R)} {p : SqU6 gr3R}
    (hp : p ∈ forceLcs H 1) : p.IsGaTwo :=
  forceLcs_one_le_gaTwoSub H hp

/-- **The `gamma_2` forcing at a marking**: every achievable five-slot `gamma_2`-refinement that
kills the relator leaves an even class-five residue.  `GradedStageNecessity.StageForces` one
filtration step wider. -/
def GaTwoForces {h : ℕ} (m : Fin (sqRank h) → SqU6 gr3R) : Prop :=
  ∀ z : Fin (sqRank h) → SqU6 gr3R,
    (∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range m)) 1) →
    sqRelWord (conFiveDress m z) = 1 → selPar (sqRelWord m).o = 0

/-- **THE PARITY LINE, one filtration step wider**: every achievable `gamma_2`-dressing moves
the class-five row by an even amount. -/
def GaTwoOrth {h : ℕ} (m : Fin (sqRank h) → SqU6 gr3R) : Prop :=
  ∀ z : Fin (sqRank h) → SqU6 gr3R,
    (∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range m)) 1) →
    (2 : gr3R) ∣ (SqU6.gaTwoShift h m z).o

/-- **THE CENTRALITY LINE, one filtration step wider**: every achievable `gamma_2`-dressing
whose shift is a central translation moves the class-five row by an even amount.
`GradedStageNecessity.StageCentral` with `gaThreeShift` replaced by `SqU6.gaTwoShift` and
`forceLcs _ 2` by `forceLcs _ 1`. -/
def GaTwoCentral {h : ℕ} (m : Fin (sqRank h) → SqU6 gr3R) : Prop :=
  ∀ (z : Fin (sqRank h) → SqU6 gr3R) (w : gr3R),
    (∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range m)) 1) →
    SqU6.gaTwoShift h m z = SqU6.liftO w → (2 : gr3R) ∣ w

/-- The parity line is the centrality line read on all tuples rather than the central ones.
No hypothesis at all: a central shift's class-five row IS its translation amount. -/
theorem gaTwoCentral_of_gaTwoOrth (hO : GaTwoOrth m) : GaTwoCentral m := by
  intro z w hz hcen
  have ho : (SqU6.gaTwoShift h m z).o = w := by rw [hcen, SqU6.liftO_o]
  rw [← ho]
  exact hO z hz

/-- ⭐⭐ **THE CENTRALITY LINE SUFFICES**, one filtration step wider.  At a marking whose
relator is a central translation, an achievable `gamma_2`-refinement that kills it must move the
relator by the central element `liftO (-c)`, and the centrality line says that element is even.
This is `GradedStageNecessity.stageForces_of_stageCentral` transposed verbatim: the only input
it needs from the wider transport is `SqU6.sqRelWord_gaTwoDress`, which holds over any
commutative ring. -/
theorem gaTwoForces_of_gaTwoCentral {c : gr3R} (hres : sqRelWord m = SqU6.liftO c)
    (hC : GaTwoCentral m) : GaTwoForces m := by
  intro z hz hkill
  have hga : ∀ i, (z i).IsGaTwo := fun i => isGaTwo_of_mem_forceLcs (hz i)
  rw [SqU6.sqRelWord_gaTwoDress hga, hres] at hkill
  have hcen : SqU6.gaTwoShift h m z = SqU6.liftO (-c) := by
    have h1 : SqU6.liftO c * SqU6.gaTwoShift h m z = SqU6.liftO c * SqU6.liftO (-c) := by
      rw [hkill, SqU6.liftO_mul_liftO, add_neg_cancel]
      ext <;> simp [SqU6.liftO]
    exact mul_left_cancel h1
  obtain ⟨k, hk⟩ := hC z (-c) hz hcen
  rw [hres, SqU6.liftO_o, show c = 2 * (-k) from by linear_combination -hk, selPar_two_mul]

/-- …and so does the parity line. -/
theorem gaTwoForces_of_gaTwoOrth {c : gr3R} (hres : sqRelWord m = SqU6.liftO c)
    (hO : GaTwoOrth m) : GaTwoForces m :=
  gaTwoForces_of_gaTwoCentral hres (gaTwoCentral_of_gaTwoOrth hO)

/-- The class-five row of an achievable `gamma_2` shift is the three-channel functional, modulo
two: `GradedFiveGammaTwo.SqU6.gaTwoShift_o_channel_even` with its two hypotheses supplied by
`stageN1` on the marking and `forceLcs_one_le_stageN2` on the dressing. -/
theorem gaTwoShift_o_sub_chan_even {z : Fin (sqRank h) → SqU6 gr3R}
    (hle : Subgroup.closure (Set.range m) ≤ stageN1)
    (hz : ∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range m)) 1) :
    (2 : gr3R) ∣ ((SqU6.gaTwoShift h m z).o - SqU6.gaTwoShiftChan h m z) :=
  SqU6.gaTwoShift_o_channel_even
    (fun i => (mem_stageN1.mp (hle (Subgroup.subset_closure ⟨i, rfl⟩))).1)
    (fun i => (mem_stageN1.mp (hle (Subgroup.subset_closure ⟨i, rfl⟩))).2)
    (fun i => stageN2_even (forceLcs_one_le_stageN2 hle (hz i)))

private theorem dvd_right_of_dvd_sub {a b : gr3R} (hab : (2 : gr3R) ∣ (a - b))
    (ha : (2 : gr3R) ∣ a) : (2 : gr3R) ∣ b := by
  have hb : b = a - (a - b) := by ring
  rw [hb]
  exact dvd_sub ha hab

private theorem dvd_left_of_dvd_sub {a b : gr3R} (hab : (2 : gr3R) ∣ (a - b))
    (hb : (2 : gr3R) ∣ b) : (2 : gr3R) ∣ a := by
  have ha : a = b + (a - b) := by ring
  rw [ha]
  exact dvd_add hb hab

/-- **The parity line IS the three-channel condition**, inside the family where wave 61's
transport applies. -/
theorem gaTwoOrth_iff_chan (hle : Subgroup.closure (Set.range m) ≤ stageN1) :
    GaTwoOrth m ↔ ∀ z : Fin (sqRank h) → SqU6 gr3R,
      (∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range m)) 1) →
      (2 : gr3R) ∣ SqU6.gaTwoShiftChan h m z :=
  ⟨fun hO z hz => dvd_right_of_dvd_sub (gaTwoShift_o_sub_chan_even hle hz) (hO z hz),
    fun hC z hz => dvd_left_of_dvd_sub (gaTwoShift_o_sub_chan_even hle hz) (hC z hz)⟩

/-- ⭐⭐ **THE CENTRALITY LINE IS THE THREE-CHANNEL CONDITION ON THE CENTRAL TUPLES**, and
nothing else.  So `GradedGammaTwoPoint`'s collision - even channels force the class-five
separation form even - applies to the centrality line verbatim; what centrality changes is only
WHICH dressings the condition is asked of.  This is the exact answer to the question the wave
was set: restating the widening on centrality does not escape the collision, it restricts its
domain. -/
theorem gaTwoCentral_iff_chan (hle : Subgroup.closure (Set.range m) ≤ stageN1) :
    GaTwoCentral m ↔ ∀ (z : Fin (sqRank h) → SqU6 gr3R) (w : gr3R),
      (∀ i, z i ∈ forceLcs (Subgroup.closure (Set.range m)) 1) →
      SqU6.gaTwoShift h m z = SqU6.liftO w → (2 : gr3R) ∣ SqU6.gaTwoShiftChan h m z := by
  constructor
  · intro hC z w hz hcen
    refine dvd_right_of_dvd_sub (gaTwoShift_o_sub_chan_even hle hz) ?_
    rw [hcen, SqU6.liftO_o]
    exact hC z w hz hcen
  · intro hC z w hz hcen
    have ho : (SqU6.gaTwoShift h m z).o = w := by rw [hcen, SqU6.liftO_o]
    rw [← ho]
    exact dvd_left_of_dvd_sub (gaTwoShift_o_sub_chan_even hle hz) (hC z w hz hcen)

end Lines

/-! ## 2 The `ZMod 8` sharpening: a central `gamma_2` shift reads the halves -/

section Sharpening

variable {R : Type} [CommRing R] {h : ℕ}

/-- The shift's first class-two row: the Frobenius weights `(-4, 2)` on the exponent slots and
nothing else.  `GradedFiveGammaTwo.SqU6.gaTwoShift_i` is the committed fourth one; the first
three are needed here and are not in the tree. -/
theorem SqU6.gaTwoShift_f (m z : Fin (sqRank h) → SqU6 R) :
    (SqU6.gaTwoShift h m z).f = -4 * (z 1).f + 2 * (z 2).f := by
  rw [SqU6.gaTwoShift, SqU6.gaThree_mul (SqU6.gaTwoHandleSum_isGaThree _ _ _ _ _)
    (SqU6.gaTwoColl_isGaFour m z).isGaThree, SqU6.mul_f]
  simp only [SqU6.gaTwoCore]
  ring

/-- …the second. -/
theorem SqU6.gaTwoShift_g (m z : Fin (sqRank h) → SqU6 R) :
    (SqU6.gaTwoShift h m z).g = -4 * (z 1).g + 2 * (z 2).g := by
  rw [SqU6.gaTwoShift, SqU6.gaThree_mul (SqU6.gaTwoHandleSum_isGaThree _ _ _ _ _)
    (SqU6.gaTwoColl_isGaFour m z).isGaThree, SqU6.mul_g]
  simp only [SqU6.gaTwoCore]
  ring

/-- …and the third. -/
theorem SqU6.gaTwoShift_h (m z : Fin (sqRank h) → SqU6 R) :
    (SqU6.gaTwoShift h m z).h = -4 * (z 1).h + 2 * (z 2).h := by
  rw [SqU6.gaTwoShift, SqU6.gaThree_mul (SqU6.gaTwoHandleSum_isGaThree _ _ _ _ _)
    (SqU6.gaTwoColl_isGaFour m z).isGaThree, SqU6.mul_h]
  simp only [SqU6.gaTwoCore]
  ring

variable {m : Fin (sqRank h) → SqU6 gr3R}

private theorem cen_two_dvd : ∀ a b : gr3R, -4 * a + 2 * b = 0 → ∃ t : gr3R, b = 2 * t := by
  decide

/-- ⭐⭐ **The `ZMod 8` sharpening of `gamma_2` centrality.**  A `gamma_2` shift that is a
central translation forces the `x1`-slot dressing's own first class-two coordinate EVEN, at
every marking and with no achievability at all, because `2 b = 4 a` in `ZMod 8` forces `b` even.
Mod `2` the same equation is vacuous.  This is `GradedStageSeparate.stageCentral_x1_j_even` one
filtration step wider. -/
theorem gaTwoCentral_x1_f_even {z : Fin (sqRank h) → SqU6 gr3R} {w : gr3R}
    (hcen : SqU6.gaTwoShift h m z = SqU6.liftO w) : (2 : gr3R) ∣ (z 2).f := by
  have h0 : -4 * (z 1).f + 2 * (z 2).f = 0 := by
    rw [← SqU6.gaTwoShift_f, hcen]
    rfl
  exact cen_two_dvd _ _ h0

/-- …the second class-two coordinate, which is NOT even on the achievable lattice. -/
theorem gaTwoCentral_x1_g_even {z : Fin (sqRank h) → SqU6 gr3R} {w : gr3R}
    (hcen : SqU6.gaTwoShift h m z = SqU6.liftO w) : (2 : gr3R) ∣ (z 2).g := by
  have h0 : -4 * (z 1).g + 2 * (z 2).g = 0 := by
    rw [← SqU6.gaTwoShift_g, hcen]
    rfl
  exact cen_two_dvd _ _ h0

/-- …the third. -/
theorem gaTwoCentral_x1_h_even {z : Fin (sqRank h) → SqU6 gr3R} {w : gr3R}
    (hcen : SqU6.gaTwoShift h m z = SqU6.liftO w) : (2 : gr3R) ∣ (z 2).h := by
  have h0 : -4 * (z 1).h + 2 * (z 2).h = 0 := by
    rw [← SqU6.gaTwoShift_h, hcen]
    rfl
  exact cen_two_dvd _ _ h0

/-- ⭐ …and the fourth, which is one of the THREE CHANNELS. -/
theorem gaTwoCentral_x1_i_even {z : Fin (sqRank h) → SqU6 gr3R} {w : gr3R}
    (hcen : SqU6.gaTwoShift h m z = SqU6.liftO w) : (2 : gr3R) ∣ (z 2).i := by
  have h0 : -4 * (z 1).i + 2 * (z 2).i = 0 := by
    rw [← SqU6.gaTwoShift_i, hcen]
    rfl
  exact cen_two_dvd _ _ h0

/-- ⭐ **Centrality kills the `x1`-slot's second channel.**  `SqU6.gaTwoChannel z L` reads
`z.i * L.j`, and a central shift makes that term even at the `x1` slot whatever the letter is.
⚠ At wave 60's binder point every letter has `L.j = 0`, so this channel is already silent
there and the sharpening is not what decides that point. -/
theorem gaTwoCentral_channel_x1 {z : Fin (sqRank h) → SqU6 gr3R} {w : gr3R}
    (hcen : SqU6.gaTwoShift h m z = SqU6.liftO w) (L : SqU6 gr3R) :
    (2 : gr3R) ∣ ((z 2).i * L.j) :=
  Dvd.dvd.mul_right (gaTwoCentral_x1_i_even hcen) _

end Sharpening

/-! ## 3 The sigma-slot dressing, and the reparametrisation it performs -/

section SigmaSlot

variable {R : Type} [CommRing R] {h : ℕ}

variable (h) in
/-- **The dressing carrying `w` on the SIGMA slot and nothing anywhere else.**
`GradedGammaTwoPoint.gaTwoSlotTwo` at slot `0` instead of slot `2`. -/
def cenSigDress (w : SqU6 R) : Fin (sqRank h) → SqU6 R :=
  fun i => if (i : ℕ) = 0 then w else 1

@[simp] theorem cenSigDress_zero (w : SqU6 R) : cenSigDress h w 0 = w := by
  simp only [cenSigDress, sqVal_zero, if_pos]

theorem cenSigDress_of_ne (w : SqU6 R) {i : Fin (sqRank h)} (hi : (i : ℕ) ≠ 0) :
    cenSigDress h w i = 1 := by
  simp only [cenSigDress, if_neg hi]

@[simp] theorem cenSigDress_one (w : SqU6 R) : cenSigDress h w 1 = 1 :=
  cenSigDress_of_ne w (by rw [sqVal_one]; omega)

@[simp] theorem cenSigDress_two (w : SqU6 R) : cenSigDress h w 2 = 1 :=
  cenSigDress_of_ne w (by rw [sqVal_two]; omega)

@[simp] theorem cenSigDress_handleU (w : SqU6 R) (k : Fin h) :
    cenSigDress h w (sqHandleIdxU k) = 1 :=
  cenSigDress_of_ne w (by rw [sqHandleIdxU_val]; omega)

@[simp] theorem cenSigDress_handleV (w : SqU6 R) (k : Fin h) :
    cenSigDress h w (sqHandleIdxV k) = 1 :=
  cenSigDress_of_ne w (by rw [sqHandleIdxV_val]; omega)

/-- **The three-channel functional at a sigma-slot dressing** is one channel: the dressing
against the `x0`-slot letter, exactly as the Fox form prescribes. -/
theorem SqU6.gaTwoShiftChan_cenSigDress (m : Fin (sqRank h) → SqU6 R) (w : SqU6 R) :
    SqU6.gaTwoShiftChan h m (cenSigDress h w) = SqU6.gaTwoChannel w (m 1) := by
  rw [SqU6.gaTwoShiftChan]
  simp only [cenSigDress_zero, cenSigDress_one, cenSigDress_two, cenSigDress_handleU,
    cenSigDress_handleV, SqU6.gaTwoChannel_one, sub_self, Finset.sum_const_zero]
  ring

variable {j : Fin h}

/-- ⭐ **Dressing the sigma slot of a one-handle-live tuple REPARAMETRISES it.**  The dressed
marking is the same tuple with its sigma letter multiplied, so no shift machinery at all is
needed to evaluate a sigma-slot dressing: the relator of the dressed frame is the relator of
another member of the same family. -/
theorem conFiveDress_fiveTuple_cenSigDress (S X Y U V w : SqU6 R) :
    conFiveDress (fiveTuple R h j S X Y U V) (cenSigDress h w)
      = fiveTuple R h j (S * w) X Y U V := by
  funext i
  rw [conFiveDress_apply]
  by_cases hi : (i : ℕ) = 0
  · rw [cenSigDress, if_pos hi]
    simp only [fiveTuple, if_pos hi]
  · rw [cenSigDress, if_neg hi, mul_one]
    simp only [fiveTuple, if_neg hi]

/-- …so at wave 60's binder point the sigma dressing moves the sigma PARAMETER. -/
theorem cenSigDress_stageWit (v w : SqU6 gr3R) :
    conFiveDress (stageWit h j v) (cenSigDress h w) = stageWit h j (v * w) := by
  rw [stageWit, stageWit, conFiveDress_fiveTuple_cenSigDress, mul_assoc]

/-- **The same reparametrisation for the `x1` slot**, which section 6 needs for wave 62's
witness. -/
theorem conFiveDress_fiveTuple_gaTwoSlotTwo (S X Y U V w : SqU6 R) :
    conFiveDress (fiveTuple R h j S X Y U V) (gaTwoSlotTwo h w)
      = fiveTuple R h j S X (Y * w) U V := by
  funext i
  rw [conFiveDress_apply]
  by_cases hi : (i : ℕ) = 2
  · rw [gaTwoSlotTwo, if_pos hi]
    simp only [fiveTuple, if_neg (show ¬ (i : ℕ) = 0 by omega),
      if_neg (show ¬ (i : ℕ) = 1 by omega), if_pos hi]
  · rw [gaTwoSlotTwo, if_neg hi, mul_one]
    simp only [fiveTuple, if_neg hi]

end SigmaSlot

/-! ## 4 The kill, and the failure of all three lines -/

section Kill

variable {h : ℕ} {j : Fin h}

/-- ⭐⭐⭐ **THE KILLING DRESSING**: the class-four coordinate `3`, and nothing else.  It is
`gamma_3`-shaped, so its SHAPE is not what is new; its class-four coordinate is ODD, and that is
what the honest `gamma_2` of the image supplies and the achievable stage-four lattice does
not. -/
def gaTwoCenKill : SqU6 gr3R := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0⟩

theorem gaTwoCenKill_isGaThree : gaTwoCenKill.IsGaThree :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem gaTwoCenKill_isGaTwo : gaTwoCenKill.IsGaTwo := gaTwoCenKill_isGaThree.isGaTwo

/-- ⭐⭐ **It is a product of a SQUARED honest commutator and an honest commutator of the point's
own letters**, as the displayed `^ 2` on the first factor shows.  Wave 61's census over the ten
pairwise commutators of the letters found no kill at any power on any single slot, and that
census was over GENERATORS: this element is a genuine product, and the search that found it is
`scripts/w63_central2/derive_central2.py` section 4. -/
theorem gaTwoCenKill_comm_form :
    gaTwoCenKill = commP (fiveSigMark gr3R * stageX)⁻¹ stageU ^ 2
      * commP stageY (stageX * stageU) := by decide

/-- ⭐⭐ **…so the dressing is ACHIEVABLE**: every slot lies in `forceLcs (stageImage) 1`, the
honest `gamma_2` of the point's image subgroup. -/
theorem cenSigDress_cenKill_mem (i : Fin (sqRank h)) :
    cenSigDress h gaTwoCenKill i ∈ forceLcs (stageImage h j stageX) 1 := by
  by_cases hi : (i : ℕ) = 0
  · rw [cenSigDress, if_pos hi]
    have hS : fiveSigMark gr3R * stageX ∈ stageImage h j stageX :=
      Subgroup.subset_closure ⟨0, by rw [stageWit, fiveTuple_zero]⟩
    have hX : stageX ∈ stageImage h j stageX :=
      Subgroup.subset_closure ⟨1, by rw [stageWit, fiveTuple_one]⟩
    have hY : stageY ∈ stageImage h j stageX :=
      Subgroup.subset_closure ⟨2, by rw [stageWit, fiveTuple_two]⟩
    have hU : stageU ∈ stageImage h j stageX :=
      Subgroup.subset_closure ⟨sqHandleIdxU j, by rw [stageWit, fiveTuple_handleU]⟩
    rw [gaTwoCenKill_comm_form]
    exact mul_mem (pow_mem (commP_mem_commSub (inv_mem hS) hU) 2)
      (commP_mem_commSub hY (mul_mem hX hU))
  · rw [cenSigDress, if_neg hi]
    exact one_mem _

/-- ⭐⭐⭐ **THE KILL.**  At wave 60's stage-four binder point, at every handle count and every
handle, the achievable `gamma_2`-dressing `gaTwoCenKill` on the sigma slot kills the dressed
frame outright.  The proof needs no transport at all: by `cenSigDress_stageWit` the dressed
marking is another member of the same one-handle-live family, and its relator is evaluated by
`sqRelWord_fiveTuple` and kernel computation. -/
theorem sqRelWord_stageWit_cenKill (h : ℕ) (j : Fin h) :
    sqRelWord (conFiveDress (stageWit h j stageX) (cenSigDress h gaTwoCenKill)) = 1 := by
  rw [cenSigDress_stageWit, stageWit, sqRelWord_fiveTuple]
  decide

/-- ⭐⭐⭐ **WAVE 60's EXCLUSION DOES NOT SURVIVE ONE FILTRATION STEP WIDER.**  The `gamma_2`
forcing is FALSE at the point wave 60 and wave 61 state their exclusions at: the residue is odd
and an achievable `gamma_2`-dressing kills.

⚠ `GradedFiveStageFour.sqRelWord_stageWit_diag_ne_one` and
`GradedGammaTwoPoint.sqRelWord_stageWit_diag_gaTwo_ne_one` are untouched; what this refutes is
the removal of their hypotheses. -/
theorem gaTwoForces_stageWit_false (h : ℕ) (j : Fin h) : ¬ GaTwoForces (stageWit h j stageX) := by
  intro hF
  have hb := hF (cenSigDress h gaTwoCenKill) (fun i => cenSigDress_cenKill_mem i)
    (sqRelWord_stageWit_cenKill h j)
  rw [sqRelWord_stageWit_diag, SqU6.liftO_o, selPar_one] at hb
  exact absurd hb (by decide)

/-- ⭐⭐ **The killing dressing acts CENTRALLY**, with the odd class-five row `7`: it is a
counterexample to the centrality line and not merely to the parity line. -/
theorem gaTwoShift_stageWit_cenKill (h : ℕ) (j : Fin h) :
    SqU6.gaTwoShift h (stageWit h j stageX) (cenSigDress h gaTwoCenKill) = SqU6.liftO 7 := by
  have hga : ∀ i, (cenSigDress h gaTwoCenKill i).IsGaTwo := by
    intro i
    by_cases hi : (i : ℕ) = 0
    · rw [cenSigDress, if_pos hi]
      exact gaTwoCenKill_isGaTwo
    · rw [cenSigDress, if_neg hi]
      exact SqU6.isGaTwo_one
  have hid := SqU6.sqRelWord_gaTwoDress (m := stageWit h j stageX) hga
  rw [sqRelWord_stageWit_cenKill, sqRelWord_stageWit_diag] at hid
  refine mul_left_cancel (a := SqU6.liftO (1 : gr3R)) ?_
  rw [← hid, SqU6.liftO_mul_liftO]
  decide

/-- ⭐⭐⭐ **…so the CENTRALITY LINE FAILS at wave 60's point.**  Restating wave 62's
conditional widening on centrality therefore cannot make it unconditional: the statement it
would have to prove is false. -/
theorem gaTwoCentral_stageWit_false (h : ℕ) (j : Fin h) :
    ¬ GaTwoCentral (stageWit h j stageX) := by
  intro hC
  obtain ⟨t, ht⟩ := hC (cenSigDress h gaTwoCenKill) 7 (fun i => cenSigDress_cenKill_mem i)
    (gaTwoShift_stageWit_cenKill h j)
  exact (by decide : ∀ t : gr3R, (7 : gr3R) ≠ 2 * t) t ht

/-- ⭐⭐ …and so does the parity line, which the centrality line implies. -/
theorem gaTwoOrth_stageWit_false (h : ℕ) (j : Fin h) : ¬ GaTwoOrth (stageWit h j stageX) :=
  fun hO => gaTwoCentral_stageWit_false h j (gaTwoCentral_of_gaTwoOrth hO)

end Kill

/-! ## 5 The boundary: what is refuted, and what is not -/

section Boundary

variable {h : ℕ} {j : Fin h}

/-- ⭐ **The killing element is NOT an achievable stage-four dressing.**  Wave 60's soundness
chain forces every element of `forceLcs (stageImage) 2` into `stageN3`, whose class-four
coordinate is EVEN; `gaTwoCenKill`'s is `3`.  So the kill lies strictly between the two
lattices, and `GradedFiveStageFour`'s exclusion is untouched by it. -/
theorem gaTwoCenKill_not_mem_stageN3 : gaTwoCenKill ∉ stageN3 := by
  intro hz
  obtain ⟨t, ht⟩ := (stageN3_even hz).2.2
  exact (by decide : ∀ t : gr3R, (3 : gr3R) ≠ 2 * t) t ht

theorem gaTwoCenKill_not_stageFour_achievable (h : ℕ) (j : Fin h) :
    gaTwoCenKill ∉ forceLcs (stageImage h j stageX) 2 :=
  fun hz => gaTwoCenKill_not_mem_stageN3
    (forceLcs_two_le_stageN3 (stageImage_le_stageN1 ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩) hz)

/-- ⭐⭐ **The killing dressing's three-channel functional is ODD.**  So wave 62's
`sqRelWord_stageWit_diag_gaTwo_ne_one` does not apply to it, its hypothesis is exactly what
keeps that theorem true, and `GradedFiveGammaTwo.stageWit_gaTwo_forced` is confirmed at the
kill: the odd residue `1` plus an odd channel is even.

⚠ Only the PARITY is proved: the statement is `selPar (...) = 1`, and no theorem in this file
names the functional's value.  The `7` of `gaTwoShift_stageWit_cenKill` is the shift's `o`-row, a
different quantity. -/
theorem cenKill_chan_odd (h : ℕ) (j : Fin h) :
    selPar (SqU6.gaTwoShiftChan h (stageWit h j stageX) (cenSigDress h gaTwoCenKill)) = 1 := by
  rw [SqU6.gaTwoShiftChan_cenSigDress, stageWit, fiveTuple_one]
  decide

/-- ⭐ **The mechanism, at the point.**  The sigma-slot dressing's class-four coordinate is
paired against `x0.e` by `GradedFiveStageFour.gaThreePair`, and wave 60's point needs that
column ODD - it is the channel its class-five residue runs on.  Here are the two data side by
side: `stageX.e` is a unit, and the killer's class-four coordinate is odd. -/
theorem cenKill_mechanism : selPar stageX.e = 1 ∧ selPar gaTwoCenKill.m = 1
    ∧ stageX.e * gaTwoCenKill.m = 7 := by decide

end Boundary

/-! ## 6 The centrality line is SEPARATED from the parity line at the point -/

section Separation

variable {h : ℕ} {j : Fin h}

/-- The relator of wave 62's odd-channel witness, dressed: `<j = 4, l = 6, o = 6>`, at every
handle count and every handle. -/
theorem sqRelWord_stageWit_gaTwoSlotTwo (h : ℕ) (j : Fin h) :
    sqRelWord (conFiveDress (stageWit h j stageX) (gaTwoSlotTwo h (commP stageX stageY)))
      = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 6, 0, 0, 6⟩ := by
  rw [stageWit, conFiveDress_fiveTuple_gaTwoSlotTwo, sqRelWord_fiveTuple]
  decide

/-- ⭐⭐ **Wave 62's odd-channel witness leaves a NON-CENTRAL dressed relator.**  `[x0, x1]` on
the `x1` slot is the dressing whose three-channel functional `GradedGammaTwoPoint` proves odd,
and it moves two lower rows.

⚠ What is stated below is about the dressed RELATOR; `GaTwoCentral` quantifies over the SHIFT
`SqU6.gaTwoShift`, and the bridge - `SqU6.sqRelWord_gaTwoDress` at a marking whose own relator is
central - is available but is not invoked here.  ⚠ That this dressing refutes the parity line at
wave 60's point is `GradedGammaTwoPoint`'s result, inherited rather than reproved.  The two lines
are genuinely separated here, which is why the refutation of section 4 needed a different
dressing - and the one it uses is central. -/
theorem stageWit_gaTwoSlotTwo_not_central (h : ℕ) (j : Fin h) :
    ¬ ∃ w : gr3R, sqRelWord (conFiveDress (stageWit h j stageX)
      (gaTwoSlotTwo h (commP stageX stageY))) = SqU6.liftO w := by
  rintro ⟨w, hc⟩
  rw [sqRelWord_stageWit_gaTwoSlotTwo] at hc
  have hj : (4 : gr3R) = 0 := congrArg SqU6.j hc
  exact absurd hj (by decide)

/-- ⭐ **The kill, cross-checked by a second route.**  Section 4 evaluates the dressed relator
through `sqRelWord_fiveTuple`; this evaluates it at one handle by `decide` on the dressed tuple
itself, so the reparametrisation identity and the kernel computation are made to meet.
(Wave 57's process finding: two results of one wave can each be right and compose to a false
one.) -/
theorem cenKill_decide_crosscheck :
    sqRelWord (conFiveDress (stageWit 1 0 stageX) (cenSigDress 1 gaTwoCenKill)) = 1 := by decide

end Separation

/-! ## 7 Axiom pins

Committed prints for every public declaration of this file: all **std-3** (`propext`,
`Classical.choice`, `Quot.sound`) or a subset; no census axiom is reachable.  Every `decide` is
on `gr3R = ZMod 8`, `ZMod 2`, `SqU6 gr3R` or tuples over them; there is no `native_decide`. -/

section AxiomPins

#print axioms forceLcs_one_le_gaTwoSub
#print axioms isGaTwo_of_mem_forceLcs
#print axioms GaTwoForces
#print axioms GaTwoOrth
#print axioms GaTwoCentral
#print axioms gaTwoCentral_of_gaTwoOrth
#print axioms gaTwoForces_of_gaTwoCentral
#print axioms gaTwoForces_of_gaTwoOrth
#print axioms gaTwoShift_o_sub_chan_even
#print axioms gaTwoOrth_iff_chan
#print axioms gaTwoCentral_iff_chan
#print axioms SqU6.gaTwoShift_f
#print axioms SqU6.gaTwoShift_g
#print axioms SqU6.gaTwoShift_h
#print axioms gaTwoCentral_x1_f_even
#print axioms gaTwoCentral_x1_g_even
#print axioms gaTwoCentral_x1_h_even
#print axioms gaTwoCentral_x1_i_even
#print axioms gaTwoCentral_channel_x1
#print axioms cenSigDress
#print axioms cenSigDress_zero
#print axioms cenSigDress_of_ne
#print axioms cenSigDress_one
#print axioms cenSigDress_two
#print axioms cenSigDress_handleU
#print axioms cenSigDress_handleV
#print axioms SqU6.gaTwoShiftChan_cenSigDress
#print axioms conFiveDress_fiveTuple_cenSigDress
#print axioms cenSigDress_stageWit
#print axioms conFiveDress_fiveTuple_gaTwoSlotTwo
#print axioms gaTwoCenKill
#print axioms gaTwoCenKill_isGaThree
#print axioms gaTwoCenKill_isGaTwo
#print axioms gaTwoCenKill_comm_form
#print axioms cenSigDress_cenKill_mem
#print axioms sqRelWord_stageWit_cenKill
#print axioms gaTwoForces_stageWit_false
#print axioms gaTwoShift_stageWit_cenKill
#print axioms gaTwoCentral_stageWit_false
#print axioms gaTwoOrth_stageWit_false
#print axioms gaTwoCenKill_not_mem_stageN3
#print axioms gaTwoCenKill_not_stageFour_achievable
#print axioms cenKill_chan_odd
#print axioms cenKill_mechanism
#print axioms sqRelWord_stageWit_gaTwoSlotTwo
#print axioms stageWit_gaTwoSlotTwo_not_central
#print axioms cenKill_decide_crosscheck

end AxiomPins

end SqCore

end Dyadic

end GQ2
