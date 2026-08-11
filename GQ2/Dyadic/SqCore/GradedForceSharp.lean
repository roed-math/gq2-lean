/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFiveGammaTwo
import GQ2.Dyadic.SqCore.GradedStageNecessity

/-!
# W65-SHARPEN: the two stage-four lattice bounds at their sharpest, both EXACT

W64-VERIFY audited the tree's nine committed lower-central lattice bounds against the sharpest
each could be (`docs/dyadic/w64-verify-note.md`, task A).  Seven are sharp as stated.  The two
that are not are the two the class-five stack runs on:

| bound | `N_in` | k | honest lattice | committed target |
|---|---|---|---|---|
| `GradedFiveGammaTwo.forceLcs_one_le_stageN2` | `stageN1` | 1 | `2^26` | `stageN2`, `2^27` |
| `GradedFiveStageFour.forceLcs_two_le_stageN3` | `stageN1` | 2 | `2^13` | `stageN3`, `2^15` |

⚠ **Nothing committed is wrong.**  Both bounds are used only in the direction that proves
EXCLUSIONS, where a weaker upper bound can fail to fire but cannot lie; the tree's
survival-shaped lattice statements are negative containments proved by exhibiting an explicit
element, hence sharp by construction.  This file is an opportunity taken, not a correction
made.

## Naming, because two statements compete for one name

The PRIMED names `forceLcs_one_le_stageN2'` and `forceLcs_two_le_stageN3'` are the recorded
W65 contracts and they carry the **sharpened** bounds, matching the ticket W64-VERIFY wrote
(`docs/dyadic/w64-verify-note.md` line 478).  They do NOT name the committed bounds re-proved.
Those recoveries are `forceSharp_recover_one_le_stageN2` and `forceSharp_recover_two_le_stageN3`.
Everything else this file introduces carries the lane prefix `forceSharp`.

## ⭐⭐ Headline 1: the two sharpened bounds

`forceLcs_one_le_stageN2'` and `forceLcs_two_le_stageN3'`, for every `H <= stageN1`:

```text
forceSharpN2 = {a..e = 0, 2 | f, 2 | g, 2 | h, 2 | j}      stageN2 is missing  2 | g
forceSharpN3 = {a..i = 0, 4 | j, 2 | k, 2 | l, 2 | m}      stageN3 has 2 | j, and nothing on k
```

Both are CONTAINMENTS, in the same shape as the bounds they replace, and both committed bounds
are recovered from them (`forceSharp_recover_one_le_stageN2`, `forceSharp_recover_two_le_stageN3`).

⭐ **The two halves are not independent: `2 | g` at depth one is exactly what buys `4 | j` at
depth two.**  The class-three left form on a `gamma_2`-element reduces to `p.f * q.c - p.g *
q.a`, and `stageN1` makes `q.a` and `q.c` even; so an even `p.g` and an even `p.f` turn two
even products into two products of two even factors.  Run the same chain from the committed
`stageN2`, which says nothing about `g`, and the `j`-coordinate is merely even
(MEASURED: `scripts/w65_sharpen/results/sharp_lattice.txt` section 1 - the commutator subgroup
`[stageN2, stageN1]` really is `2^15`, i.e. all of `stageN3`).

## ⭐⭐⭐ Headline 2: at `H = stageN1` both bounds are EQUALITIES

`forceSharp_stageN1_one_eq` and `forceSharp_stageN1_two_eq`.  The reverse
containments are proved by exhibiting each of the sixteen (resp. six) coordinate generators as
an explicit iterated commutator of single-coordinate letters of `stageN1`, and then decomposing
an arbitrary member of the target along the abelian `gamma_3` layer.

⭐ This is what the audit could only MEASURE.  Its consequence is a **decidable membership test
for achievability at the uniform level**, `forceSharp_mem_forceLcs_stageN1_two_iff`: an element of
`SqU6 gr3R` lies in `forceLcs stageN1 2` if and only if it satisfies the four congruences.
Before this the tree owned upper bounds only, so it could show a candidate killer NOT
achievable, but could never show one IS achievable except by exhibiting a commutator by hand.

## ⭐⭐ Headline 3: the class-five stack's class-four row, mod FOUR

The consumer demonstration, section 6.  `GradedStageNecessity.gaThreeShift_m` (cited, not
edited) says the stage-four shift's first class-four row is the core's `m` plus the summed
handles' `m`, and every one of those is built from the class-four graded Fox pairing
`GradedFiveStageFour.gaThreePairL z L = z.j * L.d - z.k * L.a`.

Read that form with what the COMMITTED bound supplies (`2 | z.j`, nothing at all on `z.k`) and
an even `(1,2)`-column: both monomials are even, so the row is even and no better.  Read it
with what the PRIMED bound supplies (`4 | z.j` and `2 | z.k`) and each monomial picks up a
second factor of two, so `4 | gaThreePairL z L` and the whole row is divisible by FOUR:
`forceSharp_gaThreeShift_m_dvd_four`, and end to end off the achievable lattice in
`forceSharp_stageShift_m_dvd_four`.

⭐ The gain is not an artefact of a lossy proof.  `forceSharp_gaThreePairL_committed_not_dvd_four`
exhibits a dressing in `stageN3` and a letter in `stageN1` whose pairing is `2`, so the mod-four
conclusion is UNREACHABLE from the committed hypotheses and genuinely needs the sharpening.

## ⭐ Headline 4: the correction block needs no frame hypothesis once `2 | k` is known

`forceSharp_gaThreeCorr_even_of_evenK`.  The committed `GradedFiveStageFour.gaThreeCorr_even`
takes three hypotheses on the FRAME (`2 | s.a`, `2 | x.a`, `2 | y.a`) and six on the dressing.
Of the nine
blocks of `gaThreeCorr` only one, `z2.k * (s.a * y.e + s.e * y.a)`, needs the frame at all, and
the sharpened lattice kills it from the dressing side.  So on the achievable lattice the
correction block is even for a completely arbitrary frame.

⚠ **Honest limit, and it is the reason this does not widen the exclusion.**  The class-five
PAIRING `gaThreePair z L` still contains `z.n * L.a`, and `n` is entirely free on the achievable
lattice (`forceSharpN3` puts no condition on it; MEASURED, section 1 of the certificate).  So
`gaThreeShiftO_even` keeps its frame hypothesis `∀ i, 2 | (m i).a`, and no committed exclusion
gets a wider quantifier from this file.  What section 5 records is a strictly cleaner
factorisation of the same theorem, not a stronger one.  The class-five `o`-row does not gain
mod four either, and for the same reason: `z.m * L.e` and `z.n * L.a` are only even.  It is the
class-four `m`-row, headline 3, that gains.

## What this file does NOT do

* It does not touch `GradedFiveStageFour` or `GradedFiveGammaTwo`; `stageN2`, `stageN3` and the
  two committed bounds stand unchanged, and are re-derived here from the sharp ones.
* It proves the equality only at `H = stageN1`, the uniform level.  At a concrete marking the
  honest lattice can be strictly smaller (W64-VERIFY's pointwise table); this file says nothing
  about that.
* `forceSharpN3` is the sharpest **subgroup** target, not merely the sharpest congruence lattice:
  the equality rules out every smaller subgroup at once.

## Contents

* **1** the two sharpened lattices, and how they sit inside the committed ones;
* **2** the two commutator steps, coordinate by coordinate;
* **3** ⭐⭐ the two bounds under their contract names, and the committed bounds recovered;
* **4** ⭐⭐⭐ the reverse containments, the equalities, and the achievability test;
* **5** ⭐ the correction block without a frame hypothesis;
* **6** ⭐⭐ the consumer: the class-four row mod four, and why the committed bound cannot;
* **7** axiom pins.

## Certification

`scripts/w65_sharpen/sharp_lattice.py`, output `scripts/w65_sharpen/results/sharp_lattice.txt`,
52 named checks, 0 failures, layered on `scripts/w64_verify/task_a_audit.py` and running on the
honest `6 x 6` matrices of `scripts/w59_force5/u6mat.py`.  It certifies the group orders, the
two chain identities, every coordinate identity this file's proofs rewrite to, the strictness,
and where the lattice sits in each committed consumer.  Bracket convention: the script computes
`commP x y = x⁻¹ y⁻¹ x y`, which is what `commutatorElement_eq_commP` turns the mathlib bracket
into before the coordinate algebra runs, and every subgroup it computes is a normal closure,
hence convention-immune.

⚠ Section 6 is **proved, not measured**: the certificate predates it and sweeps no mod-four
arithmetic.  A machine-checked proof is the stronger warrant, but the script should not be read
as covering it.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`.  Every `decide` is on `ZMod 8` or on
`SqU6 (ZMod 8)`.
-/

open scoped commutatorElement

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## 1 The two sharpened lattices -/

section Lattices

/-- **`M_2'`**, the sharp depth-one target: a `gamma_2`-element with `f`, `g`, `h` and `j` all
even.  `GradedFiveStageFour.stageN2` is this without the `2 | g`, and is therefore twice as
big. -/
def forceSharpN2 : Subgroup (SqU6 gr3R) where
  carrier := {z | z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0
    ∧ (2 : gr3R) ∣ z.f ∧ (2 : gr3R) ∣ z.g ∧ (2 : gr3R) ∣ z.h ∧ (2 : gr3R) ∣ z.j}
  mul_mem' := by
    rintro p q ⟨pa, pb, pc, pd, pe, pf, pg, ph, pj⟩ ⟨qa, qb, qc, qd, qe, qf, qg, qh, qj⟩
    refine ⟨by rw [SqU6.mul_a, pa, qa]; ring, by rw [SqU6.mul_b, pb, qb]; ring,
      by rw [SqU6.mul_c, pc, qc]; ring, by rw [SqU6.mul_d, pd, qd]; ring,
      by rw [SqU6.mul_e, pe, qe]; ring, ?_, ?_, ?_, ?_⟩
    · rw [SqU6.mul_f, pa, zero_mul, add_zero]; exact dvd_add pf qf
    · rw [SqU6.mul_g, pb, zero_mul, add_zero]; exact dvd_add pg qg
    · rw [SqU6.mul_h, pc, zero_mul, add_zero]; exact dvd_add ph qh
    · rw [SqU6.mul_j, pa, zero_mul, add_zero, qc, mul_zero, add_zero]; exact dvd_add pj qj
  one_mem' := ⟨rfl, rfl, rfl, rfl, rfl, by rw [SqU6.one_f]; exact dvd_zero _,
    by rw [SqU6.one_g]; exact dvd_zero _, by rw [SqU6.one_h]; exact dvd_zero _,
    by rw [SqU6.one_j]; exact dvd_zero _⟩
  inv_mem' := by
    rintro p ⟨pa, pb, pc, pd, pe, pf, pg, ph, pj⟩
    refine ⟨by rw [SqU6.inv_a, pa]; ring, by rw [SqU6.inv_b, pb]; ring,
      by rw [SqU6.inv_c, pc]; ring, by rw [SqU6.inv_d, pd]; ring,
      by rw [SqU6.inv_e, pe]; ring, ?_, ?_, ?_, ?_⟩
    · rw [SqU6.inv_f, pa, zero_mul, zero_sub]; exact pf.neg_right
    · rw [SqU6.inv_g, pb, zero_mul, zero_sub]; exact pg.neg_right
    · rw [SqU6.inv_h, pc, zero_mul, zero_sub]; exact ph.neg_right
    · rw [SqU6.inv_j, pa, pb, pc]; simpa using pj.neg_right

/-- **`M_3'`**, the sharp depth-two target: a `gamma_3`-element whose `j` is divisible by
**four**, and whose `k`, `l` and `m` are even.  `GradedFiveStageFour.stageN3` asks only `2 | j`
and says nothing at all about `k`, so it is four times as big. -/
def forceSharpN3 : Subgroup (SqU6 gr3R) where
  carrier := {z | z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0 ∧ z.f = 0 ∧ z.g = 0
    ∧ z.h = 0 ∧ z.i = 0 ∧ (4 : gr3R) ∣ z.j ∧ (2 : gr3R) ∣ z.k ∧ (2 : gr3R) ∣ z.l
    ∧ (2 : gr3R) ∣ z.m}
  mul_mem' := by
    rintro p q ⟨pa, pb, pc, pd, pe, pf, pg, ph, pi, pj, pk, pl, pm⟩
      ⟨qa, qb, qc, qd, qe, qf, qg, qh, qi, qj, qk, ql, qm⟩
    refine ⟨by rw [SqU6.mul_a, pa, qa]; ring, by rw [SqU6.mul_b, pb, qb]; ring,
      by rw [SqU6.mul_c, pc, qc]; ring, by rw [SqU6.mul_d, pd, qd]; ring,
      by rw [SqU6.mul_e, pe, qe]; ring, by rw [SqU6.mul_f, pf, qf, pa]; ring,
      by rw [SqU6.mul_g, pg, qg, pb]; ring, by rw [SqU6.mul_h, ph, qh, pc]; ring,
      by rw [SqU6.mul_i, pi, qi, pd]; ring, ?_, ?_, ?_, ?_⟩
    · rw [SqU6.mul_j, pa, zero_mul, add_zero, pf, zero_mul, add_zero]; exact dvd_add pj qj
    · rw [SqU6.mul_k, pb, zero_mul, add_zero, pg, zero_mul, add_zero]; exact dvd_add pk qk
    · rw [SqU6.mul_l, pc, zero_mul, add_zero, ph, zero_mul, add_zero]; exact dvd_add pl ql
    · rw [SqU6.mul_m, pa, zero_mul, add_zero, pf, zero_mul, add_zero, qd, mul_zero, add_zero]
      exact dvd_add pm qm
  one_mem' := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by rw [SqU6.one_j]; exact dvd_zero _,
    by rw [SqU6.one_k]; exact dvd_zero _, by rw [SqU6.one_l]; exact dvd_zero _,
    by rw [SqU6.one_m]; exact dvd_zero _⟩
  inv_mem' := by
    rintro p ⟨pa, pb, pc, pd, pe, pf, pg, ph, pi, pj, pk, pl, pm⟩
    refine ⟨by rw [SqU6.inv_a, pa]; ring, by rw [SqU6.inv_b, pb]; ring,
      by rw [SqU6.inv_c, pc]; ring, by rw [SqU6.inv_d, pd]; ring,
      by rw [SqU6.inv_e, pe]; ring, by rw [SqU6.inv_f, pf, pa, pb]; ring,
      by rw [SqU6.inv_g, pg, pb, pc]; ring, by rw [SqU6.inv_h, ph, pc, pd]; ring,
      by rw [SqU6.inv_i, pi, pd, pe]; ring, ?_, ?_, ?_, ?_⟩
    · rw [SqU6.inv_j, pa, pb, pc, pf, pg]; simpa using pj.neg_right
    · rw [SqU6.inv_k, pb, pc, pd, pg, ph]; simpa using pk.neg_right
    · rw [SqU6.inv_l, pc, pd, pe, ph, pi]; simpa using pl.neg_right
    · rw [SqU6.inv_m, pa, pb, pc, pd, pf, pg, ph]; simpa using pm.neg_right

theorem forceSharpN2_mem {z : SqU6 gr3R} :
    z ∈ forceSharpN2 ↔ z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0
      ∧ (2 : gr3R) ∣ z.f ∧ (2 : gr3R) ∣ z.g ∧ (2 : gr3R) ∣ z.h ∧ (2 : gr3R) ∣ z.j := Iff.rfl

theorem forceSharpN3_mem {z : SqU6 gr3R} :
    z ∈ forceSharpN3 ↔ z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0 ∧ z.f = 0 ∧ z.g = 0
      ∧ z.h = 0 ∧ z.i = 0 ∧ (4 : gr3R) ∣ z.j ∧ (2 : gr3R) ∣ z.k ∧ (2 : gr3R) ∣ z.l
      ∧ (2 : gr3R) ∣ z.m := Iff.rfl

/-- The sharp depth-one target sits inside the committed one: forgetting `2 | g`. -/
theorem forceSharpN2_le_stageN2 : forceSharpN2 ≤ stageN2 := by
  rintro z ⟨za, zb, zc, zd, ze, zf, -, zh, zj⟩
  exact ⟨za, zb, zc, zd, ze, zf, zh, zj⟩

/-- The sharp depth-two target sits inside the committed one: `4 | j` implies `2 | j`, and
`2 | k` is simply forgotten. -/
theorem forceSharpN3_le_stageN3 : forceSharpN3 ≤ stageN3 := by
  rintro z ⟨za, zb, zc, zd, ze, zf, zg, zh, zi, ⟨t, zj⟩, -, zl, zm⟩
  exact ⟨za, zb, zc, zd, ze, zf, zg, zh, zi, ⟨2 * t, by rw [zj]; ring⟩, zl, zm⟩

/-- ⭐ **The depth-one sharpening is strict**: `<g=1>` lies in `stageN2` and not in `forceSharpN2`,
so the index is at least two (MEASURED: exactly two). -/
theorem forceSharp_gGen_mem_stageN2_not_N2 :
    (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN2
      ∧ (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∉ forceSharpN2 := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩, ?_⟩
  rintro ⟨-, -, -, -, -, -, ⟨t, ht⟩, -, -⟩
  revert ht
  revert t
  decide

/-- ⭐ **The depth-two sharpening is strict in BOTH new conditions**: `<j=2>` and `<k=1>` lie in
`stageN3` and in neither case in `forceSharpN3`, so the index is at least four (MEASURED: exactly
four). -/
theorem forceSharp_jGen_mem_stageN3_not_N3 :
    (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN3
      ∧ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∉ forceSharpN3 := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨1, by decide⟩, ⟨0, by decide⟩,
    ⟨0, by decide⟩⟩, ?_⟩
  rintro ⟨-, -, -, -, -, -, -, -, -, ⟨t, ht⟩, -, -, -⟩
  revert ht
  revert t
  decide

theorem forceSharp_kGen_mem_stageN3_not_N3 :
    (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN3
      ∧ (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩ : SqU6 gr3R) ∉ forceSharpN3 := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨0, by decide⟩, ⟨0, by decide⟩,
    ⟨0, by decide⟩⟩, ?_⟩
  rintro ⟨-, -, -, -, -, -, -, -, -, -, ⟨t, ht⟩, -, -⟩
  revert ht
  revert t
  decide

/-- Every element of `M_2'` is `gamma_2`-shaped. -/
theorem forceSharpN2_isGaTwo {p : SqU6 gr3R} (hp : p ∈ forceSharpN2) : p.IsGaTwo :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1⟩

/-- …and its four load-bearing coordinates are even. -/
theorem forceSharpN2_even {p : SqU6 gr3R} (hp : p ∈ forceSharpN2) :
    (2 : gr3R) ∣ p.f ∧ (2 : gr3R) ∣ p.g ∧ (2 : gr3R) ∣ p.h ∧ (2 : gr3R) ∣ p.j :=
  ⟨hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2⟩

/-- Every element of `M_3'` is `gamma_3`-shaped. -/
theorem forceSharpN3_isGaThree {z : SqU6 gr3R} (hz : z ∈ forceSharpN3) : z.IsGaThree :=
  ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2.1, hz.2.2.2.2.2.2.1,
    hz.2.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.2.1⟩

/-- …its first class-three coordinate is divisible by four, and the other three are even. -/
theorem forceSharpN3_dvd {z : SqU6 gr3R} (hz : z ∈ forceSharpN3) :
    (4 : gr3R) ∣ z.j ∧ (2 : gr3R) ∣ z.k ∧ (2 : gr3R) ∣ z.l ∧ (2 : gr3R) ∣ z.m :=
  ⟨hz.2.2.2.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.2.2.2.1, hz.2.2.2.2.2.2.2.2.2.2.2.1,
    hz.2.2.2.2.2.2.2.2.2.2.2.2⟩

end Lattices

/-! ## 2 The two commutator steps -/

section Steps

/-- ⭐ **Step one, sharpened.**  A commutator of two elements with even `(1,2)`- and
`(3,4)`-columns is a `gamma_2`-element with `f`, `g`, `h` AND `j` even.  The committed
`GradedFiveStageFour.stageN2_of_commutator` proves everything here except the `g`-coordinate,
and that one is the `(b, c)`-pairing `p.b * q.c - p.c * q.b`, both of whose monomials meet the
hypothesis's even `(3,4)`-column. -/
theorem forceSharpN2_of_commutator {p q : SqU6 gr3R} (hp : p ∈ stageN1) (hq : q ∈ stageN1) :
    ⁅p, q⁆ ∈ forceSharpN2 := by
  obtain ⟨⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩⟩ := mem_stageN1.mp hp
  obtain ⟨⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩⟩ := mem_stageN1.mp hq
  rw [commutatorElement_eq_commP, forceSharpN2_mem]
  refine ⟨SqU6.commP_a _ _, SqU6.commP_b _ _, SqU6.commP_c _ _, SqU6.commP_d _ _,
    SqU6.commP_e _ _, ⟨s₁ * q.b - p.b * t₁, ?_⟩, ⟨p.b * t₂ - s₂ * q.b, ?_⟩,
    ⟨s₂ * q.d - p.d * t₂, ?_⟩,
    ⟨s₁ * q.g - p.g * t₁ - s₂ * q.f + t₂ * p.f
      - 2 * (s₁ * (q.b * t₂)) - 2 * (s₁ * (q.b * s₂)) + 2 * (t₂ * (p.b * t₁))
      + 2 * (p.b * (s₂ * t₁)), ?_⟩⟩
  · simp only [SqU6.commP_f, SqU6.inv_a, SqU6.inv_b, hs₁, ht₁]
    ring
  · simp only [SqU6.commP_g, SqU6.inv_b, SqU6.inv_c, hs₂, ht₂]
    ring
  · simp only [SqU6.commP_h, SqU6.inv_c, SqU6.inv_d, hs₂, ht₂]
    ring
  · simp only [SqU6.commP_j, SqU6.u6Comm3L, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_f,
      SqU6.inv_g, hs₁, hs₂, ht₁, ht₂]
    ring

/-- ⭐⭐ **Step two, sharpened.**  Pairing a `forceSharpN2`-element against an even-column letter
gives a `gamma_3`-element with `j` divisible by **four** and `k`, `l`, `m` even.

The two new conclusions come from opposite sides.  `4 | j` is the sharpening's own product: on
a `gamma_2`-element the class-three left form collapses to `p.f * q.c - p.g * q.a`, and BOTH
factors of BOTH monomials are even - `p.f`, `p.g` by `forceSharpN2` and `q.a`, `q.c` by `stageN1`.
`2 | k` needs nothing from the letter at all: the middle form collapses to
`p.g * q.d - p.h * q.b`, already even from the dressing side.  This is why the committed chain,
which does not know `2 | g`, cannot reach either. -/
theorem forceSharpN3_of_commutator {p q : SqU6 gr3R} (hp : p ∈ forceSharpN2) (hq : q ∈ stageN1) :
    ⁅p, q⁆ ∈ forceSharpN3 := by
  obtain ⟨pa, pb, pc, pd, pe, ⟨f', hf⟩, ⟨g', hg⟩, ⟨h', hh⟩, ⟨j', hj⟩⟩ := forceSharpN2_mem.mp hp
  obtain ⟨⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩⟩ := mem_stageN1.mp hq
  rw [commutatorElement_eq_commP, forceSharpN3_mem]
  refine ⟨SqU6.commP_a _ _, SqU6.commP_b _ _, SqU6.commP_c _ _, SqU6.commP_d _ _,
    SqU6.commP_e _ _, ?_, ?_, ?_, ?_, ⟨f' * t₂ - g' * t₁, ?_⟩,
    ⟨g' * q.d - h' * q.b, ?_⟩, ⟨h' * q.e - p.i * t₂, ?_⟩, ?_⟩
  · simp only [SqU6.commP_f, SqU6.inv_a, SqU6.inv_b, pa, pb]
    ring
  · simp only [SqU6.commP_g, SqU6.inv_b, SqU6.inv_c, pb, pc]
    ring
  · simp only [SqU6.commP_h, SqU6.inv_c, SqU6.inv_d, pc, pd]
    ring
  · simp only [SqU6.commP_i, SqU6.inv_d, SqU6.inv_e, pd, pe]
    ring
  · simp only [SqU6.commP_j, SqU6.u6Comm3L, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_f,
      SqU6.inv_g, pa, pb, pc, hf, hg, ht₁, ht₂]
    ring
  · simp only [SqU6.commP_k, SqU6.u6Comm3M, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d, SqU6.inv_g,
      SqU6.inv_h, pb, pc, pd, hg, hh]
    ring
  · simp only [SqU6.commP_l, SqU6.u6Comm3R, SqU6.inv_c, SqU6.inv_d, SqU6.inv_e, SqU6.inv_h,
      SqU6.inv_i, pc, pd, pe, hh, ht₂]
    ring
  · refine ⟨-(p.k * t₁) + j' * q.d - f' * (q.c * q.d) + f' * q.h - h' * q.f
      + 2 * (g' * (t₁ * q.d)), ?_⟩
    simp only [SqU6.commP_m, SqU6.u6Comm4L, SqU6.inv_a, SqU6.inv_b, SqU6.inv_c, SqU6.inv_d,
      SqU6.inv_f, SqU6.inv_g, SqU6.inv_h, SqU6.inv_j, SqU6.inv_k,
      pa, pb, pc, pd, hf, hg, hh, hj, ht₁]
    ring

end Steps

/-! ## 3 The two sharpened bounds -/

section Bounds

/-- ⭐⭐ **THE SHARPENED DEPTH-ONE BOUND, a CONTAINMENT.**  At any marking all of whose slots
have an even `(1,2)`-column and an even `(3,4)`-column, every achievable `gamma_2`-dressing has
`f`, `g`, `h` and `j` even.  `GradedFiveGammaTwo.forceLcs_one_le_stageN2` is this without the
`g`. -/
theorem forceLcs_one_le_stageN2' {H : Subgroup (SqU6 gr3R)} (hH : H ≤ stageN1) :
    forceLcs H 1 ≤ forceSharpN2 :=
  Subgroup.commutator_le.mpr fun _p hp _q hq => forceSharpN2_of_commutator (hH hp) (hH hq)

/-- ⭐⭐⭐ **THE SHARPENED DEPTH-TWO BOUND, a CONTAINMENT.**  At any marking all of whose slots
have an even `(1,2)`-column and an even `(3,4)`-column, every achievable `gamma_3`-dressing has
`j` divisible by **four** and `k`, `l`, `m` even.

⚠ This is a containment and nothing more; `forceSharp_stageN1_two_eq` below upgrades it
to an equality at `H = stageN1`, and only there. -/
theorem forceLcs_two_le_stageN3' {H : Subgroup (SqU6 gr3R)} (hH : H ≤ stageN1) :
    forceLcs H 2 ≤ forceSharpN3 :=
  Subgroup.commutator_le.mpr fun _p hp _q hq =>
    forceSharpN3_of_commutator (forceLcs_one_le_stageN2' hH hp) (hH hq)

/-- `GradedFiveGammaTwo.forceLcs_one_le_stageN2`, recovered.  Nothing committed changes. -/
theorem forceSharp_recover_one_le_stageN2 {H : Subgroup (SqU6 gr3R)} (hH : H ≤ stageN1) :
    forceLcs H 1 ≤ stageN2 :=
  le_trans (forceLcs_one_le_stageN2' hH) forceSharpN2_le_stageN2

/-- `GradedFiveStageFour.forceLcs_two_le_stageN3`, recovered. -/
theorem forceSharp_recover_two_le_stageN3 {H : Subgroup (SqU6 gr3R)} (hH : H ≤ stageN1) :
    forceLcs H 2 ≤ stageN3 :=
  le_trans (forceLcs_two_le_stageN3' hH) forceSharpN3_le_stageN3

/-- ⭐ **The class-three coordinates of every achievable stage-four dressing, mod four.**  The
form the class-five stack consumes: this is `GradedFiveStageFour.stageN3_even` with `2 | j`
replaced by `4 | j` and `2 | k` added. -/
theorem forceSharp_two_dvd {H : Subgroup (SqU6 gr3R)} (hH : H ≤ stageN1) {z : SqU6 gr3R}
    (hz : z ∈ forceLcs H 2) :
    (4 : gr3R) ∣ z.j ∧ (2 : gr3R) ∣ z.k ∧ (2 : gr3R) ∣ z.l ∧ (2 : gr3R) ∣ z.m :=
  forceSharpN3_dvd (forceLcs_two_le_stageN3' hH hz)

/-- …and its `gamma_2`-level companion: `GradedFiveGammaTwo.stageN2_even` with `2 | g`
added. -/
theorem forceSharp_one_dvd {H : Subgroup (SqU6 gr3R)} (hH : H ≤ stageN1) {z : SqU6 gr3R}
    (hz : z ∈ forceLcs H 1) :
    (2 : gr3R) ∣ z.f ∧ (2 : gr3R) ∣ z.g ∧ (2 : gr3R) ∣ z.h ∧ (2 : gr3R) ∣ z.j :=
  forceSharpN2_even (forceLcs_one_le_stageN2' hH hz)

end Bounds

/-! ## 4 The reverse containments, and the achievability test

Everything above is an upper bound.  This section proves the matching lower bounds at
`H = stageN1`, which is the level at which the audit's uniform question is asked, and so turns
both bounds into EQUALITIES there. -/

section Reverse

/-- A `gamma_3`-shaped element, written from its six live coordinates. -/
def forceSharpUnit3 (j k l m n o : gr3R) : SqU6 gr3R :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, j, k, l, m, n, o⟩

theorem forceSharpUnit3_one : forceSharpUnit3 0 0 0 0 0 0 = 1 := rfl

/-- The `gamma_3` layer is abelian and adds coordinatewise. -/
theorem forceSharpUnit3_mul (j k l m n o j' k' l' m' n' o' : gr3R) :
    forceSharpUnit3 j k l m n o * forceSharpUnit3 j' k' l' m' n' o'
      = forceSharpUnit3 (j + j') (k + k') (l + l') (m + m') (n + n') (o + o') := by
  ext <;>
    simp only [forceSharpUnit3, SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e,
      SqU6.mul_f, SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l,
      SqU6.mul_m, SqU6.mul_n, SqU6.mul_o] <;>
    ring

theorem forceSharpUnit3_pow (j k l m n o : gr3R) : ∀ e : ℕ,
    forceSharpUnit3 j k l m n o ^ e
      = forceSharpUnit3 (e * j) (e * k) (e * l) (e * m) (e * n) (e * o) := by
  intro e
  induction e with
  | zero => simpa using forceSharpUnit3_one.symm
  | succ e ih =>
      rw [pow_succ, ih, forceSharpUnit3_mul]
      push_cast
      ring_nf

/-- Every `gamma_3`-shaped element is its own unit form. -/
theorem forceSharpUnit3_eq {z : SqU6 gr3R} (hz : z.IsGaThree) :
    z = forceSharpUnit3 z.j z.k z.l z.m z.n z.o := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hz
  ext <;> simp only [forceSharpUnit3, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-- …and it factors coordinate by coordinate. -/
theorem forceSharpUnit3_split (j k l m n o : gr3R) :
    forceSharpUnit3 j k l m n o
      = forceSharpUnit3 j 0 0 0 0 0 * (forceSharpUnit3 0 k 0 0 0 0 * (forceSharpUnit3 0 0 l 0 0 0
          * (forceSharpUnit3 0 0 0 m 0 0 * (forceSharpUnit3 0 0 0 0 n 0
            * forceSharpUnit3 0 0 0 0 0 o)))) := by
  simp only [forceSharpUnit3_mul, add_zero, zero_add]

/-- `(t.val : gr3R) = t`, the one arithmetic fact the power argument needs. -/
private theorem forceSharpNatCast : ∀ t : gr3R, ((t.val : ℕ) : gr3R) = t := by decide

/-- If a subgroup contains the single-coordinate unit `g` at value `u`, it contains it at every
multiple of `u`. -/
private theorem forceSharpUnitDvd {K : Subgroup (SqU6 gr3R)} {u t : gr3R} (hut : u ∣ t)
    (F : gr3R → SqU6 gr3R) (hF : ∀ s s', F s * F s' = F (s + s'))
    (hF0 : F 0 = 1) (hu : F u ∈ K) : F t ∈ K := by
  obtain ⟨s, rfl⟩ := hut
  have hpow : ∀ e : ℕ, F u ^ e = F (e * u) := by
    intro e
    induction e with
    | zero => simpa using hF0.symm
    | succ e ih => rw [pow_succ, ih, hF]; push_cast; ring_nf
  have : F u ^ s.val ∈ K := pow_mem hu _
  rwa [hpow, forceSharpNatCast, mul_comm] at this


/-- ⭐⭐ **The sharp depth-two target is ACHIEVED.**  Each of its six coordinate generators is an
explicit iterated commutator of single-coordinate members of `stageN1`, and the `gamma_3` layer
is abelian, so every member of `forceSharpN3` is a product of them. -/
theorem forceSharpN3_le_forceLcs_stageN1_two : forceSharpN3 ≤ forceLcs stageN1 2 := by
  -- the four witnesses at depth one
  have mem1 : ∀ {x y : SqU6 gr3R}, x ∈ stageN1 → y ∈ stageN1 → ⁅x, y⁆ ∈ forceLcs stageN1 1 :=
    fun hx hy => Subgroup.commutator_mem_commutator hx hy
  have mem2 : ∀ {x y : SqU6 gr3R}, x ∈ forceLcs stageN1 1 → y ∈ stageN1 →
      ⁅x, y⁆ ∈ forceLcs stageN1 2 := fun hx hy => Subgroup.commutator_mem_commutator hx hy
  have hA : (⟨2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN1 :=
    ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
  have hB : (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN1 :=
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  have hC : (⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN1 :=
    ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
  have hD : (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN1 :=
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  have hE : (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN1 :=
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  have hH1 : (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN1 :=
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  have hJ7 : (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN1 :=
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  -- the six generators of `forceSharpN3`
  have gJ : forceSharpUnit3 4 0 0 0 0 0 ∈ forceLcs stageN1 2 := by
    have h := mem2 (mem1 hA hB) hC
    rwa [show ⁅⁅(⟨2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R),
      (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆,
      (⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆
        = forceSharpUnit3 4 0 0 0 0 0 from by
      rw [commutatorElement_eq_commP, commutatorElement_eq_commP]; decide] at h
  have gK : forceSharpUnit3 0 2 0 0 0 0 ∈ forceLcs stageN1 2 := by
    have h := mem2 (mem1 hB hC) hD
    rwa [show ⁅⁅(⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R),
      (⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆,
      (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆
        = forceSharpUnit3 0 2 0 0 0 0 from by
      rw [commutatorElement_eq_commP, commutatorElement_eq_commP]; decide] at h
  have gL : forceSharpUnit3 0 0 2 0 0 0 ∈ forceLcs stageN1 2 := by
    have h := mem2 (mem1 hC hD) hE
    rwa [show ⁅⁅(⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R),
      (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆,
      (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆
        = forceSharpUnit3 0 0 2 0 0 0 from by
      rw [commutatorElement_eq_commP, commutatorElement_eq_commP]; decide] at h
  have gM : forceSharpUnit3 0 0 0 2 0 0 ∈ forceLcs stageN1 2 := by
    have h := mem2 (mem1 hA hB) hH1
    rwa [show ⁅⁅(⟨2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R),
      (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆,
      (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆
        = forceSharpUnit3 0 0 0 2 0 0 from by
      rw [commutatorElement_eq_commP, commutatorElement_eq_commP]; decide] at h
  have gN : forceSharpUnit3 0 0 0 0 1 0 ∈ forceLcs stageN1 2 := by
    have h := mem2 (mem1 hB hH1) hE
    rwa [show ⁅⁅(⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R),
      (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆,
      (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆
        = forceSharpUnit3 0 0 0 0 1 0 from by
      rw [commutatorElement_eq_commP, commutatorElement_eq_commP]; decide] at h
  have gO : forceSharpUnit3 0 0 0 0 0 1 ∈ forceLcs stageN1 2 := by
    have h := mem2 (mem1 hD hE) hJ7
    rwa [show ⁅⁅(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R),
      (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆,
      (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆
        = forceSharpUnit3 0 0 0 0 0 1 from by
      rw [commutatorElement_eq_commP, commutatorElement_eq_commP]; decide] at h
  -- and now an arbitrary member
  intro z hz
  obtain ⟨hj, hk, hl, hm⟩ := forceSharpN3_dvd hz
  rw [forceSharpUnit3_eq (forceSharpN3_isGaThree hz), forceSharpUnit3_split]
  refine mul_mem ?_ (mul_mem ?_ (mul_mem ?_ (mul_mem ?_ (mul_mem ?_ ?_))))
  · exact forceSharpUnitDvd hj (fun t => forceSharpUnit3 t 0 0 0 0 0)
      (fun s s' => by simp [forceSharpUnit3_mul]) forceSharpUnit3_one gJ
  · exact forceSharpUnitDvd hk (fun t => forceSharpUnit3 0 t 0 0 0 0)
      (fun s s' => by simp [forceSharpUnit3_mul]) forceSharpUnit3_one gK
  · exact forceSharpUnitDvd hl (fun t => forceSharpUnit3 0 0 t 0 0 0)
      (fun s s' => by simp [forceSharpUnit3_mul]) forceSharpUnit3_one gL
  · exact forceSharpUnitDvd hm (fun t => forceSharpUnit3 0 0 0 t 0 0)
      (fun s s' => by simp [forceSharpUnit3_mul]) forceSharpUnit3_one gM
  · exact forceSharpUnitDvd (one_dvd _) (fun t => forceSharpUnit3 0 0 0 0 t 0)
      (fun s s' => by simp [forceSharpUnit3_mul]) forceSharpUnit3_one (by simpa using gN)
  · exact forceSharpUnitDvd (one_dvd _) (fun t => forceSharpUnit3 0 0 0 0 0 t)
      (fun s s' => by simp [forceSharpUnit3_mul]) forceSharpUnit3_one (by simpa using gO)

/-- A `gamma_2`-shaped element, written from its ten live coordinates. -/
def forceSharpUnit2 (f g h i j k l m n o : gr3R) : SqU6 gr3R :=
  ⟨0, 0, 0, 0, 0, f, g, h, i, j, k, l, m, n, o⟩

theorem forceSharpUnit2_one : forceSharpUnit2 0 0 0 0 0 0 0 0 0 0 = 1 := rfl

/-- The `gamma_2` layer is NOT abelian - unlike `gamma_3` it has three genuine correction terms,
`f * h'` on `m`, `g * i'` on `n` and `f * l' + j * i'` on `o`.  They are the reason the
factorisation below has to be ORDERED. -/
theorem forceSharpUnit2_mul (f g h i j k l m n o f' g' h' i' j' k' l' m' n' o' : gr3R) :
    forceSharpUnit2 f g h i j k l m n o * forceSharpUnit2 f' g' h' i' j' k' l' m' n' o'
      = forceSharpUnit2 (f + f') (g + g') (h + h') (i + i') (j + j') (k + k') (l + l')
          (m + m' + f * h') (n + n' + g * i') (o + o' + f * l' + j * i') := by
  ext <;>
    simp only [forceSharpUnit2, SqU6.mul_a, SqU6.mul_b, SqU6.mul_c, SqU6.mul_d, SqU6.mul_e,
      SqU6.mul_f, SqU6.mul_g, SqU6.mul_h, SqU6.mul_i, SqU6.mul_j, SqU6.mul_k, SqU6.mul_l,
      SqU6.mul_m, SqU6.mul_n, SqU6.mul_o] <;>
    ring

/-- Every `gamma_2`-shaped element is its own unit form. -/
theorem forceSharpUnit2_eq {z : SqU6 gr3R} (hz : z.IsGaTwo) :
    z = forceSharpUnit2 z.f z.g z.h z.i z.j z.k z.l z.m z.n z.o := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hz
  ext <;> simp only [forceSharpUnit2, h1, h2, h3, h4, h5]

/-- …and it factors coordinate by coordinate, provided the three coordinates that carry the
corrections - `h`, `i` and `l` - are taken FIRST. -/
theorem forceSharpUnit2_split (f g h i j k l m n o : gr3R) :
    forceSharpUnit2 f g h i j k l m n o
      = forceSharpUnit2 0 0 h 0 0 0 0 0 0 0 * (forceSharpUnit2 0 0 0 i 0 0 0 0 0 0
        * (forceSharpUnit2 0 0 0 0 0 0 l 0 0 0 * (forceSharpUnit2 f 0 0 0 0 0 0 0 0 0
          * (forceSharpUnit2 0 g 0 0 0 0 0 0 0 0 * (forceSharpUnit2 0 0 0 0 j 0 0 0 0 0
            * (forceSharpUnit2 0 0 0 0 0 k 0 0 0 0 * (forceSharpUnit2 0 0 0 0 0 0 0 m 0 0
              * (forceSharpUnit2 0 0 0 0 0 0 0 0 n 0
                * forceSharpUnit2 0 0 0 0 0 0 0 0 0 o)))))))) := by
  simp only [forceSharpUnit2_mul, add_zero, zero_add, mul_zero, zero_mul]

/-- ⭐⭐ **The sharp depth-one target is ACHIEVED.**  Each of its ten coordinate generators is a
single explicit commutator of single-coordinate members of `stageN1`. -/
theorem forceSharpN2_le_forceLcs_stageN1_one : forceSharpN2 ≤ forceLcs stageN1 1 := by
  have mem1 : ∀ {x y : SqU6 gr3R}, x ∈ stageN1 → y ∈ stageN1 → ⁅x, y⁆ ∈ forceLcs stageN1 1 :=
    fun hx hy => Subgroup.commutator_mem_commutator hx hy
  have hA : (⟨2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN1 :=
    ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
  have hB : (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN1 :=
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  have hC : (⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN1 :=
    ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
  have hD : (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN1 :=
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  have hE : (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN1 :=
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  have hG1 : (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN1 :=
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  have hH1 : (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN1 :=
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  have hH7 : (⟨0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN1 :=
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  have hJ7 : (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN1 :=
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  have hL1 : (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩ : SqU6 gr3R) ∈ stageN1 :=
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  have hM7 : (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0⟩ : SqU6 gr3R) ∈ stageN1 :=
    ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩
  have gF : forceSharpUnit2 2 0 0 0 0 0 0 0 0 0 ∈ forceLcs stageN1 1 := by
    have h := mem1 hA hB
    rwa [show ⁅(⟨2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R),
      (⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆
        = forceSharpUnit2 2 0 0 0 0 0 0 0 0 0 from by
      rw [commutatorElement_eq_commP]; decide] at h
  have gG : forceSharpUnit2 0 2 0 0 0 0 0 0 0 0 ∈ forceLcs stageN1 1 := by
    have h := mem1 hB hC
    rwa [show ⁅(⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R),
      (⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆
        = forceSharpUnit2 0 2 0 0 0 0 0 0 0 0 from by
      rw [commutatorElement_eq_commP]; decide] at h
  have gH : forceSharpUnit2 0 0 2 0 0 0 0 0 0 0 ∈ forceLcs stageN1 1 := by
    have h := mem1 hC hD
    rwa [show ⁅(⟨0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R),
      (⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆
        = forceSharpUnit2 0 0 2 0 0 0 0 0 0 0 from by
      rw [commutatorElement_eq_commP]; decide] at h
  have gI : forceSharpUnit2 0 0 0 1 0 0 0 0 0 0 ∈ forceLcs stageN1 1 := by
    have h := mem1 hD hE
    rwa [show ⁅(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R),
      (⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆
        = forceSharpUnit2 0 0 0 1 0 0 0 0 0 0 from by
      rw [commutatorElement_eq_commP]; decide] at h
  have gJ : forceSharpUnit2 0 0 0 0 2 0 0 0 0 0 ∈ forceLcs stageN1 1 := by
    have h := mem1 hA hG1
    rwa [show ⁅(⟨2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R),
      (⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆
        = forceSharpUnit2 0 0 0 0 2 0 0 0 0 0 from by
      rw [commutatorElement_eq_commP]; decide] at h
  have gK : forceSharpUnit2 0 0 0 0 0 1 0 0 0 0 ∈ forceLcs stageN1 1 := by
    have h := mem1 hB hH1
    rwa [show ⁅(⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R),
      (⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆
        = forceSharpUnit2 0 0 0 0 0 1 0 0 0 0 from by
      rw [commutatorElement_eq_commP]; decide] at h
  have gL : forceSharpUnit2 0 0 0 0 0 0 1 0 0 0 ∈ forceLcs stageN1 1 := by
    have h := mem1 hE hH7
    rwa [show ⁅(⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R),
      (⟨0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆
        = forceSharpUnit2 0 0 0 0 0 0 1 0 0 0 from by
      rw [commutatorElement_eq_commP]; decide] at h
  have gM : forceSharpUnit2 0 0 0 0 0 0 0 1 0 0 ∈ forceLcs stageN1 1 := by
    have h := mem1 hD hJ7
    rwa [show ⁅(⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R),
      (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0⟩ : SqU6 gr3R)⁆
        = forceSharpUnit2 0 0 0 0 0 0 0 1 0 0 from by
      rw [commutatorElement_eq_commP]; decide] at h
  have gN : forceSharpUnit2 0 0 0 0 0 0 0 0 1 0 ∈ forceLcs stageN1 1 := by
    have h := mem1 hB hL1
    rwa [show ⁅(⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R),
      (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩ : SqU6 gr3R)⁆
        = forceSharpUnit2 0 0 0 0 0 0 0 0 1 0 from by
      rw [commutatorElement_eq_commP]; decide] at h
  have gO : forceSharpUnit2 0 0 0 0 0 0 0 0 0 1 ∈ forceLcs stageN1 1 := by
    have h := mem1 hE hM7
    rwa [show ⁅(⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : SqU6 gr3R),
      (⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0⟩ : SqU6 gr3R)⁆
        = forceSharpUnit2 0 0 0 0 0 0 0 0 0 1 from by
      rw [commutatorElement_eq_commP]; decide] at h
  intro z hz
  obtain ⟨hf, hg, hh, hj⟩ := forceSharpN2_even hz
  rw [forceSharpUnit2_eq (forceSharpN2_isGaTwo hz), forceSharpUnit2_split]
  refine mul_mem ?_ (mul_mem ?_ (mul_mem ?_ (mul_mem ?_ (mul_mem ?_ (mul_mem ?_
    (mul_mem ?_ (mul_mem ?_ (mul_mem ?_ ?_))))))))
  · exact forceSharpUnitDvd hh (fun t => forceSharpUnit2 0 0 t 0 0 0 0 0 0 0)
      (fun s s' => by simp [forceSharpUnit2_mul]) forceSharpUnit2_one gH
  · exact forceSharpUnitDvd (one_dvd _) (fun t => forceSharpUnit2 0 0 0 t 0 0 0 0 0 0)
      (fun s s' => by simp [forceSharpUnit2_mul]) forceSharpUnit2_one (by simpa using gI)
  · exact forceSharpUnitDvd (one_dvd _) (fun t => forceSharpUnit2 0 0 0 0 0 0 t 0 0 0)
      (fun s s' => by simp [forceSharpUnit2_mul]) forceSharpUnit2_one (by simpa using gL)
  · exact forceSharpUnitDvd hf (fun t => forceSharpUnit2 t 0 0 0 0 0 0 0 0 0)
      (fun s s' => by simp [forceSharpUnit2_mul]) forceSharpUnit2_one gF
  · exact forceSharpUnitDvd hg (fun t => forceSharpUnit2 0 t 0 0 0 0 0 0 0 0)
      (fun s s' => by simp [forceSharpUnit2_mul]) forceSharpUnit2_one gG
  · exact forceSharpUnitDvd hj (fun t => forceSharpUnit2 0 0 0 0 t 0 0 0 0 0)
      (fun s s' => by simp [forceSharpUnit2_mul]) forceSharpUnit2_one gJ
  · exact forceSharpUnitDvd (one_dvd _) (fun t => forceSharpUnit2 0 0 0 0 0 t 0 0 0 0)
      (fun s s' => by simp [forceSharpUnit2_mul]) forceSharpUnit2_one (by simpa using gK)
  · exact forceSharpUnitDvd (one_dvd _) (fun t => forceSharpUnit2 0 0 0 0 0 0 0 t 0 0)
      (fun s s' => by simp [forceSharpUnit2_mul]) forceSharpUnit2_one (by simpa using gM)
  · exact forceSharpUnitDvd (one_dvd _) (fun t => forceSharpUnit2 0 0 0 0 0 0 0 0 t 0)
      (fun s s' => by simp [forceSharpUnit2_mul]) forceSharpUnit2_one (by simpa using gN)
  · exact forceSharpUnitDvd (one_dvd _) (fun t => forceSharpUnit2 0 0 0 0 0 0 0 0 0 t)
      (fun s s' => by simp [forceSharpUnit2_mul]) forceSharpUnit2_one (by simpa using gO)

/-- ⭐⭐ **THE DEPTH-ONE BOUND IS AN EQUALITY AT `H = stageN1`** as well. -/
theorem forceSharp_stageN1_one_eq : forceLcs stageN1 1 = forceSharpN2 :=
  le_antisymm (forceLcs_one_le_stageN2' le_rfl) forceSharpN2_le_forceLcs_stageN1_one

/-- ⭐⭐⭐ **THE DEPTH-TWO BOUND IS AN EQUALITY AT `H = stageN1`.**  So `forceSharpN3` is not merely
the smallest congruence lattice that works: it is the smallest SUBGROUP that works, and
`forceLcs_two_le_stageN3'` cannot be improved at the uniform level by any target whatsoever.

⚠ Scope: at `H = stageN1` only.  For a smaller `H` the honest lattice can be strictly smaller,
and W64-VERIFY's pointwise table records markings where it is. -/
theorem forceSharp_stageN1_two_eq : forceLcs stageN1 2 = forceSharpN3 :=
  le_antisymm (forceLcs_two_le_stageN3' le_rfl) forceSharpN3_le_forceLcs_stageN1_two

/-- ⭐⭐ **A decidable membership test for achievability at the uniform level.**  Before this the
tree owned upper bounds only: it could show a candidate stage-four dressing NOT achievable, but
to show one IS achievable it had to exhibit a commutator by hand. -/
theorem forceSharp_mem_forceLcs_stageN1_two_iff {z : SqU6 gr3R} :
    z ∈ forceLcs stageN1 2 ↔ z.a = 0 ∧ z.b = 0 ∧ z.c = 0 ∧ z.d = 0 ∧ z.e = 0 ∧ z.f = 0
      ∧ z.g = 0 ∧ z.h = 0 ∧ z.i = 0 ∧ (4 : gr3R) ∣ z.j ∧ (2 : gr3R) ∣ z.k ∧ (2 : gr3R) ∣ z.l
      ∧ (2 : gr3R) ∣ z.m := by
  rw [forceSharp_stageN1_two_eq]
  exact forceSharpN3_mem

end Reverse

/-! ## 5 What the sharpening does to the correction block -/

section Corr

variable {R : Type} [CommRing R]

/-- ⭐ **The correction block is even with NO hypothesis on the frame**, as soon as the
dressings' `j`, `k` and `l` are even.  The committed `GradedFiveStageFour.gaThreeCorr_even`
carries `2 | s.a`, `2 | x.a` and `2 | y.a`, and every one of those three exists to kill the
single block `z₂.k * (s.a * y.e + s.e * y.a)`; the other two `k`-blocks already have even
coefficients, and the six `j`- and `l`-blocks are killed from the dressing side.  On the
achievable lattice `2 | z.k` is now known, so the frame drops out entirely.

⚠ **This does NOT widen `gaThreeShiftO_even`**, which keeps `∀ i, 2 | (m i).a`: the class-five
pairing `gaThreePair` also contains `z.n * L.a`, and `n` is unconstrained on the achievable
lattice.  What is recorded here is a cleaner factorisation of the same theorem. -/
theorem forceSharp_gaThreeCorr_even_of_evenK {s x y z₀ z₁ z₂ : SqU6 R}
    (h0j : (2 : R) ∣ z₀.j) (h0k : (2 : R) ∣ z₀.k) (h0l : (2 : R) ∣ z₀.l)
    (h1j : (2 : R) ∣ z₁.j) (h1k : (2 : R) ∣ z₁.k) (h1l : (2 : R) ∣ z₁.l)
    (h2j : (2 : R) ∣ z₂.j) (h2k : (2 : R) ∣ z₂.k) (h2l : (2 : R) ∣ z₂.l) :
    (2 : R) ∣ gaThreeCorr s x y z₀ z₁ z₂ := by
  obtain ⟨j0, h0j⟩ := h0j
  obtain ⟨k0, h0k⟩ := h0k
  obtain ⟨l0, h0l⟩ := h0l
  obtain ⟨j1, h1j⟩ := h1j
  obtain ⟨k1, h1k⟩ := h1k
  obtain ⟨l1, h1l⟩ := h1l
  obtain ⟨j2, h2j⟩ := h2j
  obtain ⟨k2, h2k⟩ := h2k
  obtain ⟨l2, h2l⟩ := h2l
  refine ⟨j0 * (-(s.d * x.e) + s.e * x.d - 4 * (x.d * x.e) + 2 * (x.d * y.e) + y.d * y.e)
      + k0 * (8 * (x.a * x.e) - 2 * (x.a * y.e) - 2 * (x.e * y.a) - 2 * (y.a * y.e))
      + l0 * (s.a * x.b - s.b * x.a - 4 * (x.a * x.b) + 2 * (x.b * y.a) + y.a * y.b)
      + j1 * (3 * (s.d * x.e) - 2 * (s.d * y.e) + s.e * x.d - 20 * (x.d * x.e)
        + 20 * (x.d * y.e) - 4 * (y.d * y.e))
      + k1 * (2 * (s.a * s.e) - 14 * (s.a * x.e) + 10 * (s.a * y.e) - 14 * (s.e * x.a)
        + 10 * (s.e * y.a) + 130 * (x.a * x.e) - 100 * (x.a * y.e) - 100 * (x.e * y.a)
        + 80 * (y.a * y.e))
      + l1 * (-2 * (s.a * s.b) + 11 * (s.a * x.b) - 8 * (s.a * y.b) + 13 * (s.b * x.a)
        - 10 * (s.b * y.a) - 110 * (x.a * x.b) + 80 * (x.a * y.b) + 100 * (x.b * y.a)
        - 76 * (y.a * y.b))
      + j2 * (-2 * (s.d * y.e) + s.e * y.d)
      + k2 * (s.a * y.e + s.e * y.a)
      + l2 * (s.a * y.b - 2 * (s.b * y.a)), ?_⟩
  rw [gaThreeCorr, h0j, h0k, h0l, h1j, h1k, h1l, h2j, h2k, h2l]
  ring

end Corr

/-! ## 6 The consumer: the class-five stack's class-four row, mod four

`GradedStageNecessity.gaThreeShift_m` and `GradedFiveStageFour.gaThreePairL`, `gaThreeCore`,
`gaThreeHandle` are CITED here and never edited.  What changes is only which divisibility the
dressing brings to them, and the change is visible: the row moves from mod two to mod four. -/

section Consumer

section Generic

variable {R : Type} [CommRing R] {h : ℕ}

/-- ⭐ **The class-four graded Fox pairing, mod FOUR.**  `GradedFiveStageFour.gaThreePairL z L`
is `z.j * L.d - z.k * L.a`.  The sharpened lattice makes `z.j` divisible by four outright, and
pairs an even `z.k` against the even `(1,2)`-column, so each monomial carries two factors of
two.  From the committed lattice, which gives `2 | z.j` and nothing whatever on `z.k`, both
monomials are merely even. -/
theorem forceSharp_gaThreePairL_dvd_four {z L : SqU6 R}
    (hj : (4 : R) ∣ z.j) (hk : (2 : R) ∣ z.k) (ha : (2 : R) ∣ L.a) :
    (4 : R) ∣ gaThreePairL z L := by
  obtain ⟨j', hj⟩ := hj
  obtain ⟨k', hk⟩ := hk
  obtain ⟨a', ha⟩ := ha
  refine ⟨j' * L.d - k' * a', ?_⟩
  simp only [gaThreePairL, hj, hk, ha]
  ring

/-- ⭐ **The core's class-four row, mod four.**  `-4 * z₁.m` is divisible by four outright, so
the middle slot needs no hypothesis at all; `2 * z₂.m` needs only that `z₂.m` is even, which
the sharpened lattice supplies; and the three pairings are the lemma above at the three frame
letters.  The middle letter is the Fox combination `sqFoxX6 s x y`, whose `(1,2)`-column
`10 * x.a - s.a - 8 * y.a` is even as soon as `s.a` is. -/
theorem forceSharp_gaThreeCore_m_dvd_four {s x y z₀ z₁ z₂ : SqU6 R}
    (hsa : (2 : R) ∣ s.a) (hxa : (2 : R) ∣ x.a) (hya : (2 : R) ∣ y.a)
    (h0 : (4 : R) ∣ z₀.j ∧ (2 : R) ∣ z₀.k) (h1 : (4 : R) ∣ z₁.j ∧ (2 : R) ∣ z₁.k)
    (h2 : (4 : R) ∣ z₂.j ∧ (2 : R) ∣ z₂.k) (h2m : (2 : R) ∣ z₂.m) :
    (4 : R) ∣ (gaThreeCore s x y z₀ z₁ z₂).m := by
  have hfox : (2 : R) ∣ (sqFoxX6 s x y).a := by
    obtain ⟨s', hs⟩ := hsa
    obtain ⟨x', hx⟩ := hxa
    obtain ⟨y', hy⟩ := hya
    refine ⟨10 * x' - s' - 8 * y', ?_⟩
    simp only [sqFoxX6_a, hs, hx, hy]
    ring
  have hrow : (gaThreeCore s x y z₀ z₁ z₂).m
      = -4 * z₁.m + 2 * z₂.m + (gaThreePairL z₀ x + gaThreePairL z₁ (sqFoxX6 s x y)
        + gaThreePairL z₂ y) := rfl
  rw [hrow]
  refine dvd_add (dvd_add ⟨-z₁.m, by ring⟩ ?_)
    (dvd_add (dvd_add (forceSharp_gaThreePairL_dvd_four h0.1 h0.2 hxa)
      (forceSharp_gaThreePairL_dvd_four h1.1 h1.2 hfox))
      (forceSharp_gaThreePairL_dvd_four h2.1 h2.2 hya))
  obtain ⟨m', hm'⟩ := h2m
  exact ⟨m', by rw [hm']; ring⟩

/-- ⭐ **A handle's class-four row, mod four**: the difference of two pairings. -/
theorem forceSharp_gaThreeHandle_m_dvd_four {p q z w : SqU6 R}
    (hpa : (2 : R) ∣ p.a) (hqa : (2 : R) ∣ q.a)
    (hz : (4 : R) ∣ z.j ∧ (2 : R) ∣ z.k) (hw : (4 : R) ∣ w.j ∧ (2 : R) ∣ w.k) :
    (4 : R) ∣ (gaThreeHandle p q z w).m := by
  have hrow : (gaThreeHandle p q z w).m = gaThreePairL z q - gaThreePairL w p := rfl
  rw [hrow]
  exact dvd_sub (forceSharp_gaThreePairL_dvd_four hz.1 hz.2 hqa)
    (forceSharp_gaThreePairL_dvd_four hw.1 hw.2 hpa)

/-- ⭐⭐ **THE CONSUMER, at the level of the shift.**  At any marking whose slots have an even
`(1,2)`-column, a dressing whose class-three coordinates satisfy the SHARPENED congruences
moves the relator's first class-four row by a multiple of FOUR.  `gaThreeShift_m` supplies the
decomposition into the core and the handles, and both halves are mod four.

Contrast `GradedFiveStageFour.gaThreeShiftO_even`, one row up: the class-five row does NOT gain,
because `gaThreePair` contains `z.m * L.e` and `z.n * L.a`, and `n` is unconstrained on the
achievable lattice.  The gain is exactly at the class-four row. -/
theorem forceSharp_gaThreeShift_m_dvd_four {m z : Fin (sqRank h) → SqU6 R}
    (ha : ∀ i, (2 : R) ∣ (m i).a)
    (hz : ∀ i, (4 : R) ∣ (z i).j ∧ (2 : R) ∣ (z i).k)
    (h2m : (2 : R) ∣ (z 2).m) :
    (4 : R) ∣ (gaThreeShift h m z).m := by
  rw [gaThreeShift_m]
  exact dvd_add
    (forceSharp_gaThreeCore_m_dvd_four (ha 0) (ha 1) (ha 2) (hz 0) (hz 1) (hz 2) h2m)
    (Finset.dvd_sum fun k _ =>
      forceSharp_gaThreeHandle_m_dvd_four (ha _) (ha _) (hz _) (hz _))

end Generic

/-- ⭐⭐ **End to end, off the achievable lattice, through the primed bound.**  This is the
statement the sharpening buys: the hypothesis on the dressing is membership in the honest
`gamma_3` of the image subgroup, not a declared lattice, and `forceLcs_two_le_stageN3'` is what
turns it into the four congruences.  Running the same argument through the committed
`GradedFiveStageFour.forceLcs_two_le_stageN3` yields only `2 |`. -/
theorem forceSharp_stageShift_m_dvd_four {h : ℕ} {H : Subgroup (SqU6 gr3R)}
    {m z : Fin (sqRank h) → SqU6 gr3R} (hH : H ≤ stageN1)
    (hm : ∀ i, m i ∈ stageN1) (hz : ∀ i, z i ∈ forceLcs H 2) :
    (4 : gr3R) ∣ (gaThreeShift h m z).m :=
  forceSharp_gaThreeShift_m_dvd_four
    (fun i => (mem_stageN1.mp (hm i)).1)
    (fun i => ⟨(forceSharp_two_dvd hH (hz i)).1, (forceSharp_two_dvd hH (hz i)).2.1⟩)
    (forceSharp_two_dvd hH (hz 2)).2.2.2

/-- ⚠ **The committed bound provably cannot reach it, so the gain is real.**  Take the dressing
`<j = 2>`, which lies in `stageN3` because its `j`, `l` and `m` are even, and the letter
`<d = 1>`, which lies in `stageN1` because both its columns vanish.  Their pairing is `2`.

So `4 ∣ gaThreePairL` is not a consequence of the committed hypotheses by any proof whatever:
it needs `4 | z.j`, which is exactly what `forceLcs_two_le_stageN3'` adds and
`forceLcs_two_le_stageN3` does not.  Headline 3 is a genuine gain, not a sharper proof of an
already reachable statement. -/
theorem forceSharp_gaThreePairL_committed_not_dvd_four :
    ∃ z L : SqU6 gr3R, z ∈ stageN3 ∧ L ∈ stageN1 ∧ ¬ (4 : gr3R) ∣ gaThreePairL z L := by
  refine ⟨forceSharpUnit3 2 0 0 0 0 0, ⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨1, by decide⟩, ⟨0, by decide⟩,
      ⟨0, by decide⟩⟩, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, ?_⟩
  rintro ⟨c, hc⟩
  revert c
  decide

end Consumer

/-! ## 7 Axiom pins

Committed prints for every public declaration.  All **std-3** (`propext`, `Classical.choice`,
`Quot.sound`) or a subset; no census axiom is reachable.  Every `decide` is on `ZMod 8` or on
`SqU6 (ZMod 8)`; there is no `native_decide`. -/

section AxiomPins

#print axioms forceSharpN2
#print axioms forceSharpN3
#print axioms forceSharpN2_mem
#print axioms forceSharpN3_mem
#print axioms forceSharpN2_le_stageN2
#print axioms forceSharpN3_le_stageN3
#print axioms forceSharp_gGen_mem_stageN2_not_N2
#print axioms forceSharp_jGen_mem_stageN3_not_N3
#print axioms forceSharp_kGen_mem_stageN3_not_N3
#print axioms forceSharpN2_isGaTwo
#print axioms forceSharpN2_even
#print axioms forceSharpN3_isGaThree
#print axioms forceSharpN3_dvd
#print axioms forceSharpN2_of_commutator
#print axioms forceSharpN3_of_commutator
#print axioms forceLcs_one_le_stageN2'
#print axioms forceLcs_two_le_stageN3'
#print axioms forceSharp_recover_one_le_stageN2
#print axioms forceSharp_recover_two_le_stageN3
#print axioms forceSharp_two_dvd
#print axioms forceSharp_one_dvd
#print axioms forceSharpUnit3
#print axioms forceSharpUnit3_one
#print axioms forceSharpUnit3_mul
#print axioms forceSharpUnit3_pow
#print axioms forceSharpUnit3_eq
#print axioms forceSharpUnit3_split
#print axioms forceSharpN3_le_forceLcs_stageN1_two
#print axioms forceSharp_stageN1_two_eq
#print axioms forceSharp_mem_forceLcs_stageN1_two_iff
#print axioms forceSharp_gaThreeCorr_even_of_evenK
#print axioms forceSharp_gaThreePairL_dvd_four
#print axioms forceSharp_gaThreeCore_m_dvd_four
#print axioms forceSharp_gaThreeHandle_m_dvd_four
#print axioms forceSharp_gaThreeShift_m_dvd_four
#print axioms forceSharp_stageShift_m_dvd_four
#print axioms forceSharp_gaThreePairL_committed_not_dvd_four

end AxiomPins

end SqCore

end Dyadic

end GQ2
