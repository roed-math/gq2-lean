/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenPerK

/-!
# W53-KAPPA: the `M`-row frame, re-cut onto the deep seam

## The gap this file closes

W52-RECUT (`GQ2/Dyadic/Instances/StageAbstractionEvenPerK.lean`) left the even lane with one
structural defect on the `M` branch.  The committed frame layer consumes
`RowExactLevelFibreLiftSupply`, the depth-`1` row seam, and consumes it at exactly one place:
`evenFrameExactLift` (`StageAbstractionEvenFrameCore.lean` §3) calls `supply.lift` at `m = 2` and
nowhere else.  W51-EV4A refuted that seam at the even images for `α ≥ 3`, and W52 isolated the
single instance the frame layer needs as `EvenPerKLevelTwoLift`.  On the `N` branch that instance
is *recovered* from the corrected deep seam for every `α ≥ 2`
(`evenPerK_nLevelTwoLift_of_range`), because two elements of `imChiN α` agreeing mod `8` already
agree mod `2^(α+1)`.  On the `M` branch it is *refuted* at `α ≥ 3`
(`evenPerK_not_mLevelTwoLift_of_range`), with the witness `mUnit α`.

So the committed `M` frame supply `evenDegreeMCyclotomicFrattiniFrameSupply_holds`, and with it
`evenLevelThreeM_stageBase` and the base hypothesis `EvenPerKMStageBase` of the committed endpoint
`evenPerK_orientedEquivM`, had no route at `α ≥ 3`: they all pass through a binder that the range
identity refutes.  **This file supplies the missing bridge**, and it locates precisely what the
`M` branch has to pay that the `N` branch does not.

## The mechanism: one missing digit, and the class that carries it

Under `range χ = imChiM α` the image is the units `≡ ±1 (mod 2^α)`
(`evenRange_mem_imChiM_iff`), and the deep seam pins `χ(λ₂ G)` inside `1 + 2^(α+1)ℤ₂`.  The frame
layer matches its dual generators against the row values through their mod-eight shadows, that is
through the two classes `κ` (mod-four parity) and `τ` (the `ω` class).  Inside `imChiM α` those two
classes see only the sign: for `α ≥ 3` every character value is `≡ ±1 (mod 8)`, so `τ = 0`, and `κ`
reads off `ε` in `χ g ≡ ε (mod 2^α)`.  The shadow therefore determines `χ g` **mod `2^α`**, while
the deep seam needs it **mod `2^(α+1)`**.  The `M` branch is short by exactly one digit, and
`mUnit α` is the element realising the shortfall.

The missing digit is itself a character.  §1 builds it: `evenDeepDigit α u`, the parity of
`(u^2 - 1)/2^(α+1)`, is a homomorphism on the units `≡ ±1 (mod 2^α)`, and it is the depth-`α`
generalisation of Serre's `ω`; at `α = 2` it *is* `ω` (§6).  §2 composes it with `χ` into a
continuous character `evenDeepDigitChar` of `G_K(2)` and, in §4, its degree-one class
`evenDeepClass`; it proves the two facts that make the pair `(κ, μ)` a complete shadow: the `M`
row table has `μ`-values `1` at the letter `D` and `0` elsewhere (`evenDeep_mTable`), and two
image elements agreeing on `κ` and `μ` agree mod `2^(α+1)` (`evenDeep_dvd_of_shadow`).

## What is proved, and the single new input

§3 re-cuts the frame assembly.  `evenFrameDeep_of_realizers` is `evenFrame_of_adapted` with its
lifting step abstracted away: it takes the adapted model equivalence and, for each letter, one
group element that realises the coordinate functional *and* already carries the row value.  §4
produces those realizers on the `M` branch from the deep seam alone, using the doubly adapted
normal form `mEvenFrameAdaptedModelEquiv` of the committed `M` frame file at the pair `(κ, μ)`
rather than `(κ, τ)`, and lands the frame:

* `evenFrameDeep_mFrame_of_range`, the `M`-row cup-adapted frame for every `α ≥ 2`, from the
  range identity, the ramified-`i` binder, and **one** new hypothesis: `frattiniFrameCup μ μ = 0`,
  the isotropy of the depth class (packaged per field as `EvenDeepMIsotropicSupply`).

Everything else is discharged: the deep seam itself (`evenClimb_deepRowSupply_m`), the mod-eight
image seam, the attainment seam, `μ ≠ 0` and `μ ≠ κ`.

**The new input is not removable.**  §5 proves the converse: if an `M`-row frame exists at all
then, under the same range identity and deep seam, `frattiniFrameCup μ μ = 0`
(`evenFrameDeep_isotropic_of_frame`).  So the isotropy is exactly the residue of the
re-cut, not an artefact of the route, and the `M` branch genuinely owes one datum the `N` branch
does not.  §2.3 machine-checks why: on `imChiN α` the depth digit *equals* the mod-four parity
(`evenDeep_digit_imChiN`), so the `N` branch's depth class is `κ` itself and the corresponding
isotropy is the committed `evenFrameCup_kappa_self`, free at even degree.  On `imChiM α` the digit
is a third class, independent of both `κ` and `τ`.

§6 discharges the input outright on the `α = 2` stratum (`evenFrameDeep_isotropic_two`): there the
corrected depth is `1`, the committed `mEvenFrame_of_rowAttained` builds the frame, and §5 reads
the isotropy off it.  So the hypothesis is a theorem exactly where the committed route reaches,
which is the layer's non-vacuity witness.  At `α = 2` the depth class is in fact the `ω` class
itself, since both digits vanish exactly when `u^2 ≡ 1 (mod 16)`; that identification is not
proved here (nothing below needs it) but it is what makes the input the deep generalisation of
`mEvenFrameCup_omega_self`.  Its expected discharge in general is the Bockstein identity: `μ`
lifts to a `ℤ/4`-valued character of `G_K(2)` (take the `α`-digit mod `4`, a character because
`imChiM α / {±1}` is procyclic), and `x ∪ x` vanishes on classes that lift to `ℤ/4`.  That
statement is not in the tree, so it is recorded here as the route rather than proved.

§7 cashes the frame into the shapes the committed chain consumes: `evenFrameDeep_mStageBase` is
`evenLevelThreeM_stageBase` with the refuted binder replaced, and `evenFrameDeep_mPerKStageBase`
is `EvenPerKMStageBase` of `StageAbstractionEvenPerK.lean` §5, so
`evenFrameDeep_orientedEquivM` is the committed endpoint `evenPerK_orientedEquivM` with `Hbase`
discharged.

## Which committed hypothesis this discharges

`evenPerK_orientedEquivM` (`StageAbstractionEvenPerK.lean` §6) carries three per-field
hypotheses: `Hbase : EvenPerKMStageBase h K`, `Hfam`, `Hup`.  **This file discharges `Hbase`**, at
the price of the ramified-`i` binder `κ ≠ 0` and `EvenDeepMIsotropicSupply`, leaving the `M`
endpoint with `Hfam`, `Hup` and those two data.  Nothing committed is restated or modified:
`evenFrameDeep_orientedEquivM` is a new theorem assembled from committed ones.  The refuted binder
`RowExactLevelFibreLiftSupply (vM α)` appears nowhere below.

## Numbering

1. the depth-`α` digit of a `2`-adic unit, and its homomorphism law;
2. the depth character of a group, the `M` row table, the two-class determination, and the `N`
   contrast;
3. the frame assembly from realizers;
4. the `M`-row frame from the deep seam;
5. necessity of the isotropy input, the resulting equivalence, and the bypass of the refuted
   seam;
6. the `α = 2` stratum, where the input is committed;
7. the stage base and the endpoint;
8. axiom pins.
-/

namespace GQ2.Dyadic.EvenFrameDeep

noncomputable section

open GQ2 ContCoh
open GQ2.Roe.Labute
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.EvenForward
open GQ2.Dyadic.EvenRowSupply
open GQ2.Dyadic.EvenCyclotomicRange
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.LSquare.FrattiniFrameSupply

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The depth-`α` digit of a two-adic unit

`ω(u) = (u^2 - 1)/8 mod 2` is Serre's residue character, a homomorphism on all of `ℤ₂ˣ`.  Its
depth-`α` shift `(u^2 - 1)/2^(α+1) mod 2` is *not* a homomorphism on `ℤ₂ˣ` for `α ≥ 3`, but it is
one on the subgroup of units `≡ ±1 (mod 2^α)`, which is exactly `imChiM α`
(`evenRange_mem_imChiM_iff`).  That is all the `M` branch needs, and §1 proves it from the
squaring identity alone: no logarithm, no filtration.

The definition is phrased through the mod-`2^(α+2)` reduction of `u^2` rather than through the
divisibility, because that spelling makes the continuity of §2 a one-liner. -/

section Digit

open Classical in
/-- The digit, read off a residue: `0` at the trivial residue and `1` elsewhere.  Factoring the
definition through this function is what makes the character of §2 continuous for free. -/
def evenDeepDigitOfSq (α : ℕ) (w : ZMod (2 ^ (α + 2))) : ZMod 2 := if w = 1 then 0 else 1

/-- **The depth-`α` digit of a two-adic unit**: the parity of `(u^2 - 1)/2^(α+1)`, spelled as a
test on the mod-`2^(α+2)` reduction of `u^2`.  For `u ≡ ±1 (mod 2^α)` this is the `α`-th binary
digit of `±u`, and it is `ω` at `α = 2`. -/
def evenDeepDigit (α : ℕ) (u : ℤ_[2]ˣ) : ZMod 2 :=
  evenDeepDigitOfSq α (PadicInt.toZModPow (α + 2) ((u : ℤ_[2]) ^ 2))

/-- The defining test, as a divisibility. -/
theorem evenDeepDigit_map_iff {α : ℕ} {u : ℤ_[2]ˣ} :
    PadicInt.toZModPow (α + 2) ((u : ℤ_[2]) ^ 2) = 1 ↔
      (2 : ℤ_[2]) ^ (α + 2) ∣ ((u : ℤ_[2]) ^ 2 - 1) := by
  rw [show (1 : ZMod (2 ^ (α + 2))) = PadicInt.toZModPow (α + 2) (1 : ℤ_[2]) from (map_one _).symm,
    GQ2.toZModPow_eq_iff_two_pow_dvd]

/-- The digit vanishes exactly when `u^2 ≡ 1 (mod 2^(α+2))`. -/
theorem evenDeepDigit_eq_zero_iff {α : ℕ} {u : ℤ_[2]ˣ} :
    evenDeepDigit α u = 0 ↔ (2 : ℤ_[2]) ^ (α + 2) ∣ ((u : ℤ_[2]) ^ 2 - 1) := by
  rw [evenDeepDigit, evenDeepDigitOfSq]
  by_cases hcond : PadicInt.toZModPow (α + 2) ((u : ℤ_[2]) ^ 2) = 1
  · rw [if_pos hcond]
    exact iff_of_true rfl (evenDeepDigit_map_iff.mp hcond)
  · rw [if_neg hcond]
    exact iff_of_false (by decide) fun hd ↦ hcond (evenDeepDigit_map_iff.mpr hd)

/-- The digit is nonzero exactly when `u^2 ≢ 1 (mod 2^(α+2))`. -/
theorem evenDeepDigit_eq_one_iff {α : ℕ} {u : ℤ_[2]ˣ} :
    evenDeepDigit α u = 1 ↔ ¬ (2 : ℤ_[2]) ^ (α + 2) ∣ ((u : ℤ_[2]) ^ 2 - 1) := by
  rw [← evenDeepDigit_eq_zero_iff]
  rcases ZMod.eq_zero_or_eq_one (evenDeepDigit α u) with h | h <;> rw [h] <;> simp

/-- The digit takes only the two values it can. -/
theorem evenDeepDigit_eq_one_of_ne_zero {α : ℕ} {u : ℤ_[2]ˣ} (h : evenDeepDigit α u ≠ 0) :
    evenDeepDigit α u = 1 := by
  rw [evenDeepDigit, evenDeepDigitOfSq] at h ⊢
  split_ifs at h ⊢ with hcond
  · exact absurd rfl h
  · rfl

/-- The digit depends only on the mod-`2^(α+2)` reduction of the square, which is what makes it
continuous. -/
theorem evenDeepDigit_congr {α : ℕ} {u w : ℤ_[2]ˣ}
    (h : PadicInt.toZModPow (α + 2) ((u : ℤ_[2]) ^ 2) =
      PadicInt.toZModPow (α + 2) ((w : ℤ_[2]) ^ 2)) :
    evenDeepDigit α u = evenDeepDigit α w := by
  rw [evenDeepDigit, evenDeepDigit, h]

@[simp] theorem evenDeepDigit_one (α : ℕ) : evenDeepDigit α 1 = 0 := by
  rw [evenDeepDigit_eq_zero_iff]
  simp

@[simp] theorem evenDeepDigit_neg_one (α : ℕ) : evenDeepDigit α (-1) = 0 := by
  rw [evenDeepDigit_eq_zero_iff]
  have : ((-1 : ℤ_[2]ˣ) : ℤ_[2]) ^ 2 - 1 = 0 := by norm_num
  rw [this]
  exact dvd_zero _

/-- Two units of `1 + 2^(α+1)ℤ₂` in the `±` sense have vanishing digit: this is the easy half of
the digit's meaning, and it is what makes the digit kill `χ(λ₂ G)`. -/
theorem evenDeepDigit_of_deep {α : ℕ} {u : ℤ_[2]ˣ} (hu : EvenSharpPmOne (α + 1) u) :
    evenDeepDigit α u = 0 := by
  rw [evenDeepDigit_eq_zero_iff]
  have hp : (2 : ℤ_[2]) ^ (α + 1) = 2 * 2 ^ α := by ring
  have hq : (2 : ℤ_[2]) ^ (α + 2) = 4 * 2 ^ α := by ring
  rcases hu with ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [hp] at hs
    refine ⟨s * (2 ^ α * s + 1), ?_⟩
    rw [hq]
    linear_combination ((u : ℤ_[2]) + 1 + 2 * 2 ^ α * s) * hs
  · rw [hp] at hs
    refine ⟨s * (2 ^ α * s - 1), ?_⟩
    rw [hq]
    linear_combination ((u : ℤ_[2]) - 1 + 2 * 2 ^ α * s) * hs

/-- **The converse, at `α ≥ 2`**: inside the units `≡ ±1 (mod 2^α)` a vanishing digit buys the
next digit.  This is the step the `M` branch is missing without the depth class. -/
theorem evenDeepDigit_deep_of_eq_zero {α : ℕ} (hα : 2 ≤ α) {u : ℤ_[2]ˣ}
    (hu : EvenSharpPmOne α u) (h0 : evenDeepDigit α u = 0) : EvenSharpPmOne (α + 1) u := by
  obtain ⟨β, rfl⟩ : ∃ β, α = β + 2 := ⟨α - 2, by omega⟩
  obtain ⟨c, hc⟩ := evenDeepDigit_eq_zero_iff.mp h0
  have hcancel : ∀ x y : ℤ_[2], (2 : ℤ_[2]) ^ (β + 3) * x = (2 : ℤ_[2]) ^ (β + 3) * y → x = y :=
    fun x y hxy ↦ mul_left_cancel₀ (pow_ne_zero _ (two_ne_zero (α := ℤ_[2]))) hxy
  rcases hu with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hstep : (2 : ℤ_[2]) * c = 2 ^ (β + 1) * t ^ 2 + t := by
      refine hcancel _ _ ?_
      linear_combination -hc + ((u : ℤ_[2]) + 1 + 2 ^ (β + 2) * t) * ht
    refine Or.inl ⟨c - 2 ^ β * t ^ 2, ?_⟩
    linear_combination ht - 2 ^ (β + 2) * hstep
  · have hstep : (2 : ℤ_[2]) * c = 2 ^ (β + 1) * t ^ 2 - t := by
      refine hcancel _ _ ?_
      linear_combination -hc + ((u : ℤ_[2]) - 1 + 2 ^ (β + 2) * t) * ht
    refine Or.inr ⟨2 ^ β * t ^ 2 - c, ?_⟩
    linear_combination ht + 2 ^ (β + 2) * hstep

/-! ### §1.1 The homomorphism law

Both `u^2 - 1` and `w^2 - 1` are divisible by `2^(α+1)` when `u, w ≡ ±1 (mod 2^α)`, and the digit
is the parity of the cofactor.  Multiplying adds the cofactors modulo `2`, since the cross term
carries `2^(2α+2)`. -/

private theorem evenDeep_two_dvd_iff {x : ℤ_[2]} :
    (2 : ℤ_[2]) ∣ x ↔ PadicInt.toZModPow 1 x = 0 := by
  rw [show (0 : ZMod (2 ^ 1)) = PadicInt.toZModPow 1 (0 : ℤ_[2]) from (map_zero _).symm,
    GQ2.toZModPow_eq_iff_two_pow_dvd, pow_one, sub_zero]

/-- One squaring gains a digit off a `±1` congruence, with the cofactor named.  (The committed
step inside `StageAbstractionEvenRowSupply.lean` §5.1 is `private`, so it is re-proved here in the
form the digit calculus needs.) -/
theorem evenDeep_sq_sub_one {α : ℕ} (hα : 1 ≤ α) {u : ℤ_[2]ˣ} (hu : EvenSharpPmOne α u) :
    ∃ x : ℤ_[2], ((u : ℤ_[2]) ^ 2 - 1) = 2 ^ (α + 1) * x := by
  obtain ⟨β, rfl⟩ : ∃ β, α = β + 1 := ⟨α - 1, by omega⟩
  rcases hu with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact ⟨2 ^ β * s ^ 2 + s, by linear_combination ((u : ℤ_[2]) + 1 + 2 ^ (β + 1) * s) * hs⟩
  · exact ⟨2 ^ β * s ^ 2 - s, by linear_combination ((u : ℤ_[2]) - 1 + 2 ^ (β + 1) * s) * hs⟩

/-- The digit of a unit with `u^2 - 1 = 2^(α+1) x` is the parity of `x`. -/
theorem evenDeepDigit_eq_zero_iff_two_dvd {α : ℕ} {u : ℤ_[2]ˣ} {x : ℤ_[2]}
    (hx : ((u : ℤ_[2]) ^ 2 - 1) = 2 ^ (α + 1) * x) :
    evenDeepDigit α u = 0 ↔ (2 : ℤ_[2]) ∣ x := by
  rw [evenDeepDigit_eq_zero_iff, hx]
  constructor
  · rintro ⟨c, hcc⟩
    refine ⟨c, mul_left_cancel₀ (pow_ne_zero (α + 1) (two_ne_zero (α := ℤ_[2]))) ?_⟩
    linear_combination hcc
  · rintro ⟨c, hcc⟩
    exact ⟨c, by rw [hcc]; ring⟩

/-- **The homomorphism law of the digit**, on the units `≡ ±1 (mod 2^α)`.  This is the whole
reason the depth class of §2 exists; note that it is *false* on all of `ℤ₂ˣ` for `α ≥ 3`, since
the digit does not then extend to a character of `ℤ₂ˣ` at all. -/
theorem evenDeepDigit_mul {α : ℕ} (hα : 1 ≤ α) {a b : ℤ_[2]ˣ}
    (ha : EvenSharpPmOne α a) (hb : EvenSharpPmOne α b) :
    evenDeepDigit α (a * b) = evenDeepDigit α a + evenDeepDigit α b := by
  obtain ⟨x, hx⟩ := evenDeep_sq_sub_one hα ha
  obtain ⟨y, hy⟩ := evenDeep_sq_sub_one hα hb
  have hxy : (((a * b : ℤ_[2]ˣ) : ℤ_[2]) ^ 2 - 1) =
      2 ^ (α + 1) * (x + y + 2 ^ (α + 1) * (x * y)) := by
    push_cast
    linear_combination ((b : ℤ_[2]) ^ 2) * hx + (1 + 2 ^ (α + 1) * x) * hy
  have hval : ∀ (u : ℤ_[2]ˣ) (z : ℤ_[2]), ((u : ℤ_[2]) ^ 2 - 1) = 2 ^ (α + 1) * z →
      evenDeepDigit α u = if PadicInt.toZModPow 1 z = 0 then 0 else 1 := by
    intro u z hz
    by_cases hzz : PadicInt.toZModPow 1 z = 0
    · rw [if_pos hzz, evenDeepDigit_eq_zero_iff_two_dvd hz]
      exact evenDeep_two_dvd_iff.mpr hzz
    · rw [if_neg hzz]
      refine evenDeepDigit_eq_one_of_ne_zero fun hcon ↦ hzz ?_
      exact evenDeep_two_dvd_iff.mp ((evenDeepDigit_eq_zero_iff_two_dvd hz).mp hcon)
  have h2 : PadicInt.toZModPow 1 ((2 : ℤ_[2]) ^ (α + 1)) = 0 := by
    rw [map_pow, evenDeep_two_dvd_iff.mp (dvd_refl (2 : ℤ_[2])), zero_pow (by omega)]
  rw [hval _ _ hx, hval _ _ hy, hval _ _ hxy, map_add, map_add, map_mul, h2, zero_mul, add_zero]
  rcases ZMod.eq_zero_or_eq_one (PadicInt.toZModPow 1 x) with h3 | h3 <;>
    rcases ZMod.eq_zero_or_eq_one (PadicInt.toZModPow 1 y) with h4 | h4 <;>
      rw [h3, h4] <;> decide

/-- The digit is unchanged by inversion, since the subgroup law is over `ZMod 2`. -/
theorem evenDeepDigit_inv {α : ℕ} (hα : 1 ≤ α) {a : ℤ_[2]ˣ} (ha : EvenSharpPmOne α a) :
    evenDeepDigit α a⁻¹ = evenDeepDigit α a := by
  have hinv : EvenSharpPmOne α a⁻¹ :=
    evenSharp_mem_pmOneSubgroup_iff.mp (inv_mem (evenSharp_mem_pmOneSubgroup_iff.mpr ha))
  have h := evenDeepDigit_mul hα hinv ha
  rw [inv_mul_cancel, evenDeepDigit_one] at h
  rcases ZMod.eq_zero_or_eq_one (evenDeepDigit α a⁻¹) with h1 | h1 <;>
    rcases ZMod.eq_zero_or_eq_one (evenDeepDigit α a) with h2 | h2 <;>
      rw [h1, h2] at h ⊢ <;> first | rfl | exact absurd h (by decide)

/-- **The depth unit has digit one**, for `α ≥ 2`: `mUnit α = 1 + 2^α · mUnit α` has an odd
`α`-digit.  This is the row datum that makes the depth class nonzero, and the reason the `M`
branch is exactly one digit short of the deep seam. -/
theorem evenDeepDigit_mUnit {α : ℕ} (hα : 2 ≤ α) : evenDeepDigit α (mUnit α) = 1 := by
  obtain ⟨β, rfl⟩ : ∃ β, α = β + 2 := ⟨α - 2, by omega⟩
  have hm : ((mUnit (β + 2) : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ (β + 2) * ((mUnit (β + 2) : ℤ_[2]ˣ)) :=
    mUnit_sub_one (by omega)
  have hx : (((mUnit (β + 2) : ℤ_[2]ˣ) : ℤ_[2]) ^ 2 - 1) =
      2 ^ (β + 2 + 1) * (2 ^ (β + 1) * ((mUnit (β + 2) : ℤ_[2]ˣ) : ℤ_[2]) ^ 2 +
        ((mUnit (β + 2) : ℤ_[2]ˣ) : ℤ_[2])) := by
    linear_combination (((mUnit (β + 2) : ℤ_[2]ˣ) : ℤ_[2]) + 1 +
      2 ^ (β + 2) * ((mUnit (β + 2) : ℤ_[2]ˣ) : ℤ_[2])) * hm
  refine evenDeepDigit_eq_one_of_ne_zero fun hcon ↦ ?_
  obtain ⟨c, hc⟩ := (evenDeepDigit_eq_zero_iff_two_dvd hx).mp hcon
  have hunit : ((mUnit (β + 2) : ℤ_[2]ˣ) : ℤ_[2]) =
      2 * (c - 2 ^ β * ((mUnit (β + 2) : ℤ_[2]ˣ) : ℤ_[2]) ^ 2) := by
    linear_combination hc
  exact not_isUnit_two (isUnit_of_mul_isUnit_left (hunit ▸ (mUnit (β + 2)).isUnit))

end Digit

/-! ## §2 The depth class, the `M` row table, and the two-class determination

The digit becomes a character of the group as soon as every character value is `≡ ±1 (mod 2^α)`,
which on the `M` branch is the range identity read through `evenRange_mem_imChiM_iff`.  §2.2 then
proves the two facts that make `(κ, μ)` a *complete* mod-`2^(α+1)` shadow on that image, where
`(κ, τ)` is only a mod-`2^α` shadow: the `M` row's digit table, and the determination itself. -/

section DeepChar

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The depth-`α` digit character of `G`**, as a monoid homomorphism.  The multiplicativity is
§1.1, and it is exactly here that the `±1 (mod 2^α)` bound on the character values is consumed. -/
def evenDeepDigitHom (α : ℕ) (hα : 1 ≤ α) (chi : ContinuousMonoidHom G ℤ_[2]ˣ)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g)) : G →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (evenDeepDigit α (chi g))
  map_one' := by
    show Multiplicative.ofAdd (evenDeepDigit α (chi 1)) = 1
    rw [map_one, evenDeepDigit_one]
    rfl
  map_mul' g g' := by
    show Multiplicative.ofAdd (evenDeepDigit α (chi (g * g'))) =
      Multiplicative.ofAdd (evenDeepDigit α (chi g)) *
        Multiplicative.ofAdd (evenDeepDigit α (chi g'))
    rw [map_mul, evenDeepDigit_mul hα (hbound g) (hbound g')]
    rfl

/-- **The depth-`α` digit character**, continuous: it factors through the mod-`2^(α+2)` reduction
of the square, which is locally constant. -/
def evenDeepDigitChar (α : ℕ) (hα : 1 ≤ α) (chi : ContinuousMonoidHom G ℤ_[2]ˣ)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g)) :
    ContinuousMonoidHom G (Multiplicative (ZMod 2)) where
  toMonoidHom := evenDeepDigitHom α hα chi hbound
  continuous_toFun := by
    refine IsLocallyConstant.continuous fun s ↦ ?_
    have hfact : (fun g : G ↦ Multiplicative.ofAdd (evenDeepDigit α (chi g))) ⁻¹' s =
        (fun g : G ↦ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) ^ 2) ⁻¹'
          (PadicInt.toZModPow (p := 2) (α + 2) ⁻¹'
            {c : ZMod (2 ^ (α + 2)) | Multiplicative.ofAdd (evenDeepDigitOfSq α c) ∈ s}) := rfl
    show IsOpen ((fun g : G ↦ Multiplicative.ofAdd (evenDeepDigit α (chi g))) ⁻¹' s)
    rw [hfact]
    exact (isOpen_preimage_toZModPow (α + 2) _).preimage
      ((continuous_pow 2).comp (Units.continuous_val.comp chi.continuous_toFun))

omit [IsTopologicalGroup G] in
@[simp] theorem evenDeepDigitChar_apply {α : ℕ} (hα : 1 ≤ α) {chi : ContinuousMonoidHom G ℤ_[2]ˣ}
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g)) (g : G) :
    evenDeepDigitChar α hα chi hbound g = Multiplicative.ofAdd (evenDeepDigit α (chi g)) := rfl

omit [IsTopologicalGroup G] in
/-- The `±1 (mod 2^α)` bound, from the `M` image identification. -/
theorem evenDeep_bound_of_range {α : ℕ} (hα : 1 ≤ α) {chi : ContinuousMonoidHom G ℤ_[2]ˣ}
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM α) (g : G) :
    EvenSharpPmOne α (chi g) := by
  have hg : chi g ∈ MonoidHom.range chi.toMonoidHom := ⟨g, rfl⟩
  rw [hrange] at hg
  exact evenSharp_pmOne_of_mem_imChiM hα hg

end DeepChar

/-! ### §2.1 The `M` row's digit table -/

/-- **The digit table of the `M` row**: `1` at the letter `D` (index `3`) and `0` at every other
letter.  Compare the parity table (`evenDegreeM_parity_table`), supported at `B` (index `1`): the
two tables are supported at *different* letters, which is why the pair `(κ, μ)` sees the two
independent directions of `imChiM α / (1 + 2^(α+1)ℤ₂)`. -/
theorem evenDeep_mTable {α h : ℕ} (hα : 2 ≤ α) (i : Fin (MarkedCore.coreRank h)) :
    evenDeepDigit α (vM α i) = if (i : ℕ) = 3 then 1 else 0 := by
  refine evenIndex_cases
    (P := fun i ↦ evenDeepDigit α (vM α i) = if (i : ℕ) = 3 then 1 else 0) ?_ ?_ ?_ ?_ ?_ ?_ i
  · rw [vM_zero, evenDeepDigit_one, if_neg (by rw [MarkedCore.coreVal_zero]; omega)]
  · rw [vM_one, evenDeepDigit_neg_one, if_neg (by rw [MarkedCore.coreVal_one]; omega)]
  · rw [vM_two, evenDeepDigit_one, if_neg (by rw [MarkedCore.coreVal_two]; omega)]
  · rw [vM_three, evenDeepDigit_mUnit hα, if_pos (MarkedCore.coreVal_three h)]
  · intro j
    rw [vM_handleU, evenDeepDigit_one, if_neg (by rw [MarkedCore.handleIdxU_val]; omega)]
  · intro j
    rw [vM_handleV, evenDeepDigit_one, if_neg (by rw [MarkedCore.handleIdxV_val]; omega)]

/-- Every `vM α` row value is `≡ ±1 (mod 2^α)`: the row table lies in the branch image. -/
theorem evenDeep_mTable_pmOne {α h : ℕ} (hα : 1 ≤ α) (i : Fin (MarkedCore.coreRank h)) :
    EvenSharpPmOne α (vM α i) :=
  evenSharp_pmOne_of_mem_imChiM hα (by
    refine evenIndex_cases (P := fun i ↦ vM α i ∈ imChiM α) ?_ ?_ ?_ ?_ ?_ ?_ i
    · rw [vM_zero]; exact one_mem _
    · rw [vM_one]; exact neg_one_mem_imChiM α
    · rw [vM_two]; exact one_mem _
    · rw [vM_three]; exact mUnit_mem_imChiM α
    · intro j; rw [vM_handleU]; exact one_mem _
    · intro j; rw [vM_handleV]; exact one_mem _)

/-! ### §2.2 The determination

Two elements of `imChiM α` with the same mod-four parity and the same digit agree modulo
`2^(α+1)`, which is exactly the modulus the deep seam asks for at level two.  Without the digit
the same data gives only `2^α`, and `mUnit α` is the element that falls in the gap: this is the
whole content of `evenPerK_not_mLevelTwoLift_of_range`. -/

private theorem evenDeep_eq_one_of_parity_zero {w : (ZMod 4)ˣ}
    (hw : Multiplicative.toAdd (unitsModFourParity w) = 0) : w = 1 := by
  rcases unitsModFour_eq_one_or_neg_one w with h1 | h1
  · exact h1
  · rw [h1] at hw
    exact absurd hw (by decide)

private theorem evenDeep_not_four_dvd_two : ¬ (2 : ℤ_[2]) ^ 2 ∣ (2 : ℤ_[2]) := by
  rintro ⟨c, hc⟩
  have hone : (1 : ℤ_[2]) = 2 * c :=
    mul_left_cancel₀ (two_ne_zero (α := ℤ_[2])) (by linear_combination hc)
  exact not_isUnit_two (isUnit_of_mul_isUnit_left (hone ▸ isUnit_one))

/-- **The two-class determination.**  On the units `≡ ±1 (mod 2^α)`, mod-four parity together with
the depth digit determines the class modulo `2^(α+1)`. -/
theorem evenDeep_dvd_of_shadow {α : ℕ} (hα : 2 ≤ α) {a b : ℤ_[2]ˣ}
    (ha : EvenSharpPmOne α a) (hb : EvenSharpPmOne α b)
    (hpar : Multiplicative.toAdd (unitsModFourParity
        (Units.map (PadicInt.toZModPow 2).toMonoidHom a)) =
      Multiplicative.toAdd (unitsModFourParity
        (Units.map (PadicInt.toZModPow 2).toMonoidHom b)))
    (hdig : evenDeepDigit α a = evenDeepDigit α b) :
    (2 : ℤ_[2]) ^ (α + 1) ∣ (a : ℤ_[2]) - (b : ℤ_[2]) := by
  have hbinv : EvenSharpPmOne α b⁻¹ :=
    evenSharp_mem_pmOneSubgroup_iff.mp (inv_mem (evenSharp_mem_pmOneSubgroup_iff.mpr hb))
  set u : ℤ_[2]ˣ := a * b⁻¹ with hu
  have hupm : EvenSharpPmOne α u :=
    evenSharp_mem_pmOneSubgroup_iff.mp (mul_mem (evenSharp_mem_pmOneSubgroup_iff.mpr ha)
      (evenSharp_mem_pmOneSubgroup_iff.mpr hbinv))
  -- the mod-four parity of `u` vanishes, so `u ≡ 1 (mod 4)`
  have hfour : (2 : ℤ_[2]) ^ 2 ∣ (u : ℤ_[2]) - 1 := by
    have hmapu : Units.map (PadicInt.toZModPow 2).toMonoidHom u =
        Units.map (PadicInt.toZModPow 2).toMonoidHom a *
          (Units.map (PadicInt.toZModPow 2).toMonoidHom b)⁻¹ := by
      rw [hu, map_mul, map_inv]
    have hparu : Multiplicative.toAdd (unitsModFourParity
        (Units.map (PadicInt.toZModPow 2).toMonoidHom u)) = 0 := by
      rw [hmapu, map_mul, map_inv, toAdd_mul, toAdd_inv, hpar]
      ring
    have hone : Units.map (PadicInt.toZModPow 2).toMonoidHom u = 1 :=
      evenDeep_eq_one_of_parity_zero hparu
    exact evenSharp_mem_ker_iff.mp (MonoidHom.mem_ker.mpr hone)
  -- the digit of `u` vanishes, so `u ≡ ±1 (mod 2^(α+1))`
  have hdigu : evenDeepDigit α u = 0 := by
    rw [hu, evenDeepDigit_mul (by omega) ha hbinv, evenDeepDigit_inv (by omega) hb, hdig]
    exact CharTwo.add_self_eq_zero _
  have hdeep : EvenSharpPmOne (α + 1) u :=
    evenDeepDigit_deep_of_eq_zero hα hupm hdigu
  -- the `-1` branch is excluded by the mod-four datum
  have husub : (2 : ℤ_[2]) ^ (α + 1) ∣ (u : ℤ_[2]) - 1 := by
    rcases hdeep with h | h
    · exact h
    · exfalso
      have h4 : (2 : ℤ_[2]) ^ 2 ∣ (u : ℤ_[2]) + 1 :=
        (pow_dvd_pow (2 : ℤ_[2]) (by omega)).trans h
      obtain ⟨c, hc⟩ := hfour
      obtain ⟨d, hd⟩ := h4
      exact evenDeep_not_four_dvd_two ⟨d - c, by linear_combination hd - hc⟩
  obtain ⟨c, hc⟩ := husub
  refine ⟨(b : ℤ_[2]) * c, ?_⟩
  have hubU : u * b = a := by rw [hu, inv_mul_cancel_right]
  have hub : ((u : ℤ_[2]) * (b : ℤ_[2])) = (a : ℤ_[2]) := by
    rw [← Units.val_mul, hubU]
  linear_combination (b : ℤ_[2]) * hc - hub

/-- The determination, in the shape the depth-`(α - 1)` seam consumes at level two. -/
theorem evenDeep_map_eq_of_shadow {α : ℕ} (hα : 2 ≤ α) {a b : ℤ_[2]ˣ}
    (ha : EvenSharpPmOne α a) (hb : EvenSharpPmOne α b)
    (hpar : Multiplicative.toAdd (unitsModFourParity
        (Units.map (PadicInt.toZModPow 2).toMonoidHom a)) =
      Multiplicative.toAdd (unitsModFourParity
        (Units.map (PadicInt.toZModPow 2).toMonoidHom b)))
    (hdig : evenDeepDigit α a = evenDeepDigit α b) :
    Units.map (PadicInt.toZModPow (2 + (α - 1))).toMonoidHom a =
      Units.map (PadicInt.toZModPow (2 + (α - 1))).toMonoidHom b := by
  have hidx : 2 + (α - 1) = α + 1 := by omega
  rw [hidx]
  exact Units.ext (by
    simpa using evenRange_toZModPow_eq_iff.mpr (evenDeep_dvd_of_shadow hα ha hb hpar hdig))

/-! ### §2.3 The `N` branch, for contrast

The digit exists on the `N` image too, and there it is not new: it *equals* the mod-four parity.
That single identity is the whole `N`/`M` asymmetry.  On `imChiN α` the two classes of the image
modulo `2^(α+1)` are `1` and `nUnit α`, and `nUnit α` has digit `1` and parity `1`, so `κ` already
carries the missing digit; this is `evenPerK_dvd_of_modEight_imChiN` read as a statement about
characters rather than about elements.  Consequently the `N` analogue of §4's isotropy input is
`frattiniFrameCup κ κ = 0`, which is the committed `evenFrameCup_kappa_self`, free at even degree.
On `imChiM α` the digit is instead a *third* class, independent of both `κ` and `τ`
(`evenDeep_class_indep`), and its isotropy is exactly what the `M` branch has to buy. -/

/-- The depth unit of the `N` row has digit `1`: `nUnit α ^ 2 - 1` has exact depth `α + 1`. -/
theorem evenDeepDigit_nUnit {α : ℕ} (hα : 2 ≤ α) : evenDeepDigit α (nUnit α) = 1 := by
  obtain ⟨b, hb⟩ := nUnit_sq_sub_one (α := α) hα
  have hb' : (((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) ^ 2 - 1) = 2 ^ (α + 1) * ((b : ℤ_[2]ˣ) : ℤ_[2]) := by
    rw [← hb]
    push_cast
    ring
  refine evenDeepDigit_eq_one_of_ne_zero fun hcon ↦ ?_
  obtain ⟨c, hc⟩ := (evenDeepDigit_eq_zero_iff_two_dvd hb').mp hcon
  exact not_isUnit_two (isUnit_of_mul_isUnit_left (hc ▸ b.isUnit))

/-- **On the `N` image the depth digit is the mod-four parity.**  So the `N` branch's depth class
is `κ`, not a new class, and the recovery `evenPerK_nLevelTwoLift_of_range` needs no extra datum.
This is the exact sense in which the `M` branch is the one that pays. -/
theorem evenDeep_digit_imChiN {α : ℕ} (hα : 2 ≤ α) {u : ℤ_[2]ˣ} (hu : u ∈ imChiN α) :
    evenDeepDigit α u = Multiplicative.toAdd (unitsModFourParity
      (Units.map (PadicInt.toZModPow 2).toMonoidHom u)) := by
  rcases evenRange_mem_imChiN_dvd hα hu with h | h
  · have h4 : PadicInt.toZModPow 2 ((u : ℤ_[2])) = 1 :=
      evenRange_toZModPow_eq_one_iff.mpr ((pow_dvd_pow (2 : ℤ_[2]) (by omega)).trans h)
    rw [evenDeepDigit_of_deep (Or.inl h),
      frattiniFrame_parity_of_val_one (u := Units.map (PadicInt.toZModPow 2).toMonoidHom u)
        (by simpa using h4)]
  · obtain ⟨c, hc⟩ := id h
    have hp1 : (2 : ℤ_[2]) ^ (α + 1) = 2 * 2 ^ α := by ring
    have hp2 : (2 : ℤ_[2]) ^ (α + 2) = 4 * 2 ^ α := by ring
    rw [hp1] at hc
    have hsq : PadicInt.toZModPow (α + 2) ((u : ℤ_[2]) ^ 2) =
        PadicInt.toZModPow (α + 2) (((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) ^ 2) := by
      refine evenRange_toZModPow_eq_iff.mpr ⟨((c : ℤ_[2]) *
        (((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) + 2 ^ α * c)), ?_⟩
      rw [hp2]
      linear_combination ((u : ℤ_[2]) + ((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) + 2 * 2 ^ α * c) * hc
    have h4 : (2 : ℤ_[2]) ^ 2 ∣ (u : ℤ_[2]) - ((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) :=
      (pow_dvd_pow (2 : ℤ_[2]) (by omega)).trans h
    have hmap : Units.map (PadicInt.toZModPow 2).toMonoidHom u =
        Units.map (PadicInt.toZModPow 2).toMonoidHom (nUnit α) :=
      Units.ext (by simpa using evenRange_toZModPow_eq_iff.mpr h4)
    rw [evenDeepDigit_congr hsq, evenDeepDigit_nUnit hα, hmap, evenDegreeN_parity_nUnit hα]

/-! ## §3 The frame assembly from realizers

`evenFrame_of_adapted` (`StageAbstractionEvenFrameCore.lean` §4.1) does two things: it realises
each coordinate functional by a group element, and it corrects that element to the exact row value
inside its Frattini coset, through `evenFrameExactLift` and hence through the refuted depth-`1`
seam.  Only the *outcome* of those two steps is used, namely a family of elements each of which
realises its functional and already carries its row value.  §3 is `evenFrame_of_adapted` with that
outcome as the hypothesis, so the lifting seam is a parameter of the route rather than a fixed
binder.  Nothing else in the assembly changes: the Frattini generation is still duality, and the
cup adaptation is still the model Gram. -/

section EvenFieldDeep

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance evenFrameDeepScalar : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance evenFrameDeepContinuousScalar :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **The ramified-`i` binder is implied by the sign datum.**  If `-1` is a cyclotomic value then
the group element realising it has mod-four parity `1` (`evenDegreeM_parity_negOne`), so the
mod-four class is not zero.

This lives here because both of the two files that need it — `EvenDeepIsotropy` (as
`evenDeep_kappa_ne_zero_of_neg`) and `StageAbstractionEvenEndpoint` (as
`evenEndpoint_kappa_of_negOne`) — import this one and neither imports the other, so this is
their earliest common home.  They had proved it independently, with the same statement. -/
theorem evenFrameDeep_kappa_ne_zero_of_negOne
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom) :
    cyclotomicModFourClassKTwo (K := K) ≠ 0 := by
  obtain ⟨g, hg⟩ := hneg
  intro h0
  have h1 : frattiniFrameEval (cyclotomicModFourClassKTwo (K := K)) g = 0 := by
    rw [h0]
    exact frattiniFrameEval_zero g
  rw [frattiniFrameEval_modFour, show chiCycKTwo (K := K) g = -1 from hg,
    evenDegreeM_parity_negOne] at h1
  exact one_ne_zero h1

/-- **The even frame from exact realizers.**  Given an adapted coordinate system on
`H¹(G_K(2), 𝔽₂)` and, for each letter, one group element realising that letter's coordinate
functional and having exactly the row value, the family is a `StageGeneric.Frame` at the row
table, cup-adapted at the even Gram.

This is `evenFrame_of_adapted` with the lifting step hoisted into the hypothesis: it consumes no
row seam at all, so a consumer may reach the realizers by any route.  `evenFrame_of_adapted` is
the instance where they come from `evenFrameExactLift`, that is from the depth-`1` seam; §4 is the
instance where they come from the corrected deep seam. -/
theorem evenFrameDeep_of_realizers {h : ℕ} (v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ)
    (Φ : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2) ≃ₗ[ZMod 2] evenFrameModel h)
    (hGram : ∀ x y, frattiniFrameCup x y = evenFrameGramModel h (Φ x) (Φ y))
    (hreal : ∀ i : Fin (MarkedCore.coreRank h), ∃ g : maxProPQuotient 2 (GalK K),
      chiCycKTwo (K := K) g = v i ∧
        ∀ x, frattiniFrameEval x g = evenFrameCoord i (Φ x)) :
    ∃ F : Frame v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)),
      F.IsCupAdapted (evenFrameGram h) (evenFramePairing (K := K)) := by
  classical
  choose gens hchi hD using hreal
  refine ⟨⟨gens, hchi, ?_⟩, ?_⟩
  · -- Frattini generation, by duality
    by_contra hne
    haveI hFfin : Finite (levelQuot (maxProPQuotient 2 (GalK K)) 2) :=
      finite_levelQuot _ (maxProTwoGalK_isTopologicallyFinGen K) isProP_maxProPQuotient 2
    haveI hFdisc : DiscreteTopology (levelQuot (maxProPQuotient 2 (GalK K)) 2) :=
      discreteTopology_levelQuot _ (maxProTwoGalK_isTopologicallyFinGen K)
        isProP_maxProPQuotient 2
    obtain ⟨c, hcH, hcne⟩ := frattiniFrame_exists_modTwo_character
      (frattiniFrame_levelTwo_mul_comm (maxProPQuotient 2 (GalK K)))
      (frattiniFrame_levelTwo_sq (maxProPQuotient 2 (GalK K))) hne
    set cQ : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)) :=
      ⟨c.comp (levelMk (maxProPQuotient 2 (GalK K)) 2), by
        have h1 : Continuous c := continuous_of_discreteTopology
        exact h1.comp (continuous_levelMk (maxProPQuotient 2 (GalK K)) 2)⟩ with hcQ
    have hvanish : ∀ i, frattiniFrameEval
        (SqCyclotomicFrattiniFrame.characterClass (K := K) cQ) (gens i) = 0 := by
      intro i
      rw [frattiniFrameEval_characterClass]
      show Multiplicative.toAdd (c (levelMk (maxProPQuotient 2 (GalK K)) 2 (gens i))) = 0
      rw [hcH _ (Subgroup.subset_closure ⟨i, rfl⟩)]
      rfl
    have hΦ0 : Φ (SqCyclotomicFrattiniFrame.characterClass (K := K) cQ) = 0 := by
      refine evenFrameCoord_eq_zero _ fun i ↦ ?_
      rw [← hD i]
      exact hvanish i
    have hcc0 : SqCyclotomicFrattiniFrame.characterClass (K := K) cQ = 0 := by
      have hs := congrArg Φ.symm hΦ0
      rwa [LinearEquiv.symm_apply_apply, map_zero] at hs
    apply hcne
    apply MonoidHom.ext
    intro fq
    obtain ⟨g, rfl⟩ := levelMk_surjective (maxProPQuotient 2 (GalK K)) 2 fq
    have hg : frattiniFrameEval
        (SqCyclotomicFrattiniFrame.characterClass (K := K) cQ) g =
          Multiplicative.toAdd (cQ g) := frattiniFrameEval_characterClass cQ g
    rw [hcc0, frattiniFrameEval_zero] at hg
    show c (levelMk (maxProPQuotient 2 (GalK K)) 2 g) = 1
    have hone : cQ g = 1 := by
      apply Multiplicative.toAdd.injective
      rw [← hg]
      rfl
    exact hone
  · -- cup adaptation, against the extended even Gram
    intro c d
    show frattiniFrameCup (SqCyclotomicFrattiniFrame.characterClass (K := K) c)
        (SqCyclotomicFrattiniFrame.characterClass (K := K) d) =
      evenFrameGram h (fun i j ↦ Multiplicative.toAdd (c (gens i)) *
        Multiplicative.toAdd (d (gens j)))
    rw [hGram, ← evenFrameGram_modelCoord]
    congr 1
    funext i j
    rw [← hD i (SqCyclotomicFrattiniFrame.characterClass (K := K) c),
      ← hD j (SqCyclotomicFrattiniFrame.characterClass (K := K) d),
      frattiniFrameEval_characterClass, frattiniFrameEval_characterClass]

/-! ## §4 The `M`-row frame from the deep seam

The depth class is the second half of the shadow the deep seam needs, and the doubly adapted
normal form `mEvenFrameAdaptedModelEquiv` of the committed `M` frame file places it.  Note which
pair is placed: the committed `α = 2` branch places `(κ, τ)`, this one places `(κ, μ)`, and the
two coincide at `α = 2` because `μ` *is* `ω` there.  Above `α = 2` the class `τ` vanishes and
carries no information, which is exactly why the committed route stalls. -/

/-- **The depth class of `K` at branch depth `α`.**  The degree-one class of `G_K(2)` attached to
the depth-`α` digit of the cyclotomic value.  It is defined only under the branch identification,
which is what makes the digit multiplicative. -/
def evenDeepClass (α : ℕ) (hα : 1 ≤ α)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α) :
    H1 (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  SqCyclotomicFrattiniFrame.characterClass (K := K)
    (evenDeepDigitChar α hα (chiCycKTwo (K := K)) (evenDeep_bound_of_range hα hrange))

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- Evaluating the depth class is taking the depth digit of the cyclotomic value. -/
@[simp] theorem evenDeepClass_eval {α : ℕ} (hα : 1 ≤ α)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α)
    (g : maxProPQuotient 2 (GalK K)) :
    frattiniFrameEval (evenDeepClass α hα hrange) g =
      evenDeepDigit α (chiCycKTwo (K := K) g) := rfl

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **The depth class is nonzero**, and **independent of `κ`**: the depth row value `mUnit α` is
attained, has depth digit `1` and mod-four parity `0`, so it separates `μ` from both `0` and `κ`.
This is the `M` analogue of `mEvenFrame_omega_indep`, with the attained row value doing at depth
`α` what `mUnit 2 ≡ 5 (mod 8)` does at depth `2`. -/
theorem evenDeep_class_indep {α : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α) :
    evenDeepClass α (Nat.le_of_succ_le hα) hrange ≠ 0 ∧
      evenDeepClass α (Nat.le_of_succ_le hα) hrange ≠ cyclotomicModFourClassKTwo (K := K) := by
  obtain ⟨g0, hg0⟩ : ∃ g : maxProPQuotient 2 (GalK K), chiCycKTwo (K := K) g = mUnit α := by
    have hm : mUnit α ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom := by
      rw [hrange]; exact mUnit_mem_imChiM α
    obtain ⟨g, hg⟩ := hm
    exact ⟨g, hg⟩
  have hone : frattiniFrameEval (evenDeepClass α (Nat.le_of_succ_le hα) hrange) g0 = 1 := by
    rw [evenDeepClass_eval, hg0, evenDeepDigit_mUnit hα]
  refine ⟨fun h0 ↦ ?_, fun heq ↦ ?_⟩
  · rw [h0, frattiniFrameEval_zero] at hone
    exact zero_ne_one hone
  · rw [heq, frattiniFrameEval_modFour, hg0, evenDegreeM_parity_mUnit hα] at hone
    exact zero_ne_one hone

/-- **The `M`-row cup-adapted Frattini frame, from the deep seam.**  For every `α ≥ 2`, from the
branch image identification, the ramified-`i` binder, and the isotropy of the depth class.

This is the re-cut of `evenFrame_of_kappaPin` the `M` branch needs: the refuted binder
`RowExactLevelFibreLiftSupply (vM α)` of `evenDegreeMCyclotomicFrattiniFrameSupply` is gone, and
the corrected seam `EvenRowDeepFibreLiftSupply (α - 1)` that replaces it is *discharged* here, not
carried, by `evenClimb_deepRowSupply_m`.  What is carried instead is the one datum §5 shows cannot
be avoided. -/
theorem evenFrameDeep_mFrame_of_range {α h : ℕ} (hα : 2 ≤ α)
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 2)
    (hkappa : cyclotomicModFourClassKTwo (K := K) ≠ 0)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α)
    (hiso : frattiniFrameCup (evenDeepClass α (Nat.le_of_succ_le hα) hrange)
      (evenDeepClass α (Nat.le_of_succ_le hα) hrange) = 0) :
    ∃ F : Frame (vM (h := h) α) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)),
      F.IsCupAdapted (evenFrameGram h) (evenFramePairing (K := K)) := by
  classical
  have hfin : Finite (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) := by
    apply Nat.finite_of_card_ne_zero
    rw [card_H1_zmodTwo_maxProTwoGalK (K := K)]
    positivity
  haveI := hfin
  have hcard : Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) = 2 ^ (2 * h + 4) := by
    rw [card_H1_zmodTwo_maxProTwoGalK (K := K), hdeg,
      show 2 * h + 2 + 2 = 2 * h + 4 from by omega]
  obtain ⟨hne0, hnekap⟩ := evenDeep_class_indep hα hrange
  obtain ⟨Φ, hGram, hΦkappa, hΦmu⟩ :=
    mEvenFrameAdaptedModelEquiv (isCupFormFp2_frattiniFrameCup (K := K))
      (nondegFp2_frattiniFrameCup (K := K)) (frattiniFrameCup_kappa (K := K))
      (evenFrameCup_kappa_self (K := K) ⟨h + 1, by omega⟩) hkappa hiso hne0 hnekap hcard
  refine evenFrameDeep_of_realizers (vM (h := h) α) Φ hGram fun i ↦ ?_
  obtain ⟨g', hg'⟩ := frattiniFrameEval_realizable (K := K) hfin
    ((evenFrameCoordL i).comp Φ.toLinearMap)
  have hD : ∀ x, frattiniFrameEval x g' = evenFrameCoord i (Φ x) := fun x ↦ hg' x
  -- the two shadows of the realizer match the row value
  have hpar : Multiplicative.toAdd (unitsModFourParity
        (Units.map (PadicInt.toZModPow 2).toMonoidHom (chiCycKTwo (K := K) g'))) =
      Multiplicative.toAdd (unitsModFourParity
        (Units.map (PadicInt.toZModPow 2).toMonoidHom (vM (h := h) α i))) := by
    rw [← frattiniFrameEval_modFour, hD (cyclotomicModFourClassKTwo (K := K)), hΦkappa,
      evenFrameCoord_kappaVec, evenDegreeM_parity_table hα i]
  have hdig : evenDeepDigit α (chiCycKTwo (K := K) g') = evenDeepDigit α (vM (h := h) α i) := by
    rw [← evenDeepClass_eval (Nat.le_of_succ_le hα) hrange g',
      hD (evenDeepClass α (Nat.le_of_succ_le hα) hrange), hΦmu, mEvenFrameCoord_tauVec,
      evenDeep_mTable hα i]
  obtain ⟨x, hx1, hx2⟩ := (evenClimb_deepRowSupply_m (h := h) hα hrange).lift 2 (le_refl 2) i g'
    (evenDeep_map_eq_of_shadow hα (evenDeep_bound_of_range (Nat.le_of_succ_le hα) hrange g')
      (evenDeep_mTable_pmOne (Nat.le_of_succ_le hα) i) hpar hdig)
  exact ⟨x, hx1, fun z ↦ (frattiniFrameEval_eq_of_levelMk_eq z hx2).symm.trans (hD z)⟩

/-! ## §5 The isotropy input is not removable, and the refuted seam is bypassed

The pin the frame imposes on the depth class is forced by the row table: the frame's generators
have the row values on the nose, so the depth class evaluates on them as the row's digit table,
which is the coordinate vector of `mEvenFrameTauVec h`, which is isotropic in the model.  Hence
any `M`-row cup-adapted frame at all, however obtained, already witnesses the hypothesis §4
carries.  Note that the deep seam plays no role here: the necessity is a statement about the row
table and the cup form. -/

omit [T2Space (GalK K)] in
/-- **Necessity of the isotropy.**  An `M`-row cup-adapted frame forces the depth class to be
isotropic.  So `evenFrameDeep_mFrame_of_range` is sharp: its extra hypothesis is equivalent, given
everything else, to the conclusion it helps prove, and no bookkeeping can remove it. -/
theorem evenFrameDeep_isotropic_of_frame {α h : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α)
    (F : Frame (vM (h := h) α) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)))
    (hcup : F.IsCupAdapted (evenFrameGram h) (evenFramePairing (K := K))) :
    frattiniFrameCup (evenDeepClass α (Nat.le_of_succ_le hα) hrange)
      (evenDeepClass α (Nat.le_of_succ_le hα) hrange) = 0 := by
  set c := evenDeepDigitChar α (Nat.le_of_succ_le hα) (chiCycKTwo (K := K))
    (evenDeep_bound_of_range (Nat.le_of_succ_le hα) hrange) with hc
  have hval : ∀ i : Fin (MarkedCore.coreRank h),
      Multiplicative.toAdd (c (F.generators i)) = evenFrameCoord i (mEvenFrameTauVec h) := by
    intro i
    show evenDeepDigit α (chiCycKTwo (K := K) (F.generators i)) = _
    rw [F.rows i, evenDeep_mTable hα i, mEvenFrameCoord_tauVec]
  calc frattiniFrameCup (evenDeepClass α (Nat.le_of_succ_le hα) hrange)
        (evenDeepClass α (Nat.le_of_succ_le hα) hrange)
      = evenFrameGram h (fun i j ↦ Multiplicative.toAdd (c (F.generators i)) *
          Multiplicative.toAdd (c (F.generators j))) := hcup c c
    _ = evenFrameGram h (fun i j ↦ evenFrameCoord i (mEvenFrameTauVec h) *
          evenFrameCoord j (mEvenFrameTauVec h)) := by
        congr 1
        funext i j
        rw [hval i, hval j]
    _ = evenFrameGramModel h (mEvenFrameTauVec h) (mEvenFrameTauVec h) :=
        evenFrameGram_modelCoord h _ _
    _ = 0 := mEvenFrameTauVec_self h

/-- **The `M`-row frame exists exactly when the depth class is isotropic.**  §4 and §5 combined:
under the branch identification, the ramified-`i` binder and the even-degree binder, the isotropy
of the depth class is not merely sufficient for the `M` frame, it is equivalent to it.  This is
the precise statement of what the `M` branch owes. -/
theorem evenFrameDeep_mFrame_iff_isotropic {α h : ℕ} (hα : 2 ≤ α)
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 2)
    (hkappa : cyclotomicModFourClassKTwo (K := K) ≠ 0)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α) :
    (∃ F : Frame (vM (h := h) α) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)),
        F.IsCupAdapted (evenFrameGram h) (evenFramePairing (K := K))) ↔
      frattiniFrameCup (evenDeepClass α (Nat.le_of_succ_le hα) hrange)
        (evenDeepClass α (Nat.le_of_succ_le hα) hrange) = 0 :=
  ⟨fun ⟨F, hcup⟩ ↦ evenFrameDeep_isotropic_of_frame hα hrange F hcup,
    fun hiso ↦ evenFrameDeep_mFrame_of_range hα hdeg hkappa hrange hiso⟩

/-- **The bypass, as one statement.**  At `α ≥ 3` the level-two instance that the committed frame
layer consumes is FALSE (`evenPerK_not_mLevelTwoLift_of_range`), and the `M`-row cup-adapted frame
exists nevertheless.  So the re-cut is a genuine change of route, not a rearrangement of the same
one: the refuted seam is not merely unused below, it is unavailable, and the frame is built
anyway. -/
theorem evenFrameDeep_mFrame_off_refutedSeam {α h : ℕ} (hα3 : 3 ≤ α)
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 2)
    (hkappa : cyclotomicModFourClassKTwo (K := K) ≠ 0)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α)
    (hiso : frattiniFrameCup
        (evenDeepClass α (Nat.le_of_succ_le (Nat.le_of_succ_le hα3)) hrange)
        (evenDeepClass α (Nat.le_of_succ_le (Nat.le_of_succ_le hα3)) hrange) = 0) :
    ¬ EvenPerK.EvenPerKLevelTwoLift (vM (h := h) α) (maxProPQuotient 2 (GalK K))
        (chiCycKTwo (K := K)) ∧
      ∃ F : Frame (vM (h := h) α) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)),
        F.IsCupAdapted (evenFrameGram h) (evenFramePairing (K := K)) :=
  ⟨EvenPerK.evenPerK_not_mLevelTwoLift_of_range (h := h) hα3 hrange,
    evenFrameDeep_mFrame_of_range (Nat.le_of_succ_le hα3) hdeg hkappa hrange hiso⟩

/-! ## §6 The `α = 2` stratum, where the input is committed

At `α = 2` the corrected depth is `α - 1 = 1`, the deep seam is the committed depth-`1` seam, and
`imChiM 2 = ⊤` makes it true; the committed `mEvenFrame_of_rowAttained` therefore builds the frame
outright.  Feeding that frame to §5 discharges the isotropy input on the whole stratum, which is
the layer's non-vacuity witness: the new hypothesis is a theorem where the committed route
reaches, and it is the exact depth-`α` generalisation of `mEvenFrameCup_omega_self`, since the
depth class at `α = 2` is the `ω` class, both vanishing exactly when `u^2 ≡ 1 (mod 16)`. -/

/-- **The isotropy input holds at `α = 2`**, from the committed `α = 2` frame through §5.  So the
hypothesis of §4 is not vacuous, and the whole `α = 2` stratum needs nothing new. -/
theorem evenFrameDeep_isotropic_two {h : ℕ} (hdeg : Module.finrank ℚ_[2] K = 2 * h + 2)
    (hkappa : cyclotomicModFourClassKTwo (K := K) ≠ 0)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM 2) :
    frattiniFrameCup (evenDeepClass 2 one_le_two hrange)
      (evenDeepClass 2 one_le_two hrange) = 0 := by
  obtain ⟨F, hcup⟩ := mEvenFrame_of_rowAttained (h := h) hdeg hkappa
    (evenRow_rowSupply_imChiM_two hrange (vM (h := h) 2))
    (evenRange_evenDegreeMModEightRowAttained hrange)
  exact evenFrameDeep_isotropic_of_frame (h := h) (le_refl 2) hrange F hcup

/-! ## §7 The stage base and the endpoint

The frame is cashed exactly as the committed `evenLevelThreeM_stageBase` cashes its own: the
level-three relation realization of `StageAbstractionEvenTransgression.lean` and
`Frame.toLevelThree`.  The only difference is which theorem produced the frame.

The per-field isotropy supply is stated at every branch depth that the identity could produce;
since the identity produces exactly one depth per field, it is a single datum in disguise. -/

/-- **The per-field isotropy supply**, quantified over the branch depth exactly as the carried
inputs of `StageAbstractionEvenPerK.lean` §5 are.  The range identity produces one `α` per field,
so an instance of this `Prop` is one equation. -/
def EvenDeepMIsotropicSupply (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop :=
  ∀ (alpha : ℕ) (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha),
    frattiniFrameCup (evenDeepClass alpha (Nat.le_of_succ_le halpha) hrange)
      (evenDeepClass alpha (Nat.le_of_succ_le halpha) hrange) = 0

/-- **The `M` level-three base, re-cut.**  The committed `evenLevelThreeM_stageBase` with its
refuted `RowExactLevelFibreLiftSupply (vM α)` binder replaced by the branch identification and the
isotropy of the depth class.  This is the statement that discharges `Hbase` of
`evenPerK_orientedEquivM` at the branch depth the range identity produces; the mod-eight image and
attainment seams are discharged here as well, from the identity. -/
theorem evenFrameDeep_mStageBase {α h : ℕ} (hα : 2 ≤ α)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (hkappa : cyclotomicModFourClassKTwo (K := K) ≠ 0)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α)
    (hiso : frattiniFrameCup (evenDeepClass α (Nat.le_of_succ_le hα) hrange)
      (evenDeepClass α (Nat.le_of_succ_le hα) hrange) = 0) :
    Nonempty (Tuple (mStageWord α h (Nat.le_of_succ_le hα)) (vM α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) 3) := by
  obtain ⟨F, hcup⟩ := evenFrameDeep_mFrame_of_range (h := h) hα (by omega) hkappa hrange hiso
  exact ⟨F.toLevelThree
    (evenTransgression.mLevelThreeRelationRealization_fieldCup K hα
      (evenLevelThree_isEvenGram h) F hcup)
    (maxProTwoGalK_isTopologicallyFinGen K) isProP_maxProPQuotient⟩

/-- **The even `M` endpoint with the base discharged.**  The committed
`evenPerK_orientedEquivM` carries `Hbase : EvenPerKMStageBase h K`; here that binder is replaced
by the ramified-`i` datum and the isotropy supply, and the remaining two inputs are the committed
`Hfam` and `Hup` verbatim.

The endpoint is re-assembled from the committed `evenPerK_forwardGeneratorDataM` rather than
obtained by instantiating `evenPerK_orientedEquivM`, because `EvenPerKMStageBase h K` is
quantified over *every* `α ≥ 1` while the range identity produces exactly one, so the base can
only be supplied at the depth the identity gives.  Nothing committed is restated: every step below
is a committed theorem applied to §7's base. -/
theorem evenFrameDeep_orientedEquivM {R : LocalReciprocity} (B : MarkedRecip R K)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (hkappa : cyclotomicModFourClassKTwo (K := K) ≠ 0)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hiso : EvenDeepMIsotropicSupply K)
    (Hfam : EvenPerK.EvenPerKMFamilySupply h K) (Hup : EvenPerK.EvenPerKMRawToBracket h K) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) := by
  obtain ⟨alpha, halpha, hrange⟩ := evenRange_range_eq_imChiM B hneg
  obtain ⟨base⟩ := evenFrameDeep_mStageBase (h := h) halpha hev hkappa hrange
    (Hiso alpha halpha hrange)
  exact ⟨alpha, halpha, nonempty_orientedEquivM_evenDegree_of_forwardGeneratorData alpha h
    (Nat.le_of_succ_le halpha) hev (EvenDemushkin.evenDem_mModelDemushkin alpha h halpha)
    (EvenPerK.evenPerK_forwardGeneratorDataM halpha hrange base
      (Hfam alpha (Nat.le_of_succ_le halpha)) (Hup alpha (Nat.le_of_succ_le halpha)))⟩

end EvenFieldDeep

end

end GQ2.Dyadic.EvenFrameDeep

/-! ## §8 Axiom pins

Every public declaration of this file, printed, the two local coefficient-action instances
included.  §1 and §2 are pure two-adic arithmetic and are expected at std-3 (`propext`,
`Classical.choice`, `Quot.sound`).  §3 to §7 reach the field layer, so they acquire exactly the
census axioms of their committed inputs (the frame scaffolding, the transgression realization, the
range identity, and the model Demushkin package).  No axiom of this file is new.  The endpoint
print is character-identical to the committed `evenPerK_orientedEquivM_two`, which is the
committed statement that also *builds* its level-three base; it exceeds the print of
`evenPerK_orientedEquivM` by exactly `hilbertSymbol_normCriterion_finiteDyadic`, which is the cost
of building the base rather than carrying it. -/

section AxiomPins

open GQ2.Dyadic.EvenFrameDeep

-- §1 the depth digit
#print axioms evenDeepDigitOfSq
#print axioms evenDeepDigit
#print axioms evenDeepDigit_map_iff
#print axioms evenDeepDigit_eq_zero_iff
#print axioms evenDeepDigit_eq_one_iff
#print axioms evenDeepDigit_eq_one_of_ne_zero
#print axioms evenDeepDigit_congr
#print axioms evenDeepDigit_one
#print axioms evenDeepDigit_neg_one
#print axioms evenDeepDigit_of_deep
#print axioms evenDeepDigit_deep_of_eq_zero
#print axioms evenDeep_sq_sub_one
#print axioms evenDeepDigit_eq_zero_iff_two_dvd
#print axioms evenDeepDigit_mul
#print axioms evenDeepDigit_inv
#print axioms evenDeepDigit_mUnit

-- §2 the depth character, the `M` table, and the determination
#print axioms evenDeepDigitHom
#print axioms evenDeepDigitChar
#print axioms evenDeepDigitChar_apply
#print axioms evenDeep_bound_of_range
#print axioms evenDeep_mTable
#print axioms evenDeep_mTable_pmOne
#print axioms evenDeep_dvd_of_shadow
#print axioms evenDeep_map_eq_of_shadow
#print axioms evenDeepDigit_nUnit
#print axioms evenDeep_digit_imChiN

-- §3 the frame assembly, and its two coefficient-action instances
#print axioms evenFrameDeepScalar
#print axioms evenFrameDeepContinuousScalar
#print axioms evenFrameDeep_of_realizers

-- §4 the depth class and the `M` frame
#print axioms evenDeepClass
#print axioms evenDeepClass_eval
#print axioms evenDeep_class_indep
#print axioms evenFrameDeep_mFrame_of_range

-- §5 necessity, the equivalence, and the bypass
#print axioms evenFrameDeep_isotropic_of_frame
#print axioms evenFrameDeep_mFrame_iff_isotropic
#print axioms evenFrameDeep_mFrame_off_refutedSeam

-- §6 the `α = 2` stratum
#print axioms evenFrameDeep_isotropic_two

-- §7 the stage base and the endpoint
#print axioms EvenDeepMIsotropicSupply
#print axioms evenFrameDeep_mStageBase
#print axioms evenFrameDeep_orientedEquivM

end AxiomPins
