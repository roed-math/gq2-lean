/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.PivotSeedTransport
import GQ2.Dyadic.Instances.SqModelPresentingFrameCupAdapted

/-!
# The parity of the pivot row is an invariant of the χ-preserving automorphism group

Work in progress.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore GQ2.Dyadic.LSquare

/-! ## §1 Mod-two reduction of a `ℤ₂`-marking -/

section ModTwo

/-- `Multiplicative (ZMod 2)` is pro-`2` (a finite `2`-group). -/
theorem isProP_multZMod2 : IsProP 2 (Multiplicative (ZMod 2)) :=
  SectionThree.isProP_two_multZMod2

/-- Every element of `Multiplicative (ZMod 2)` squares to `1`. -/
theorem sq_eq_one_multZMod2 (y : Multiplicative (ZMod 2)) : y ^ 2 = 1 := by
  revert y
  decide

/-- In `Multiplicative (ZMod 2)` a `ℤ₂`-power at an **even** exponent is trivial. -/
theorem zpowZtwo_multZMod2_of_even (y : Multiplicative (ZMod 2)) {t : ℤ_[2]}
    (ht : (2 : ℤ_[2]) ∣ t) : zpowZtwo isProP_multZMod2 y t = 1 := by
  obtain ⟨s, rfl⟩ := ht
  rw [show (2 : ℤ_[2]) * s = ((2 : ℕ) : ℤ_[2]) * s by push_cast; ring, ← zpowZtwo_zpowZtwo,
    zpowZtwo_natCast, sq_eq_one_multZMod2, zpowZtwo_one_base]

/-- …and at an **odd** exponent it is the base. -/
theorem zpowZtwo_multZMod2_of_odd (y : Multiplicative (ZMod 2)) {t : ℤ_[2]}
    (ht : ¬ (2 : ℤ_[2]) ∣ t) : zpowZtwo isProP_multZMod2 y t = y := by
  obtain ⟨q, hq⟩ := two_dvd_sub_of_isUnit (isUnit_iff_not_two_dvd.mpr ht) isUnit_one
  have hsplit : t = 1 + 2 * q := by linear_combination hq
  rw [hsplit, zpowZtwo_add, zpowZtwo_one_exp,
    zpowZtwo_multZMod2_of_even y ⟨q, rfl⟩, mul_one]

/-- **The mod-two reduction morphism** `Multiplicative ℤ₂ → Multiplicative (ZMod 2)`. -/
noncomputable def sqModTwo : ContinuousMonoidHom (Multiplicative ℤ_[2]) (Multiplicative (ZMod 2)) :=
  zpowZtwoHom isProP_multZMod2 (ofAdd (1 : ZMod 2))

theorem sqModTwo_apply (t : ℤ_[2]) :
    sqModTwo (ofAdd t) = zpowZtwo isProP_multZMod2 (ofAdd (1 : ZMod 2)) t := rfl

theorem sqModTwo_eq_one_of_even {t : ℤ_[2]} (ht : (2 : ℤ_[2]) ∣ t) : sqModTwo (ofAdd t) = 1 := by
  rw [sqModTwo_apply]
  exact zpowZtwo_multZMod2_of_even _ ht

theorem sqModTwo_eq_of_odd {t : ℤ_[2]} (ht : ¬ (2 : ℤ_[2]) ∣ t) :
    sqModTwo (ofAdd t) = ofAdd (1 : ZMod 2) := by
  rw [sqModTwo_apply]
  exact zpowZtwo_multZMod2_of_odd _ ht

theorem toAdd_sqModTwo_of_even {t : ℤ_[2]} (ht : (2 : ℤ_[2]) ∣ t) :
    toAdd (sqModTwo (ofAdd t)) = 0 := by rw [sqModTwo_eq_one_of_even ht]; rfl

theorem toAdd_sqModTwo_of_odd {t : ℤ_[2]} (ht : ¬ (2 : ℤ_[2]) ∣ t) :
    toAdd (sqModTwo (ofAdd t)) = 1 := by rw [sqModTwo_eq_of_odd ht, toAdd_ofAdd]

/-- `ofAdd 1 ≠ 1` in `Multiplicative (ZMod 2)`. -/
theorem ofAdd_one_ne_one_multZMod2 : (ofAdd (1 : ZMod 2)) ≠ 1 := by decide

/-- **The reduction detects parity**: `sqModTwo (ofAdd t) = 1` exactly for even `t`. -/
theorem sqModTwo_eq_one_iff {t : ℤ_[2]} : sqModTwo (ofAdd t) = 1 ↔ (2 : ℤ_[2]) ∣ t := by
  refine ⟨fun ht => ?_, sqModTwo_eq_one_of_even⟩
  by_contra hc
  exact ofAdd_one_ne_one_multZMod2 ((sqModTwo_eq_of_odd hc).symm.trans ht)

/-- The reduction of a marking, as a mod-two character of the model. -/
noncomputable def sqRedMark {h : ℕ}
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2)) :=
  sqModTwo.comp nu'

theorem sqRedMark_apply {h : ℕ}
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (x : (DSq h : Type)) :
    sqRedMark nu' x = sqModTwo (ofAdd (toAdd (nu' x))) := rfl

/-- Two `2`-adic values have the same reduction exactly when they agree modulo `2`. -/
theorem sqModTwo_eq_iff {s t : ℤ_[2]} :
    sqModTwo (ofAdd s) = sqModTwo (ofAdd t) ↔ (2 : ℤ_[2]) ∣ s - t := by
  rw [← sqModTwo_eq_one_iff, ofAdd_sub, map_div, div_eq_one]

/-- Two elements have the same reduction exactly when their rows agree modulo `2`. -/
theorem sqRedMark_eq_iff {h : ℕ}
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (x y : (DSq h : Type)) :
    sqRedMark nu' x = sqRedMark nu' y ↔ (2 : ℤ_[2]) ∣ toAdd (nu' x) - toAdd (nu' y) := by
  rw [sqRedMark_apply, sqRedMark_apply, sqModTwo_eq_iff]

end ModTwo

end SqCore

end Dyadic

end GQ2
