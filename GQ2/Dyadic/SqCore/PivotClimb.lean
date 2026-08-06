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

/-! ## §2 The Frattini cup form is an invariant of `Aut(D_sq h)` -/

section CupInvariance

noncomputable local instance (h : ℕ) : DistribMulAction (DSq h : Type) (ZMod 2) :=
  scalarActionZmodTwo _

noncomputable local instance (h : ℕ) : ContinuousSMul (DSq h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

variable {h : ℕ}

/-- The mod-two cup form of the model, read at a pair of mod-two characters: the improved
relator's quadratic initial Gram on the rank-one matrix of their generator values
(`dsqFrattiniCupForm`). -/
noncomputable def sqGram (h : ℕ)
    (c d : ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2))) : ZMod 2 :=
  GQ2.ContCoh.sqRelatorQuadraticInitialGram h
    (fun i j => toAdd (c (sqGen h i)) * toAdd (d (sqGen h j)))

theorem sqGram_congr {c₁ c₂ d₁ d₂ : ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2))}
    (hc : ∀ i, c₁ (sqGen h i) = c₂ (sqGen h i)) (hd : ∀ i, d₁ (sqGen h i) = d₂ (sqGen h i)) :
    sqGram h c₁ d₁ = sqGram h c₂ d₂ := by
  unfold sqGram
  congr 1
  funext i j
  rw [hc i, hd j]

/-- The image of the canonical marking under an automorphism is again a marked relator. -/
theorem markedRelator_aut (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type)) :
    WordCoh.MarkedRelator (DSq h : Type) (MarkedCore.sqNatWord h) (fun i => Ψ (sqGen h i)) :=
  ⟨sqNatWord_isFrattini h, by
    show sqRelWord (fun i => Ψ (sqGen h i)) = 1
    rw [← map_sqRelWord Ψ (sqGen h), dsq_relation h, map_one]⟩

/-- **Transport of the presentation along an automorphism**: lifts are composed with `Ψ⁻¹`, and
homs out of `D_sq h` are determined on the image marking because `Ψ` is surjective. -/
noncomputable def presentedBy_aut (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type)) :
    WordCoh.PresentedBy (DSq h : Type) (MarkedCore.sqNatWord h) (fun i => Ψ (sqGen h i)) where
  liftHom hP ν hν :=
    ((presentedBy_DSq h).liftHom hP ν hν).comp ⟨Ψ.symm.toMonoidHom, Ψ.symm.continuous_toFun⟩
  liftHom_mark hP ν hν k := by
    show (presentedBy_DSq h).liftHom hP ν hν (Ψ.symm (Ψ (sqGen h k))) = ν k
    rw [Ψ.symm_apply_apply]
    exact (presentedBy_DSq h).liftHom_mark hP ν hν k
  hom_ext φ ψ hgen := by
    have hcomp : φ.comp ⟨Ψ.toMonoidHom, Ψ.continuous_toFun⟩ =
        ψ.comp ⟨Ψ.toMonoidHom, Ψ.continuous_toFun⟩ :=
      (presentedBy_DSq h).hom_ext _ _ hgen
    refine DFunLike.ext _ _ fun x => ?_
    have hx := DFunLike.congr_fun hcomp (Ψ.symm x)
    show φ x = ψ x
    rw [← Ψ.apply_symm_apply x]
    exact hx

/-- The one-relator obstruction functional attached to the improved word at the marking
`Ψ ∘ sqGen h`. -/
noncomputable def sqAutObs (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type)) :
    ContCoh.H2 (DSq h : Type) (ZMod 2) →+ ZMod 2 :=
  WordCoh.obsH2 (fun _ _ => rfl) (MarkedCore.sqNatWord h) (fun i => Ψ (sqGen h i))
    (markedRelator_aut Ψ)

theorem sqAutObs_injective (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type)) :
    Function.Injective (sqAutObs Ψ) :=
  WordCoh.obsH2_injective (fun _ _ => rfl) (MarkedCore.sqNatWord h) (fun i => Ψ (sqGen h i))
    (markedRelator_aut Ψ) (presentedBy_aut Ψ) (isProP_DSq h)

/-- The two obstruction functionals — at the canonical marking and at its image under `Ψ` —
are both injective, hence equal: `H²(D_sq h, 𝔽₂)`'s identification with `𝔽₂` is unique. -/
theorem dsqObs_eq_sqAutObs (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type)) :
    dsqObs h = sqAutObs Ψ :=
  addMonoidHom_zmodTwo_eq_of_injective _ _ (dsqObs_injective h) (sqAutObs_injective Ψ)

/-- **The Frattini cup form is `Aut(D_sq h)`-invariant.**  No orientation clause: *every*
continuous automorphism preserves the mod-two cup form, because both obstruction functionals on
`H²(D_sq h, 𝔽₂)` are injective and `H²` is one-dimensional. -/
theorem sqGram_comp_autHom (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type))
    (c d : ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2))) :
    sqGram h (c.comp (autHom Ψ)) (d.comp (autHom Ψ)) = sqGram h c d := by
  have hΨ := obsH2_sqNatWord_characterCup (G := (DSq h : Type)) (fun _ _ => rfl) h
    (fun i => Ψ (sqGen h i)) (markedRelator_aut Ψ) c d
  have hid := dsqFrattiniCupForm h c d
  have hobs : ∀ z, WordCoh.obsH2 (fun _ _ => rfl) (MarkedCore.sqNatWord h)
      (fun i => Ψ (sqGen h i)) (markedRelator_aut Ψ) z = dsqObs h z := fun z =>
    congrArg (fun F : ContCoh.H2 (DSq h : Type) (ZMod 2) →+ ZMod 2 => F z)
      (dsqObs_eq_sqAutObs Ψ).symm
  show GQ2.ContCoh.sqRelatorQuadraticInitialGram h
      (fun i j => toAdd (c (Ψ (sqGen h i))) * toAdd (d (Ψ (sqGen h j)))) =
    GQ2.ContCoh.sqRelatorQuadraticInitialGram h
      (fun i j => toAdd (c (sqGen h i)) * toAdd (d (sqGen h j)))
  exact hΨ.symm.trans ((hobs _).trans hid)

end CupInvariance

end SqCore

end Dyadic

end GQ2
