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

/-! ## §3 The χ-exponent row modulo two, and the Gram identity that names the pivot -/

section LamRow

variable {h : ℕ}

/-- **The χ-exponent row is preserved modulo two by every χ-preserving automorphism.**  Only
`χ_sq² = X^{2λ}` and `X² ≠ 1` are used: an odd difference would make `X²` trivial. -/
theorem two_dvd_toAdd_nuLam_sub_of_chiPreserving
    (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type))
    (hchi : ∀ x, chiSq h (Ψ x) = chiSq h x) (x : (DSq h : Type)) :
    (2 : ℤ_[2]) ∣ toAdd (nuLam h (Ψ x)) - toAdd (nuLam h x) := by
  by_contra hc
  have hu : IsUnit (toAdd (nuLam h (Ψ x)) - toAdd (nuLam h x)) := isUnit_iff_not_two_dvd.mpr hc
  have h1 : zpowZtwo isProP_two_unitsPadicInt (rootXUnit ^ 2) (toAdd (nuLam h (Ψ x)))
      = zpowZtwo isProP_two_unitsPadicInt (rootXUnit ^ 2) (toAdd (nuLam h x)) := by
    rw [← xPowLamSq_apply, ← xPowLamSq_apply, ← chiSq_sq_eq_lam, ← chiSq_sq_eq_lam, hchi]
  refine rootXUnit_sq_ne_one
    (eq_one_of_zpowZtwo_eq_one_of_isUnit isProP_two_unitsPadicInt _ hu ?_)
  rw [sub_eq_add_neg, zpowZtwo_add, h1, ← zpowZtwo_add, add_neg_cancel, zpowZtwo_zero_exp]

/-- The reduced χ-exponent row is literally `Aut_χ`-invariant. -/
theorem sqRedMark_nuLam_aut (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type))
    (hchi : ∀ x, chiSq h (Ψ x) = chiSq h x) (x : (DSq h : Type)) :
    sqRedMark (nuLam h) (Ψ x) = sqRedMark (nuLam h) x :=
  (sqRedMark_eq_iff (nuLam h) (Ψ x) x).mpr
    (two_dvd_toAdd_nuLam_sub_of_chiPreserving Ψ hchi x)

/-! ### The generator values of the reduced χ-exponent row: `(1, 1, 0, 0, …, 0)` -/

theorem toAdd_sqRedMark_nuLam_zero (h : ℕ) :
    toAdd (sqRedMark (nuLam h) (sqGen h 0)) = 1 := by
  show toAdd (sqModTwo (nuLam h (dsqSigma h))) = 1
  rw [nuLam_sigma]
  exact toAdd_sqModTwo_of_odd (isUnit_iff_not_two_dvd.mp isUnit_sqPivotExp)

theorem toAdd_sqRedMark_nuLam_one (h : ℕ) :
    toAdd (sqRedMark (nuLam h) (sqGen h 1)) = 1 := by
  show toAdd (sqModTwo (nuLam h (dsqX0 h))) = 1
  rw [nuLam_x0]
  exact toAdd_sqModTwo_of_odd (isUnit_iff_not_two_dvd.mp isUnit_one)

theorem toAdd_sqRedMark_nuLam_two (h : ℕ) :
    toAdd (sqRedMark (nuLam h) (sqGen h 2)) = 0 := by
  show toAdd (sqModTwo (nuLam h (dsqX1 h))) = 0
  rw [nuLam_x1]
  exact toAdd_sqModTwo_of_even ⟨1, by ring⟩

theorem toAdd_sqRedMark_nuLam_handleU (j : Fin h) :
    toAdd (sqRedMark (nuLam h) (sqGen h (sqHandleIdxU j))) = 0 := by
  show toAdd (sqModTwo (nuLam h (sqGen h (sqHandleIdxU j)))) = 0
  rw [nuLam_handleU, map_one]
  rfl

theorem toAdd_sqRedMark_nuLam_handleV (j : Fin h) :
    toAdd (sqRedMark (nuLam h) (sqGen h (sqHandleIdxV j))) = 0 := by
  show toAdd (sqModTwo (nuLam h (sqGen h (sqHandleIdxV j)))) = 0
  rw [nuLam_handleV, map_one]
  rfl

/-- The mod-two pivot row of a character, in the two core coordinates: `c(w) = c(σ) + c(x₀)`
(the exponent `c₀` is odd, and `−1 = 1` in `𝔽₂`). -/
theorem toAdd_modTwo_sqPivot
    (c : ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2))) :
    toAdd (c (sqPivot h)) = toAdd (c (sqGen h 0)) + toAdd (c (sqGen h 1)) := by
  have hodd : ¬ (2 : ℤ_[2]) ∣ sqPivotExp := isUnit_iff_not_two_dvd.mp isUnit_sqPivotExp
  have hval : c (sqPivot h) = c (dsqSigma h) * (c (dsqX0 h))⁻¹ := by
    show c (sqMixPivotElem h sqPivotExp) = _
    rw [sqMixPivotElem, map_mul, map_inv,
      map_zpowZtwo (isProP_DSq h) isProP_multZMod2 c (dsqX0 h) sqPivotExp,
      zpowZtwo_multZMod2_of_odd _ hodd]
  have hneg : ∀ z : ZMod 2, -z = z := by decide
  rw [hval, toAdd_mul, toAdd_inv, hneg]
  rfl

/-- **The Gram identity that names the pivot.**  Paired against the reduced χ-exponent row, the
Frattini cup form of the model *is* evaluation at the χ-trivial pivot:

```text
  λ̄ ⌣ c = c(w)   for every mod-two character c.
```

In the relator's constructor table this is the single line
`Gram(λ̄, c) = λ̄₂c₂ + (λ̄₀c₁ + λ̄₁c₀) + Σⱼ(…) = c₁ + c₀ = c(w)`.  It is the mod-two form of
"`w̄` is the vector cup-dual to `λ̄`", and it is what makes the pivot row a cup-form
invariant. -/
theorem sqGram_nuLam (h : ℕ)
    (c : ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2))) :
    sqGram h (sqRedMark (nuLam h)) c = toAdd (c (sqPivot h)) := by
  have hsum : ∑ j : Fin h,
      (toAdd (sqRedMark (nuLam h) (sqGen h (sqHandleIdxU j))) *
          toAdd (c (sqGen h (sqHandleIdxV j))) +
        toAdd (sqRedMark (nuLam h) (sqGen h (sqHandleIdxV j))) *
          toAdd (c (sqGen h (sqHandleIdxU j)))) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [toAdd_sqRedMark_nuLam_handleU, toAdd_sqRedMark_nuLam_handleV, zero_mul, zero_mul,
        add_zero]
  show GQ2.ContCoh.sqRelatorQuadraticInitialGram h
      (fun i j => toAdd (sqRedMark (nuLam h) (sqGen h i)) * toAdd (c (sqGen h j))) = _
  rw [GQ2.ContCoh.sqRelatorQuadraticInitialGram_eq, hsum, toAdd_sqRedMark_nuLam_zero,
    toAdd_sqRedMark_nuLam_one, toAdd_sqRedMark_nuLam_two, toAdd_modTwo_sqPivot,
    zero_mul, one_mul, one_mul, zero_add, add_zero]
  ring

end LamRow

/-! ## §4 The parity of the pivot row is `Aut_χ`-invariant -/

section PivotParity

variable {h : ℕ}

/-- **THE INVARIANCE.**  Every χ-preserving continuous automorphism of `D_sq h` fixes the
χ-trivial pivot `w` in the Frattini quotient: every mod-two character takes the same value at
`Ψ w` and at `w`.

Two inputs, both proved above: the cup form is `Aut(D_sq h)`-invariant (§2, no orientation
clause), and the reduced χ-exponent row `λ̄` is `Aut_χ`-invariant (§3).  The bridge is the Gram
identity `λ̄ ⌣ c = c(w)`: it turns invariance of the *functional* `λ̄` into invariance of the
*vector* `w̄`, because the cup form identifies the two. -/
theorem modTwoChar_aut_sqPivot (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type))
    (hchi : ∀ x, chiSq h (Ψ x) = chiSq h x)
    (c : ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2))) :
    c (Ψ (sqPivot h)) = c (sqPivot h) := by
  have hinv := sqGram_comp_autHom Ψ (sqRedMark (nuLam h)) c
  have hL : sqGram h ((sqRedMark (nuLam h)).comp (autHom Ψ)) (c.comp (autHom Ψ))
      = sqGram h (sqRedMark (nuLam h)) (c.comp (autHom Ψ)) :=
    sqGram_congr (fun i => sqRedMark_nuLam_aut Ψ hchi (sqGen h i)) (fun _ => rfl)
  rw [hL, sqGram_nuLam, sqGram_nuLam] at hinv
  exact Multiplicative.toAdd.injective hinv

/-- **The pivot row is fixed modulo two** by every χ-preserving automorphism, against every
marking. -/
theorem two_dvd_toAdd_nu_aut_sqPivot_sub (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type))
    (hchi : ∀ x, chiSq h (Ψ x) = chiSq h x)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    (2 : ℤ_[2]) ∣ toAdd (nu' (Ψ (sqPivot h))) - toAdd (nu' (sqPivot h)) :=
  (sqRedMark_eq_iff nu' (Ψ (sqPivot h)) (sqPivot h)).mp
    (modTwoChar_aut_sqPivot Ψ hchi (sqRedMark nu'))

/-- **The unit locus of the pivot row is `Aut_χ`-invariant.**  No χ-preserving automorphism can
turn an even pivot row into a unit one, or the other way round. -/
theorem isUnit_toAdd_nu_aut_sqPivot_iff
    (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type))
    (hchi : ∀ x, chiSq h (Ψ x) = chiSq h x)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    IsUnit (toAdd (nu' (Ψ (sqPivot h)))) ↔ IsUnit (toAdd (nu' (sqPivot h))) := by
  obtain ⟨s, hs⟩ := two_dvd_toAdd_nu_aut_sqPivot_sub Ψ hchi nu'
  constructor
  · exact fun hu => isUnit_iff_not_two_dvd.mpr fun ⟨p, hp⟩ =>
      (isUnit_iff_not_two_dvd.mp hu) ⟨s + p, by linear_combination hs + hp⟩
  · exact fun hu => isUnit_iff_not_two_dvd.mpr fun ⟨p, hp⟩ =>
      (isUnit_iff_not_two_dvd.mp hu) ⟨p - s, by linear_combination hp - hs⟩

end PivotParity

/-! ## §5 A marking with a unit handle row -/

section HandleMark

variable {h : ℕ}

theorem sqZero_ne_handleU (j : Fin h) : (0 : Fin (sqRank h)) ≠ sqHandleIdxU j :=
  Ne.symm (sqHandleIdxU_ne_of_val_lt j (i := 0) (by rw [sqVal_zero]; omega))

theorem sqOne_ne_handleU (j : Fin h) : (1 : Fin (sqRank h)) ≠ sqHandleIdxU j :=
  Ne.symm (sqHandleIdxU_ne_of_val_lt j (i := 1) (by rw [sqVal_one]; omega))

theorem sqTwo_ne_handleU (j : Fin h) : (2 : Fin (sqRank h)) ≠ sqHandleIdxU j :=
  Ne.symm (sqHandleIdxU_ne_of_val_lt j (i := 2) (by rw [sqVal_two]; omega))

/-- The marking of `D_sq h` with core rows `(a, b, 2b)`, `u_j`-row `1`, and every other handle
row `0`.  Its pivot row is `a − c₀·b`, so at `(a, b) = (0, 0)` the pivot row is **even** while
the `u_j`-row is a **unit** — the configuration `sqJointSurjective_isUnit_pivot_or_handle`
allows at `h ≥ 1` and forbids at `h = 0`. -/
noncomputable def nuHandleU (h : ℕ) (a b : ℤ_[2]) (j : Fin h) :
    ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
  sqLiftHom h PropOneOne.isProP_two_multPadicInt
    (Function.update (sqMark (ofAdd a) (ofAdd b) (ofAdd (2 * b))) (sqHandleIdxU j)
      (ofAdd (1 : ℤ_[2]))) (by
      rw [sqRelWord_comm, Function.update_of_ne (sqOne_ne_handleU j),
        Function.update_of_ne (sqTwo_ne_handleU j), sqMark_one, sqMark_two,
        ← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add, ← ofAdd_zero]
      congr 1
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      ring)

variable (a b : ℤ_[2]) (j : Fin h)

@[simp] theorem nuHandleU_sigma : nuHandleU h a b j (dsqSigma h) = ofAdd a :=
  (sqLiftHom_gen _ _ _ _ 0).trans
    (by rw [Function.update_of_ne (sqZero_ne_handleU j), sqMark_zero])

@[simp] theorem nuHandleU_x0 : nuHandleU h a b j (dsqX0 h) = ofAdd b :=
  (sqLiftHom_gen _ _ _ _ 1).trans
    (by rw [Function.update_of_ne (sqOne_ne_handleU j), sqMark_one])

@[simp] theorem nuHandleU_self : nuHandleU h a b j (sqGen h (sqHandleIdxU j)) = ofAdd (1 : ℤ_[2]) :=
  (sqLiftHom_gen _ _ _ _ _).trans (Function.update_self _ _ _)

/-- The pivot row of the handle marking. -/
theorem toAdd_nuHandleU_sqPivot :
    toAdd (nuHandleU h a b j (sqPivot h)) = a - sqPivotExp * b := by
  rw [toAdd_nu_sqPivot, nuHandleU_sigma, nuHandleU_x0, toAdd_ofAdd, toAdd_ofAdd]

end HandleMark

/-! ## §6 The consequences: the transfers, the unitizer, and the oriented residual -/

section Consequences

variable {h : ℕ}

/-- **The handle-to-core transfer forces its letter's row to be even, against every marking.**
The move shifts the pivot row by exactly the row of the transferred letter, and §4 says the
pivot row cannot move modulo `2`. -/
theorem two_dvd_toAdd_of_sqHandleToCoreMove {i : Fin (sqRank h)} (H : SqHandleToCoreMove h i)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) :
    (2 : ℤ_[2]) ∣ toAdd (nu' (sqGen h i)) := by
  obtain ⟨Ψ, hchi, hs, hx, _, _⟩ := H nu'
  have hx' : toAdd (nu' (Ψ (dsqX0 h))) = toAdd (nu' (dsqX0 h)) := by rw [hx]
  have hval : toAdd (nu' (Ψ (sqPivot h)))
      = toAdd (nu' (sqPivot h)) + toAdd (nu' (sqGen h i)) := by
    rw [toAdd_aut_sqPivot, hs, hx', toAdd_nu_sqPivot]
    ring
  obtain ⟨s, hs2⟩ := two_dvd_toAdd_nu_aut_sqPivot_sub Ψ hchi nu'
  exact ⟨s, by linear_combination hs2 - hval⟩

/-- **THE TRANSFERS ARE FALSE.**  At every `h ≥ 1` and every handle index `j`, the
handle-to-core move at `u_j` does not exist: the marking `nuHandleU h 0 0 j` has an odd
`u_j`-row, and the move would push that odd row onto the `Aut_χ`-invariant pivot row. -/
theorem not_sqHandleToCoreMove_handleU (j : Fin h) : ¬ SqHandleToCoreMove h (sqHandleIdxU j) := by
  intro H
  obtain ⟨s, hs⟩ := two_dvd_toAdd_of_sqHandleToCoreMove H (nuHandleU h 0 0 j)
  rw [nuHandleU_self, toAdd_ofAdd] at hs
  exact (isUnit_iff_not_two_dvd.mp isUnit_one) ⟨s, hs⟩

/-- **The unitizer carries no automorphism content.**  `SqPivotUnitizer h` is *equivalent* to the
purely numerical statement that joint surjectivity already forces a unit pivot row: the "only
if" direction is §4's invariance, the "if" direction is the identity automorphism.

At `h = 0` the right-hand side is `sqJointSurjective_isUnit_pivot_zero`, which is why
`sqPivotUnitizer_zero` is a theorem.  At `h ≥ 1` the right-hand side is **false** (§6,
`not_sqPivotUnitizer`). -/
theorem sqPivotUnitizer_iff :
    SqPivotUnitizer h ↔ ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      SqJointSurjective h nu' → IsUnit (toAdd (nu' (sqPivot h))) := by
  constructor
  · intro H nu' hjs
    obtain ⟨Ψ, hchi, hu⟩ := H nu' hjs
    exact (isUnit_toAdd_nu_aut_sqPivot_iff Ψ hchi nu').mp hu
  · exact fun H nu' hjs => ⟨ContinuousMulEquiv.refl _, fun _ => rfl, H nu' hjs⟩

/-- The oriented residual forces the same numerical statement (it implies the unitizer). -/
theorem isUnit_toAdd_sqPivot_of_orientedClear (H : SqNuOrientedClear h)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hjs : SqJointSurjective h nu') : IsUnit (toAdd (nu' (sqPivot h))) :=
  sqPivotUnitizer_iff.mp (sqPivotUnitizer_of_orientedClear H) nu' hjs

end Consequences

/-! ## §7 The witness: `χ_sq` is onto, so the even-pivot configuration really occurs -/

section Witness

/-- **An index-two open normal subgroup of `ℤ₂ˣ` cannot contain both `X` and `−1`.**  This is
the `ℤ₂ˣ`-only half of `GQ2.Roe.chiR_surjective`, isolated so that it can be run at `χ_sq`
instead of `χ_R`: the quotient has order two so it kills every square, `−3 ≡ X (mod 8)` makes
`−3` a square times `X`, and `mod8_sq` then exhausts `ℤ₂ˣ`. -/
theorem not_index_two_of_rootXUnit_negOne_mem (M : OpenNormalSubgroup ℤ_[2]ˣ)
    (hM : M.toSubgroup.index = 2) (hrootX : rootXUnit ∈ M.toSubgroup)
    (hneg1 : (-1 : ℤ_[2]ˣ) ∈ M.toSubgroup) : False := by
  haveI : Finite (ℤ_[2]ˣ ⧸ M.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hsq : ∀ u : ℤ_[2]ˣ, u ^ 2 ∈ M.toSubgroup := by
    intro u
    have hpow : (QuotientGroup.mk' M.toSubgroup u) ^ 2 = 1 := by
      have hd := orderOf_dvd_natCard (QuotientGroup.mk' M.toSubgroup u)
      rw [← Subgroup.index_eq_card, hM] at hd
      exact orderOf_dvd_iff_pow_eq_one.mp hd
    have h2 : QuotientGroup.mk' M.toSubgroup (u ^ 2) = 1 := by rw [map_pow]; exact hpow
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  have hrootX3 : PadicInt.toZModPow 3 rootX = 5 := by
    have hr := congrArg (PadicInt.toZModPow (p := 2) 3) rootX_isRoot
    simp only [map_add, map_mul, map_pow, map_ofNat, map_one, map_zero] at hr
    exact (by decide : ∀ r : ZMod (2 ^ 3), r ^ 3 + 2 * r ^ 2 + 1 = 0 → r = 5) _ hr
  have hn3v : (SectionThree.neg3Int : ℤ_[2]) = -3 := by
    simp only [SectionThree.neg3Int]; exact IsUnit.unit_spec _
  have hn3val3 : PadicInt.toZModPow 3 (SectionThree.neg3Int : ℤ_[2]) = 5 := by
    rw [hn3v, show (-3 : ℤ_[2]) = ((-3 : ℤ) : ℤ_[2]) by push_cast; ring, map_intCast]; decide
  have hres : PadicInt.toZModPow 3 (SectionThree.neg3Int : ℤ_[2])
      = PadicInt.toZModPow 3 (rootXUnit : ℤ_[2]) := by
    rw [hn3val3, val_rootXUnit, hrootX3]
  have hdvd : (8 : ℤ_[2]) ∣ ((SectionThree.neg3Int : ℤ_[2]) - rootXUnit) := by
    rw [← SectionThree.toZModPow3_eq_zero_iff, map_sub, hres, sub_self]
  have hs1 : (rootXUnit : ℤ_[2]) * ((rootXUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have heq : ((SectionThree.neg3Int * rootXUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1
      = ((SectionThree.neg3Int : ℤ_[2]) - rootXUnit) * ((rootXUnit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) := by
    rw [Units.val_mul, sub_mul, hs1]
  obtain ⟨t, ht⟩ := SectionThree.hensel_sq (SectionThree.neg3Int * rootXUnit⁻¹)
    (by rw [heq]; exact hdvd.mul_right _)
  have hn3eq : SectionThree.neg3Int = rootXUnit * t ^ 2 := by
    rw [← ht, mul_comm SectionThree.neg3Int rootXUnit⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
  have hn3 : SectionThree.neg3Int ∈ M.toSubgroup := by
    rw [hn3eq]; exact M.toSubgroup.mul_mem hrootX (hsq t)
  have htop : M.toSubgroup = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro v
    obtain ⟨s₂, hs₂, w, hvw⟩ := SectionThree.mod8_sq v
    have hs₂mem : s₂ ∈ M.toSubgroup := by
      rcases hs₂ with rfl | rfl | rfl | rfl
      · exact M.toSubgroup.one_mem
      · exact hneg1
      · exact hn3
      · rw [show (-SectionThree.neg3Int : ℤ_[2]ˣ) = (-1) * SectionThree.neg3Int from
          (neg_one_mul _).symm]
        exact M.toSubgroup.mul_mem hneg1 hn3
    rw [hvw]; exact M.toSubgroup.mul_mem hs₂mem (hsq w)
  rw [htop, Subgroup.index_top] at hM
  omega

/-- **`χ_sq` is onto `ℤ₂ˣ`** at every handle count: the `x₀`-row supplies `X` and the
`x₁`-row supplies `−1 = Y·X⁻²`. -/
theorem chiSq_surjective (h : ℕ) : Function.Surjective (chiSq h) := by
  refine surjective_of_forall_not_le_index_p (p := 2) isProP_two_unitsPadicInt (chiSq h) ?_
  intro M hM hle
  have hrootX : rootXUnit ∈ M.toSubgroup := hle ⟨dsqX0 h, chiSq_x0 h⟩
  have htors : chiSq h (dsqX1 h * ((dsqX0 h) ^ 2)⁻¹) = -1 := by
    rw [map_mul, map_inv, map_pow, chiSq_x0, chiSq_x1, YvalUnit_eq_neg_sq, neg_mul,
      mul_inv_cancel]
  exact not_index_two_of_rootXUnit_negOne_mem M hM hrootX
    (hle ⟨dsqX1 h * ((dsqX0 h) ^ 2)⁻¹, htors⟩)

variable {h : ℕ}

/-- **The handle marking is jointly surjective**: its `u_j`-row is a unit and `χ_sq(u_j) = 1`,
so the `u_j`-powers of any χ-preimage sweep out every `ν`-value at a fixed χ-value. -/
theorem sqJointSurjective_nuHandleU (a b : ℤ_[2]) (j : Fin h) :
    SqJointSurjective h (nuHandleU h a b j) := by
  intro u y
  obtain ⟨g, hg⟩ := chiSq_surjective h u
  refine ⟨g * zpowZtwo (isProP_DSq h) (sqGen h (sqHandleIdxU j))
    (y - toAdd (nuHandleU h a b j g)), ?_, ?_⟩
  · rw [map_mul, hg, map_zpowZtwo (isProP_DSq h) isProP_two_unitsPadicInt (chiSq h),
      chiSq_handleU, zpowZtwo_one_base, mul_one]
  · refine Multiplicative.toAdd.injective ?_
    rw [map_mul, toAdd_mul, toAdd_map_zpowZtwo (isProP_DSq h) (nuHandleU h a b j),
      nuHandleU_self, toAdd_ofAdd, toAdd_ofAdd, mul_one]
    ring

/-- **THE REFUTATION.**  `SqPivotUnitizer h` is **false** at every `h ≥ 1`.

*Witness*: the marking `ν' = nuHandleU h 0 0 j`, rows `(0, 0, 0, …, u_j ↦ 1, …, 0)`.  It is
jointly surjective with `χ_sq` (§7) and its pivot row is `0`, not a unit.  By §4 no
χ-preserving automorphism can change that parity, so no `Ψ` can unitize the pivot row.

This kills the `h ≥ 1` half of `PivotUnitizer.lean`'s reduction outright: the "one bit" the
handle-to-core transfers were supposed to supply cannot be supplied by *any* automorphism. -/
theorem not_sqPivotUnitizer (hh : 0 < h) : ¬ SqPivotUnitizer h := by
  intro H
  have hu := sqPivotUnitizer_iff.mp H (nuHandleU h 0 0 ⟨0, hh⟩)
    (sqJointSurjective_nuHandleU 0 0 ⟨0, hh⟩)
  rw [toAdd_nuHandleU_sqPivot] at hu
  exact (isUnit_iff_not_two_dvd.mp hu) ⟨0, by ring⟩

/-- **The uniform oriented residual is false too.**  `SqNuOrientedClear h` implies the unitizer,
so it fails at every `h ≥ 1`, at the same witness. -/
theorem not_sqNuOrientedClear (hh : 0 < h) : ¬ SqNuOrientedClear h := fun H =>
  not_sqPivotUnitizer hh (sqPivotUnitizer_of_orientedClear H)

/-- …and so does the un-oriented one, since the clearing automorphism of `SqNuJointClear`
carries the pivot row to `ν_sq(w) = 1` — but here without any χ-clause the invariance is not
available, so this is recorded only in the oriented form above. -/
theorem not_sqNuOrientedClear' (hh : 0 < h) :
    ¬ ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      SqJointSurjective h nu' → IsUnit (toAdd (nu' (sqPivot h))) := fun H =>
  not_sqPivotUnitizer hh (sqPivotUnitizer_iff.mpr H)

end Witness

end SqCore

end Dyadic

end GQ2
