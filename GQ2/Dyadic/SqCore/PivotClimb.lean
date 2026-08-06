/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.PivotSeedTransport
import GQ2.Dyadic.Instances.SqModelPresentingFrameCupAdapted

/-!
# W41 — the `h ≥ 1` climb: the pivot unitizer is **false**, with witness

`SqCore/PivotUnitizer.lean` reduced the oriented clearing residual at every handle count to three
inputs — the banked handle stratum `SqHandleMixFixesCore h c₀`, the pivot core family, and the
**one-bit unitizer** `SqPivotUnitizer h` ("every jointly-surjective marking can be moved, by a
χ-preserving automorphism, to one whose pivot row is a unit").  At `h = 0` the unitizer is a
theorem because joint surjectivity there *is* the unit pivot row.  This file settles the `h ≥ 1`
case, and the answer is a refutation.

## Headline

```text
theorem not_sqPivotUnitizer  : 0 < h → ¬ SqPivotUnitizer h
theorem not_sqNuOrientedClear : 0 < h → ¬ SqNuOrientedClear h
theorem not_sqHandleToCoreMove_handleU (j : Fin h) : ¬ SqHandleToCoreMove h (sqHandleIdxU j)
```

all at std-3, with an explicit witness.  So the residual's `h ≥ 1` supply list as it stands is
**unsatisfiable**: `gammaR_lSq_equiv_galK_oddDegree_of_subgroups`'s `hunit` slot cannot be
filled, and the theorem is vacuous above degree one (§10 pins this).

## The mechanism: the pivot row's parity is a cup-form invariant

The refutation is not a word-level computation.  It is one line of linear algebra over `𝔽₂`,
made available by three things already in the tree:

1. **The cup form is an invariant of the *whole* automorphism group** (§2,
   `sqGram_comp_autHom`), with **no orientation clause**.  Proof: the improved word's obstruction
   functional `H²(D_sq h, 𝔽₂) →+ 𝔽₂` is injective at *any* presenting marking
   (`WordCoh.obsH2_injective` at the transported presentation `presentedBy_aut`), and two
   injective additive maps to `𝔽₂` are equal (`addMonoidHom_zmodTwo_eq_of_injective`).  So the
   functional at `Ψ ∘ sqGen h` *is* the functional at `sqGen h`, and
   `obsH2_sqNatWord_characterCup` reads both sides as the relator's quadratic initial Gram.

2. **The χ-exponent row `λ` is `Aut_χ`-invariant modulo `2`** (§3), from `χ_sq² = X^{2λ}` and
   `X² ≠ 1` — the same parity engine `JointClearing` §3 already runs.

3. **The Gram identity that names the pivot** (§3, `sqGram_nuLam`):

   ```text
   λ̄ ⌣ c = c(w)     for every mod-two character c,     w = σ·x₀^{−c₀}.
   ```

   In the relator's constructor table `Gram κ = κ₂₂ + (κ₀₁ + κ₁₀) + Σⱼ(κ_{UⱼVⱼ} + κ_{VⱼUⱼ})`
   this is `0·c₂ + (1·c₁ + 1·c₀) + 0 = c₀ + c₁ = c(w)`: the reduced row `λ̄ = (1,1,0,…,0)` is
   cup-dual to `w̄ = σ̄ + x̄₀`.

Combining: for χ-preserving `Ψ`, `c(Ψ w) = λ̄ ⌣ (c∘Ψ) = (λ̄∘Ψ) ⌣ (c∘Ψ) = λ̄ ⌣ c = c(w)`.  So
**`Ψ` fixes `w` in the Frattini quotient**, and every marking's pivot row keeps its parity
(§4, `isUnit_toAdd_nu_aut_sqPivot_iff`).

The same machinery hands back a second fixed direction for free: `c ⌣ c = c(x₁)` in the
constructor table, so the **torsion coordinate is fixed by the whole automorphism group**
(`modTwoChar_aut_dsqX1`, no orientation clause) — the mod-two shadow of the forced row
`ν(x₁) = 2ν(x₀)`.

## The witness

`nuHandleU h 0 0 j` (§5): rows `(0, 0, 0, …, u_j ↦ 1, …, 0)`.  Its pivot row is `0` — even —
while its `u_j`-row is a unit, which is precisely the second disjunct that
`sqJointSurjective_isUnit_pivot_or_handle` allows at `h ≥ 1` and forbids at `h = 0`.  It is
jointly surjective because `χ_sq` is onto `ℤ₂ˣ` (§7, `chiSq_surjective`, the `χ_R` Burnside
argument re-run at `χ_sq`) and `χ_sq(u_j) = 1`.

## What this costs, and what it does not

* **`SqPivotUnitizer` is dead, and so is every route to it.**  The handle-to-core transfers
  `SqHandleToCoreMove h i` — the only known producer (`sqPivotUnitizer_of_handleToCore`) — are
  refuted at every handle letter, by the same invariant: they shift the pivot row by the
  transferred letter's row.
* **`SqHandleMixFixesCore h c₀` is untouched.**  Its clearing automorphism fixes both core rows,
  hence fixes the pivot row exactly, which is consistent with the invariance; and the mod-`2`
  shape the Eichler family needs (`u_j ↦ u_j + k·w̄` with the compensating `k·v̄_j` on *both*
  core slots, invisible once the `v_j`-row vanishes) is an isometry fixing `w̄`.  The cup form
  therefore raises no obstruction there.  It remains open.
* **The corrected residual** (§8) is `SqNuOrientedClearAtUnitPivot h`: the same statement with
  `IsUnit ν'(w)` as a hypothesis.  It follows from the handle stratum and the pivot family alone
  (`sqNuOrientedClearAtUnitPivot_of_families`) — the supply list *loses* an entry.  And
  `SqNuOrientedClear h ↔ SqNuOrientedClearAtUnitPivot h ∧ SqPivotUnitizer h` is exact, so the
  refutation is confined to the second factor.
* **The odd-degree bridge needs an arithmetic input at `h ≥ 1`** (§9).  Any two oriented
  equivalences `D_sq h ≅ G` differ by a χ-preserving automorphism, so the parity of the
  transported pivot row `ν_ur(f w)` is an **invariant of the target**, not a choice
  (`isUnit_toAdd_transported_sqPivot_iff`).  `GammaLOddDegreeBridge` currently feeds
  `SqNuOrientedClear h` an arbitrary `orientedEquiv_of_oddDegree`; at `h ≥ 1` it must instead
  supply P3's `SqMarkedForwardSupply` (whose two `ν`-rows give `ν(f w) = 1` on the nose,
  `nuUrKTwo_sqMixPivotElem_eq_one`).  P3 already recorded that the row is *selected*; this file
  upgrades that to: the model side **cannot** repair it.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`.  Every declaration prints **std-3** (`propext`,
`Classical.choice`, `Quot.sound`) — in particular the two `Instances` imports contribute nothing:
`dsqObs_injective`, `card_H2_DSq`, `obsH2_sqNatWord_characterCup` and
`addMonoidHom_zmodTwo_eq_of_injective` are all axiom-free.  Census unchanged at **11**.
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

/-- In `Multiplicative (ZMod 2)` a `ℤ₂`-power at an **even** exponent is trivial. -/
theorem zpowZtwo_multZMod2_of_even (y : Multiplicative (ZMod 2)) {t : ℤ_[2]}
    (ht : (2 : ℤ_[2]) ∣ t) : zpowZtwo isProP_multZMod2 y t = 1 := by
  obtain ⟨s, rfl⟩ := ht
  rw [show (2 : ℤ_[2]) * s = ((2 : ℕ) : ℤ_[2]) * s by push_cast; ring, ← zpowZtwo_zpowZtwo,
    zpowZtwo_natCast, MarkedCore.sq_eq_one_multZMod2', zpowZtwo_one_base]

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

/-- The cup square of a mod-two character is its `x₁`-coordinate: in the constructor table the
two off-diagonal blocks each appear twice, so they die in characteristic two, and `z² = z` on
`𝔽₂`. -/
theorem sqGram_self (c : ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2))) :
    sqGram h c c = toAdd (c (sqGen h 2)) := by
  have hsq : ∀ z : ZMod 2, z * z = z := by decide
  have hsum : ∑ j : Fin h,
      (toAdd (c (sqGen h (sqHandleIdxU j))) * toAdd (c (sqGen h (sqHandleIdxV j))) +
        toAdd (c (sqGen h (sqHandleIdxV j))) * toAdd (c (sqGen h (sqHandleIdxU j)))) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      generalize toAdd (c (sqGen h (sqHandleIdxU j))) = p
      generalize toAdd (c (sqGen h (sqHandleIdxV j))) = q
      revert p q
      decide
  show GQ2.ContCoh.sqRelatorQuadraticInitialGram h
      (fun i j => toAdd (c (sqGen h i)) * toAdd (c (sqGen h j))) = _
  rw [GQ2.ContCoh.sqRelatorQuadraticInitialGram_eq, hsum, hsq, add_zero]
  generalize toAdd (c (sqGen h 0)) = p
  generalize toAdd (c (sqGen h 1)) = q
  generalize toAdd (c (sqGen h 2)) = r
  revert p q r
  decide

/-- **The torsion direction is fixed by the *whole* automorphism group** — no orientation clause.
`x₁` spans the radical of the polar form of the relator's quadratic initial form, and its
coordinate is read off by the cup square `c ⌣ c`, which §2 shows is `Aut`-invariant.  This is the
mod-two shadow of the forced row `ν(x₁) = 2ν(x₀)`. -/
theorem modTwoChar_aut_dsqX1 (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type))
    (c : ContinuousMonoidHom (DSq h : Type) (Multiplicative (ZMod 2))) :
    c (Ψ (dsqX1 h)) = c (dsqX1 h) := by
  have hinv := sqGram_comp_autHom Ψ c c
  rw [sqGram_self, sqGram_self] at hinv
  exact Multiplicative.toAdd.injective hinv

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

/-- **The numerical form**: at `h ≥ 1` joint surjectivity does **not** force a unit pivot row —
the missing disjunct of `sqJointSurjective_isUnit_pivot_or_handle` genuinely occurs.  (At
`h = 0` the same statement is the theorem `sqJointSurjective_isUnit_pivot_zero`.) -/
theorem not_forall_isUnit_toAdd_sqPivot (hh : 0 < h) :
    ¬ ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      SqJointSurjective h nu' → IsUnit (toAdd (nu' (sqPivot h))) := fun H =>
  not_sqPivotUnitizer hh (sqPivotUnitizer_iff.mpr H)

end Witness

/-! ## §8 The corrected residual, and what it costs -/

section Corrected

variable {h : ℕ}

/-- **The corrected oriented clearing residual**: the same statement as `SqNuOrientedClear`, with
the marking's pivot row required to be a **unit**.  §7 shows the extra hypothesis cannot be
dropped at `h ≥ 1`, and §4 shows it cannot be arranged by an automorphism — so this is the
strongest model-side statement of this shape that is not already refuted. -/
def SqNuOrientedClearAtUnitPivot (h : ℕ) : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    SqJointSurjective h nu' → IsUnit (toAdd (nu' (sqPivot h))) →
      ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
        (∀ x, chiSq h (Ψ x) = chiSq h x) ∧ ∀ x, nu' (Ψ x) = nuSq h x

/-- **The exact split of the old residual**: `SqNuOrientedClear` is the corrected residual plus
the unitizer, and the second factor is exactly what §7 refutes. -/
theorem sqNuOrientedClear_iff :
    SqNuOrientedClear h ↔ SqNuOrientedClearAtUnitPivot h ∧ SqPivotUnitizer h := by
  constructor
  · exact fun H => ⟨fun nu' hjs _ => H nu' hjs, sqPivotUnitizer_of_orientedClear H⟩
  · exact fun ⟨H, hu⟩ nu' hjs => H nu' hjs (sqPivotUnitizer_iff.mp hu nu' hjs)

/-- **The corrected residual over the banked handle stratum and the pivot family.**  Same three
steps as `sqNuOrientedClear_of_pivotMoves_of_unitizer`, with the (now refuted) unitizer replaced
by the hypothesis it was supposed to produce — so the `h ≥ 1` model-side supply list loses one
entry and gains no new one. -/
theorem sqNuOrientedClearAtUnitPivot_of_pivotMoves
    (hfix : SqHandleMixFixesCore h sqPivotExp)
    (hmv : ∀ m k : ℤ_[2], IsUnit (sqPivotDet m k) → SqPivotCoreMove h m k) :
    SqNuOrientedClearAtUnitPivot h := by
  intro nu' _ hpiv
  obtain ⟨Ψ₁, hchi₁, hU₁, hV₁, hs₁, hx₁⟩ := hfix nu' hpiv
  set rho : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
    nu'.comp (autHom Ψ₁) with hrhodef
  have hrhopiv : IsUnit (toAdd (rho (sqPivot h))) := by
    have hval : toAdd (rho (sqPivot h)) = toAdd (nu' (sqPivot h)) := by
      show toAdd (nu' (Ψ₁ (sqPivot h))) = _
      rw [toAdd_aut_sqPivot, hs₁, hx₁, toAdd_nu_sqPivot]
    rw [hval]
    exact hpiv
  obtain ⟨Ψ₂, hchi₂, hs₂, hx₂, hU₂, hV₂⟩ := sqCoreRows_of_pivotMove hmv rho hrhopiv
  refine ⟨Ψ₂.trans Ψ₁, fun x => ?_, fun x => ?_⟩
  · show chiSq h (Ψ₁ (Ψ₂ x)) = chiSq h x
    rw [hchi₁, hchi₂]
  · have hcore : ∀ y, (rho.comp (autHom Ψ₂)) y = nuSq h y := by
      refine nu_eq_nuSq_of_core _ hs₂ hx₂ (fun j => ?_) (fun j => ?_)
      · show rho (Ψ₂ (sqGen h (sqHandleIdxU j))) = 1
        rw [hU₂ j]
        exact hU₁ j
      · show rho (Ψ₂ (sqGen h (sqHandleIdxV j))) = 1
        rw [hV₂ j]
        exact hV₁ j
    exact hcore x

/-- The corrected residual over the two one-parameter pivot subgroups and the handle stratum. -/
theorem sqNuOrientedClearAtUnitPivot_of_families
    (hfix : SqHandleMixFixesCore h sqPivotExp)
    (htr : ∀ c : ℤ_[2], SqPivotTranslation h c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqPivotScaling h a) : SqNuOrientedClearAtUnitPivot h :=
  sqNuOrientedClearAtUnitPivot_of_pivotMoves hfix
    (fun m k hd => sqPivotCoreMove_of_translation_scaling m k (htr k) (hsc _ hd))

/-- **The unit-pivot hypothesis is sharp**: adding it is not a convenience, since without it the
statement is refuted (§7).  Recorded as an implication so the two forms sit side by side. -/
theorem not_sqNuOrientedClearAtUnitPivot_without_hypothesis (hh : 0 < h) :
    ¬ ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
        SqJointSurjective h nu' →
          ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
            (∀ x, chiSq h (Ψ x) = chiSq h x) ∧ ∀ x, nu' (Ψ x) = nuSq h x :=
  not_sqNuOrientedClear hh

/-- At `h = 0` the two forms coincide, since the unitizer is a theorem there. -/
theorem sqNuOrientedClear_zero_of_atUnitPivot (H : SqNuOrientedClearAtUnitPivot 0) :
    SqNuOrientedClear 0 :=
  sqNuOrientedClear_iff.mpr ⟨H, sqPivotUnitizer_zero⟩

end Corrected

/-! ## §9 The `K`-facing form: the parity of the transported pivot row is not a choice -/

section Transported

variable {h : ℕ}

/-- **Any two oriented equivalences give the same pivot-row parity.**  Two topological
isomorphisms `f₁, f₂ : D_sq h ≅ G` inducing the same orientation differ by the χ-preserving
automorphism `f₁⁻¹ ∘ f₂`, so §4 applies: the parity of `ν_G(fᵢ w)` is the same for both.

Consequence for the odd-degree bridge: whether the transported pivot row `ν_ur(f w)` is a unit
is an **invariant of `(G, χ_G, ν_G)`**, not something the choice of `f` can arrange, and — by §7
— not something a further automorphism of the model can repair.  So the `h ≥ 1` bridge genuinely
needs the *arithmetic* input (P3's `SqMarkedForwardSupply`, whose two `ν`-rows force
`ν(f w) = 1`); the model-side supply list cannot produce it. -/
theorem two_dvd_toAdd_transported_sqPivot_sub {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (chiG : ContinuousMonoidHom G ℤ_[2]ˣ)
    (nuG : ContinuousMonoidHom G (Multiplicative ℤ_[2]))
    (f₁ f₂ : ContinuousMulEquiv (DSq h : Type) G)
    (hc₁ : ∀ x, chiG (f₁ x) = chiSq h x) (hc₂ : ∀ x, chiG (f₂ x) = chiSq h x) :
    (2 : ℤ_[2]) ∣ toAdd (nuG (f₂ (sqPivot h))) - toAdd (nuG (f₁ (sqPivot h))) := by
  set Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type) := f₂.trans f₁.symm with hΨ
  have happ : ∀ x, f₁ (Ψ x) = f₂ x := fun x => f₁.apply_symm_apply (f₂ x)
  have hchi : ∀ x, chiSq h (Ψ x) = chiSq h x := by
    intro x
    rw [← hc₁ (Ψ x), happ, hc₂]
  have hpull := two_dvd_toAdd_nu_aut_sqPivot_sub Ψ hchi
    (nuG.comp ⟨f₁.toMonoidHom, f₁.continuous_toFun⟩)
  rw [show (nuG.comp ⟨f₁.toMonoidHom, f₁.continuous_toFun⟩) (Ψ (sqPivot h))
      = nuG (f₁ (Ψ (sqPivot h))) from rfl, happ,
    show (nuG.comp ⟨f₁.toMonoidHom, f₁.continuous_toFun⟩) (sqPivot h)
      = nuG (f₁ (sqPivot h)) from rfl] at hpull
  exact hpull

/-- The unit-locus form of the same statement. -/
theorem isUnit_toAdd_transported_sqPivot_iff {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (chiG : ContinuousMonoidHom G ℤ_[2]ˣ)
    (nuG : ContinuousMonoidHom G (Multiplicative ℤ_[2]))
    (f₁ f₂ : ContinuousMulEquiv (DSq h : Type) G)
    (hc₁ : ∀ x, chiG (f₁ x) = chiSq h x) (hc₂ : ∀ x, chiG (f₂ x) = chiSq h x) :
    IsUnit (toAdd (nuG (f₂ (sqPivot h)))) ↔ IsUnit (toAdd (nuG (f₁ (sqPivot h)))) := by
  obtain ⟨s, hs⟩ := two_dvd_toAdd_transported_sqPivot_sub chiG nuG f₁ f₂ hc₁ hc₂
  constructor
  · exact fun hu => isUnit_iff_not_two_dvd.mpr fun ⟨p, hp⟩ =>
      (isUnit_iff_not_two_dvd.mp hu) ⟨s + p, by linear_combination hs + hp⟩
  · exact fun hu => isUnit_iff_not_two_dvd.mpr fun ⟨p, hp⟩ =>
      (isUnit_iff_not_two_dvd.mp hu) ⟨p - s, by linear_combination hp - hs⟩

end Transported

/-! ## §10 Regression: the determinant condition, reproved from the invariance

`PivotCoreMoves` §4 proves `isUnit_sqPivotDet_of_sqPivotCoreMove` by the `χ_sq² = X^{2λ}` parity
engine run at the standard marking.  The cup-form invariance gives the same theorem by a
different route — the pivot core move scales the pivot row by `D = 1 + m − k·c₀`, and §4 says
that scaling must be odd.  Two independent proofs of one statement is the cross-check that the
new machinery agrees with the committed one. -/

section Regression

variable {h : ℕ}

/-- **`isUnit_sqPivotDet_of_sqPivotCoreMove`, reproved from §4.** -/
theorem isUnit_sqPivotDet_of_sqPivotCoreMove_via_cup {m k : ℤ_[2]}
    (H : SqPivotCoreMove h m k) : IsUnit (sqPivotDet m k) := by
  obtain ⟨Ψ, hchi, hs, hx, _, _⟩ := H (nuSq h)
  have hpiv : toAdd (nuSq h (sqPivot h)) = 1 := by rw [nuSq_sqPivot, toAdd_ofAdd]
  have hval : toAdd (nuSq h (Ψ (sqPivot h))) = sqPivotDet m k := by
    rw [toAdd_aut_sqPivot, hs, hx, hpiv, nuSq_sigma, nuSq_x0, toAdd_ofAdd, toAdd_ofAdd,
      sqPivotDet]
    ring
  obtain ⟨s, hs2⟩ := two_dvd_toAdd_nu_aut_sqPivot_sub Ψ hchi (nuSq h)
  rw [hval, hpiv] at hs2
  exact isUnit_iff_not_two_dvd.mpr fun ⟨p, hp⟩ =>
    (isUnit_iff_not_two_dvd.mp isUnit_one) ⟨p - s, by linear_combination hp - hs2⟩

/-- The two proofs land on the same statement. -/
example {m k : ℤ_[2]} (H : SqPivotCoreMove h m k) :
    IsUnit (sqPivotDet m k) ∧ IsUnit (sqPivotDet m k) :=
  ⟨isUnit_sqPivotDet_of_sqPivotCoreMove H, isUnit_sqPivotDet_of_sqPivotCoreMove_via_cup H⟩

end Regression

/-! ## §11 Stress pins -/

section StressTests

/-- The `h = 0` unitizer, reproved through §6's characterization: at `h = 0` the right-hand side
of `sqPivotUnitizer_iff` is `sqJointSurjective_isUnit_pivot_zero`. -/
example : SqPivotUnitizer 0 :=
  sqPivotUnitizer_iff.mpr fun _ hjs => sqJointSurjective_isUnit_pivot_zero hjs

/-- …and it agrees with the committed `h = 0` theorem. -/
example : SqPivotUnitizer 0 := sqPivotUnitizer_zero

/-- **The `h ≥ 1` supply list of `gammaR_lSq_equiv_galK_oddDegree_of_subgroups` is
unsatisfiable.**  Whatever the other three binders are, the fourth cannot be filled — so that
theorem is *vacuous* at every positive handle count. -/
example (_hfix : SqHandleMixFixesCore 1 sqPivotExp) (_htr : ∀ c : ℤ_[2], SqPivotTranslation 1 c)
    (_hsc : ∀ a : ℤ_[2], IsUnit a → SqPivotScaling 1 a) (hunit : SqPivotUnitizer 1) : False :=
  not_sqPivotUnitizer (by omega) hunit

/-- The one-handle witness marking has an even pivot row… -/
example : toAdd (nuHandleU 1 0 0 ⟨0, by omega⟩ (sqPivot 1)) = 0 := by
  rw [toAdd_nuHandleU_sqPivot]; ring

/-- …and a unit handle row… -/
example :
    IsUnit (toAdd (nuHandleU 1 0 0 ⟨0, by omega⟩ (sqGen 1 (sqHandleIdxU ⟨0, by omega⟩)))) := by
  rw [nuHandleU_self, toAdd_ofAdd]
  exact isUnit_one

/-- …and is jointly surjective with `χ_sq`. -/
example : SqJointSurjective 1 (nuHandleU 1 0 0 ⟨0, by omega⟩) :=
  sqJointSurjective_nuHandleU 0 0 ⟨0, by omega⟩

/-- At one handle the transfers do not exist. -/
example : ¬ SqHandleToCoreMove 1 (sqHandleIdxU ⟨0, by omega⟩) :=
  not_sqHandleToCoreMove_handleU ⟨0, by omega⟩

/-- The corrected residual at one handle, over the two one-parameter subgroups and the handle
stratum — the shape that survives. -/
example (hfix : SqHandleMixFixesCore 1 sqPivotExp) (htr : ∀ c : ℤ_[2], SqPivotTranslation 1 c)
    (hsc : ∀ a : ℤ_[2], IsUnit a → SqPivotScaling 1 a) : SqNuOrientedClearAtUnitPivot 1 :=
  sqNuOrientedClearAtUnitPivot_of_families hfix htr hsc

/-- The split is exact. -/
example (h : ℕ) : SqNuOrientedClear h ↔ SqNuOrientedClearAtUnitPivot h ∧ SqPivotUnitizer h :=
  sqNuOrientedClear_iff

/-- The `h = 0` milestone is untouched: there the corrected residual gives the old one back. -/
example (H : SqNuOrientedClearAtUnitPivot 0) : SqNuOrientedClear 0 :=
  sqNuOrientedClear_zero_of_atUnitPivot H

end StressTests

/-! ## §12 Axiom pins -/

section AxiomPins

#print axioms sqModTwo
#print axioms sqRedMark_eq_iff
#print axioms sqGram_comp_autHom
#print axioms two_dvd_toAdd_nuLam_sub_of_chiPreserving
#print axioms sqGram_nuLam
#print axioms modTwoChar_aut_sqPivot
#print axioms isUnit_toAdd_nu_aut_sqPivot_iff
#print axioms sqGram_self
#print axioms modTwoChar_aut_dsqX1
#print axioms nuHandleU
#print axioms two_dvd_toAdd_of_sqHandleToCoreMove
#print axioms not_sqHandleToCoreMove_handleU
#print axioms sqPivotUnitizer_iff
#print axioms chiSq_surjective
#print axioms sqJointSurjective_nuHandleU
#print axioms not_sqPivotUnitizer
#print axioms not_sqNuOrientedClear
#print axioms not_forall_isUnit_toAdd_sqPivot
#print axioms SqNuOrientedClearAtUnitPivot
#print axioms sqNuOrientedClear_iff
#print axioms sqNuOrientedClearAtUnitPivot_of_families
#print axioms two_dvd_toAdd_transported_sqPivot_sub
#print axioms isUnit_toAdd_transported_sqPivot_iff
#print axioms isUnit_sqPivotDet_of_sqPivotCoreMove_via_cup

end AxiomPins

end SqCore

end Dyadic

end GQ2
