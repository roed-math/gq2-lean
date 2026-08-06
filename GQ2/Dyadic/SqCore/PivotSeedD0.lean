/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.PivotSeedTransport
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldCoreRankOne
import GQ2.Dyadic.Instances.GammaLOddDegreeBridgePivot

/-!
# The two pivot subgroups, transported from `D₀`

`SqCore/PivotSeedTransport.lean` reduced the `h = 0` model-side residual to one package of
linear data, `SqPivotAffine`.  This file **builds** that package, and therefore proves the two
one-parameter automorphism subgroups of `D_sq(0) = D_R` outright.

## The route

Three already-banked facts do all the work.

* **`bLab`** (`GQ2/Roe/Labute/Assembly.lean`, axiom-free) gives an isomorphism `f : D_R ≅ D₀`
  onto the Labute normal-form group `D₀ = ⟨A, S, Y | A²S⁴[S,Y]⟩`.  Composed with the marked
  identification `sqEquivDRMarked : D_sq(0) ≅ D_R` this is a single equivalence
  `g : D_sq(0) ≅ D₀`.
* **`prop_3_8_lift`** (`GQ2/AnabelianBridge/Construction.lean`, axiom **B8**) gives, for every
  unit `u` and every `b : ℤ₂`, an automorphism `Ψ_{u,b}` of `D₀` acting on the abelianized frame
  by `S̄ ↦ u·S̄`, `Ȳ ↦ b·S̄ + Ȳ` — the affine group of the `S̄`-line.  Transporting it along `g`
  supplies `SqPivotAffine.psi`.
* **`chiD0G_comp_rankThreeLabuteEquiv`** (axiom **B3c**) says the `D₀`-orientation pulls back
  along *any* `D_R ≅ D₀` to `χ_R` — the uniqueness half of the Labute orientation.  Applied to
  `g` and to `g ∘ Ψ_{u,b}` it gives the χ-clause for free, and applied to the χ-trivial pivot it
  gives the one geometric hypothesis `qS = c₀·qX`: the `Ȳ`-coordinate of `g(w)` vanishes, since
  `χ_{D₀}(S) = 1` and `χ_{D₀}(Y) = (−3)⁻¹` generates.

The reason the `S̄`-line is the right one is exactly this last point: `Ψ_{u,b}` scales it by an
arbitrary unit while preserving `χ_{D₀}`, so it *is* the χ-trivial line, and the χ-trivial line
of `D_sq(0)` is `ℤ₂·w̄`.

## Contents

* **§1** `sRowD0`, `yRowD0`: the two `ℤ₂`-coordinate characters of `D₀`, with their six
  generator values; `forcedRow_d0A` (`ν(A) = −2ν(S)` for every marking, from the relator) and
  `toAdd_mark_d0` (every marking of `D₀` is `ν(S)`-times-the-`S̄`-row plus `ν(Y)`-times-the-
  `Ȳ`-row).
* **§2** the `B`-frame dictionary `sRowD0_eq_mid`, `yRowD0_eq_thd`, and `prop_3_8_rows`: the
  affine family in the two rows rather than in the frame.
* **§3** `chiD0G_sq_eq_yRow` (`χ_{D₀}² = ((−3)⁻¹)^{2·Ȳ-row}`) and its consequence
  `yRowD0_eq_zero_of_chiD0G_eq_one`.
* **§4** `sqPivotAffineD0`, the package, and the three headline theorems
  `sqPivotTranslation_zero`, `sqPivotScaling_zero`, `sqNuOrientedClear_zero`.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`.  §1–§2 up to `bE_d0A`/`sRowD0_eq_mid` and
`nonempty_equiv_DR_D0` print **std-3**; `prop_3_8_rows` adds `peripheralCyclotomicAction` (B8);
`chiD0G_sq_eq_yRow` adds `dyadicOrientation` (B3c).  The three headline theorems therefore print

```text
propext, Classical.choice, Quot.sound, dyadicOrientation, peripheralCyclotomicAction
```

and the milestone of §6 prints those together with the seven census members the odd-degree row
already carried (`hilbertSymbol_normCriterion_finiteDyadic`, `localReciprocity`,
`markedRecipAt`, `relativeStiefelWhitney_dyadic`, `tateDualityAt`,
`Foundations.absGalQ2_isTopologicallyFinitelyGenerated`,
`Foundations.absGalQ2_localEulerCharacteristic`).  Both additions are **pre-existing census
members**, so the census is unchanged at **11**; the two new members are the exact price of
routing the automorphisms through `D₀`.
-/

open Multiplicative

namespace GQ2

open Roe SectionThree

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The two coordinate characters of `D₀` -/

section D0Rows

/-- The `S̄`-row of `D₀`, as a character of `D₀` itself: `A ↦ −2`, `S ↦ 1`, `Y ↦ 0`. -/
noncomputable def sRowD0 : ContinuousMonoidHom (D0 : Type) (Multiplicative ℤ_[2]) :=
  SectionThree.sHom.comp ⟨abMk, continuous_abMk⟩

/-- The `Ȳ`-row of `D₀`, as a character of `D₀` itself: `A ↦ 0`, `S ↦ 0`, `Y ↦ 1`. -/
noncomputable def yRowD0 : ContinuousMonoidHom (D0 : Type) (Multiplicative ℤ_[2]) :=
  SectionThree.yHom.comp ⟨abMk, continuous_abMk⟩

theorem sRowD0_apply (z : (D0 : Type)) : sRowD0 z = SectionThree.sHom (abMk z) := rfl

theorem yRowD0_apply (z : (D0 : Type)) : yRowD0 z = SectionThree.yHom (abMk z) := rfl

/-- The relator dies on the `S̄`-coordinate marking; the proof `sHom` uses. -/
private theorem sRowRel : (![ofAdd (-2 : ℤ_[2]), ofAdd (1 : ℤ_[2]), ofAdd (0 : ℤ_[2])] 0) ^ 2 *
    (![ofAdd (-2 : ℤ_[2]), ofAdd (1 : ℤ_[2]), ofAdd (0 : ℤ_[2])] 1) ^ 4 *
    commP (![ofAdd (-2 : ℤ_[2]), ofAdd (1 : ℤ_[2]), ofAdd (0 : ℤ_[2])] 1)
      (![ofAdd (-2 : ℤ_[2]), ofAdd (1 : ℤ_[2]), ofAdd (0 : ℤ_[2])] 2) = 1 := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, commP, ← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
  rw [← ofAdd_zero]; congr 1; simp only [nsmul_eq_mul]; push_cast; ring

/-- The same for the `Ȳ`-coordinate marking. -/
private theorem yRowRel : (![ofAdd (0 : ℤ_[2]), ofAdd (0 : ℤ_[2]), ofAdd (1 : ℤ_[2])] 0) ^ 2 *
    (![ofAdd (0 : ℤ_[2]), ofAdd (0 : ℤ_[2]), ofAdd (1 : ℤ_[2])] 1) ^ 4 *
    commP (![ofAdd (0 : ℤ_[2]), ofAdd (0 : ℤ_[2]), ofAdd (1 : ℤ_[2])] 1)
      (![ofAdd (0 : ℤ_[2]), ofAdd (0 : ℤ_[2]), ofAdd (1 : ℤ_[2])] 2) = 1 := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, commP, ← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
  rw [← ofAdd_zero]; congr 1; simp only [nsmul_eq_mul]; push_cast; ring

@[simp] theorem sRowD0_A : sRowD0 d0A = ofAdd (-2 : ℤ_[2]) :=
  d0LiftHom_A PropOneOne.isProP_two_multPadicInt _ sRowRel

@[simp] theorem sRowD0_S : sRowD0 d0S = ofAdd (1 : ℤ_[2]) :=
  d0LiftHom_S PropOneOne.isProP_two_multPadicInt _ sRowRel

@[simp] theorem sRowD0_Y : sRowD0 d0Y = ofAdd (0 : ℤ_[2]) :=
  d0LiftHom_Y PropOneOne.isProP_two_multPadicInt _ sRowRel

@[simp] theorem yRowD0_A : yRowD0 d0A = ofAdd (0 : ℤ_[2]) :=
  d0LiftHom_A PropOneOne.isProP_two_multPadicInt _ yRowRel

@[simp] theorem yRowD0_S : yRowD0 d0S = ofAdd (0 : ℤ_[2]) :=
  d0LiftHom_S PropOneOne.isProP_two_multPadicInt _ yRowRel

@[simp] theorem yRowD0_Y : yRowD0 d0Y = ofAdd (1 : ℤ_[2]) :=
  d0LiftHom_Y PropOneOne.isProP_two_multPadicInt _ yRowRel

/-- **The forced `A`-row**: the relator `A²S⁴[S,Y]` forces `ν(A) = −2·ν(S)` for every
`ℤ₂`-marking of `D₀`. -/
theorem forcedRow_d0A (mu : ContinuousMonoidHom (D0 : Type) (Multiplicative ℤ_[2])) :
    toAdd (mu d0A) = -2 * toAdd (mu d0S) := by
  have hrel := congrArg mu d0_relation
  rw [map_mul, map_mul, map_pow, map_pow, map_one] at hrel
  have hcomm : mu (commP d0S d0Y) = 1 := by
    rw [commP, map_mul, map_mul, map_mul, map_inv, map_inv]
    refine Multiplicative.toAdd.injective ?_
    rw [toAdd_mul, toAdd_mul, toAdd_mul, toAdd_inv, toAdd_inv, toAdd_one]
    ring
  rw [hcomm, mul_one] at hrel
  have h2 : (2 : ℤ_[2]) * (toAdd (mu d0A) + 2 * toAdd (mu d0S)) = 0 := by
    have := congrArg toAdd hrel
    rw [toAdd_mul, toAdd_pow, toAdd_pow, toAdd_one] at this
    simp only [nsmul_eq_mul, Nat.cast_ofNat] at this
    linear_combination this
  have := mul_eq_zero.mp h2
  rcases this with h | h
  · exact absurd h (by norm_num)
  · linear_combination h

/-- The `(A, C)`-combination of the two rows, as a character of `D₀`. -/
noncomputable def comboRowD0 (A C : ℤ_[2]) :
    ContinuousMonoidHom (D0 : Type) (Multiplicative ℤ_[2]) where
  toFun z := ofAdd (toAdd (sRowD0 z) * A + toAdd (yRowD0 z) * C)
  map_one' := by simp
  map_mul' z w := by
    simp only [map_mul, toAdd_mul, ← ofAdd_add]
    congr 1
    ring
  continuous_toFun := by
    refine continuous_ofAdd.comp (Continuous.add ?_ ?_)
    · exact (continuous_toAdd.comp sRowD0.continuous_toFun).mul continuous_const
    · exact (continuous_toAdd.comp yRowD0.continuous_toFun).mul continuous_const

@[simp] theorem comboRowD0_apply (A C : ℤ_[2]) (z : (D0 : Type)) :
    comboRowD0 A C z = ofAdd (toAdd (sRowD0 z) * A + toAdd (yRowD0 z) * C) := rfl

/-- **Every marking of `D₀` is a combination of the two rows.** -/
theorem toAdd_mark_d0 (mu : ContinuousMonoidHom (D0 : Type) (Multiplicative ℤ_[2]))
    (z : (D0 : Type)) :
    toAdd (mu z)
      = toAdd (sRowD0 z) * toAdd (mu d0S) + toAdd (yRowD0 z) * toAdd (mu d0Y) := by
  have hext : mu = comboRowD0 (toAdd (mu d0S)) (toAdd (mu d0Y)) := by
    refine d0Hom_ext ?_ ?_ ?_ <;> refine Multiplicative.toAdd.injective ?_
    · rw [comboRowD0_apply, toAdd_ofAdd, sRowD0_A, yRowD0_A, toAdd_ofAdd, toAdd_ofAdd,
        forcedRow_d0A]
      ring
    · rw [comboRowD0_apply, toAdd_ofAdd, sRowD0_S, yRowD0_S, toAdd_ofAdd, toAdd_ofAdd]
      ring
    · rw [comboRowD0_apply, toAdd_ofAdd, sRowD0_Y, yRowD0_Y, toAdd_ofAdd, toAdd_ofAdd]
      ring
  have hz : mu z = comboRowD0 (toAdd (mu d0S)) (toAdd (mu d0Y)) z := DFunLike.congr_fun hext z
  rw [hz, comboRowD0_apply, toAdd_ofAdd]

end D0Rows

/-! ## §2 The `B`-frame dictionary, and the affine family in the two rows -/

section Frame

/-- The middle coordinate of the frame group, as a character. -/
noncomputable def midRow : ContinuousMonoidHom (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2]))
    (Multiplicative ℤ_[2]) where
  toFun w := ofAdd (toAdd w).2.1
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    continuous_ofAdd.comp (continuous_fst.comp (continuous_snd.comp continuous_toAdd))

/-- The last coordinate of the frame group, as a character. -/
noncomputable def thdRow : ContinuousMonoidHom (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2]))
    (Multiplicative ℤ_[2]) where
  toFun w := ofAdd (toAdd w).2.2
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    continuous_ofAdd.comp (continuous_snd.comp (continuous_snd.comp continuous_toAdd))

@[simp] theorem midRow_ofAdd (a : ZMod 2) (p q : ℤ_[2]) :
    midRow (ofAdd (a, p, q)) = ofAdd p := rfl

@[simp] theorem thdRow_ofAdd (a : ZMod 2) (p q : ℤ_[2]) :
    thdRow (ofAdd (a, p, q)) = ofAdd q := rfl

variable (B : SectionThree.BDecomposition)

/-- The `A`-row of the frame, re-derived from `map_t` and `map_S`. -/
theorem bE_d0A : B.e (abMk d0A)
    = ofAdd ((1 : ZMod 2), (-2 : ℤ_[2]), (0 : ℤ_[2])) := by
  have hsplit : abMk d0A = abMk (d0A * d0S ^ 2) * ((abMk d0S) ^ 2)⁻¹ := by
    rw [map_mul, map_pow]
    group
  rw [hsplit, map_mul, map_inv, map_pow, B.map_t, B.map_S]
  refine Multiplicative.toAdd.injective ?_
  rw [toAdd_mul, toAdd_inv, toAdd_pow, toAdd_ofAdd, toAdd_ofAdd]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

/-- The `S̄`-row is the middle frame coordinate. -/
theorem sRowD0_eq_mid (z : (D0 : Type)) : sRowD0 z = midRow (B.e (abMk z)) := by
  have hext : sRowD0 = midRow.comp ⟨(B.e.toMulEquiv.toMonoidHom).comp abMk,
      B.e.continuous_toFun.comp continuous_abMk⟩ := by
    refine d0Hom_ext ?_ ?_ ?_
    · show sRowD0 d0A = midRow (B.e (abMk d0A))
      rw [sRowD0_A, bE_d0A, midRow_ofAdd]
    · show sRowD0 d0S = midRow (B.e (abMk d0S))
      rw [sRowD0_S, B.map_S, midRow_ofAdd]
    · show sRowD0 d0Y = midRow (B.e (abMk d0Y))
      rw [sRowD0_Y, B.map_Y, midRow_ofAdd]
  exact DFunLike.congr_fun hext z

/-- The `Ȳ`-row is the last frame coordinate. -/
theorem yRowD0_eq_thd (z : (D0 : Type)) : yRowD0 z = thdRow (B.e (abMk z)) := by
  have hext : yRowD0 = thdRow.comp ⟨(B.e.toMulEquiv.toMonoidHom).comp abMk,
      B.e.continuous_toFun.comp continuous_abMk⟩ := by
    refine d0Hom_ext ?_ ?_ ?_
    · show yRowD0 d0A = thdRow (B.e (abMk d0A))
      rw [yRowD0_A, bE_d0A, thdRow_ofAdd]
    · show yRowD0 d0S = thdRow (B.e (abMk d0S))
      rw [yRowD0_S, B.map_S, thdRow_ofAdd]
    · show yRowD0 d0Y = thdRow (B.e (abMk d0Y))
      rw [yRowD0_Y, B.map_Y, thdRow_ofAdd]
  exact DFunLike.congr_fun hext z

include B in
/-- **The affine family, read in the two rows.**  `prop_3_8_lift` with the frame eliminated:
the `S̄`-row is scaled by `u` and receives `b` times the `Ȳ`-row, and the `Ȳ`-row is fixed. -/
theorem prop_3_8_rows (u : ℤ_[2]ˣ) (b : ℤ_[2]) :
    ∃ Ψ : ContinuousMulEquiv (D0 : Type) (D0 : Type),
      (∀ z, toAdd (sRowD0 (Ψ z))
        = (u : ℤ_[2]) * toAdd (sRowD0 z) + b * toAdd (yRowD0 z)) ∧
      (∀ z, toAdd (yRowD0 (Ψ z)) = toAdd (yRowD0 z)) := by
  obtain ⟨Ψ, hA, hS, hY⟩ := SectionThree.prop_3_8_lift B u b
  have hs : sRowD0.comp ⟨Ψ.toMulEquiv.toMonoidHom, Ψ.continuous_toFun⟩
      = comboRowD0 (u : ℤ_[2]) b := by
    refine d0Hom_ext ?_ ?_ ?_
    · show sRowD0 (Ψ d0A) = comboRowD0 (u : ℤ_[2]) b d0A
      rw [sRowD0_eq_mid B, hA, midRow_ofAdd, comboRowD0_apply, sRowD0_A, yRowD0_A,
        toAdd_ofAdd, toAdd_ofAdd]
      congr 1
      ring
    · show sRowD0 (Ψ d0S) = comboRowD0 (u : ℤ_[2]) b d0S
      rw [sRowD0_eq_mid B, hS, midRow_ofAdd, comboRowD0_apply, sRowD0_S, yRowD0_S,
        toAdd_ofAdd, toAdd_ofAdd]
      congr 1
      ring
    · show sRowD0 (Ψ d0Y) = comboRowD0 (u : ℤ_[2]) b d0Y
      rw [sRowD0_eq_mid B, hY, midRow_ofAdd, comboRowD0_apply, sRowD0_Y, yRowD0_Y,
        toAdd_ofAdd, toAdd_ofAdd]
      congr 1
      ring
  have hy : yRowD0.comp ⟨Ψ.toMulEquiv.toMonoidHom, Ψ.continuous_toFun⟩ = yRowD0 := by
    refine d0Hom_ext ?_ ?_ ?_
    · show yRowD0 (Ψ d0A) = yRowD0 d0A
      rw [yRowD0_eq_thd B, hA, thdRow_ofAdd, yRowD0_A]
    · show yRowD0 (Ψ d0S) = yRowD0 d0S
      rw [yRowD0_eq_thd B, hS, thdRow_ofAdd, yRowD0_S]
    · show yRowD0 (Ψ d0Y) = yRowD0 d0Y
      rw [yRowD0_eq_thd B, hY, thdRow_ofAdd, yRowD0_Y]
  refine ⟨Ψ, fun z => ?_, fun z => ?_⟩
  · have hz : sRowD0 (Ψ z) = comboRowD0 (u : ℤ_[2]) b z := DFunLike.congr_fun hs z
    rw [hz, comboRowD0_apply, toAdd_ofAdd]
    ring
  · have hz : yRowD0 (Ψ z) = yRowD0 z := DFunLike.congr_fun hy z
    rw [hz]

end Frame

/-! ## §3 The orientation of `D₀` is the `Ȳ`-row -/

section Orientation

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- `−3` as a unit of `ℤ₂`, matching `unitNegThree`. -/
theorem unitNegThree_val_eq : (unitNegThree : ℤ_[2]) = -3 := by
  rw [unitNegThree, IsUnit.unit_spec]; push_cast; ring

/-- **The orientation of `D₀` is the `Ȳ`-row, after squaring**: `χ_{D₀}(z)² = ((−3)⁻¹)^{2q}`,
where `q` is the `Ȳ`-row of `z`.  The `A`-generator is where the torsion sits (`χ(A) = −1`), and
squaring kills it; the `S`-generator is χ-trivial outright. -/
theorem chiD0G_sq_eq_yRow (z : (D0 : Type)) :
    (chiD0G z) ^ 2
      = zpowZtwo isProP_two_unitsPadicInt ((unitNegThree⁻¹ : ℤ_[2]ˣ) ^ 2)
          (toAdd (yRowD0 z)) := by
  obtain ⟨hA, hS, hY⟩ := chiD0G_values
  have hext : unitsSquareHom.comp chiD0G
      = (zpowZtwoHom isProP_two_unitsPadicInt ((unitNegThree⁻¹ : ℤ_[2]ˣ) ^ 2)).comp yRowD0 := by
    refine d0Hom_ext ?_ ?_ ?_
    · show (chiD0G d0A) ^ 2
        = zpowZtwo isProP_two_unitsPadicInt ((unitNegThree⁻¹ : ℤ_[2]ˣ) ^ 2) (toAdd (yRowD0 d0A))
      rw [hA, yRowD0_A, toAdd_ofAdd, zpowZtwo_zero_exp]
      exact neg_one_sq
    · show (chiD0G d0S) ^ 2
        = zpowZtwo isProP_two_unitsPadicInt ((unitNegThree⁻¹ : ℤ_[2]ˣ) ^ 2) (toAdd (yRowD0 d0S))
      rw [hS, yRowD0_S, toAdd_ofAdd, zpowZtwo_zero_exp, one_pow]
    · show (chiD0G d0Y) ^ 2
        = zpowZtwo isProP_two_unitsPadicInt ((unitNegThree⁻¹ : ℤ_[2]ˣ) ^ 2) (toAdd (yRowD0 d0Y))
      rw [hY, yRowD0_Y, toAdd_ofAdd, zpowZtwo_one_exp]
  exact DFunLike.congr_fun hext z

/-- **The χ-trivial elements of `D₀` are exactly the ones with vanishing `Ȳ`-row.**  Only the
easy direction is needed: `χ_{D₀}(z) = 1` forces the row to vanish, because `(−3)⁻¹` has exact
level `2` and so powers it injectively. -/
theorem yRowD0_eq_zero_of_chiD0G_eq_one {z : (D0 : Type)} (hz : chiD0G z = 1) :
    toAdd (yRowD0 z) = 0 := by
  have hsq := chiD0G_sq_eq_yRow z
  rw [hz, one_pow] at hsq
  have hstep : zpowZtwo isProP_two_unitsPadicInt ((unitNegThree⁻¹ : ℤ_[2]ˣ) ^ 2)
      (toAdd (yRowD0 z))
      = zpowZtwo isProP_two_unitsPadicInt (unitNegThree⁻¹ : ℤ_[2]ˣ)
          (2 * toAdd (yRowD0 z)) := by
    rw [← zpowZtwo_unit_two (unitNegThree⁻¹ : ℤ_[2]ˣ), zpowZtwo_zpowZtwo]
  rw [hstep] at hsq
  have hzero : zpowZtwo isProP_two_unitsPadicInt (unitNegThree⁻¹ : ℤ_[2]ˣ) (0 : ℤ_[2]) = 1 :=
    zpowZtwo_zero_exp _ _
  have hinj := zpowZtwo_injective_neg_three_inv unitNegThree unitNegThree_val_eq
  have h2 : 2 * toAdd (yRowD0 z) = 0 := hinj (by rw [← hsq, hzero])
  have := mul_eq_zero.mp h2
  rcases this with h | h
  · exact absurd h (by norm_num)
  · exact h

end Orientation

/-! ## §4 The package, and the two subgroups -/

section Package

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **The transported affine package.**  Everything is read off the single equivalence
`g = sqEquivDRMarked ∘ f : D_sq(0) ≅ D₀`. -/
noncomputable def sqPivotAffineD0 (B : SectionThree.BDecomposition)
    (f : ContinuousMulEquiv (DR : Type) (D0 : Type)) : SqPivotAffine := by
  classical
  set g : ContinuousMulEquiv (DSq 0 : Type) (D0 : Type) := sqEquivDRMarked.trans f with hg
  set gHom : ContinuousMonoidHom (DSq 0 : Type) (D0 : Type) :=
    ⟨g.toMulEquiv.toMonoidHom, g.continuous_toFun⟩ with hgHom
  set gInv : ContinuousMonoidHom (D0 : Type) (DSq 0 : Type) :=
    ⟨g.symm.toMulEquiv.toMonoidHom, g.symm.continuous_toFun⟩ with hgInv
  -- the orientation transports through `g`
  have hchiG : ∀ x : (DSq 0 : Type), chiD0G (g x) = chiSq 0 x := fun x => by
    rw [hg]
    exact (LSquare.chiD0G_comp_rankThreeLabuteEquiv f (sqEquivDRMarked x)).trans
      (chiR_sqEquivDRMarked x)
  -- the affine family, transported
  have hfam : ∀ (u : ℤ_[2]ˣ) (b : ℤ_[2]),
      ∃ Ψ : ContinuousMulEquiv (DSq 0 : Type) (DSq 0 : Type),
        (∀ x, chiSq 0 (Ψ x) = chiSq 0 x) ∧
        (∀ x, toAdd (sRowD0 (g (Ψ x)))
          = (u : ℤ_[2]) * toAdd (sRowD0 (g x)) + b * toAdd (yRowD0 (g x))) ∧
        (∀ x, toAdd (yRowD0 (g (Ψ x))) = toAdd (yRowD0 (g x))) := by
    intro u b
    obtain ⟨Ψ₀, hs, hy⟩ := prop_3_8_rows B u b
    refine ⟨g.trans (Ψ₀.trans g.symm), fun x => ?_, fun x => ?_, fun x => ?_⟩
    · show chiSq 0 (g.symm (Ψ₀ (g x))) = chiSq 0 x
      have hval : g (g.symm (Ψ₀ (g x))) = Ψ₀ (g x) := g.apply_symm_apply _
      have h1 := hchiG (g.symm (Ψ₀ (g x)))
      rw [hval] at h1
      rw [← h1, ← hchiG x]
      exact (LSquare.chiD0G_comp_rankThreeLabuteEquiv (f.trans Ψ₀) (sqEquivDRMarked x)).trans
        (LSquare.chiD0G_comp_rankThreeLabuteEquiv f (sqEquivDRMarked x)).symm
    · show toAdd (sRowD0 (g (g.symm (Ψ₀ (g x))))) = _
      rw [g.apply_symm_apply]
      exact hs (g x)
    · show toAdd (yRowD0 (g (g.symm (Ψ₀ (g x))))) = _
      rw [g.apply_symm_apply]
      exact hy (g x)
  choose psi hchi hs hy using hfam
  refine
    { pS := toAdd (sRowD0 (g (dsqSigma 0)))
      pX := toAdd (sRowD0 (g (dsqX0 0)))
      qS := toAdd (yRowD0 (g (dsqSigma 0)))
      qX := toAdd (yRowD0 (g (dsqX0 0)))
      cS := fun nu' => toAdd (nu' (g.symm d0S))
      cY := fun nu' => toAdd (nu' (g.symm d0Y))
      psi := psi
      chi_psi := fun u b x => hchi u b x
      sigma_row := ?_
      x0_row := ?_
      psi_sigma := ?_
      psi_x0 := ?_
      pivot_on_line := ?_ }
  · intro nu'
    have := toAdd_mark_d0 (nu'.comp gInv) (g (dsqSigma 0))
    show toAdd (nu' (dsqSigma 0)) = _
    rw [show ((nu'.comp gInv) (g (dsqSigma 0))) = nu' (dsqSigma 0) from by
      show nu' (g.symm (g (dsqSigma 0))) = _
      rw [g.symm_apply_apply]] at this
    exact this
  · intro nu'
    have := toAdd_mark_d0 (nu'.comp gInv) (g (dsqX0 0))
    show toAdd (nu' (dsqX0 0)) = _
    rw [show ((nu'.comp gInv) (g (dsqX0 0))) = nu' (dsqX0 0) from by
      show nu' (g.symm (g (dsqX0 0))) = _
      rw [g.symm_apply_apply]] at this
    exact this
  · intro u b nu'
    have hmk := toAdd_mark_d0 (nu'.comp gInv) (g (psi u b (dsqSigma 0)))
    rw [hs u b (dsqSigma 0), hy u b (dsqSigma 0),
      show toAdd ((nu'.comp gInv) d0S) = toAdd (nu' (g.symm d0S)) from rfl,
      show toAdd ((nu'.comp gInv) d0Y) = toAdd (nu' (g.symm d0Y)) from rfl] at hmk
    show toAdd (nu' (psi u b (dsqSigma 0))) = _
    rw [show ((nu'.comp gInv) (g (psi u b (dsqSigma 0)))) = nu' (psi u b (dsqSigma 0)) from by
      show nu' (g.symm (g (psi u b (dsqSigma 0)))) = _
      rw [g.symm_apply_apply]] at hmk
    rw [hmk]
  · intro u b nu'
    have hmk := toAdd_mark_d0 (nu'.comp gInv) (g (psi u b (dsqX0 0)))
    rw [hs u b (dsqX0 0), hy u b (dsqX0 0),
      show toAdd ((nu'.comp gInv) d0S) = toAdd (nu' (g.symm d0S)) from rfl,
      show toAdd ((nu'.comp gInv) d0Y) = toAdd (nu' (g.symm d0Y)) from rfl] at hmk
    show toAdd (nu' (psi u b (dsqX0 0))) = _
    rw [show ((nu'.comp gInv) (g (psi u b (dsqX0 0)))) = nu' (psi u b (dsqX0 0)) from by
      show nu' (g.symm (g (psi u b (dsqX0 0)))) = _
      rw [g.symm_apply_apply]] at hmk
    rw [hmk]
  · -- the pivot is χ-trivial, hence its `Ȳ`-row vanishes
    have hpiv : chiD0G (g (sqPivot 0)) = 1 := by
      rw [hchiG (sqPivot 0)]
      exact chiSq_sqPivot 0
    have hzero := yRowD0_eq_zero_of_chiD0G_eq_one hpiv
    have hval : toAdd (yRowD0 (g (sqPivot 0)))
        = toAdd (yRowD0 (g (dsqSigma 0))) - sqPivotExp * toAdd (yRowD0 (g (dsqX0 0))) := by
      have hw : sqPivot 0
          = dsqSigma 0 * (zpowZtwo (isProP_DSq 0) (dsqX0 0) sqPivotExp)⁻¹ := rfl
      rw [hw]
      show toAdd ((yRowD0.comp gHom) (dsqSigma 0
        * (zpowZtwo (isProP_DSq 0) (dsqX0 0) sqPivotExp)⁻¹)) = _
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv,
        toAdd_map_zpowZtwo (isProP_DSq 0) (yRowD0.comp gHom) (dsqX0 0) sqPivotExp]
      show toAdd (yRowD0 (g (dsqSigma 0)))
        + -(sqPivotExp * toAdd (yRowD0 (g (dsqX0 0)))) = _
      ring
    rw [hzero] at hval
    linear_combination -hval

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The rank-three Labute equivalence `D_R ≅ D₀`, with `bLab`'s four antecedents discharged. -/
theorem nonempty_equiv_DR_D0 : Nonempty (ContinuousMulEquiv (DR : Type) (D0 : Type)) :=
  GQ2.Roe.Labute.bLab GQ2.isDemushkin_DR GQ2.demushkinRank_DR GQ2.demushkinQ_DR
    ⟨GQ2.Roe.chiR.toMonoidHom, GQ2.Roe.chiR.continuous_toFun,
      GQ2.Roe.isLabuteOrientation_chiR, GQ2.Roe.chiR_surjective⟩

/-- **The translation subgroup at `h = 0`.** -/
theorem sqPivotTranslation_zero (c : ℤ_[2]) : SqPivotTranslation 0 c := by
  obtain ⟨B⟩ := SectionThree.b_decomposition
  obtain ⟨f⟩ := nonempty_equiv_DR_D0
  exact (sqPivotAffineD0 B f).sqPivotTranslation_zero_of_affine c

/-- **The scaling subgroup at `h = 0`.** -/
theorem sqPivotScaling_zero {a : ℤ_[2]} (ha : IsUnit a) : SqPivotScaling 0 a := by
  obtain ⟨B⟩ := SectionThree.b_decomposition
  obtain ⟨f⟩ := nonempty_equiv_DR_D0
  exact (sqPivotAffineD0 B f).sqPivotScaling_zero_of_affine ha

/-- **Every pivot core move at `h = 0` on the determinant locus.** -/
theorem sqPivotCoreMove_zero_of_isUnit {m k : ℤ_[2]} (h : IsUnit (sqPivotDet m k)) :
    SqPivotCoreMove 0 m k :=
  sqPivotCoreMove_of_translation_scaling m k (sqPivotTranslation_zero k)
    (sqPivotScaling_zero h)

/-- **THE MODEL-SIDE RESIDUAL AT `h = 0`.** -/
theorem sqNuOrientedClear_zero : SqNuOrientedClear 0 :=
  sqNuOrientedClear_zero_of_two_subgroups sqPivotTranslation_zero
    (fun _ ha => sqPivotScaling_zero ha)

end Package

/-! ## §5 Stress pins -/

section StressTests

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The two subgroups exist at concrete parameters. -/
example : SqPivotTranslation 0 5 ∧ SqPivotScaling 0 (-1) :=
  ⟨sqPivotTranslation_zero 5, sqPivotScaling_zero (IsUnit.neg isUnit_one)⟩

/-- **Consistency against the necessity theorem**: the moves this file constructs feed
`isUnit_sqPivotDet_of_sqPivotCoreMove` and land back on the unit locus. -/
example (a : ℤ_[2]) (ha : IsUnit a) : IsUnit (sqPivotDet (a - 1) 0) :=
  isUnit_sqPivotDet_of_sqPivotCoreMove (sqPivotScaling_zero ha)

/-- …and the same for the translations, whose determinant is `1`. -/
example (c : ℤ_[2]) : IsUnit (sqPivotDet (c * sqPivotExp) c) :=
  isUnit_sqPivotDet_of_sqPivotCoreMove (sqPivotTranslation_zero c)

/-- The linear interface of `PivotSeedTransport` is inhabited, so it was not vacuous. -/
noncomputable example (B : SectionThree.BDecomposition)
    (f : ContinuousMulEquiv (DR : Type) (D0 : Type)) : SqPivotAffine := sqPivotAffineD0 B f

/-- The model-side residual at `h = 0`, in the shape `PivotUnitizer` states it. -/
example : SqNuOrientedClear 0 := sqNuOrientedClear_zero

end StressTests

/-! ## §5' Axiom pins -/

section AxiomPins

#print axioms sRowD0_A
#print axioms forcedRow_d0A
#print axioms toAdd_mark_d0
#print axioms bE_d0A
#print axioms sRowD0_eq_mid
#print axioms prop_3_8_rows
#print axioms chiD0G_sq_eq_yRow
#print axioms yRowD0_eq_zero_of_chiD0G_eq_one
#print axioms nonempty_equiv_DR_D0
#print axioms sqPivotAffineD0
#print axioms sqPivotCoreMove_zero_of_isUnit
#print axioms sqPivotTranslation_zero
#print axioms sqPivotScaling_zero
#print axioms sqNuOrientedClear_zero

end AxiomPins

end SqCore

/-! ## §6 The milestone: the odd-degree row at `[K : ℚ₂] = 1`, unconditionally -/

namespace LSquare

noncomputable section

open GQ2 GQ2.Dyadic SqCore Multiplicative

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

namespace NuAdapted

section Milestone

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **THE MILESTONE.**  `gammaR_lSq_equiv_galK_degreeOne_of_subgroups` with its two model-side
hypotheses discharged: at `[K : ℚ₂] = 1` the odd-degree row of the general-`K` machine holds
outright, i.e. `Γ_{R_K} ≅ G_K`. -/
theorem gammaR_lSq_equiv_galK_degreeOne (B : MarkedRecip Rec K)
    (FF : DyadicUnitFiltration K) (T : OrientedTameQuotientK B FF)
    (D : FiniteDyadicParameters K FF) (hdeg : Module.finrank ℚ_[2] K = 1)
    (ramifiedData : ∀ {Dg : Type} [Group Dg] [TopologicalSpace Dg] [DiscreteTopology Dg]
      [Finite Dg] (W : Type) [AddCommGroup W] [DistribMulAction Dg W]
      (cc : ContinuousMonoidHom (Tq D.params.qK) Dg)
      (rho : ContinuousMonoidHom (GalK K) Dg),
      (∃ v : W, cc (tqTau D.params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate D.params (GalKsub K) W cc rho)) :
    Nonempty (ContinuousMulEquiv (gamma 0 (qOf K FF) : Type) (GalK K)) :=
  gammaR_lSq_equiv_galK_degreeOne_of_subgroups B FF T D hdeg
    SqCore.sqPivotTranslation_zero (fun _ ha => SqCore.sqPivotScaling_zero ha) ramifiedData

end Milestone

#print axioms gammaR_lSq_equiv_galK_degreeOne

end NuAdapted

end

end LSquare

end Dyadic

end GQ2
