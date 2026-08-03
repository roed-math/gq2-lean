/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.MarkedCore.HandleMixInst
public import GQ2.FrattiniCriterion

@[expose] public section

/-!
# MC-M: the Smith–Witt stabilizer of the `M_α` core — classification and lifting

**Ticket MC3** of the dyadic campaign (lane MC) — the **MC-M obligation** (plan §2, board
"Obligation tracker"), implementing the MC1 design memo `docs/dyadic/mc-design.md` §2.3–§2.5,
§5, §6.2, §6.4 and §8 on the `M`-side.  The parallel ticket MC4 owns `N.lean`; per the
reserved-name rule every declaration here is `m`-prefixed or `M`-headed, and the two
generic-looking helpers (`mZpowZtwo_injective_of_level`, `mExists_unit_pow_two_pow_sub_one`)
carry dedup notes for the `N`-side.

The file consumes MC2 (`Cores.lean`: the presented core `DM α h`, the closed-form orientation
unit `mUnit α = (1−2^α)⁻¹`, the standard character `chiM` and marking `nuM`, the rank-four
frame `MDecomposition`, and the B8 transport `peripheralTriple_scaling`) and the HM lane
(`HandleMix*.lean`: the handle stratum as a *theorem*, `dmParamEquiv`, `dmTauDEquiv`,
`mHandleMixLift`, and the `MLiftSplit`/`MCoreMixHypothesis` split shapes).

## Contents

* **§1–§2** the powering/parity toolkit and the χ-row extraction engine: the rank-four analogue
  of the ℚ₂ mod-4 argument (`GQ2/AnabelianBridge/Classification.lean`, `chi_row_extract`) at the
  general depth-`α` unit `mUnit α` (memo §2.2(i)).  `mZpowZtwo_injective_of_level` extends
  `zpowZtwo_injective_of_exact_level` from exact level 2 to exact level `s ≥ 2`;
  `mChi_row_extract` is the resulting row extraction.  Also the ℤ₂ parity API
  (`mParityZ`, `mSign`) with "odd ⟺ unit" in both directions.
* **§3** coordinates through a frame `B : MDecomposition α`: hom-extensionality on `D_M^{ab}`
  (`mAb_hom_ext`), the frame character `mChiModel`/`mChi_frame`, and the torsion row —
  every continuous automorphism fixes `t = Ā·C̄₀^{2^{α−1}}` (`mXi_fixes_t`), the rank-four
  `xi_fixes_t`, so the relation-vector clause of the stabilizer is automatic.
* **§4** the mod-2 cup Gram `mGram` (memo §2.2(iii), V4), the stabilizer predicate
  `IsMStabilizer` (χ-preservation plus the isometry `M̄ᵀ·G_M·M̄ = G_M`), and **the
  classification** `mStabilizer_classification`: every χ-preserving Gram-isometric continuous
  automorphism of `D_M^{ab}` is given in the frame by the memo §2.3 closed form — seven
  parameters `(τ, β, B_c, c₁, γ, d₁, e)` with the single Witt coupling `τ_D = B_c mod 2` —
  **uniquely**.  Pure `ℤ₂`/`𝔽₂` linear algebra: unconditional, axiom-free, uniform in `α ≥ 2`.
  `mStabilizer_A_row` is the forced `Ā`-row, the only place `α` appears.
* **§5** the seven Nielsen families (memo §2.4) as `MStabParam` values, the closed form as a
  coordinate map `MStabParam.act` with its four basis rows, and **completeness**
  `mNielsen_factorization`: every parameter's frame action is a composite of the seven.
* **§6** the S1 lift (memo §2.5): `mLambdaEquiv` (family M1, `B ↦ A^k·B`) as an honest
  continuous automorphism of `D_M` at general `(α, h)`, with its ν-frame row
  (`nuFrame_mLambdaEquiv`) and χ-preservation (`chiM_mLambdaEquiv`).  Family M2
  (`D ↦ C₀^e·D`) **is** HM4's `dmTauDEquiv` — recorded (`mFamM2_eq_frameTauD`), not duplicated.
* **§7** the binders, never axioms: `MLabHypothesis`/`imChiM` (memo §6.4, G-Lab Decision 1) and
  `MMixHypothesis` (memo §8 Decision 2(B), the S3 residue), plus `mLiftSplit_of_handle` /
  `mLiftSplit_empty` measuring how much of HM4's `MLiftSplit` contract is free.
* **§8** **the correction assembly** (packet Prop. 7.2 at the `M`-core, memo §6.3's `hLift`):
  `prop_MC_M_correction` — under the S3 binder, every transported marking `ν'` with
  `ν'(C̄₀) ∈ ℤ₂ˣ` admits a correction `Ψ ∈ Aut(D_M)` with `χ_M∘Ψ = χ_M` and `ν'∘Ψ = ν_M` —
  plus `prop_MC_M_correction_zero` (`h = 0`) and `prop_MC_M_correction_split` (HM4's
  `MLiftSplit`-threading shape, for MC5).
* **§9** stress pins at `(α, h) = (2, 0)` and `(2, 1)`.

## Recorded findings (deviations and gaps surfaced by this ticket)

1. **The cup-isometry variance is the transpose side.**  The memo §2.3 closed form is the
   solution set of `M̄ᵀ·G_M·M̄ = G_M`, *not* of `M̄·G_M·M̄ᵀ`.  (An automorphism acts on `H¹` by
   precomposition, so the induced map on the cup form is the transpose.)  The two conditions are
   genuinely different here: the other variance forces `τ = 0`, losing family M1 entirely.
   **Layout matters and is the whole story**: this file's `M̄` (`mFrameMatrix`) has the images
   of the frame basis in its **rows**.  MC4's `N.lean` uses the transposed layout (images in
   **columns**) and therefore states the *same* condition as `M̄·G_N·M̄ᵀ = G_N` — "the same
   side" means the same condition, not the same formula.  Machine-checked dictionary:
   `GQ2/Dyadic/MarkedCore/Variance.lean`.  See §4's preamble.
2. **β is a unit by χ, γ is a unit by Witt.**  Unlike the rank-three `prop_3_8_classification`,
   which obtains unit-ness of its `S̄`-exponent from a second row analysis applied to `ξ⁻¹`, the
   rank-four classification never needs the inverse automorphism: the χ-condition forces `β`
   odd and the Gram entry `(2,3)` forces `γ` odd.  The Gram condition also rules out `ξ(t) = 1`
   on its own, so bijectivity of `ξ` is never used in the classification.
3. **The seven-family factorization needs parameter adjustments, and cannot avoid them.**  No
   ordering of the seven families composes to the closed form with `p`'s own coordinates
   verbatim: `Y_c` reads the `C̄₀`-coordinate and writes the `B̄` one while `X_b` reads `B̄` and
   writes `C̄₀`, so one of the two always sees a modified input.  This is exactly the memo §2.4
   remark "each step perturbs only parameters killed later"; the perturbations are all **even**,
   which is why the adjusted `β₄` is still a unit.  See §5.
4. **`DmRealizes` is scoped to the handle stratum**, so no core-stratum piece is routed through
   it here; `MMixHypothesis` demands χ-preservation directly, and `MCoreMixHypothesis` /
   `MLiftSplit` are threaded *literally* in `prop_MC_M_correction_split`.  See §7's preamble.
5. **The S2 (unit-scaling) lift is built one layer above this file.**
   `MarkedCore/MScaling.lean` retains the canonical `deltaHom` conjugators from the two nested
   B8 triples, splices them at `w_M = A·A^B`, proves Frattini surjectivity, and constructs the
   χ-preserving `ContinuousMulEquiv` at handle level zero.  This file itself still has **no B8
   consumer**; §5's family `mFamM3` records the frame row realized by that construction.
6. The classification takes the orientation as an abstract character with pinned generator
   values (`hχA`–`hχD`), exactly as `prop_3_8_classification` does on the ℚ₂ side — no descended
   `chiMab` is constructed, and `mChi_frame` shows none is needed.
7. **`MLabHypothesis` carries its orientation-canonicity predicate as a parameter** — the
   abstract-`G` form is forced (memo R6: the other side is `G_K(2)`, not a presented group), the
   repo has no abstract dualizing-module characterisation (`GQ2/Orientation.lean` deferral), and
   quantifying over *all* characters with the stated image would be false.  See §7.

## Axiom hygiene

**Every declaration in this file is axiom-free (std-3: `propext`, `Classical.choice`,
`Quot.sound`)** — including the obligation headline `prop_MC_M_correction`, whose handle
stratum comes from the HM lane's axiom-free theorem `mHandleMixLift`.  In particular there are
**zero B8 and zero B3c citers**: the memo §5.2 B8 route would enter only through the S2 lift,
which is finding 5's deferral.  Census unchanged at 11; no new axiom; the obligation headline
is a `theorem` whose only assumption is a `def`.
-/

open Multiplicative

namespace GQ2

open SectionThree

namespace Dyadic

namespace MarkedCore

/-! ## §1 The powering and parity toolkit

Small general lemmas about `conjP`, `zpowZtwo`, and mod-2/mod-4 reduction that the ℚ₂ files
prove privately inside the (non-module) `GQ2/AnabelianBridge` stack and are therefore restated
here, `m`-named, for the module-side MarkedCore lane. -/

section Toolkit

variable {G : Type*} [Group G]

theorem mConjP_conjP (x a b : G) : conjP (conjP x a) b = conjP x (a * b) := by
  simp only [conjP, mul_inv_rev]
  group

@[simp] theorem mConjP_one (x : G) : conjP x (1 : G) = x := by
  simp [conjP]

theorem mConjP_inv (x c : G) : (conjP x c)⁻¹ = conjP x⁻¹ c := by
  simp only [conjP, mul_inv_rev, inv_inv]
  group

theorem mConjP_pow (x c : G) (n : ℕ) : conjP x c ^ n = conjP (x ^ n) c := by
  induction n with
  | zero => simp [conjP]
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [conjP]
    group

/-- A homomorphism into a commutative group is blind to conjugation. -/
theorem mChar_conjP {A : Type*} [CommGroup A] {F : Type*} [FunLike F G A]
    [MonoidHomClass F G A] (f : F) (x c : G) : f (conjP x c) = f x := by
  simp only [conjP, map_mul, map_inv]
  rw [mul_comm ((f c)⁻¹) (f x), mul_assoc, inv_mul_cancel, mul_one]

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P]

/-- `x` commutes with its own 2-adic powers. -/
theorem mCommute_zpowZtwo (hP : IsProP 2 P) (x : P) (u : ℤ_[2]) :
    Commute x (zpowZtwo hP x u) := by
  have h1 : zpowZtwo hP x (1 + u) = x * zpowZtwo hP x u := by
    rw [zpowZtwo_add, zpowZtwo_one_exp]
  have h2 : zpowZtwo hP x (u + 1) = zpowZtwo hP x u * x := by
    rw [zpowZtwo_add, zpowZtwo_one_exp]
  show x * zpowZtwo hP x u = zpowZtwo hP x u * x
  rw [← h1, ← h2, add_comm]

/-- 2-adic powering commutes with conjugation. -/
theorem mConjP_zpowZtwo (hP : IsProP 2 P) (x g : P) (u : ℤ_[2]) :
    conjP (zpowZtwo hP x u) g = zpowZtwo hP (conjP x g) u := by
  set φ : ContinuousMonoidHom P P :=
    ⟨(MulEquiv.mk' (Equiv.mulRight g |>.trans (Equiv.mulLeft g⁻¹))
        (fun a b => by simp [mul_assoc])).toMonoidHom,
      by
        show Continuous fun a => g⁻¹ * (a * g)
        exact (continuous_const_mul g⁻¹).comp (continuous_mul_const g)⟩ with hφ
  have hφx : ∀ y : P, φ y = conjP y g := fun y => by
    show g⁻¹ * (y * g) = g⁻¹ * y * g
    group
  have h := map_zpowZtwo hP hP φ x u
  rw [hφx, hφx] at h
  exact h

/-- 2-adic powering of an inverse is the inverse of the power. -/
theorem mZpowZtwo_inv (hP : IsProP 2 P) (x : P) (u : ℤ_[2]) :
    zpowZtwo hP x⁻¹ u = (zpowZtwo hP x u)⁻¹ := by
  set φ : Multiplicative ℤ_[2] →* P :=
    { toFun := fun w => (zpowZtwoHom hP x w)⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv_rev]
        have hc : Commute (zpowZtwoHom hP x a) (zpowZtwoHom hP x b) :=
          (Commute.all a b).map (zpowZtwoHom hP x)
        exact hc.inv_inv.eq.symm } with hφ
  have hφc : Continuous φ := (zpowZtwoHom hP x).continuous_toFun.inv
  have h := zpowZtwoHom_unique hP hφc u
  have h1 : φ (ofAdd (1 : ℤ_[2])) = x⁻¹ := by
    show (zpowZtwoHom hP x (ofAdd (1 : ℤ_[2])))⁻¹ = x⁻¹
    rw [zpowZtwoHom_ofAdd_one]
  rw [h1] at h
  exact h.symm

/-- Natural powers commute with 2-adic powers: `(x^u)^n = (x^n)^u`. -/
theorem mZpowZtwo_pow (hP : IsProP 2 P) (x : P) (u : ℤ_[2]) (n : ℕ) :
    zpowZtwo hP x u ^ n = zpowZtwo hP (x ^ n) u := by
  rw [← zpowZtwo_natCast hP (zpowZtwo hP x u) n, zpowZtwo_zpowZtwo,
    ← zpowZtwo_natCast hP x n, zpowZtwo_zpowZtwo, mul_comm]

/-- A continuous endomorphism of `Multiplicative ℤ₂` is multiplication by its value at `1`. -/
theorem mMultHom_ofAdd (f : Multiplicative ℤ_[2] →* Multiplicative ℤ_[2]) (hf : Continuous f)
    (w : ℤ_[2]) : f (ofAdd w) = ofAdd (toAdd (f (ofAdd 1)) * w) := by
  set g : Multiplicative ℤ_[2] →* Multiplicative ℤ_[2] :=
    AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft (toAdd (f (ofAdd 1)))) with hg
  have hgc : Continuous g :=
    continuous_ofAdd.comp ((continuous_const_mul _).comp continuous_toAdd)
  have h := multPadicIntHom_ext hf hgc ?_
  · exact DFunLike.congr_fun h (ofAdd w)
  · show f (ofAdd 1) = ofAdd (toAdd (f (ofAdd 1)) * 1)
    rw [mul_one, ofAdd_toAdd]

/-- A continuous homomorphism `Multiplicative ℤ₂ → ℤ₂ˣ` is 2-adic powering of its value
at `1`. -/
theorem mUnitsHom_ofAdd (f : Multiplicative ℤ_[2] →* ℤ_[2]ˣ) (hf : Continuous f) (w : ℤ_[2]) :
    f (ofAdd w) = zpowZtwo isProP_two_unitsPadicInt (f (ofAdd 1)) w := by
  have h := multPadicIntHom_ext hf
    (zpowZtwoHom isProP_two_unitsPadicInt (f (ofAdd 1))).continuous_toFun ?_
  · exact DFunLike.congr_fun h (ofAdd w)
  · show f (ofAdd 1) = zpowZtwoHom isProP_two_unitsPadicInt (f (ofAdd 1)) (ofAdd 1)
    rw [zpowZtwoHom_ofAdd_one]

end Toolkit

/-! ### The mod-2 parity and the sign character -/

section Parity

/-- **Mod-2 parity of a 2-adic integer**, valued in `ZMod 2` (the coefficient ring of the mod-2
frame).  Routed through `PadicInt.toZModPow 1` so that every fact reduces to a finite check. -/
noncomputable def mParityZ (b : ℤ_[2]) : ZMod 2 :=
  ((PadicInt.toZModPow (p := 2) 1 b).val : ZMod 2)

theorem mParityZ_add (a b : ℤ_[2]) : mParityZ (a + b) = mParityZ a + mParityZ b := by
  unfold mParityZ
  rw [map_add]
  exact (by decide : ∀ x y : ZMod (2 ^ 1),
    (((x + y).val : ℕ) : ZMod 2) = ((x.val : ℕ) : ZMod 2) + ((y.val : ℕ) : ZMod 2)) _ _

@[simp] theorem mParityZ_one : mParityZ 1 = 1 := by
  unfold mParityZ
  rw [map_one]
  decide

@[simp] theorem mParityZ_zero : mParityZ 0 = 0 := by
  unfold mParityZ
  rw [map_zero]
  decide

theorem mToZModPow_one_two : PadicInt.toZModPow (p := 2) 1 (2 : ℤ_[2]) = 0 := by
  rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num, map_natCast]
  decide

@[simp] theorem mParityZ_two_mul (x : ℤ_[2]) : mParityZ (2 * x) = 0 := by
  unfold mParityZ
  rw [map_mul, mToZModPow_one_two, zero_mul]
  decide

/-- **The sign of a 2-adic exponent**: `(−1)^b` read through the parity. -/
noncomputable def mSign (b : ℤ_[2]) : ℤ_[2]ˣ := (-1) ^ (PadicInt.toZModPow (p := 2) 1 b).val

/-- `(−1)²  = 1` in `ℤ₂ˣ`. -/
theorem mNegOne_sq : ((-1 : ℤ_[2]ˣ)) ^ 2 = 1 := by
  rw [pow_two]
  exact Units.ext (by push_cast; ring)

/-- 2-adic powers of `−1` are the sign character. -/
theorem mNegOne_zpow (b : ℤ_[2]) :
    zpowZtwo isProP_two_unitsPadicInt (-1 : ℤ_[2]ˣ) b = mSign b :=
  SectionThree.zpowZtwo_of_sq_eq_one isProP_two_unitsPadicInt (-1) mNegOne_sq b

@[simp] theorem mSign_two_mul (x : ℤ_[2]) : mSign (2 * x) = 1 := by
  unfold mSign
  rw [map_mul, mToZModPow_one_two, zero_mul, ZMod.val_zero, pow_zero]

/-- The sign at parity `ε ∈ ZMod 2`, in the exponent normal form `(−1)^{ε.val}`. -/
theorem mSign_eq_pow_val (b : ℤ_[2]) :
    mSign b = (-1 : ℤ_[2]ˣ) ^ (mParityZ b).val := by
  unfold mSign mParityZ
  congr 1
  exact (by decide : ∀ x : ZMod (2 ^ 1), x.val = (((x.val : ℕ) : ZMod 2)).val) _

end Parity

/-! ### The depth-`α` unit: exact level, injectivity, mod 4

`mUnit α = (1−2^α)⁻¹` has `v₂(mUnit α − 1) = α` exactly (memo §2.2(i): "depth exactly α").
The ℚ₂ file's `zpowZtwo_injective_of_exact_level` covers level 2; the classification needs the
general level `s ≥ 2`, proved here by the same telescoping argument. -/

section Depth

/-- `mUnit α − 1 = 2^α·mUnit α` — the exact-depth witness (memo §2.2(i)). -/
theorem mUnit_sub_one {α : ℕ} (hα : 1 ≤ α) :
    ((mUnit α : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ α * ((mUnit α : ℤ_[2]ˣ) : ℤ_[2]) := by
  have h := mUnit_mul hα
  linear_combination h

/-- Level telescoping: from `η − 1 = 2^s·a` (`a` a unit, `s ≥ 2`) the `2^m`-th power has
`η^{2^m} − 1 = 2^{m+s}·(unit)`.  Generalizes `exists_unit_pow_two_pow_sub_one` (level 2);
dedup note: MC4's `N`-side consumes this same lemma — it is stated once, here, `m`-prefixed
per the reserved-name rule. -/
theorem mExists_unit_pow_two_pow_sub_one (η a : ℤ_[2]ˣ) (s : ℕ) (hs : 2 ≤ s)
    (hη : ((η : ℤ_[2])) - 1 = 2 ^ s * a) (m : ℕ) :
    ∃ b : ℤ_[2]ˣ, ((η ^ 2 ^ m : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ (m + s) * b := by
  induction m with
  | zero => exact ⟨a, by simpa using hη⟩
  | succ m ih =>
    obtain ⟨b, hb⟩ := ih
    have hunit : IsUnit (1 + 2 ^ (m + s - 1) * (b : ℤ_[2])) := by
      have hms : m + s - 1 = m + s - 2 + 1 := by omega
      have hsplit : (2 : ℤ_[2]) ^ (m + s - 1) * (b : ℤ_[2])
          = 2 * (2 ^ (m + s - 2) * (b : ℤ_[2])) := by
        rw [hms, pow_succ]
        ring
      rw [hsplit]
      exact isUnit_one_add_two_mul _
    refine ⟨b * hunit.unit, ?_⟩
    have hpow : (η ^ 2 ^ (m + 1) : ℤ_[2]ˣ) = (η ^ 2 ^ m) ^ 2 := by
      rw [← pow_mul, pow_succ]
    have hplus : ((η ^ 2 ^ m : ℤ_[2]ˣ) : ℤ_[2]) + 1
        = 2 * (1 + 2 ^ (m + s - 1) * (b : ℤ_[2])) := by
      have h2pow : (2 : ℤ_[2]) ^ (m + s) = 2 * 2 ^ (m + s - 1) := by
        obtain ⟨k, hk⟩ : ∃ k, m + s = k + 1 := ⟨m + s - 1, by omega⟩
        rw [hk, Nat.add_sub_cancel, pow_succ]
        ring
      have hx : ((η ^ 2 ^ m : ℤ_[2]ˣ) : ℤ_[2]) = 1 + 2 ^ (m + s) * (b : ℤ_[2]) := by
        linear_combination hb
      rw [hx, h2pow]
      ring
    have hfact : (((η ^ 2 ^ m : ℤ_[2]ˣ) : ℤ_[2])) ^ 2 - 1
        = (((η ^ 2 ^ m : ℤ_[2]ˣ) : ℤ_[2]) - 1) * (((η ^ 2 ^ m : ℤ_[2]ˣ) : ℤ_[2]) + 1) := by
      ring
    have hexp : (2 : ℤ_[2]) ^ (m + 1 + s) = 2 ^ (m + s) * 2 := by
      rw [show m + 1 + s = m + s + 1 by omega, pow_succ]
    rw [hpow, Units.val_pow_eq_pow_val, hfact, hb, hplus, Units.val_mul, IsUnit.unit_spec, hexp]
    ring

/-- **Level-`s` injectivity of unit powering**: if `η − 1 = 2^s·a` with `a ∈ ℤ₂ˣ` and `s ≥ 2`
then `u ↦ η^u` is injective on 2-adic exponents.  Extends
`zpowZtwo_injective_of_exact_level` (the `s = 2` case); same proof, with the level-`s`
telescoping.  Dedup note: shared with MC4 (`N`-side unit `nUnit α`), stated once here. -/
theorem mZpowZtwo_injective_of_level (η a : ℤ_[2]ˣ) (s : ℕ) (hs : 2 ≤ s)
    (hη : ((η : ℤ_[2])) - 1 = 2 ^ s * a) :
    Function.Injective (zpowZtwo isProP_two_unitsPadicInt η) := by
  intro c₁ c₂ hc
  by_contra hne
  have hc0 : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hne
  have hker : zpowZtwo isProP_two_unitsPadicInt η (c₁ - c₂) = 1 := by
    have hadd := zpowZtwo_add isProP_two_unitsPadicInt η (c₁ - c₂) c₂
    rw [sub_add_cancel, hc] at hadd
    exact right_eq_mul.mp hadd
  set m := (c₁ - c₂).valuation with hm
  set w := PadicInt.unitCoeff hc0 with hwdef
  have hspec : c₁ - c₂ = (w : ℤ_[2]) * 2 ^ m := PadicInt.unitCoeff_spec hc0
  have hfactor : zpowZtwo isProP_two_unitsPadicInt (η ^ 2 ^ m) ((w : ℤ_[2]))
      = zpowZtwo isProP_two_unitsPadicInt η (c₁ - c₂) := by
    rw [← zpowZtwo_natCast isProP_two_unitsPadicInt η (2 ^ m), zpowZtwo_zpowZtwo]
    congr 1
    rw [hspec]
    push_cast
    ring
  have hbase : (η ^ 2 ^ m : ℤ_[2]ˣ) = 1 := by
    refine (zpowZtwo_bijective isProP_two_unitsPadicInt w).injective ?_
    show zpowZtwo _ (η ^ 2 ^ m) ((w : ℤ_[2])) = zpowZtwo _ 1 ((w : ℤ_[2]))
    rw [hfactor, hker, zpowZtwo_one_base]
  obtain ⟨b, hb⟩ := mExists_unit_pow_two_pow_sub_one η a s hs hη m
  rw [hbase] at hb
  have hzero : (2 : ℤ_[2]) ^ (m + s) * (b : ℤ_[2]) = 0 := by
    rw [← hb]
    simp
  exact mul_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℤ_[2]) ≠ 0)) b.ne_zero hzero

/-- `u ↦ (mUnit α)^u` is injective for `α ≥ 2` — the rank-four `η`-injectivity. -/
theorem mUnit_zpow_injective {α : ℕ} (hα : 2 ≤ α) :
    Function.Injective (zpowZtwo isProP_two_unitsPadicInt (mUnit α)) :=
  mZpowZtwo_injective_of_level (mUnit α) (mUnit α) α hα (mUnit_sub_one (by omega))

/-- `2^α·x` dies mod 4 for `α ≥ 2`. -/
theorem mToZModPow_two_pow_mul {α : ℕ} (hα : 2 ≤ α) (x : ℤ_[2]) :
    PadicInt.toZModPow (p := 2) 2 ((2 : ℤ_[2]) ^ α * x) = 0 := by
  rw [map_mul, map_pow, show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num, map_natCast]
  have h4 : ((2 : ℕ) : ZMod (2 ^ 2)) ^ α = 0 := by
    rw [show α = 2 + (α - 2) by omega, pow_add]
    have : ((2 : ℕ) : ZMod (2 ^ 2)) ^ 2 = 0 := by decide
    rw [this, zero_mul]
  rw [h4, zero_mul]

/-- `mUnit α ≡ 1 (mod 4)` for `α ≥ 2`. -/
theorem mUnit_toZModPow_two {α : ℕ} (hα : 2 ≤ α) :
    PadicInt.toZModPow (p := 2) 2 ((mUnit α : ℤ_[2])) = 1 := by
  have h := mUnit_sub_one (α := α) (by omega)
  have hval : ((mUnit α : ℤ_[2]ˣ) : ℤ_[2]) = 1 + 2 ^ α * ((mUnit α : ℤ_[2]ˣ) : ℤ_[2]) := by
    linear_combination h
  rw [hval, map_add, map_one, mToZModPow_two_pow_mul hα, add_zero]

/-- `(mUnit α)^w ≡ 1 (mod 4)` for every 2-adic exponent `w` — the rank-four `eta_pow_mod4`. -/
theorem mUnit_zpow_toZModPow_two {α : ℕ} (hα : 2 ≤ α) (w : ℤ_[2]) :
    PadicInt.toZModPow (p := 2) 2
      ((zpowZtwo isProP_two_unitsPadicInt (mUnit α) w : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
  letI : TopologicalSpace (ZMod (2 ^ 2)) := ⊥
  letI : DiscreteTopology (ZMod (2 ^ 2)) := ⟨rfl⟩
  have hcont : Continuous (PadicInt.toZModPow (p := 2) 2 : ℤ_[2] → ZMod (2 ^ 2)) := by
    rw [continuous_def]
    intro T _
    exact isOpen_preimage_toZModPow 2 T
  set f : Multiplicative ℤ_[2] →* ZMod (2 ^ 2) :=
    (PadicInt.toZModPow (p := 2) 2 : ℤ_[2] →+* ZMod (2 ^ 2)).toMonoidHom.comp
      ((Units.coeHom ℤ_[2]).comp
        (zpowZtwoHom isProP_two_unitsPadicInt (mUnit α)).toMonoidHom) with hfdef
  have hfcont : Continuous f :=
    hcont.comp (Units.continuous_val.comp
      (zpowZtwoHom isProP_two_unitsPadicInt (mUnit α)).continuous_toFun)
  have hf1 : f = (1 : Multiplicative ℤ_[2] →* ZMod (2 ^ 2)) := by
    refine multPadicIntHom_ext hfcont continuous_const ?_
    show (PadicInt.toZModPow (p := 2) 2)
      ((zpowZtwoHom isProP_two_unitsPadicInt (mUnit α) (ofAdd (1 : ℤ_[2])) : ℤ_[2]ˣ) : ℤ_[2])
      = 1
    rw [zpowZtwoHom_ofAdd_one]
    exact mUnit_toZModPow_two hα
  have hw := DFunLike.congr_fun hf1 (ofAdd w)
  rw [MonoidHom.one_apply] at hw
  exact hw

end Depth

/-! ## §2 The χ-row extraction engine

The rank-four analogue of `chi_row_extract`: from an equation
`(−1)^{parity} · (mUnit α)^d = (−1)^{ε} · (mUnit α)^w` in `ℤ₂ˣ`, the mod-4 evaluation kills
the sign ambiguity (`mUnit`-powers are `≡ 1`, `−1` is not) and the level-`α` injectivity pins
the exponent.  This is the entire χ-condition analysis of memo §2.3. -/

section Extract

theorem mToZModPow_two_negOne :
    PadicInt.toZModPow (p := 2) 2 ((-1 : ℤ_[2])) = 3 := by
  rw [show (-1 : ℤ_[2]) = ((-1 : ℤ) : ℤ_[2]) by push_cast; ring, map_intCast]
  decide

/-- **The χ-row extraction** (memo §2.3): `mSign b · u^d = (−1)^{ε.val} · u^w` forces
`parity b = ε` and `d = w`, for the depth-`α` unit `u = mUnit α`, `α ≥ 2`. -/
theorem mChi_row_extract {α : ℕ} (hα : 2 ≤ α) {b d w : ℤ_[2]} {ε : ZMod 2}
    (h : mSign b * zpowZtwo isProP_two_unitsPadicInt (mUnit α) d
       = (-1 : ℤ_[2]ˣ) ^ ε.val * zpowZtwo isProP_two_unitsPadicInt (mUnit α) w) :
    mParityZ b = ε ∧ d = w := by
  -- mod-4 evaluation of both sides
  have h4 := congrArg
    (fun v : ℤ_[2]ˣ => PadicInt.toZModPow (p := 2) 2 ((v : ℤ_[2]))) h
  simp only [Units.val_mul, map_mul] at h4
  rw [mUnit_zpow_toZModPow_two hα d, mUnit_zpow_toZModPow_two hα w, mul_one, mul_one] at h4
  have hpow : ∀ n : ℕ, PadicInt.toZModPow (p := 2) 2 (((-1 : ℤ_[2]ˣ) ^ n : ℤ_[2]ˣ) : ℤ_[2])
      = 3 ^ n := by
    intro n
    rw [Units.val_pow_eq_pow_val, map_pow, show ((-1 : ℤ_[2]ˣ) : ℤ_[2]) = -1 from rfl,
      mToZModPow_two_negOne]
  rw [show mSign b = (-1 : ℤ_[2]ˣ) ^ (PadicInt.toZModPow (p := 2) 1 b).val from rfl,
    hpow, hpow] at h4
  -- both exponents are 0 or 1; `3⁰ ≠ 3¹` in `ZMod 4`
  have hb2 : (PadicInt.toZModPow (p := 2) 1 b).val < 2 := by
    have := ZMod.val_lt (PadicInt.toZModPow (p := 2) 1 b)
    simpa using this
  have hε2 : ε.val < 2 := by
    have := ZMod.val_lt ε
    simpa using this
  have hvals : (PadicInt.toZModPow (p := 2) 1 b).val = ε.val := by
    have hb01 : (PadicInt.toZModPow (p := 2) 1 b).val = 0
        ∨ (PadicInt.toZModPow (p := 2) 1 b).val = 1 := by omega
    have hε01 : ε.val = 0 ∨ ε.val = 1 := by omega
    rcases hb01 with hb | hb <;> rcases hε01 with hε | hε <;> rw [hb, hε] at h4 ⊢ <;>
      revert h4 <;> decide
  refine ⟨?_, ?_⟩
  · unfold mParityZ
    rw [hvals]
    exact (by decide : ∀ x : ZMod 2, ((x.val : ℕ) : ZMod 2) = x) ε
  · have hsign : mSign b = (-1 : ℤ_[2]ˣ) ^ ε.val := by
      rw [show mSign b = (-1 : ℤ_[2]ˣ) ^ (PadicInt.toZModPow (p := 2) 1 b).val from rfl, hvals]
    rw [hsign] at h
    exact mUnit_zpow_injective hα (mul_left_cancel h)

/-! ### Parity as a divisibility statement -/

theorem mParityZ_eq_zero_iff (x : ℤ_[2]) : mParityZ x = 0 ↔ ∃ y : ℤ_[2], x = 2 * y := by
  constructor
  · intro h
    have hval : (PadicInt.toZModPow (p := 2) 1 x).val = 0 := by
      have hlt : (PadicInt.toZModPow (p := 2) 1 x).val < 2 := by
        simpa using ZMod.val_lt (PadicInt.toZModPow (p := 2) 1 x)
      rcases (by omega : (PadicInt.toZModPow (p := 2) 1 x).val = 0
          ∨ (PadicInt.toZModPow (p := 2) 1 x).val = 1) with h0 | h1
      · exact h0
      · rw [mParityZ, h1] at h
        exact absurd h (by decide)
    have hzero : PadicInt.toZModPow (p := 2) 1 x = 0 := by
      haveI : NeZero (2 ^ 1) := ⟨by norm_num⟩
      exact (ZMod.val_eq_zero _).mp hval
    have hker : x ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 1) := hzero
    rw [PadicInt.ker_toZModPow, pow_one, Ideal.mem_span_singleton] at hker
    obtain ⟨y, hy⟩ := hker
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    exact mParityZ_two_mul y

theorem mParityZ_eq_one_iff (x : ℤ_[2]) : mParityZ x = 1 ↔ ∃ y : ℤ_[2], x = 1 + 2 * y := by
  constructor
  · intro h
    have hsub : mParityZ (x - 1) = 0 := by
      have hadd := mParityZ_add (x - 1) 1
      rw [sub_add_cancel, h, mParityZ_one] at hadd
      have : mParityZ (x - 1) + 1 - 1 = (1 : ZMod 2) - 1 := by rw [← hadd]
      simpa using this
    obtain ⟨y, hy⟩ := (mParityZ_eq_zero_iff _).mp hsub
    exact ⟨y, by linear_combination hy⟩
  · rintro ⟨y, rfl⟩
    rw [mParityZ_add, mParityZ_one, mParityZ_two_mul, add_zero]

/-- An odd 2-adic integer is a unit — the `β`/`γ` half of the classification's parameter
extraction (memo §2.3). -/
theorem mIsUnit_of_parity_one {x : ℤ_[2]} (h : mParityZ x = 1) : IsUnit x := by
  obtain ⟨y, rfl⟩ := (mParityZ_eq_one_iff x).mp h
  exact isUnit_one_add_two_mul y

theorem mParityZ_mul (a b : ℤ_[2]) : mParityZ (a * b) = mParityZ a * mParityZ b := by
  unfold mParityZ
  rw [map_mul]
  exact (by decide : ∀ x y : ZMod (2 ^ 1),
    (((x * y).val : ℕ) : ZMod 2) = ((x.val : ℕ) : ZMod 2) * ((y.val : ℕ) : ZMod 2)) _ _

/-- A 2-adic unit is odd — the converse of `mIsUnit_of_parity_one`, used to check that the
Nielsen families really lie in the stabilizer. -/
theorem mParityZ_of_isUnit {x : ℤ_[2]} (h : IsUnit x) : mParityZ x = 1 := by
  obtain ⟨u, rfl⟩ := h
  have h1 : mParityZ ((u : ℤ_[2]) * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mParityZ_one]
  rw [mParityZ_mul] at h1
  exact (by decide : ∀ z w : ZMod 2, z * w = 1 → z = 1) _ _ h1

@[simp] theorem mSign_zero : mSign 0 = 1 := by
  have h := mSign_two_mul 0
  rwa [mul_zero] at h

theorem mSign_add (a b : ℤ_[2]) : mSign (a + b) = mSign a * mSign b := by
  rw [← mNegOne_zpow, ← mNegOne_zpow, ← mNegOne_zpow, zpowZtwo_add]

theorem mSign_continuous : Continuous mSign := by
  have h : mSign = zpowZtwo isProP_two_unitsPadicInt (-1 : ℤ_[2]ˣ) :=
    funext fun b => (mNegOne_zpow b).symm
  rw [h]
  exact continuous_zpowZtwo _ _

end Extract

/-! ## §3 The `M`-frame in coordinates: hom-extensionality, χ, and the torsion row

MC3 consumes a frame `B : MDecomposition α` as a hypothesis, exactly as
`prop_3_8_classification` consumes `BDecomposition`
(`GQ2/AnabelianBridge/Classification.lean:342`); MC2's scope note (`Cores.lean`, §7 preamble)
records the same split.  The frame is the rank-four (`h = 0`) one: the `2h` handle coordinates
are extra free `ℤ₂` summands and belong to MC5 (memo §4.2).

Three things live here.

* `mAb_hom_ext` — two continuous homs out of `D_M^{ab}` that agree on the marked generators are
  equal.
* `mChiModel` / `mChi_frame` — the canonical orientation read in the frame is
  `(τ, b, c, d) ↦ (−1)^b · u^d` (memo §2.2(i): `χ̄(t) = 1`, `χ̄(B̄) = −1`, `χ̄(C̄₀) = 1`,
  `χ̄(D̄) = u`), so *every* continuous character with the pinned generator values is that
  formula composed with `B.e`.
* `mSqEqOne_iff` / `mXi_fixes_t` — `t = Ā·C̄₀^{2^{α−1}}` is the unique nontrivial 2-torsion
  class, hence fixed by every continuous automorphism: the rank-four `xi_fixes_t`
  (`GQ2/AnabelianBridge/Classification.lean:161`). -/

section Frame

open Multiplicative

/-- The frame model `ℤ/2 ⊕ ℤ₂³` of the rank-four `M`-core, multiplicatively. -/
abbrev MModel : Type := Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2])

/-- Coordinate extensionality in the model. -/
theorem mCoord_ext {ε : ZMod 2} {b c d : ℤ_[2]} {z : MModel} (h1 : (toAdd z).1 = ε)
    (h2 : (toAdd z).2.1 = b) (h3 : (toAdd z).2.2.1 = c) (h4 : (toAdd z).2.2.2 = d) :
    z = ofAdd (ε, b, c, d) := by
  conv_lhs => rw [← ofAdd_toAdd z]
  exact congrArg ofAdd (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4)))

/-- The four core indices of the rank-four marking. -/
theorem mCoreIdx_cases (i : Fin (coreRank 0)) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have h4 : (i : ℕ) < 4 := by
    have := i.isLt
    simpa only [coreRank] using this
  have h0 := coreVal_zero 0
  have h1 := coreVal_one 0
  have h2 := coreVal_two 0
  have h3 := coreVal_three 0
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 2 ∨ (i : ℕ) = 3) with h | h | h | h
  · exact Or.inl (Fin.val_injective (by rw [h, h0]))
  · exact Or.inr (Or.inl (Fin.val_injective (by rw [h, h1])))
  · exact Or.inr (Or.inr (Or.inl (Fin.val_injective (by rw [h, h2]))))
  · exact Or.inr (Or.inr (Or.inr (Fin.val_injective (by rw [h, h3]))))

/-- `abMk` as a continuous monoid hom. -/
noncomputable def mAbMkHom (α h : ℕ) :
    ContinuousMonoidHom (DM α h : Type) (topAbelianization (DM α h : Type)) :=
  ⟨abMk, continuous_abMk⟩

@[simp] theorem mAbMkHom_apply (α h : ℕ) (x : (DM α h : Type)) : mAbMkHom α h x = abMk x := rfl

/-- **Hom-extensionality on `D_M^{ab}`**: two continuous homs out of the abelianization that
agree on the images of the marked generators are equal (the `dm_hom_ext` pattern, pushed through
the surjection `abMk`). -/
theorem mAb_hom_ext {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    {α h : ℕ} (f g : ContinuousMonoidHom (topAbelianization (DM α h : Type)) A)
    (hgen : ∀ i, f (abMk (dmGen α h i)) = g (abMk (dmGen α h i))) (x) : f x = g x := by
  obtain ⟨y, rfl⟩ := abMk_surjective (G := (DM α h : Type)) x
  have hcomp : f.comp (mAbMkHom α h) = g.comp (mAbMkHom α h) :=
    dm_hom_ext _ _ fun i => hgen i
  exact DFunLike.congr_fun hcomp y

/-- **χ in the frame** (memo §2.2(i)): the model character `(τ, b, c, d) ↦ (−1)^b · u^d`. -/
noncomputable def mChiModel (α : ℕ) : MModel →* ℤ_[2]ˣ where
  toFun z := mSign (toAdd z).2.1 * zpowZtwo isProP_two_unitsPadicInt (mUnit α) (toAdd z).2.2.2
  map_one' := by
    show mSign 0 * zpowZtwo isProP_two_unitsPadicInt (mUnit α) 0 = 1
    rw [mSign_zero, zpowZtwo_zero, mul_one]
  map_mul' x y := by
    show mSign ((toAdd x).2.1 + (toAdd y).2.1)
        * zpowZtwo isProP_two_unitsPadicInt (mUnit α) ((toAdd x).2.2.2 + (toAdd y).2.2.2)
      = (mSign (toAdd x).2.1 * zpowZtwo isProP_two_unitsPadicInt (mUnit α) (toAdd x).2.2.2)
        * (mSign (toAdd y).2.1 * zpowZtwo isProP_two_unitsPadicInt (mUnit α) (toAdd y).2.2.2)
    rw [mSign_add, zpowZtwo_add]
    exact mul_mul_mul_comm _ _ _ _

@[simp] theorem mChiModel_ofAdd (α : ℕ) (ε : ZMod 2) (b c d : ℤ_[2]) :
    mChiModel α (ofAdd (ε, b, c, d))
      = mSign b * zpowZtwo isProP_two_unitsPadicInt (mUnit α) d := rfl

theorem mChiModel_continuous (α : ℕ) : Continuous (mChiModel α) := by
  have hb : Continuous fun z : MModel => (toAdd z).2.1 :=
    continuous_fst.comp (continuous_snd.comp continuous_toAdd)
  have hd : Continuous fun z : MModel => (toAdd z).2.2.2 :=
    continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_toAdd))
  exact (mSign_continuous.comp hb).mul
    ((continuous_zpowZtwo isProP_two_unitsPadicInt (mUnit α)).comp hd)

/-- The model character bundled with its continuity. -/
noncomputable def mChiModelHom (α : ℕ) : ContinuousMonoidHom MModel ℤ_[2]ˣ :=
  ⟨mChiModel α, mChiModel_continuous α⟩

/-- The frame coordinate isomorphism as a continuous monoid hom. -/
noncomputable def mFrameHom {α : ℕ} (B : MDecomposition α) :
    ContinuousMonoidHom (topAbelianization (DM α 0 : Type)) MModel :=
  ⟨B.e.toMulEquiv.toMonoidHom, B.e.continuous_toFun⟩

@[simp] theorem mFrameHom_apply {α : ℕ} (B : MDecomposition α)
    (x : topAbelianization (DM α 0 : Type)) : mFrameHom B x = B.e x := rfl

/-- **The canonical orientation is the frame character** (memo §2.2(i), V3).  Every continuous
character of `D_M^{ab}` taking the pinned values `(1, −1, 1, u)` on the marked generators is
`mChiModel α` read through the frame.  (The classification therefore never needs a descended
`chiMab`: it works with an abstract `χ` and the four pins, exactly like
`prop_3_8_classification`.) -/
theorem mChi_frame {α : ℕ} (B : MDecomposition α)
    (χ : ContinuousMonoidHom (topAbelianization (DM α 0 : Type)) ℤ_[2]ˣ)
    (hχA : χ (abMk (dmA α 0)) = 1) (hχB : χ (abMk (dmB α 0)) = -1)
    (hχC : χ (abMk (dmC α 0)) = 1) (hχD : χ (abMk (dmD α 0)) = mUnit α)
    (x : topAbelianization (DM α 0 : Type)) : χ x = mChiModel α (B.e x) := by
  refine mAb_hom_ext χ ((mChiModelHom α).comp (mFrameHom B)) (fun i => ?_) x
  have hval : ∀ z : topAbelianization (DM α 0 : Type),
      ((mChiModelHom α).comp (mFrameHom B)) z = mChiModel α (B.e z) := fun _ => rfl
  rcases mCoreIdx_cases i with rfl | rfl | rfl | rfl
  · rw [hval, show dmGen α 0 0 = dmA α 0 from rfl, hχA, mE_A B, mChiModel_ofAdd, mSign_zero,
      zpowZtwo_zero, mul_one]
  · rw [hval, show dmGen α 0 1 = dmB α 0 from rfl, hχB, B.map_B, mChiModel_ofAdd,
      zpowZtwo_zero, mul_one]
    show (-1 : ℤ_[2]ˣ) = mSign 1
    rw [← mNegOne_zpow, zpowZtwo_one_exp]
  · rw [hval, show dmGen α 0 2 = dmC α 0 from rfl, hχC, B.map_C, mChiModel_ofAdd, mSign_zero,
      zpowZtwo_zero, mul_one]
  · rw [hval, show dmGen α 0 3 = dmD α 0 from rfl, hχD, B.map_D, mChiModel_ofAdd, mSign_zero,
      zpowZtwo_one_exp, one_mul]

/-! ### The torsion row -/

/-- **The 2-torsion of `D_M^{ab}` is `{1, t}`** (memo §2.2(ii)): the rank-four `sq_eq_one_iff`. -/
theorem mSqEqOne_iff {α : ℕ} (hα : 1 ≤ α) (B : MDecomposition α)
    (z : topAbelianization (DM α 0 : Type)) :
    z ^ 2 = 1 ↔ z = 1 ∨ z = abMk (dmA α 0 * dmC α 0 ^ (2 ^ (α - 1))) := by
  constructor
  · intro h
    have hBe : (B.e z) ^ 2 = 1 := by rw [← map_pow, h, map_one]
    have hcomp : (2 : ℕ) • (toAdd (B.e z)) = 0 := by
      have h' := congrArg toAdd hBe
      rwa [show toAdd ((B.e z) ^ 2) = (2 : ℕ) • (toAdd (B.e z)) from rfl] at h'
    have hkill : ∀ w : ℤ_[2], (2 : ℕ) • w = 0 → w = 0 := by
      intro w hw
      have hw' : (2 : ℤ_[2]) * w = 0 := by rw [← hw, nsmul_eq_mul]; norm_num
      exact (mul_eq_zero.mp hw').resolve_left (by norm_num)
    have hb : (toAdd (B.e z)).2.1 = 0 := by
      have := congrArg (fun p : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2] => p.2.1) hcomp
      simp only [Prod.smul_snd, Prod.smul_fst, Prod.snd_zero, Prod.fst_zero] at this
      exact hkill _ this
    have hc : (toAdd (B.e z)).2.2.1 = 0 := by
      have := congrArg (fun p : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2] => p.2.2.1) hcomp
      simp only [Prod.smul_snd, Prod.smul_fst, Prod.snd_zero, Prod.fst_zero] at this
      exact hkill _ this
    have hd : (toAdd (B.e z)).2.2.2 = 0 := by
      have := congrArg (fun p : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2] => p.2.2.2) hcomp
      simp only [Prod.smul_snd, Prod.snd_zero] at this
      exact hkill _ this
    rcases (by decide : ∀ e : ZMod 2, e = 0 ∨ e = 1) (toAdd (B.e z)).1 with hε | hε
    · left
      refine EquivLike.injective B.e ?_
      rw [map_one]
      exact (mCoord_ext hε hb hc hd).trans rfl
    · right
      refine EquivLike.injective B.e ?_
      rw [B.map_t]
      exact mCoord_ext hε hb hc hd
  · rintro (rfl | rfl)
    · exact one_pow 2
    · exact dm_torsionGen_sq hα 0

/-- **Every continuous automorphism of `D_M^{ab}` fixes `t`** (memo §2.2(ii)) — the rank-four
`xi_fixes_t`.  `t` is the unique element of order two, so the relation-vector clause of the
stabilizer is automatic on `L_M`. -/
theorem mXi_fixes_t {α : ℕ} (hα : 1 ≤ α) (B : MDecomposition α)
    (ξ : ContinuousMulEquiv (topAbelianization (DM α 0 : Type))
      (topAbelianization (DM α 0 : Type))) :
    ξ (abMk (dmA α 0 * dmC α 0 ^ (2 ^ (α - 1))))
      = abMk (dmA α 0 * dmC α 0 ^ (2 ^ (α - 1))) := by
  have ht2 : (abMk (dmA α 0 * dmC α 0 ^ (2 ^ (α - 1))) :
      topAbelianization (DM α 0 : Type)) ^ 2 = 1 := dm_torsionGen_sq hα 0
  have hξ2 : (ξ (abMk (dmA α 0 * dmC α 0 ^ (2 ^ (α - 1))))) ^ 2 = 1 := by
    rw [← map_pow, ht2, map_one]
  rcases (mSqEqOne_iff hα B _).mp hξ2 with h1 | ht
  · exfalso
    have hteq : (abMk (dmA α 0 * dmC α 0 ^ (2 ^ (α - 1))) :
        topAbelianization (DM α 0 : Type)) = 1 := by
      have hs := congrArg ξ.symm h1
      rwa [ContinuousMulEquiv.symm_apply_apply, map_one] at hs
    have hBet := congrArg B.e hteq
    rw [B.map_t, map_one] at hBet
    exact absurd (congrArg (fun z : MModel => (toAdd z).1) hBet) (by decide)
  · exact ht

end Frame

/-! ## §4 The mod-2 cup Gram, the stabilizer predicate, and the classification

The Gram matrix is memo §2.2(iii)/V4: reading the initial form of `P_M = A²[A,B]C₀^{2^α}[C₀,D]`,
the square `A²` gives the diagonal Bockstein entry, `[A,B]` and `[C₀,D]` give the two hyperbolic
pairs, and `C₀^{2^α}` gives **nothing** because `2^α ≡ 0 (mod 4)` for `α ≥ 2` (the mod-4 rule
that MC2's `diagCoeff_mod_four` isolates).  In the frame basis `(t, B̄, C̄₀, D̄)` — which reduces
mod 2 to the generator basis `(Ā, B̄, C̄₀, D̄)`, since `m = 2^{α−1}` is even — this is

```
G_M = [[1,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]],   α-independent.
```

**Variance.**  The cup form lives on `H¹`, on which an automorphism of `D_M` acts by
*pre*composition, i.e. by the transpose of its action on `H₁ = L_M/2L_M`.  The isometry
condition is therefore `M̄ᵀ·G_M·M̄ = G_M` on the mod-2 frame matrix `M̄` (rows = images of the
frame basis), not `M̄·G_M·M̄ᵀ`.  The two differ: the `τ`-parameter of memo §2.3 is free for the
transpose-side condition and would be forced to `0` by the other, so this variance choice is
what makes the memo's seven-parameter closed form come out.  `mCupIsometry_entry` writes the
`(i,j)` entry of `M̄ᵀ·G_M·M̄` in terms of the four rows, which is how the three Witt relations
are read off. -/

section Gram

open Multiplicative

/-- The frame basis of the rank-four `M`-frame, in the order `(t, B̄, C̄₀, D̄)`. -/
noncomputable def mFrameBasis (α : ℕ) : Fin 4 → topAbelianization (DM α 0 : Type) :=
  ![abMk (dmA α 0 * dmC α 0 ^ (2 ^ (α - 1))), abMk (dmB α 0), abMk (dmC α 0), abMk (dmD α 0)]

@[simp] theorem mFrameBasis_zero (α : ℕ) :
    mFrameBasis α 0 = abMk (dmA α 0 * dmC α 0 ^ (2 ^ (α - 1))) := rfl
@[simp] theorem mFrameBasis_one (α : ℕ) : mFrameBasis α 1 = abMk (dmB α 0) := rfl
@[simp] theorem mFrameBasis_two (α : ℕ) : mFrameBasis α 2 = abMk (dmC α 0) := rfl
@[simp] theorem mFrameBasis_three (α : ℕ) : mFrameBasis α 3 = abMk (dmD α 0) := rfl

/-- The mod-2 reduction of a frame coordinate vector: `L_M/2L_M = 𝔽₂⁴`. -/
noncomputable def mRedTwo (v : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2]) : Fin 4 → ZMod 2 :=
  ![v.1, mParityZ v.2.1, mParityZ v.2.2.1, mParityZ v.2.2.2]

@[simp] theorem mRedTwo_zero (v : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2]) : mRedTwo v 0 = v.1 := rfl
@[simp] theorem mRedTwo_one (v : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2]) :
    mRedTwo v 1 = mParityZ v.2.1 := rfl
@[simp] theorem mRedTwo_two (v : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2]) :
    mRedTwo v 2 = mParityZ v.2.2.1 := rfl
@[simp] theorem mRedTwo_three (v : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2]) :
    mRedTwo v 3 = mParityZ v.2.2.2 := rfl

/-- **The mod-2 cup Gram of the `M`-core** (memo §2.2(iii), V4) — α-independent for `α ≥ 2`. -/
def mGram : Matrix (Fin 4) (Fin 4) (ZMod 2) := !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

@[simp] theorem mGram_00 : mGram 0 0 = 1 := rfl
@[simp] theorem mGram_01 : mGram 0 1 = 1 := rfl
@[simp] theorem mGram_02 : mGram 0 2 = 0 := rfl
@[simp] theorem mGram_03 : mGram 0 3 = 0 := rfl
@[simp] theorem mGram_10 : mGram 1 0 = 1 := rfl
@[simp] theorem mGram_11 : mGram 1 1 = 0 := rfl
@[simp] theorem mGram_12 : mGram 1 2 = 0 := rfl
@[simp] theorem mGram_13 : mGram 1 3 = 0 := rfl
@[simp] theorem mGram_20 : mGram 2 0 = 0 := rfl
@[simp] theorem mGram_21 : mGram 2 1 = 0 := rfl
@[simp] theorem mGram_22 : mGram 2 2 = 0 := rfl
@[simp] theorem mGram_23 : mGram 2 3 = 1 := rfl
@[simp] theorem mGram_30 : mGram 3 0 = 0 := rfl
@[simp] theorem mGram_31 : mGram 3 1 = 0 := rfl
@[simp] theorem mGram_32 : mGram 3 2 = 1 := rfl
@[simp] theorem mGram_33 : mGram 3 3 = 0 := rfl

/-- The mod-2 frame matrix of `ξ`: row `i` is the mod-2 reduction of the frame coordinates of
the image of the `i`-th frame basis vector. -/
noncomputable def mFrameMatrix {α : ℕ} (B : MDecomposition α)
    (ξ : ContinuousMulEquiv (topAbelianization (DM α 0 : Type))
      (topAbelianization (DM α 0 : Type))) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun i j => mRedTwo (toAdd (B.e (ξ (mFrameBasis α i)))) j

@[simp] theorem mFrameMatrix_apply {α : ℕ} (B : MDecomposition α)
    (ξ : ContinuousMulEquiv (topAbelianization (DM α 0 : Type))
      (topAbelianization (DM α 0 : Type))) (i j : Fin 4) :
    mFrameMatrix B ξ i j = mRedTwo (toAdd (B.e (ξ (mFrameBasis α i)))) j := rfl

/-- **The `(i,j)` entry of `M̄ᵀ·G_M·M̄` in terms of the four rows of `M̄`.**  This is where the
`H¹`-variance is cashed out: the entry pairs the `i`-th and `j`-th **columns** of the frame
matrix under `G_M`. -/
theorem mCupIsometry_entry {α : ℕ} (B : MDecomposition α)
    (ξ : ContinuousMulEquiv (topAbelianization (DM α 0 : Type))
      (topAbelianization (DM α 0 : Type))) (i j : Fin 4) :
    ((mFrameMatrix B ξ).transpose * mGram * mFrameMatrix B ξ) i j
      = mFrameMatrix B ξ 0 i * mFrameMatrix B ξ 0 j
        + mFrameMatrix B ξ 0 i * mFrameMatrix B ξ 1 j
        + mFrameMatrix B ξ 1 i * mFrameMatrix B ξ 0 j
        + mFrameMatrix B ξ 2 i * mFrameMatrix B ξ 3 j
        + mFrameMatrix B ξ 3 i * mFrameMatrix B ξ 2 j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four, mGram_00, mGram_01,
    mGram_02, mGram_03, mGram_10, mGram_11, mGram_12, mGram_13, mGram_20, mGram_21, mGram_22,
    mGram_23, mGram_30, mGram_31, mGram_32, mGram_33]
  ring

/-- **The Smith–Witt stabilizer condition** (memo §2.3): χ-preservation plus the mod-2 cup
isometry.  The relation-vector clause is *automatic* on `L_M` — `mXi_fixes_t` — so it is not a
field here. -/
def IsMStabilizer {α : ℕ} (B : MDecomposition α)
    (χ : ContinuousMonoidHom (topAbelianization (DM α 0 : Type)) ℤ_[2]ˣ)
    (ξ : ContinuousMulEquiv (topAbelianization (DM α 0 : Type))
      (topAbelianization (DM α 0 : Type))) : Prop :=
  (∀ x, χ (ξ x) = χ x)
    ∧ (mFrameMatrix B ξ).transpose * mGram * mFrameMatrix B ξ = mGram

/-- **The seven parameters of `St_M`** (memo §2.3): `(τ, β, B_c, c₁, γ, d₁, e)`.  The
`t`-component of `φ(D̄)` is **not** an eighth parameter — the Witt coupling pins it to
`B_c mod 2`, and the `t`-component of `φ(C̄₀)` is pinned to `0`. -/
@[ext] structure MStabParam where
  /-- `τ`: the `t`-component of `φ(B̄)`. -/
  tau : ZMod 2
  /-- `β`: the `B̄`-component of `φ(B̄)`; a **unit**, forced by the χ-condition. -/
  beta : ℤ_[2]ˣ
  /-- `B_c`: the `C̄₀`-component of `φ(B̄)`; its parity is the coupled `t`-component of `φ(D̄)`. -/
  bc : ℤ_[2]
  /-- `c₁`: half the `B̄`-component of `φ(C̄₀)` (that component is even, forced by χ). -/
  c1 : ℤ_[2]
  /-- `γ`: the `C̄₀`-component of `φ(C̄₀)`; a **unit**, forced by the Witt condition. -/
  gamma : ℤ_[2]ˣ
  /-- `d₁`: half the `B̄`-component of `φ(D̄)` (even, forced by χ). -/
  d1 : ℤ_[2]
  /-- `e`: the `C̄₀`-component of `φ(D̄)`. -/
  e : ℤ_[2]

/-- `ξ` acts on the frame by the memo §2.3 closed form with parameter `p`. -/
def MStabParam.Realizes {α : ℕ} (p : MStabParam) (B : MDecomposition α)
    (ξ : ContinuousMulEquiv (topAbelianization (DM α 0 : Type))
      (topAbelianization (DM α 0 : Type))) : Prop :=
  B.e (ξ (abMk (dmB α 0))) = ofAdd (p.tau, (p.beta : ℤ_[2]), p.bc, 0)
    ∧ B.e (ξ (abMk (dmC α 0))) = ofAdd (0, 2 * p.c1, (p.gamma : ℤ_[2]), 0)
    ∧ B.e (ξ (abMk (dmD α 0))) = ofAdd (mParityZ p.bc, 2 * p.d1, p.e, 1)

/-- **The χ-row extraction in the frame** (memo §2.3): a χ-preserving automorphism has, on every
frame vector, its `B̄`-parity and its `D̄`-component pinned by the χ-value of the source. -/
theorem mChi_row {α : ℕ} (hα : 2 ≤ α) (B : MDecomposition α)
    (χ : ContinuousMonoidHom (topAbelianization (DM α 0 : Type)) ℤ_[2]ˣ)
    (hχA : χ (abMk (dmA α 0)) = 1) (hχB : χ (abMk (dmB α 0)) = -1)
    (hχC : χ (abMk (dmC α 0)) = 1) (hχD : χ (abMk (dmD α 0)) = mUnit α)
    (ξ : ContinuousMulEquiv (topAbelianization (DM α 0 : Type))
      (topAbelianization (DM α 0 : Type))) (hpres : ∀ x, χ (ξ x) = χ x)
    (x : topAbelianization (DM α 0 : Type)) (ε : ZMod 2) (w : ℤ_[2])
    (hx : χ x = (-1 : ℤ_[2]ˣ) ^ ε.val * zpowZtwo isProP_two_unitsPadicInt (mUnit α) w) :
    mParityZ (toAdd (B.e (ξ x))).2.1 = ε ∧ (toAdd (B.e (ξ x))).2.2.2 = w := by
  refine mChi_row_extract hα ?_
  show mChiModel α (B.e (ξ x))
    = (-1 : ℤ_[2]ˣ) ^ ε.val * zpowZtwo isProP_two_unitsPadicInt (mUnit α) w
  rw [← hx, ← hpres x]
  exact (mChi_frame B χ hχA hχB hχC hχD (ξ x)).symm

/-- **The classification of `St_M`** (memo §2.3, packet §14).  Every continuous automorphism of
`D_M^{ab}` that preserves the canonical orientation and the mod-2 cup Gram is given in the frame
by the memo's closed form, with a **unique** seven-tuple `(τ, β, B_c, c₁, γ, d₁, e)`; the
`t`-row is `t ↦ t`, the `t`-component of `φ(C̄₀)` vanishes, and the `t`-component of `φ(D̄)` is
the **Witt coupling** `B_c mod 2`.  Pure `ℤ₂`/`𝔽₂` linear algebra: unconditional, axiom-free,
and uniform in `α ≥ 2` (α enters only through the forced `Ā`-row `Ā = t − 2^{α−1}C̄₀`). -/
theorem mStabilizer_classification {α : ℕ} (hα : 2 ≤ α) (B : MDecomposition α)
    (χ : ContinuousMonoidHom (topAbelianization (DM α 0 : Type)) ℤ_[2]ˣ)
    (hχA : χ (abMk (dmA α 0)) = 1) (hχB : χ (abMk (dmB α 0)) = -1)
    (hχC : χ (abMk (dmC α 0)) = 1) (hχD : χ (abMk (dmD α 0)) = mUnit α)
    (ξ : ContinuousMulEquiv (topAbelianization (DM α 0 : Type))
      (topAbelianization (DM α 0 : Type)))
    (hξ : IsMStabilizer B χ ξ) : ∃! p : MStabParam, p.Realizes B ξ := by
  obtain ⟨hpres, hcup⟩ := hξ
  have hα1 : 1 ≤ α := le_trans (by norm_num) hα
  -- the three χ-rows
  obtain ⟨hBb, hBd⟩ := mChi_row hα B χ hχA hχB hχC hχD ξ hpres (abMk (dmB α 0)) 1 0 (by
    rw [hχB, zpowZtwo_zero, mul_one, show ((1 : ZMod 2)).val = 1 from rfl, pow_one])
  obtain ⟨hCb, hCd⟩ := mChi_row hα B χ hχA hχB hχC hχD ξ hpres (abMk (dmC α 0)) 0 0 (by
    rw [hχC, zpowZtwo_zero, mul_one, show ((0 : ZMod 2)).val = 0 from rfl, pow_zero])
  obtain ⟨hDb, hDd⟩ := mChi_row hα B χ hχA hχB hχC hχD ξ hpres (abMk (dmD α 0)) 0 1 (by
    rw [hχD, zpowZtwo_one_exp, show ((0 : ZMod 2)).val = 0 from rfl, pow_zero, one_mul])
  -- the `t`-row
  have hT : B.e (ξ (mFrameBasis α 0)) = ofAdd ((1 : ZMod 2), (0 : ℤ_[2]), 0, 0) := by
    rw [mFrameBasis_zero, mXi_fixes_t hα1 B ξ, B.map_t]
  -- the mod-2 frame matrix, row by row
  have hM0 : ∀ j, mFrameMatrix B ξ 0 j = ![(1 : ZMod 2), 0, 0, 0] j := by
    intro j
    rw [mFrameMatrix_apply, hT]
    fin_cases j <;> simp [mRedTwo]
  have hM1 : ∀ j, mFrameMatrix B ξ 1 j
      = ![(toAdd (B.e (ξ (abMk (dmB α 0))))).1, 1,
          mParityZ (toAdd (B.e (ξ (abMk (dmB α 0))))).2.2.1, 0] j := by
    intro j
    rw [mFrameMatrix_apply, mFrameBasis_one]
    fin_cases j <;> simp [mRedTwo, hBb, hBd]
  have hM2 : ∀ j, mFrameMatrix B ξ 2 j
      = ![(toAdd (B.e (ξ (abMk (dmC α 0))))).1, 0,
          mParityZ (toAdd (B.e (ξ (abMk (dmC α 0))))).2.2.1, 0] j := by
    intro j
    rw [mFrameMatrix_apply, mFrameBasis_two]
    fin_cases j <;> simp [mRedTwo, hCb, hCd]
  have hM3 : ∀ j, mFrameMatrix B ξ 3 j
      = ![(toAdd (B.e (ξ (abMk (dmD α 0))))).1, 0,
          mParityZ (toAdd (B.e (ξ (abMk (dmD α 0))))).2.2.1, 1] j := by
    intro j
    rw [mFrameMatrix_apply, mFrameBasis_three]
    fin_cases j <;> simp [mRedTwo, hDb, hDd]
  -- the three Witt relations
  have hentry : ∀ i j : Fin 4,
      mFrameMatrix B ξ 0 i * mFrameMatrix B ξ 0 j + mFrameMatrix B ξ 0 i * mFrameMatrix B ξ 1 j
        + mFrameMatrix B ξ 1 i * mFrameMatrix B ξ 0 j
        + mFrameMatrix B ξ 2 i * mFrameMatrix B ξ 3 j
        + mFrameMatrix B ξ 3 i * mFrameMatrix B ξ 2 j = mGram i j := fun i j => by
    rw [← mCupIsometry_entry B ξ i j, hcup]
  have hC0 : (toAdd (B.e (ξ (abMk (dmC α 0))))).1 = 0 := by
    have h := hentry 0 3
    rw [hM0 0, hM0 3, hM1 3, hM1 0, hM2 0, hM2 3, hM3 0, hM3 3] at h
    simpa [mGram] using h
  have hGamma : mParityZ (toAdd (B.e (ξ (abMk (dmC α 0))))).2.2.1 = 1 := by
    have h := hentry 2 3
    rw [hM0 2, hM0 3, hM1 3, hM1 2, hM2 2, hM2 3, hM3 2, hM3 3] at h
    simpa [mGram] using h
  have hCouple : (toAdd (B.e (ξ (abMk (dmD α 0))))).1
      = mParityZ (toAdd (B.e (ξ (abMk (dmB α 0))))).2.2.1 := by
    have h := hentry 0 2
    rw [hM0 0, hM0 2, hM1 2, hM1 0, hM2 0, hM2 2, hM3 0, hM3 2] at h
    rw [hC0, hGamma] at h
    exact (by decide : ∀ x y : ZMod 2, x + y = 0 → y = x) _ _ (by simpa [mGram] using h)
  -- the parameters
  obtain ⟨βu, hβu⟩ : ∃ u : ℤ_[2]ˣ, (u : ℤ_[2]) = (toAdd (B.e (ξ (abMk (dmB α 0))))).2.1 :=
    ⟨(mIsUnit_of_parity_one hBb).unit, IsUnit.unit_spec _⟩
  obtain ⟨γu, hγu⟩ : ∃ u : ℤ_[2]ˣ, (u : ℤ_[2]) = (toAdd (B.e (ξ (abMk (dmC α 0))))).2.2.1 :=
    ⟨(mIsUnit_of_parity_one hGamma).unit, IsUnit.unit_spec _⟩
  obtain ⟨c1, hc1⟩ := (mParityZ_eq_zero_iff _).mp hCb
  obtain ⟨d1, hd1⟩ := (mParityZ_eq_zero_iff _).mp hDb
  refine ⟨⟨(toAdd (B.e (ξ (abMk (dmB α 0))))).1, βu,
      (toAdd (B.e (ξ (abMk (dmB α 0))))).2.2.1, c1, γu, d1,
      (toAdd (B.e (ξ (abMk (dmD α 0))))).2.2.1⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact mCoord_ext rfl hβu.symm rfl hBd
  · exact mCoord_ext hC0 hc1 hγu.symm hCd
  · exact mCoord_ext hCouple hd1 rfl hDd
  · rintro q ⟨hq1, hq2, hq3⟩
    have e1 := hq1.symm.trans (mCoord_ext (z := B.e (ξ (abMk (dmB α 0)))) rfl hβu.symm rfl hBd)
    have e2 := hq2.symm.trans (mCoord_ext (z := B.e (ξ (abMk (dmC α 0)))) hC0 hc1 hγu.symm hCd)
    have e3 := hq3.symm.trans (mCoord_ext (z := B.e (ξ (abMk (dmD α 0)))) hCouple hd1 rfl hDd)
    have htwo : (2 : ℤ_[2]) ≠ 0 := by norm_num
    refine MStabParam.ext (congrArg (fun z : MModel => (toAdd z).1) e1)
      (Units.ext (congrArg (fun z : MModel => (toAdd z).2.1) e1))
      (congrArg (fun z : MModel => (toAdd z).2.2.1) e1)
      (mul_left_cancel₀ htwo (congrArg (fun z : MModel => (toAdd z).2.1) e2))
      (Units.ext (congrArg (fun z : MModel => (toAdd z).2.2.1) e2))
      (mul_left_cancel₀ htwo (congrArg (fun z : MModel => (toAdd z).2.1) e3))
      (congrArg (fun z : MModel => (toAdd z).2.2.1) e3)

/-- **The forced `Ā`-row of a stabilizer element** (memo §2.3, "α enters only through the
dictionary `Ā = t − mC̄₀`"): `Ā ↦ (1, −2^α c₁, −2^{α−1}γ, 0)`. -/
theorem mStabilizer_A_row {α : ℕ} (hα : 1 ≤ α) (B : MDecomposition α) {p : MStabParam}
    (ξ : ContinuousMulEquiv (topAbelianization (DM α 0 : Type))
      (topAbelianization (DM α 0 : Type))) (hp : p.Realizes B ξ) :
    B.e (ξ (abMk (dmA α 0)))
      = ofAdd ((1 : ZMod 2), -(2 : ℤ_[2]) ^ (α - 1) * (2 * p.c1),
          -(2 : ℤ_[2]) ^ (α - 1) * (p.gamma : ℤ_[2]), 0) := by
  have hAdec : (abMk (dmA α 0) : topAbelianization (DM α 0 : Type))
      = abMk (dmA α 0 * dmC α 0 ^ (2 ^ (α - 1))) * ((abMk (dmC α 0)) ^ (2 ^ (α - 1)))⁻¹ := by
    rw [map_mul, map_pow, mul_inv_cancel_right]
  rw [hAdec, map_mul, map_inv, map_pow, mXi_fixes_t hα B ξ, map_mul, map_inv, map_pow,
    B.map_t, hp.2.1, ← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
  refine congrArg ofAdd (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · show (1 : ZMod 2) + -((2 ^ (α - 1) : ℕ) • (0 : ZMod 2)) = 1
    rw [smul_zero, neg_zero, add_zero]
  · show (0 : ℤ_[2]) + -((2 ^ (α - 1) : ℕ) • (2 * p.c1)) = -(2 : ℤ_[2]) ^ (α - 1) * (2 * p.c1)
    rw [nsmul_eq_mul]
    push_cast
    ring
  · show (0 : ℤ_[2]) + -((2 ^ (α - 1) : ℕ) • (p.gamma : ℤ_[2]))
      = -(2 : ℤ_[2]) ^ (α - 1) * (p.gamma : ℤ_[2])
    rw [nsmul_eq_mul]
    push_cast
    ring
  · show (0 : ℤ_[2]) + -((2 ^ (α - 1) : ℕ) • (0 : ℤ_[2])) = 0
    rw [smul_zero, neg_zero, add_zero]

end Gram

/-! ## §5 The seven Nielsen families and the factorization

Memo §2.4's table, as elements of `MStabParam`, together with the completeness statement:
*every* stabilizer parameter's frame action is a composite of the seven.  The order used is
`Σ_γ, Λ_k, X_b, E_e, Σ_β, Y_c, Z_d` (leftmost applied first) — the `C̄₀`-writing families first,
then the `B̄`-writing ones, so that the `C̄₀`-writers still read the untouched `B̄`-coordinate.
The parameter *adjustments* (`b₅ = B_c + k·2^{α−1}`, `c₆ = c₁·γ⁻¹`, `β₄ = β − 2c₆B_c`,
`d₇ = d₁ − c₆e`) are exactly the memo's "each step kills one parameter and perturbs only
parameters killed later"; the corrections are all even, so `β₄` is still a unit.

`MStabParam.act` is the closed form as a map on frame coordinate vectors, and
`act_t`/`act_B`/`act_C`/`act_D` check that it reproduces the four rows of
`MStabParam.Realizes` on the nose — so the factorization below really is a statement about the
frame action of the classified automorphism. -/

section Nielsen

open Multiplicative

theorem mParityZ_neg (x : ℤ_[2]) : mParityZ (-x) = mParityZ x := by
  have h := mParityZ_add x (-x)
  rw [add_neg_cancel, mParityZ_zero] at h
  exact (by decide : ∀ a b : ZMod 2, 0 = a + b → b = a) _ _ h

theorem mParityZ_sub (x y : ℤ_[2]) : mParityZ (x - y) = mParityZ x + mParityZ y := by
  rw [sub_eq_add_neg, mParityZ_add, mParityZ_neg]

theorem mParityZ_natCast_val (ε : ZMod 2) : mParityZ ((ε.val : ℤ_[2])) = ε := by
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) ε with rfl | rfl
  · rw [show ((0 : ZMod 2).val : ℤ_[2]) = 0 by rw [show ((0 : ZMod 2).val) = 0 from rfl,
      Nat.cast_zero], mParityZ_zero]
  · rw [show ((1 : ZMod 2).val : ℤ_[2]) = 1 by rw [show ((1 : ZMod 2).val) = 1 from rfl,
      Nat.cast_one], mParityZ_one]

/-- `2^{α−1}` is even for `α ≥ 2` — the reason `Λ_k`'s `C̄₀`-shift is invisible mod 2, and hence
the reason the `M1` family does not disturb the Witt coupling. -/
theorem mParityZ_mul_two_pow {α : ℕ} (hα : 2 ≤ α) (k : ℤ_[2]) :
    mParityZ (k * 2 ^ (α - 1)) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, α - 1 = j + 1 := ⟨α - 2, by omega⟩
  rw [hj, pow_succ, show k * (2 ^ j * 2) = 2 * (k * 2 ^ j) by ring, mParityZ_two_mul]

/-- **The frame action of a stabilizer parameter** — the memo §2.3 closed form as a map on
coordinate vectors `(τ_v, b, c, d)` in the basis `(t, B̄, C̄₀, D̄)`.  The `t`-slot is `ZMod 2`, so
the `B̄`- and `D̄`-coefficients enter it only through their parities. -/
noncomputable def MStabParam.act (p : MStabParam) (v : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2]) :
    ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2] :=
  (v.1 + mParityZ v.2.1 * p.tau + mParityZ v.2.2.2 * mParityZ p.bc,
   v.2.1 * (p.beta : ℤ_[2]) + v.2.2.1 * (2 * p.c1) + v.2.2.2 * (2 * p.d1),
   v.2.1 * p.bc + v.2.2.1 * (p.gamma : ℤ_[2]) + v.2.2.2 * p.e,
   v.2.2.2)

theorem MStabParam.act_apply (p : MStabParam) (v1 : ZMod 2) (b c d : ℤ_[2]) :
    p.act (v1, b, c, d)
      = (v1 + mParityZ b * p.tau + mParityZ d * mParityZ p.bc,
         b * (p.beta : ℤ_[2]) + c * (2 * p.c1) + d * (2 * p.d1),
         b * p.bc + c * (p.gamma : ℤ_[2]) + d * p.e, d) := rfl

theorem MStabParam.act_t (p : MStabParam) :
    p.act ((1 : ZMod 2), 0, 0, 0) = ((1 : ZMod 2), 0, 0, 0) := by
  rw [MStabParam.act_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · show (1 : ZMod 2) + mParityZ 0 * p.tau + mParityZ 0 * mParityZ p.bc = 1
    rw [mParityZ_zero]
    ring
  · show (0 : ℤ_[2]) * _ + 0 * _ + 0 * _ = 0
    ring
  · show (0 : ℤ_[2]) * _ + 0 * _ + 0 * _ = 0
    ring

theorem MStabParam.act_B (p : MStabParam) :
    p.act ((0 : ZMod 2), 1, 0, 0) = (p.tau, (p.beta : ℤ_[2]), p.bc, 0) := by
  rw [MStabParam.act_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · show (0 : ZMod 2) + mParityZ 1 * p.tau + mParityZ 0 * mParityZ p.bc = p.tau
    rw [mParityZ_zero, mParityZ_one]
    ring
  · show (1 : ℤ_[2]) * _ + 0 * _ + 0 * _ = _
    ring
  · show (1 : ℤ_[2]) * _ + 0 * _ + 0 * _ = _
    ring

theorem MStabParam.act_C (p : MStabParam) :
    p.act ((0 : ZMod 2), 0, 1, 0) = (0, 2 * p.c1, (p.gamma : ℤ_[2]), 0) := by
  rw [MStabParam.act_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · show (0 : ZMod 2) + mParityZ 0 * p.tau + mParityZ 0 * mParityZ p.bc = 0
    rw [mParityZ_zero]
    ring
  · show (0 : ℤ_[2]) * _ + 1 * _ + 0 * _ = _
    ring
  · show (0 : ℤ_[2]) * _ + 1 * _ + 0 * _ = _
    ring

theorem MStabParam.act_D (p : MStabParam) :
    p.act ((0 : ZMod 2), 0, 0, 1) = (mParityZ p.bc, 2 * p.d1, p.e, 1) := by
  rw [MStabParam.act_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · show (0 : ZMod 2) + mParityZ 0 * p.tau + mParityZ 1 * mParityZ p.bc = mParityZ p.bc
    rw [mParityZ_zero, mParityZ_one]
    ring
  · show (0 : ℤ_[2]) * _ + 0 * _ + 1 * _ = _
    ring
  · show (0 : ℤ_[2]) * _ + 0 * _ + 1 * _ = _
    ring

/-- Family **M1**, `Λ_k : B ↦ A^k·B` (memo §2.4, stratum **S1**): frame action `τ = k mod 2`,
`B_c = −k·2^{α−1}`. -/
noncomputable def mFamM1 (α : ℕ) (k : ℤ_[2]) : MStabParam :=
  ⟨mParityZ k, 1, -(k * 2 ^ (α - 1)), 0, 1, 0, 0⟩

/-- Family **M2**, `E_e : D ↦ C₀^e·D` (memo §2.4, stratum **S1**; this is HM4's
`dmTauDEquiv`). -/
noncomputable def mFamM2 (e : ℤ_[2]) : MStabParam := ⟨0, 1, 0, 0, 1, 0, e⟩

/-- Family **M3**, `Σ_γ : C₀ ↦ C₀^γ`, `A ↦ A·C₀^{m(1−γ)}` (memo §2.4, stratum **S2**, B8). -/
noncomputable def mFamM3 (γ : ℤ_[2]ˣ) : MStabParam := ⟨0, 1, 0, 0, γ, 0, 0⟩

/-- Family **M4**, `Σ_β : B ↦ B^β` (memo §2.4, stratum **S3**). -/
noncomputable def mFamM4 (β : ℤ_[2]ˣ) : MStabParam := ⟨0, β, 0, 0, 1, 0, 0⟩

/-- Family **M5**, `X_b : B ↦ B·C₀^{B_c}`, `D ↦ t^{B_c}·D` (memo §2.4, stratum **S3**) — the
family that carries the Witt coupling. -/
noncomputable def mFamM5 (bc : ℤ_[2]) : MStabParam := ⟨0, 1, bc, 0, 1, 0, 0⟩

/-- Family **M6**, `Y_c : C₀ ↦ B^{2c₁}·C₀` (memo §2.4, stratum **S3**). -/
noncomputable def mFamM6 (c1 : ℤ_[2]) : MStabParam := ⟨0, 1, 0, c1, 1, 0, 0⟩

/-- Family **M7**, `Z_d : D ↦ B^{2d₁}·D` (memo §2.4, stratum **S3**). -/
noncomputable def mFamM7 (d1 : ℤ_[2]) : MStabParam := ⟨0, 1, 0, 0, 1, d1, 0⟩

theorem mFamM1_act {α : ℕ} (hα : 2 ≤ α) (k : ℤ_[2]) (v1 : ZMod 2) (b c d : ℤ_[2]) :
    (mFamM1 α k).act (v1, b, c, d)
      = (v1 + mParityZ b * mParityZ k, b, c - k * 2 ^ (α - 1) * b, d) := by
  rw [mFamM1, MStabParam.act_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · show v1 + mParityZ b * mParityZ k + mParityZ d * mParityZ (-(k * 2 ^ (α - 1))) = _
    rw [mParityZ_neg, mParityZ_mul_two_pow hα]
    ring
  · show b * ((1 : ℤ_[2]ˣ) : ℤ_[2]) + c * (2 * 0) + d * (2 * 0) = b
    rw [Units.val_one]
    ring
  · show b * -(k * 2 ^ (α - 1)) + c * ((1 : ℤ_[2]ˣ) : ℤ_[2]) + d * 0 = _
    rw [Units.val_one]
    ring

theorem mFamM2_act (e : ℤ_[2]) (v1 : ZMod 2) (b c d : ℤ_[2]) :
    (mFamM2 e).act (v1, b, c, d) = (v1, b, c + d * e, d) := by
  rw [mFamM2, MStabParam.act_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · show v1 + mParityZ b * 0 + mParityZ d * mParityZ 0 = v1
    rw [mParityZ_zero]
    ring
  · show b * ((1 : ℤ_[2]ˣ) : ℤ_[2]) + c * (2 * 0) + d * (2 * 0) = b
    rw [Units.val_one]
    ring
  · show b * 0 + c * ((1 : ℤ_[2]ˣ) : ℤ_[2]) + d * e = _
    rw [Units.val_one]
    ring

theorem mFamM3_act (γ : ℤ_[2]ˣ) (v1 : ZMod 2) (b c d : ℤ_[2]) :
    (mFamM3 γ).act (v1, b, c, d) = (v1, b, c * (γ : ℤ_[2]), d) := by
  rw [mFamM3, MStabParam.act_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · show v1 + mParityZ b * 0 + mParityZ d * mParityZ 0 = v1
    rw [mParityZ_zero]
    ring
  · show b * ((1 : ℤ_[2]ˣ) : ℤ_[2]) + c * (2 * 0) + d * (2 * 0) = b
    rw [Units.val_one]
    ring
  · show b * 0 + c * (γ : ℤ_[2]) + d * 0 = _
    ring

theorem mFamM4_act (β : ℤ_[2]ˣ) (v1 : ZMod 2) (b c d : ℤ_[2]) :
    (mFamM4 β).act (v1, b, c, d) = (v1, b * (β : ℤ_[2]), c, d) := by
  rw [mFamM4, MStabParam.act_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · show v1 + mParityZ b * 0 + mParityZ d * mParityZ 0 = v1
    rw [mParityZ_zero]
    ring
  · show b * (β : ℤ_[2]) + c * (2 * 0) + d * (2 * 0) = _
    ring
  · show b * 0 + c * ((1 : ℤ_[2]ˣ) : ℤ_[2]) + d * 0 = c
    rw [Units.val_one]
    ring

theorem mFamM5_act (bc : ℤ_[2]) (v1 : ZMod 2) (b c d : ℤ_[2]) :
    (mFamM5 bc).act (v1, b, c, d) = (v1 + mParityZ d * mParityZ bc, b, b * bc + c, d) := by
  rw [mFamM5, MStabParam.act_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · show v1 + mParityZ b * 0 + mParityZ d * mParityZ bc = _
    ring
  · show b * ((1 : ℤ_[2]ˣ) : ℤ_[2]) + c * (2 * 0) + d * (2 * 0) = b
    rw [Units.val_one]
    ring
  · show b * bc + c * ((1 : ℤ_[2]ˣ) : ℤ_[2]) + d * 0 = _
    rw [Units.val_one]
    ring

theorem mFamM6_act (c1 : ℤ_[2]) (v1 : ZMod 2) (b c d : ℤ_[2]) :
    (mFamM6 c1).act (v1, b, c, d) = (v1, b + c * (2 * c1), c, d) := by
  rw [mFamM6, MStabParam.act_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · show v1 + mParityZ b * 0 + mParityZ d * mParityZ 0 = v1
    rw [mParityZ_zero]
    ring
  · show b * ((1 : ℤ_[2]ˣ) : ℤ_[2]) + c * (2 * c1) + d * (2 * 0) = _
    rw [Units.val_one]
    ring
  · show b * 0 + c * ((1 : ℤ_[2]ˣ) : ℤ_[2]) + d * 0 = c
    rw [Units.val_one]
    ring

theorem mFamM7_act (d1 : ℤ_[2]) (v1 : ZMod 2) (b c d : ℤ_[2]) :
    (mFamM7 d1).act (v1, b, c, d) = (v1, b + d * (2 * d1), c, d) := by
  rw [mFamM7, MStabParam.act_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · show v1 + mParityZ b * 0 + mParityZ d * mParityZ 0 = v1
    rw [mParityZ_zero]
    ring
  · show b * ((1 : ℤ_[2]ˣ) : ℤ_[2]) + c * (2 * 0) + d * (2 * d1) = _
    rw [Units.val_one]
    ring
  · show b * 0 + c * ((1 : ℤ_[2]ˣ) : ℤ_[2]) + d * 0 = c
    rw [Units.val_one]
    ring

/-- **Completeness of the seven Nielsen families** (memo §2.4, packet §14).  Every element of
the Smith–Witt stabilizer — equivalently, by `mStabilizer_classification`, every parameter
`p : MStabParam` — has its frame action equal to a composite of the seven families
`Σ_γ, Λ_k, X_b, E_e, Σ_β, Y_c, Z_d`, applied in that order.  The witnesses are

```
γ₃ = γ,  k = τ.val,  b₅ = B_c + k·2^{α−1},  e₅ = e,
c₆ = c₁·γ⁻¹,  β₄ = β − 2c₆B_c,  d₇ = d₁ − c₆·e.
```

The order puts the `C̄₀`-writing families first so that they still read the untouched
`B̄`-coordinate; the adjustments are the memo's "each step perturbs only parameters killed
later", and all of them are even, so `β₄` is still a unit.  Unconditional and axiom-free;
`α ≥ 2` is used exactly once, to know `2^{α−1}` is even so that `Λ_k` does not disturb the
Witt coupling. -/
theorem mNielsen_factorization {α : ℕ} (hα : 2 ≤ α) (p : MStabParam) :
    ∃ (k b₅ e₅ c₆ d₇ : ℤ_[2]) (β₄ : ℤ_[2]ˣ),
      p.act = (mFamM7 d₇).act ∘ (mFamM6 c₆).act ∘ (mFamM4 β₄).act ∘ (mFamM2 e₅).act ∘
        (mFamM5 b₅).act ∘ (mFamM1 α k).act ∘ (mFamM3 p.gamma).act := by
  set k : ℤ_[2] := (p.tau.val : ℤ_[2]) with hkdef
  set c₆ : ℤ_[2] := p.c1 * ((p.gamma⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) with hc6def
  have hβ4 : mParityZ ((p.beta : ℤ_[2]) - 2 * (c₆ * p.bc)) = 1 := by
    rw [mParityZ_sub, mParityZ_two_mul, mParityZ_of_isUnit p.beta.isUnit, add_zero]
  have hγinv : (p.gamma : ℤ_[2]) * ((p.gamma⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hβ4val : (((mIsUnit_of_parity_one hβ4).unit : ℤ_[2]ˣ) : ℤ_[2])
      = (p.beta : ℤ_[2]) - 2 * (c₆ * p.bc) := IsUnit.unit_spec _
  refine ⟨k, p.bc + k * 2 ^ (α - 1), p.e, c₆, p.d1 - c₆ * p.e,
    (mIsUnit_of_parity_one hβ4).unit, ?_⟩
  funext v
  obtain ⟨v1, b, c, d⟩ := v
  rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, Function.comp_apply,
    Function.comp_apply, Function.comp_apply, mFamM3_act, mFamM1_act hα, mFamM5_act,
    mFamM2_act, mFamM4_act, mFamM6_act, mFamM7_act, MStabParam.act_apply, hβ4val]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · show v1 + mParityZ b * p.tau + mParityZ d * mParityZ p.bc = _
    rw [mParityZ_add, mParityZ_mul_two_pow hα, hkdef, mParityZ_natCast_val]
    ring
  · show b * (p.beta : ℤ_[2]) + c * (2 * p.c1) + d * (2 * p.d1) = _
    rw [hc6def]
    linear_combination (-(2 * c * p.c1)) * hγinv
  · show b * p.bc + c * (p.gamma : ℤ_[2]) + d * p.e = _
    ring

end Nielsen

/-! ## §6 The S1 lift: family M1 as an honest automorphism of `D_M`

Memo §2.5's `Λ_k : B ↦ A^k·B`, all other letters fixed.  The relator is preserved **exactly**,
for every 2-adic `k`: the peripheral head `w_M = A·A^B` has `A^{A^kB} = A^B` because `A`
commutes with its own 2-adic powers (`mCommute_zpowZtwo`, §1), and the `(C₀, D)`-half and the
handle block are untouched.  Axiom-free, at general `(α, h)`.

Family **M2** (`E_e : D ↦ C₀^e·D`) is *already* in the repo — it is HM4's `dmTauDEquiv`, with
frame action `dmRealizes_tauD` and χ-preservation `chiM_dmTauDEquiv` — so it is recorded here
(`mFamM2_eq_frameTauD`), not duplicated.  Families M3–M7 are strata S2/S3; see §7. -/

section Lambda

open Multiplicative

private theorem mCoreIdx_ne_one {h : ℕ} {i : Fin (coreRank h)} (hi : (i : ℕ) ≠ 1) :
    i ≠ (1 : Fin (coreRank h)) := by
  intro hc
  rw [hc, coreVal_one] at hi
  exact hi rfl

/-- **Structure of a one-slot update of the `M_α` relator at the letter `1`** — the `B`-slot
analogue of HM4's `mRelWord_update_three`. -/
theorem mRelWord_update_one {G : Type*} [Group G] {h : ℕ} (α : ℕ)
    (m : Fin (coreRank h) → G) (w : G) :
    mRelWord α (Function.update m 1 w)
      = mWord α (m 0) w (m 2) (m 3)
        * handleWord (fun i => m (handleIdxU i)) (fun i => m (handleIdxV i)) := by
  have hU : (fun i => Function.update m 1 w (handleIdxU i)) = fun i => m (handleIdxU i) :=
    funext fun i =>
      Function.update_of_ne (handleIdxU_ne_of_val_lt i (by rw [coreVal_one]; omega)) _ _
  have hV : (fun i => Function.update m 1 w (handleIdxV i)) = fun i => m (handleIdxV i) :=
    funext fun i =>
      Function.update_of_ne (handleIdxV_ne_of_val_lt i (by rw [coreVal_one]; omega)) _ _
  rw [mRelWord, Function.update_self, hU, hV,
    Function.update_of_ne (mCoreIdx_ne_one (by rw [coreVal_zero]; omega)),
    Function.update_of_ne (mCoreIdx_ne_one (by rw [coreVal_two]; omega)),
    Function.update_of_ne (mCoreIdx_ne_one (by rw [coreVal_three]; omega))]

section Mark

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P] {h : ℕ}

/-- `[a, a^k·b] = [a, b]`: the one-line identity behind family M1 (memo §2.5, "`A^{A^k} = A`"). -/
theorem mCommP_zpow_left (hP : IsProP 2 P) (a b : P) (k : ℤ_[2]) :
    commP a (zpowZtwo hP a k * b) = commP a b := by
  have hc : Commute a (zpowZtwo hP a k) := mCommute_zpowZtwo hP a k
  have hza : (zpowZtwo hP a k)⁻¹ * a * zpowZtwo hP a k = a := by
    rw [hc.symm.inv_left.eq, inv_mul_cancel_right]
  show a⁻¹ * (zpowZtwo hP a k * b)⁻¹ * a * (zpowZtwo hP a k * b) = a⁻¹ * b⁻¹ * a * b
  rw [mul_inv_rev]
  calc a⁻¹ * (b⁻¹ * (zpowZtwo hP a k)⁻¹) * a * (zpowZtwo hP a k * b)
      = a⁻¹ * b⁻¹ * ((zpowZtwo hP a k)⁻¹ * a * zpowZtwo hP a k) * b := by group
    _ = a⁻¹ * b⁻¹ * a * b := by rw [hza]

/-- **Family M1 fixes the `M_α` core word**: `mWord α a (a^k·b) c d = mWord α a b c d`. -/
theorem mWord_lambda (hP : IsProP 2 P) (α : ℕ) (a b c d : P) (k : ℤ_[2]) :
    mWord α a (zpowZtwo hP a k * b) c d = mWord α a b c d := by
  rw [mWord, mWord, mCommP_zpow_left]

/-- **Memo §2.5's `Λ_k`** as a substitution on markings: `B ↦ A^k·B`, exact for every 2-adic
`k`.  The `B`-slot analogue of HM4's `tauDMark`. -/
noncomputable def mLambdaMark (hP : IsProP 2 P) (k : ℤ_[2]) (m : Fin (coreRank h) → P) :
    Fin (coreRank h) → P :=
  Function.update m 1 (zpowZtwo hP (m 0) k * m 1)

variable (hP : IsProP 2 P) (k l : ℤ_[2]) (m : Fin (coreRank h) → P)

@[simp] theorem mLambdaMark_one : mLambdaMark hP k m 1 = zpowZtwo hP (m 0) k * m 1 :=
  Function.update_self _ _ _

theorem mLambdaMark_of_ne {i : Fin (coreRank h)} (hi : i ≠ 1) : mLambdaMark hP k m i = m i :=
  Function.update_of_ne hi _ _

@[simp] theorem mLambdaMark_zero_idx : mLambdaMark hP k m 0 = m 0 :=
  mLambdaMark_of_ne _ _ _ (mCoreIdx_ne_one (by rw [coreVal_zero]; omega))

theorem mLambdaMark_mLambdaMark :
    mLambdaMark hP k (mLambdaMark hP l m) = mLambdaMark hP (k + l) m := by
  funext i
  by_cases hi : i = 1
  · subst hi
    rw [mLambdaMark_one, mLambdaMark_zero_idx, mLambdaMark_one, mLambdaMark_one, zpowZtwo_add,
      mul_assoc]
  rw [mLambdaMark_of_ne _ _ _ hi, mLambdaMark_of_ne _ _ _ hi, mLambdaMark_of_ne _ _ _ hi]

@[simp] theorem mLambdaMark_zero : mLambdaMark hP (0 : ℤ_[2]) m = m := by
  funext i
  by_cases hi : i = 1
  · subst hi
    rw [mLambdaMark_one, zpowZtwo_zero_exp, one_mul]
  rw [mLambdaMark_of_ne _ _ _ hi]

/-- **`Λ_k` fixes the full `M_α` relator** — the handle block and the `(C₀, D)`-half are
untouched, and `mWord_lambda` handles the `(A, B)`-half. -/
theorem mRelWord_mLambdaMark (α : ℕ) : mRelWord α (mLambdaMark hP k m) = mRelWord α m := by
  rw [mLambdaMark, mRelWord_update_one, mWord_lambda hP, mRelWord]

/-- The ν-frame row of family **M1**: `B̄ ↦ B̄ + k·Ā` (memo §2.4's `Λ_k` row, additively). -/
noncomputable def mFrameLambda {n : ℕ} (c : ℤ_[2]) (v : Fin (coreRank n) → ℤ_[2]) :
    Fin (coreRank n) → ℤ_[2] :=
  Function.update v 1 (v 1 + c * v 0)

theorem nuFrame_mLambdaMark (f : ContinuousMonoidHom P (Multiplicative ℤ_[2])) :
    nuFrame f (mLambdaMark hP k m) = mFrameLambda k (nuFrame f m) := by
  funext i
  by_cases hi : i = 1
  · subst hi
    rw [nuFrame_apply, mLambdaMark_one, mFrameLambda, Function.update_self, map_mul, toAdd_mul,
      toAdd_map_zpowZtwo hP]
    show k • toAdd (f (m 0)) + toAdd (f (m 1)) = toAdd (f (m 1)) + k * toAdd (f (m 0))
    rw [smul_eq_mul, add_comm]
  rw [nuFrame_apply, mLambdaMark_of_ne _ _ _ hi, mFrameLambda, Function.update_of_ne hi,
    nuFrame_apply]

end Mark

section Natural

variable {P Q : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P] [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q] {h : ℕ}

theorem map_mLambdaMark (hP : IsProP 2 P) (hQ : IsProP 2 Q) (f : ContinuousMonoidHom P Q)
    (k : ℤ_[2]) (m : Fin (coreRank h) → P) (i : Fin (coreRank h)) :
    f (mLambdaMark hP k m i) = mLambdaMark hQ k (fun i => f (m i)) i := by
  by_cases hi : i = 1
  · subst hi
    rw [mLambdaMark_one, mLambdaMark_one, map_mul, map_zpowZtwo hP hQ]
  rw [mLambdaMark_of_ne _ _ _ hi, mLambdaMark_of_ne _ _ _ hi]

end Natural

/-- `Λ_k` on `D_M`, as a continuous endomorphism. -/
noncomputable def mLambdaHom (α h : ℕ) (k : ℤ_[2]) :
    ContinuousMonoidHom (DM α h : Type) (DM α h : Type) :=
  mLiftHom α h (isProP_DM α h) (mLambdaMark (isProP_DM α h) k (dmGen α h))
    (by rw [mRelWord_mLambdaMark]; exact dm_relation α h)

@[simp] theorem mLambdaHom_gen (α h : ℕ) (k : ℤ_[2]) (i : Fin (coreRank h)) :
    mLambdaHom α h k (dmGen α h i) = mLambdaMark (isProP_DM α h) k (dmGen α h) i :=
  mLiftHom_gen _ _ _ _ _ _

/-- **Family M1 as a continuous automorphism of `D_M`** (memo §2.5, stratum S1; axiom-free, at
general `(α, h)`).  The inverse is the member at `−k`. -/
noncomputable def mLambdaEquiv (α h : ℕ) (k : ℤ_[2]) :
    ContinuousMulEquiv (DM α h : Type) (DM α h : Type) :=
  dmParamEquiv α h (mLambdaHom α h) (mLambdaMark (isProP_DM α h)) (mLambdaHom_gen α h)
    (fun k f m i => map_mLambdaMark (isProP_DM α h) (isProP_DM α h) f k m i)
    (fun k l m => mLambdaMark_mLambdaMark _ k l m) (fun m => mLambdaMark_zero _ m) k

@[simp] theorem mLambdaEquiv_gen (α h : ℕ) (k : ℤ_[2]) (i : Fin (coreRank h)) :
    mLambdaEquiv α h k (dmGen α h i) = mLambdaMark (isProP_DM α h) k (dmGen α h) i :=
  mLambdaHom_gen α h k i

/-- **`Λ_k` preserves the canonical orientation** — `χ_M(A) = 1`, so the inserted `A^k` is
invisible.  Axiom-free; the M1 row of memo §2.4 therefore really does land in the stabilizer. -/
theorem chiM_mLambdaEquiv (α h : ℕ) (k : ℤ_[2]) (x : (DM α h : Type)) :
    chiM α h (mLambdaEquiv α h k x) = chiM α h x := by
  refine dm_char_fixed (chiM α h) (mLambdaEquiv α h k) (fun i => ?_) x
  rw [mLambdaEquiv_gen]
  by_cases hi : i = 1
  · subst hi
    rw [mLambdaMark_one, map_mul, map_zpowZtwo (isProP_DM α h) isProP_two_unitsPadicInt,
      show dmGen α h 0 = dmA α h from rfl, chiM_dmA, zpowZtwo_one_base, one_mul]
  rw [mLambdaMark_of_ne _ _ _ hi]

/-- **The ν-frame action of `Λ_k`**: `B̄ ↦ B̄ + k·Ā` (memo §2.4's M1 row). -/
theorem nuFrame_mLambdaEquiv (α h : ℕ) (k : ℤ_[2])
    (f : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2])) :
    nuFrame f (fun i => mLambdaEquiv α h k (dmGen α h i))
      = mFrameLambda k (nuFrame f (dmGen α h)) := by
  rw [← nuFrame_mLambdaMark (isProP_DM α h)]
  exact congrArg (nuFrame f) (funext fun i => mLambdaEquiv_gen α h k i)

/-- **Family M2 is HM4's `dmTauDEquiv`** — recorded, not duplicated: `E_e : D ↦ C₀^e·D` is the
`τ_c(e)` transvection, its ν-frame row is `frameTauD e`, and it preserves `χ_M`. -/
theorem mFamM2_eq_frameTauD (α h : ℕ) (e : ℤ_[2]) :
    DmRealizes α h (dmTauDEquiv α h e) (frameEnd (frameTauD e))
      ∧ ∀ x : (DM α h : Type), chiM α h (dmTauDEquiv α h e x) = chiM α h x :=
  ⟨dmRealizes_tauD α h e, chiM_dmTauDEquiv α h e⟩

end Lambda

/-! ## §7 The hypothesis binders (never axioms)

Two binders, both `def`s and both listed in `check_dyadic.sh`'s D2 obligation guard so that
they can never silently become axioms.

* `MLabHypothesis` (memo §6.4, G-Lab Decision 1) — Labute's classification of Demushkin groups
  of even rank with `q = 2`, specialised to the `M_α` core.  **Deviation from the rank-three
  `BLabHypothesis`** (`GQ2/Roe/MarkedPro2.lean:141`): there the hypothesis is specialised to
  the concrete presented group `D_R`; here the other side is `G_K(2)`, which is not presented,
  so the abstract-`G` form is forced (the memo's R6).  The orientation-canonicity clause is a
  **parameter** `mIsCanonical`, for two reasons — the repo has no abstract dualizing-module
  characterisation of the canonical orientation (`GQ2/Orientation.lean` deferral), and
  quantifying over *all* continuous characters with the stated image would be false, since
  `N_α` also admits characters whose image is `imChiM α` when `α` is small.  Consumers (MC5)
  instantiate the parameter with whatever descent characterisation their `G` supports.
* `MMixHypothesis` (memo §5.3/§8 Decision 2(B)) — the S3 core-mixing residue.

**Recorded finding: `DmRealizes` is scoped to the handle stratum.**  HM4's
`MCoreMixHypothesis α h S3` is `DmRealizesAll α h S3`, whose first clause demands that the
realizing automorphism lie in `Submonoid.closure (dmClearAuts α h)` — the **handle** generating
set.  Every generator of that monoid (`dmTauUEquiv`, `dmTauVEquiv`, `dmTauDEquiv`,
`dmMixEquiv`) fixes the letters `B` and `C₀` *pointwise*, so no element of it moves the `B̄`- or
`C̄₀`-row of a ν-frame vector: a core-stratum move is never realizable *through `DmRealizes` as
currently stated*, because such a move's realizing automorphism is a **new generator** rather
than a word in the handle ones.  (Ticket HM6 reports the same scoping trap and queues the
mechanical widenings HM6e/HM6f; ticket HM6 has since proved family **M5** outright, leaving
`⟨M4, M6, M7⟩` — the non-symplectic directions — as the structural residue.)

Consequently this file does **not** route any core-stratum piece through `DmRealizes`.
`MMixHypothesis` below demands χ-preservation directly — which is what the membership clause
was standing in for, since `chiM_of_mem_dmClearAuts` is exactly what consumers extract from it
— and `MCoreMixHypothesis`/`MLiftSplit` are threaded *literally*, unchanged, in
`prop_MC_M_correction_split`, so the downstream discharge composes with no reshaping here.
`mLiftSplit_of_handle` measures what the `MLiftSplit` contract gives for free: everything
inside the handle monoid is a *theorem* (`mLiftSplit_handle`). -/

section Binders

open Multiplicative

/-- **The `M_α` orientation image** `im χ_M = ⟨−1⟩ × ⟨(1−2^α)⁻¹⟩ = {±1}·(1 + 2^αℤ₂)` (memo
§2.2(i), packet §8 line 765's `C`).  This is the `M`/`N` separator: `im χ_N` is procyclic. -/
noncomputable def imChiM (α : ℕ) : Subgroup ℤ_[2]ˣ :=
  (Subgroup.closure ({-1, mUnit α} : Set ℤ_[2]ˣ)).topologicalClosure

theorem neg_one_mem_imChiM (α : ℕ) : (-1 : ℤ_[2]ˣ) ∈ imChiM α :=
  Subgroup.le_topologicalClosure _ (Subgroup.subset_closure (by simp))

theorem mUnit_mem_imChiM (α : ℕ) : mUnit α ∈ imChiM α :=
  Subgroup.le_topologicalClosure _ (Subgroup.subset_closure (by simp))

/-- **M-Lab (hypothesis form — never an axiom).**  Labute's classification of Demushkin groups
of even rank with `q = 2` (Labute 1967, Thm 8: such groups are separated by `(rank, q, im χ)`),
specialised to the `M_α` core of rank `coreRank h = 4 + 2h`.  See the §6 preamble for the two
deviations from `BLabHypothesis`. -/
def MLabHypothesis (α h : ℕ)
    (mIsCanonical : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
      (G →* ℤ_[2]ˣ) → Prop) : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G] [DistribMulAction G (ZMod 2)]
    [ContinuousSMul G (ZMod 2)],
    IsDemushkin 2 G → demushkinRank 2 G = coreRank h → demushkinQ G = 2 →
      (∃ χ : G →* ℤ_[2]ˣ, Continuous χ ∧ mIsCanonical G χ ∧ MonoidHom.range χ = imChiM α) →
        Nonempty (ContinuousMulEquiv G (DM α h : Type))

/-- **The S3 core-mixing residue as a hypothesis binder** (memo §5.3, §8 Decision 2(B);
a `def`, never an axiom).  Given a transported marking `ν'` that is already cleared on the
handle letters and unimodular on `C₀`, a χ-preserving automorphism of `D_M` carries `ν'` to the
standard marking `ν_M`.  This is the honest reshape of HM4's `MCoreMixHypothesis` — see the §6
preamble for why the literal form is unsatisfiable for every non-trivial core move. -/
def MMixHypothesis (α h : ℕ) (hα : 1 ≤ α) : Prop :=
  ∀ nu' : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2]),
    IsUnit (toAdd (nu' (dmC α h))) →
    (∀ j : Fin h, nu' (dmGen α h (handleIdxU j)) = 1) →
    (∀ j : Fin h, nu' (dmGen α h (handleIdxV j)) = 1) →
      ∃ Ψ : ContinuousMulEquiv (DM α h : Type) (DM α h : Type),
        (∀ x, chiM α h (Ψ x) = chiM α h x)
          ∧ ∀ i, nu' (Ψ (dmGen α h i)) = nuM α h hα (dmGen α h i)

/-- **How much of the `MLiftSplit` contract is free.**  Both stratum sets, as long as they lie
inside the handle monoid `Submonoid.closure (frameClearGens h)`, are covered by the HM lane's
theorem `mLiftSplit_handle` — no hypothesis at all.  In particular `MLiftSplit α h ∅ ∅` holds
unconditionally, and at `h = 0` the handle monoid is trivial, so this is the whole of it. -/
theorem mLiftSplit_of_handle (α h : ℕ)
    {S12 S3 : Set (Function.End (Fin (coreRank h) → ℤ_[2]))}
    (h12 : S12 ⊆ (Submonoid.closure (frameClearGens h) : Set _))
    (h3 : S3 ⊆ (Submonoid.closure (frameClearGens h) : Set _)) :
    MLiftSplit α h S12 S3 :=
  (mLiftSplit_iff α h S12 S3).mpr
    ⟨fun F hF => mLiftSplit_handle α h F (h12 hF), fun F hF => mLiftSplit_handle α h F (h3 hF)⟩

theorem mLiftSplit_empty (α h : ℕ) : MLiftSplit α h ∅ ∅ :=
  mLiftSplit_of_handle α h (Set.empty_subset _) (Set.empty_subset _)

end Binders

/-! ## §8 The correction assembly — the MC-M obligation

Packet Prop. 7.2 at the `M`-core, in the shape memo §6.3 calls `hLift`.  The proof is the
two-stratum composition:

1. **handles — a THEOREM.**  `mHandleMixLift` (HM lane, HM1–HM5) produces a χ-preserving
   `Ψ₁ ∈ ⟨dmClearAuts⟩` killing `ν'` on every handle letter and fixing `ν'(C₀)`.
2. **core — the binder.**  `MMixHypothesis` applied to the transported marking `ν'∘Ψ₁`.

The composite `Ψ₂.trans Ψ₁` is the correction: it preserves `χ_M` (both factors do) and carries
`ν'` to `ν_M` on every marked generator.  Nothing here discharges the binder; the obligation
headline is a `theorem` whose only assumption is a `def`. -/

section Assembly

open Multiplicative

/-- **MC-M (correction form)** — packet Prop. 7.2 at the `M`-core.  Under the S3 binder
`MMixHypothesis`, every transported marking `ν'` with `ν'(C̄₀) ∈ ℤ₂ˣ` admits a correction
`Ψ ∈ Aut(D_M)` with `χ_M ∘ Ψ = χ_M` and `ν' ∘ Ψ = ν_M` on the marked generators.  The handle
stratum is discharged, not assumed.

The pivot datum `hc` stays a hypothesis here so the statement remains uniform in `h`.  At rank
four it is not an extra assumption at all: `MarkedCore/CompactCoV.lean` (ticket MC-CoV) proves
it **equivalent** to the compact row's own branch condition `r = 0`, and
`prop_MC_M_correction_of_chiKer` is this theorem with `hc` replaced by that clause.  So the
preferred compact `M` API has no marked-core binder: `MScaling.lean` supplies its M3 face from
existing B8 and exact M2/M5/handle moves supply the remainder. -/
theorem prop_MC_M_correction {α h : ℕ} (hα : 1 ≤ α) (hMix : MMixHypothesis α h hα)
    (nu' : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2]))
    (hc : IsUnit (toAdd (nu' (dmC α h)))) :
    ∃ Ψ : ContinuousMulEquiv (DM α h : Type) (DM α h : Type),
      (∀ x, chiM α h (Ψ x) = chiM α h x)
        ∧ ∀ i, nu' (Ψ (dmGen α h i)) = nuM α h hα (dmGen α h i) := by
  obtain ⟨Ψ₁, -, hΨ₁chi, hU, hV, hC⟩ := mHandleMixLift α h nu' hc
  have hc₁ : IsUnit (toAdd ((nu'.comp (autHom Ψ₁)) (dmC α h))) := by
    show IsUnit (toAdd (nu' (Ψ₁ (dmC α h))))
    rw [hC]
    exact hc
  obtain ⟨Ψ₂, hΨ₂chi, hΨ₂nu⟩ := hMix (nu'.comp (autHom Ψ₁)) hc₁ hU hV
  refine ⟨Ψ₂.trans Ψ₁, fun x => ?_, fun i => ?_⟩
  · show chiM α h (Ψ₁ (Ψ₂ x)) = chiM α h x
    rw [hΨ₁chi, hΨ₂chi]
  · exact hΨ₂nu i

/-- **MC-M at rank four** (`h = 0`, no handles): the uniform compatibility form still accepts
the old S3 binder.  The preferred `CompactCoV.prop_MC_M_correction_of_chiKer` drops both it and
`hc`, using existing B8 through `MScaling.lean` and the intrinsic χ-kernel clause. -/
theorem prop_MC_M_correction_zero {α : ℕ} (hα : 1 ≤ α) (hMix : MMixHypothesis α 0 hα)
    (nu' : ContinuousMonoidHom (DM α 0 : Type) (Multiplicative ℤ_[2]))
    (hc : IsUnit (toAdd (nu' (dmC α 0)))) :
    ∃ Ψ : ContinuousMulEquiv (DM α 0 : Type) (DM α 0 : Type),
      (∀ x, chiM α 0 (Ψ x) = chiM α 0 x)
        ∧ ∀ i, nu' (Ψ (dmGen α 0 i)) = nuM α 0 hα (dmGen α 0 i) :=
  prop_MC_M_correction hα hMix nu' hc

/-- **MC-M in the `MLiftSplit` shape** (HM4's contract, threaded literally): the same
correction, with the handle stratum certified by an `MLiftSplit` record.  The record's `handle`
field is the HM lane's theorem, so this adds no assumption beyond `MMixHypothesis`; it exists
so that MC5 can consume the obligation in the shape the split API advertises. -/
theorem prop_MC_M_correction_split {α h : ℕ} (hα : 1 ≤ α)
    {S12 S3 : Set (Function.End (Fin (coreRank h) → ℤ_[2]))}
    (_hs : MLiftSplit α h S12 S3) (hMix : MMixHypothesis α h hα)
    (nu' : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2]))
    (hc : IsUnit (toAdd (nu' (dmC α h)))) :
    ∃ Ψ : ContinuousMulEquiv (DM α h : Type) (DM α h : Type),
      (∀ x, chiM α h (Ψ x) = chiM α h x)
        ∧ ∀ i, nu' (Ψ (dmGen α h i)) = nuM α h hα (dmGen α h i) :=
  prop_MC_M_correction hα hMix nu' hc

end Assembly

/-! ## §9 Stress pins at `(α, h) = (2, 0)` and `(2, 1)` -/

section Pins

open Multiplicative

/-- Pin: the rank-four core has four letters. -/
theorem mPin_coreRank_zero : coreRank 0 = 4 := rfl

/-- Pin: one handle adds two letters. -/
theorem mPin_coreRank_one : coreRank 1 = 6 := rfl

/-- Pin `(α, h) = (2, 1)`: the handle letters of the first (only) handle are the indices
`4` and `5`. -/
theorem mPin_handleIdx_one :
    ((handleIdxU (0 : Fin 1) : Fin (coreRank 1)) : ℕ) = 4
      ∧ ((handleIdxV (0 : Fin 1) : Fin (coreRank 1)) : ℕ) = 5 :=
  ⟨by simp [handleIdxU_val], by simp [handleIdxV_val]⟩

/-- **Pin `(α, h) = (2, 0)`: the `M₂` orientation unit is the ℚ₂ unit `η = (−3)⁻¹`.**  Setting
`α = 2` in `u = (1 − 2^α)⁻¹` gives `(1 − 4)⁻¹ = (−3)⁻¹`, which is exactly the `y₀⁻¹` of
`GQ2/AnabelianBridge/Classification.lean`'s `chi_row_extract` and of `chiD0G`'s generator
values.  The rank-four χ-row engine therefore specialises to the rank-three one on the nose. -/
theorem mPin_mUnit_two : ((mUnit 2 : ℤ_[2]ˣ) : ℤ_[2]) * (-3) = 1 := by
  have h := mUnit_mul (α := 2) (by norm_num)
  rw [show ((2 : ℤ_[2]) ^ 2) = 4 by norm_num] at h
  linear_combination h

/-- Pin: the mod-2 cup Gram is symmetric (it is a cup form). -/
theorem mPin_mGram_symm : mGram.transpose = mGram := by decide

/-- Pin: the mod-2 cup Gram is nondegenerate (`det = 1` over `𝔽₂`) — the Witt-cancellation
input of memo §2.3. -/
theorem mPin_mGram_det : mGram.det = 1 := by decide

/-- Pin: the identity parameter acts trivially on the frame. -/
theorem mPin_act_id (v : ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2]) :
    (⟨0, 1, 0, 0, 1, 0, 0⟩ : MStabParam).act v = v := by
  obtain ⟨v1, b, c, d⟩ := v
  rw [MStabParam.act_apply]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · show v1 + mParityZ b * 0 + mParityZ d * mParityZ 0 = v1
    rw [mParityZ_zero]
    ring
  · show b * ((1 : ℤ_[2]ˣ) : ℤ_[2]) + c * (2 * 0) + d * (2 * 0) = b
    rw [Units.val_one]
    ring
  · show b * 0 + c * ((1 : ℤ_[2]ˣ) : ℤ_[2]) + d * 0 = c
    rw [Units.val_one]
    ring

/-- **Pin: the Witt coupling is not vacuous.**  `X_b` at `B_c = 1` really does move the torsion
coordinate of `φ(D̄)` — the `t`-component of `φ(D̄)` is `B_c mod 2` — while at `B_c = 2` it does
not.  (This is the relation the memo verifies by hand: `B ↦ B+C` alone breaks `⟨A*,C*⟩ = 0`,
and adding `D ↦ D+A` restores it.) -/
theorem mPin_witt_coupling :
    (mFamM5 1).act ((0 : ZMod 2), 0, 0, 1) = ((1 : ZMod 2), 0, 0, 1)
      ∧ (mFamM5 2).act ((0 : ZMod 2), 0, 0, 1) = ((0 : ZMod 2), 0, 0, 1) := by
  constructor
  · rw [mFamM5_act]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
    · show (0 : ZMod 2) + mParityZ 1 * mParityZ 1 = 1
      rw [mParityZ_one]
      ring
    · show (0 : ℤ_[2]) = 0
      rfl
    · show (0 : ℤ_[2]) * 1 + 0 = 0
      ring
  · rw [mFamM5_act]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
    · show (0 : ZMod 2) + mParityZ 1 * mParityZ 2 = 0
      rw [show (2 : ℤ_[2]) = 2 * 1 by ring, mParityZ_two_mul]
      ring
    · show (0 : ℤ_[2]) = 0
      rfl
    · show (0 : ℤ_[2]) * 2 + 0 = 0
      ring

/-- **Pin `(α, h) = (2, 0)`: family M1's frame row.**  `Λ_k` at `α = 2` sends
`B̄ ↦ (k mod 2)·t + B̄ − 2k·C̄₀`; at `k = 1` the `C̄₀`-shift is `−2`, which is even — the reason
`Λ_k` never disturbs the Witt coupling. -/
theorem mPin_famM1_two :
    (mFamM1 2 1).act ((0 : ZMod 2), 1, 0, 0) = ((1 : ZMod 2), 1, -2, 0) := by
  rw [MStabParam.act_B, mFamM1]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · show mParityZ 1 = 1
    exact mParityZ_one
  · show ((1 : ℤ_[2]ˣ) : ℤ_[2]) = 1
    exact Units.val_one
  · show -((1 : ℤ_[2]) * 2 ^ (2 - 1)) = -2
    norm_num

end Pins

end MarkedCore

end Dyadic

end GQ2
