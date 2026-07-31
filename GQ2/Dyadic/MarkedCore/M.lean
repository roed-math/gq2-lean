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
§5, §6.2 and §8 on the `M`-side.  The parallel ticket MC4 owns `N.lean`; per the reserved-name
rule every declaration here is `m`-prefixed or `M`-headed, and the two generic-looking helpers
(`mPeripheralTriple_scaling_delta`, `mZpowZtwo_injective_of_level`) carry dedup notes.

The file consumes MC2 (`Cores.lean`: the presented core `DM α h`, the canonical orientation
`chiM` with its closed-form unit `mUnit α = (1−2^α)⁻¹`, the standard marking `nuM`, the h = 0
frame `MDecomposition`, and the B8 transport `peripheralTriple_scaling`) and the HM lane
(`HandleMix*.lean`: the handle stratum as a *theorem*, the `A(P,h)`-machinery, the
`MLiftSplit`/`MCoreMixHypothesis` split shapes).

## Contents

* **§1–§2** the powering/parity toolkit and the χ-row extraction engine: the rank-four analogue
  of the ℚ₂ mod-4 argument (`GQ2/AnabelianBridge/Classification.lean`, `chi_row_extract`), at
  the general depth-`α` unit `mUnit α` (memo §2.2(i)).  `mZpowZtwo_injective_of_level` extends
  `zpowZtwo_injective_of_exact_level` from exact level 2 to exact level `s ≥ 2`.
* **§3** coordinates through a frame `B : MDecomposition α` and the torsion row: every
  continuous automorphism of `D_M^{ab}` fixes `t = Ā·C̄₀^{2^{α−1}}` (`mXi_fixes_t`), the
  rank-four `xi_fixes_t`.
* **§4** the mod-2 cup Gram `mGramTwo` (memo §2.2(iii), V4) and the stabilizer predicate
  `IsMStabilizer`: χ-preservation plus the contragredient isometry condition
  `Mᵀ·G·M = G` on the mod-2 frame matrix.  (H¹ carries the cup form and automorphisms act by
  *pre*composition, so the matrix condition is on the transpose side; §4's docstrings record
  the variance computation.)
* **§5** **the classification** (`mStabilizer_classification`): every χ-preserving Gram-isometric
  continuous automorphism of `D_M^{ab}` is given in the frame by the memo §2.3 closed form —
  seven parameters `(τ, β, B_c, c₁, γ, d₁, e)` with the single Witt coupling
  `τ_D = B_c mod 2` — **uniquely**.  Pure `ℤ₂`/`𝔽₂` linear algebra, unconditional, uniform in
  `α ≥ 2` (memo §10: "it can and should land first, unconditionally").
* **§6** the S1 lifts (memo §2.5, stratum S1): `mLambdaEquiv` (family M1, `B ↦ A^k·B`) as an
  honest continuous automorphism at general `(α, h)`; family M2 (`D ↦ C₀^e·D`) **is** HM4's
  `dmTauDEquiv` — recorded, not duplicated.
* **§7** the S2 lift (memo §5.2, stratum S2): the `γ`-scaling `mPsiHom`/`mScaling_exists`
  at `h = 0` from **two nested applications of the existing axiom B8** through MC2's
  `deltaHom` transport — no new axiom, census unchanged.
* **§8** the binders (never axioms): `MMixHypothesis` (memo §8 Decision 2(B), the S3 residue),
  the pinned stratum sets `mTauDMoves`/`mSolveMoves` for HM4's `MLiftSplit`, and
  `MLabHypothesis`/`imChiM` (memo §6.4) with the orientation-canonicity clause as an explicit
  parameter (memo §9 Q3/R6 — see the docstring there).
* **§9** **the correction assembly** (packet Prop. 7.2 shape, memo §6.3's `hLift`):
  `prop_MC_M_correction` — under the S3 binder and B8, every transported marking `ν'` with
  `ν'(C̄₀) ∈ ℤ₂ˣ` admits a correction `Ψ ∈ Aut(D_M)` with `χ_M∘Ψ = χ_M` and `ν'∘Ψ = ν_M` —
  plus the general-`h` `MLiftSplit`-consuming form `prop_MC_M_correction_split`.
* **§10** stress pins at `(α, h) = (2, 0)` and `(2, 1)`.

## Recorded findings (deviations and gaps surfaced by this ticket)

1. **`DmRealizes`' membership clause makes the schematic S3/S12 binders undischargeable as
   stated.**  HM4's `MCoreMixHypothesis α h S3 = DmRealizesAll α h S3` requires the realizing
   automorphism to lie in `Submonoid.closure (dmClearAuts α h)`; every generator of that monoid
   fixes the letters `B` and `C₀` *pointwise*, so for any move in `S3` that changes the
   `B̄`- or `C̄₀`-row on a reachable ν-frame vector (all of M3–M7 with nontrivial parameter) no
   such automorphism exists.  The clause was the χ-preservation certificate; the honest reshape
   is to demand χ-preservation itself, which is what `MMixHypothesis` (§8) does.  This file
   therefore proves the assembly twice: from the honest binder (`prop_MC_M_correction`), and in
   HM4's shape (`prop_MC_M_correction_split`, threading `MCoreMixHypothesis` literally per the
   MLiftSplit contract).  G-Lab should adopt the reshape; nothing here discharges either binder.
2. **The B8 transport does not cross the handle block** (memo §4.2 R3, sharpened): at `h > 0`
   the outer peripheral triple's third slot is `C₀^D·∏[u_j,v_j]`, and the scaled word
   `(C₀^D·H)^u` is not a product of a conjugate of `(C₀^D)^u` with a handle word in new letters,
   so the §7 construction is stated at `h = 0`.  At `h > 0` the `γ`-scaling move rides the S3
   stratum set (`mSolveMoves`) of the split form.  This is MC5/G-Lab news, not a patchable
   defect.
3. **`MLabHypothesis` carries its orientation-canonicity predicate as a parameter** — the
   abstract-`G` form is forced (memo R6), the repo has no abstract dualizing-module
   characterization (`GQ2/Orientation.lean` deferral), and quantifying over *all* characters
   with the stated image is false (`N_α` admits characters of `M`-shaped image).  See §8.
4. The classification takes the orientation as an abstract character with pinned generator
   values (`hχA`–`hχD`), exactly as `prop_3_8_classification` does on the ℚ₂ side — no
   descended `chiMab` is constructed.

## Axiom hygiene

The classification (§3–§5), the S1 lift (§6) and the assembly glue are axiom-free (std-3).
§7 and everything consuming it cite the **existing** axiom **B8**
(`PeripheralCyclotomicAction`, `GQ2/Foundations/Axioms.lean`) through MC2's `deltaHom`
transport — owner-accepted for the MC lane (memo §5.2, board R3(a) wave), census unchanged
at 11.  No new axiom; the obligation headline is a `theorem`.
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

end MarkedCore

end Dyadic

end GQ2
