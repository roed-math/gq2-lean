/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5.1
-/
import GQ2.Dyadic.MarkedCore.NNielsenGenerators
import GQ2.Dyadic.MarkedCore.NStabilizerFullLift

/-!
# The N frame-stabilizer factorization into the six Nielsen families

Wave 364, lane MC-N, at the rank-four core (`h = 0`). This is the half of the packet's **MC-N**
finite-list artifact that wave 363 found absent (`docs/dyadic/w363-nielsen-note.md`): the six N
Nielsen families of `docs/dyadic/mc-design.md` section 3.4 as frame actions, the completeness
theorem factoring every admissible `NStabParam` through a **fixed** finite slot list, and the
resulting finite list of continuous automorphisms of the actual full N frame `NFrameModel 0`,
each of which lifts to `D_N`. Together with wave 363's `NNielsenGenerators.lean` (the lifting
bridge) it is the N twin of `MNielsenGenerators.lean`.

## What is here

* **The frame action.** `NStabParam.act` is memo §3.3's closed form as a map on coordinate
  vectors `(τ_v, a, b, c)` in the basis `(t, x̄₁, σ̄, x̄₂)`, the N twin of `MStabParam.act`; its
  three basis rows are `NStabParam.rows` on the nose (`act_x1`, `act_sigma`, `act_x2`) and it
  fixes `t` (`act_t`).
* **The six families (T1).** `nFamN1` through `nFamN6` as `NStabParam` values, with closed-form
  actions and admissibility. Families N2, N3, N4 are the pure block parameters
  `nNielsenFacBlock` at `E(k)`, `F(k)` and `diag(κ, 1)`, and `nNielsenFacBlock_act_comp` says the
  block action is the matrix action on the column `(b, c)`.
* **The factorization (T2).** `nNielsenFac_gl2_factor`: every `g ∈ GL₂(ℤ₂)` is
  `F(w)·diag(det g, 1)·E(x)·F(y)·E(z)` with `w ∈ {0, 1}`, the bounded form of `N.lean`'s
  `nGL_factor` (`ℤ₂` is local, so one of `g₁₀`, `g₁₀ − g₀₀` is a unit). `nNielsen_factorization`:
  every admissible parameter's frame action is the composite of the **eight** slots
  `N2(z), N3(y), N2(x), N4(κ), N3(w), N5(p), N6(q), N1(k)` (leftmost applied first). The two
  admissibility couplings are used exactly once, to show that the `t`-shifts carried by N5 and N6
  recombine to `(τ_σ, τ_{x₂})` (`nNielsenFac_couple`). The statement is `α`-free, as the N
  stabilizer is.
* **The artifact (T3).** `nNielsenFacMap` carries the action onto `NFrameModel 0`; every parameter
  (each equivalence takes a parameter `P` together with a supplied inverse parameter `Q` and the
  mutual-inverse hypotheses; no inverse or group structure on `NStabParam` exists in the tree,
  and the eight families supply their own inverses)
  fixes the integral `x̄₁` coordinate, hence preserves `nFrameOrientation`
  (`nNielsenFac_orientation`); every admissible parameter is an `NFrameCupIsometry` through wave
  363's `nNielsenGen_cup_of_mat` and the bridge `nNielsenFac_mat` (the reduced matrix of the frame
  action is `NRows.mat` at the rows), hence lifts by `nFullStabilizer_lift`. `nNielsenFacN1`
  through `nNielsenFacN6` are the families as honest `ContinuousMulEquiv`s (each inverts inside its
  own family), `nNielsenFacList` is the eight-member list, and `nNielsenFac_finite_list` is the
  MC-N twin of `mNielsenGen_finite_list`: length eight, every member orientation-preserving, a cup
  isometry and lifting, the composite equal to the parameter's frame action, the composite
  lifting. `nNielsenFac_param_realized` projects the list away.
* **The quantifier closure.** `nNielsenFacRows` reads the `NRows` of a continuous frame
  automorphism, `nNielsenFac_frameAction_of_rows` identifies an automorphism with a parameter's
  rows with `nNielsenFacMap` at that parameter (hom-extensionality on the marks plus the automatic
  `t`-row `nFrameModel_map_t`), so `nNielsenFac_stabilizer_list` and
  `nNielsenFac_stabilizer_induced` read over *every element of the Smith-Witt stabilizer*
  (`IsNStab`, through `nStabilizer_classification`) rather than over every `NStabParam`: each is
  the composite of the list, and is induced by an actual `chiN`-preserving continuous automorphism
  of `D_N` with the exact square `abMk (Psi x) = xi (abMk x)`.
* **The per-family route.** `nNielsenFacLifts_of_param_families`: every member of the list is
  *also* lifted by the automorphism that `nStabParam_fullFrame_lift_general` assembles from the
  six families' own constructions (N1, N2, N3 the exact `dnTauBEquiv`, `dnTauDEquiv`,
  `dnTauCEquiv`; N5, N6 from `nMixPairHypothesis_coreMix`; N4 from
  `nPlaneScalingHypothesis_general`; then the exact N1 torsion adjustment), through
  `nNielsenFac_fullFrameMark`, which identifies
  `NStabilizerFullRows.fullFrameMark` at `h = 0` with the frame action on the marks. So at N,
  unlike at M, each generator carries two independent lifts.

## What this does *not* do

The lifts in `nNielsenFac_finite_list` come from `nFullStabilizer_lift`, i.e. from the uniform
filtered-correction and compactness argument, exactly as at M. The per-family route above is a
genuinely different theorem, but its N4 ingredient (`nPlaneScalingHypothesis_general`) is itself
a compactness limit of the N-plane stages, so **not every generator is lifted by a closed
formula**, and none is claimed to be; N1, N2, N3 are (`dnTauBEquiv`, `dnTauDEquiv`,
`dnTauCEquiv`), and N5, N6 are the `CoreMix`/`ClearWide` constructions. "Finite list" means
finitely many *families*, each parameterized by a 2-adic number or unit, and what the theorem
produces for a given stabilizer element is one member of each slot; a literally finite generating
set is impossible for a pro-2 group that is not finitely generated as an abstract group.

Scope: handle rank **zero** only, since `nStabilizer_classification` is a rank-four statement;
`alpha >= 2` wherever the actual frame is involved. Every declaration in this file is std-3
(`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section

open GQ2 GQ2.SectionThree Multiplicative
open GQ2.Dyadic.EvenModel
open scoped GQ2.SectionThree.TopAbInstances

/-! ## The frame action of a stabilizer parameter tuple -/

/-- **The frame action of a stabilizer parameter tuple** on coordinate vectors `(τ_v, a, b, c)`
in the basis `(t, x̄₁, σ̄, x̄₂)`: the closed form of memo §3.3 read linearly on coordinates. The
`t`-slot is `ZMod 2`, so the three `ℤ₂`-coefficients enter it only through `nRed`; the `x̄₁`-slot
is fixed on the nose (the integral pin of `IsNStab.x1_coord`), and the `(σ̄, x̄₂)`-block acts by
`g` on the column `(b, c)`. This is the N twin of `MStabParam.act`. -/
def NStabParam.act (P : NStabParam) (v : NVec) : NVec :=
  (v.1 + nRed v.2.1 * P.tau + nRed v.2.2.1 * P.tauSigma + nRed v.2.2.2 * P.tauX2,
   v.2.1,
   v.2.1 * P.p + v.2.2.1 * P.g 0 0 + v.2.2.2 * P.g 0 1,
   v.2.1 * P.q + v.2.2.1 * P.g 1 0 + v.2.2.2 * P.g 1 1)

theorem NStabParam.act_apply (P : NStabParam) (v1 : ZMod 2) (a b c : ℤ_[2]) :
    P.act (v1, a, b, c)
      = (v1 + nRed a * P.tau + nRed b * P.tauSigma + nRed c * P.tauX2, a,
         a * P.p + b * P.g 0 0 + c * P.g 0 1, a * P.q + b * P.g 1 0 + c * P.g 1 1) := rfl

/-- The action fixes the torsion generator `t`, as `NRows.col` builds in. -/
theorem NStabParam.act_t (P : NStabParam) :
    P.act ((1 : ZMod 2), 0, 0, 0) = ((1 : ZMod 2), 0, 0, 0) := by
  rw [NStabParam.act_apply, map_zero]
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ ?_)) <;> simp

/-- The action reproduces the `x̄₁`-row of `NStabParam.rows`. -/
theorem NStabParam.act_x1 (P : NStabParam) :
    P.act ((0 : ZMod 2), 1, 0, 0) = P.rows.x1 := by
  rw [NStabParam.act_apply, NStabParam.rows_x1, map_zero, map_one]
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ ?_)) <;> simp

/-- The action reproduces the `σ̄`-row of `NStabParam.rows`. -/
theorem NStabParam.act_sigma (P : NStabParam) :
    P.act ((0 : ZMod 2), 0, 1, 0) = P.rows.sigma := by
  rw [NStabParam.act_apply, NStabParam.rows_sigma, map_zero, map_one]
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ ?_)) <;> simp

/-- The action reproduces the `x̄₂`-row of `NStabParam.rows`. -/
theorem NStabParam.act_x2 (P : NStabParam) :
    P.act ((0 : ZMod 2), 0, 0, 1) = P.rows.x2 := by
  rw [NStabParam.act_apply, NStabParam.rows_x2, map_zero, map_one]
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ ?_)) <;> simp

/-! ## The six Nielsen families of memo §3.4 -/

/-- A pure `(σ̄, x̄₂)`-block parameter: no `t`-shifts, no `(p, q)`. Families N2, N3 and N4 are
its instances at the elementary matrices and at `diag(κ, 1)`. -/
def nNielsenFacBlock (g : Matrix (Fin 2) (Fin 2) ℤ_[2]) : NStabParam := ⟨0, 0, 0, 0, 0, g⟩

/-- Family **N1**, `x₁ ↦ x₀^k·x₁` (memo §3.4, stratum **S1**): frame action `τ = k mod 2`. -/
def nFamN1 (k : ℤ_[2]) : NStabParam := ⟨nRed k, 0, 0, 0, 0, 1⟩

/-- Family **N2**, `x₂ ↦ x₂·σ^k` (memo §3.4, stratum **S1**): the transvection
`x̄₂ ↦ x̄₂ + k·σ̄`, block `E(k) = [[1, k], [0, 1]]`. -/
def nFamN2 (k : ℤ_[2]) : NStabParam := nNielsenFacBlock (planeElemU k)

/-- Family **N3**, `σ ↦ σ·x₂^k` (memo §3.4, stratum **S1**): the transvection
`σ̄ ↦ σ̄ + k·x̄₂`, block `F(k) = [[1, 0], [k, 1]]`. -/
def nFamN3 (k : ℤ_[2]) : NStabParam := nNielsenFacBlock (planeElemV k)

/-- Family **N4**, the handle determinant (memo §3.4, stratum **S2**, B8): `σ̄ ↦ κ·σ̄`, block
`diag(κ, 1)`. -/
def nFamN4 (κ : ℤ_[2]ˣ) : NStabParam := nNielsenFacBlock (nPlaneDet κ)

/-- Family **N5**, `x₁ ↦ x₁·σ^p` with its coupled `x₂ ↦ x₀^p·x₂` (memo §3.4, stratum **S3**):
`x̄₁ ↦ x̄₁ + p·σ̄`, and the coupled `t`-shift `τ_{x₂} = p mod 2`. -/
def nFamN5 (p : ℤ_[2]) : NStabParam := ⟨0, p, 0, 0, nRed p, 1⟩

/-- Family **N6**, `x₁ ↦ x₁·x₂^q` with its coupled `σ ↦ x₀^q·σ` (memo §3.4, stratum **S3**):
`x̄₁ ↦ x̄₁ + q·x̄₂`, and the coupled `t`-shift `τ_σ = q mod 2`. -/
def nFamN6 (q : ℤ_[2]) : NStabParam := ⟨0, 0, q, nRed q, 0, 1⟩

theorem nNielsenFacBlock_act (g : Matrix (Fin 2) (Fin 2) ℤ_[2]) (v1 : ZMod 2) (a b c : ℤ_[2]) :
    (nNielsenFacBlock g).act (v1, a, b, c)
      = (v1, a, b * g 0 0 + c * g 0 1, b * g 1 0 + c * g 1 1) := by
  rw [nNielsenFacBlock, NStabParam.act_apply]
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ ?_)) <;> simp

/-- The block action is the matrix action on the column `(b, c)`: composition is matrix
multiplication. -/
theorem nNielsenFacBlock_act_comp (g₁ g₂ : Matrix (Fin 2) (Fin 2) ℤ_[2]) :
    (nNielsenFacBlock g₁).act ∘ (nNielsenFacBlock g₂).act = (nNielsenFacBlock (g₁ * g₂)).act := by
  funext v
  obtain ⟨v1, a, b, c⟩ := v
  rw [Function.comp_apply, nNielsenFacBlock_act, nNielsenFacBlock_act, nNielsenFacBlock_act]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
  · show (b * g₂ 0 0 + c * g₂ 0 1) * g₁ 0 0 + (b * g₂ 1 0 + c * g₂ 1 1) * g₁ 0 1 = _
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · show (b * g₂ 0 0 + c * g₂ 0 1) * g₁ 1 0 + (b * g₂ 1 0 + c * g₂ 1 1) * g₁ 1 1 = _
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    ring

@[simp] theorem nNielsenFacBlock_one_act (v : NVec) : (nNielsenFacBlock 1).act v = v := by
  obtain ⟨v1, a, b, c⟩ := v
  rw [nNielsenFacBlock_act]
  simp

theorem nFamN1_act (k : ℤ_[2]) (v1 : ZMod 2) (a b c : ℤ_[2]) :
    (nFamN1 k).act (v1, a, b, c) = (v1 + nRed a * nRed k, a, b, c) := by
  rw [nFamN1, NStabParam.act_apply]
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ ?_)) <;> simp

theorem nFamN2_act (k : ℤ_[2]) (v1 : ZMod 2) (a b c : ℤ_[2]) :
    (nFamN2 k).act (v1, a, b, c) = (v1, a, b + c * k, c) := by
  rw [nFamN2, nNielsenFacBlock_act, planeElemU]
  simp

theorem nFamN3_act (k : ℤ_[2]) (v1 : ZMod 2) (a b c : ℤ_[2]) :
    (nFamN3 k).act (v1, a, b, c) = (v1, a, b, b * k + c) := by
  rw [nFamN3, nNielsenFacBlock_act, planeElemV]
  simp

theorem nFamN4_act (κ : ℤ_[2]ˣ) (v1 : ZMod 2) (a b c : ℤ_[2]) :
    (nFamN4 κ).act (v1, a, b, c) = (v1, a, b * (κ : ℤ_[2]), c) := by
  rw [nFamN4, nNielsenFacBlock_act, nPlaneDet]
  simp

theorem nFamN5_act (p : ℤ_[2]) (v1 : ZMod 2) (a b c : ℤ_[2]) :
    (nFamN5 p).act (v1, a, b, c) = (v1 + nRed c * nRed p, a, a * p + b, c) := by
  rw [nFamN5, NStabParam.act_apply]
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ ?_)) <;> simp

theorem nFamN6_act (q : ℤ_[2]) (v1 : ZMod 2) (a b c : ℤ_[2]) :
    (nFamN6 q).act (v1, a, b, c) = (v1 + nRed b * nRed q, a, b, a * q + c) := by
  rw [nFamN6, NStabParam.act_apply]
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ ?_)) <;> simp

/-! ### Every family member is admissible -/

theorem nNielsenFacBlock_admissible {g : Matrix (Fin 2) (Fin 2) ℤ_[2]} (hg : IsUnit g.det) :
    (nNielsenFacBlock g).Admissible where
  det := hg
  couple_p := by simp [nNielsenFacBlock]
  couple_q := by simp [nNielsenFacBlock]

theorem nFamN1_admissible (k : ℤ_[2]) : (nFamN1 k).Admissible where
  det := by rw [nFamN1, Matrix.det_one]; exact isUnit_one
  couple_p := by simp [nFamN1]
  couple_q := by simp [nFamN1]

theorem nFamN2_admissible (k : ℤ_[2]) : (nFamN2 k).Admissible :=
  nNielsenFacBlock_admissible (by rw [planeElemU_det]; exact isUnit_one)

theorem nFamN3_admissible (k : ℤ_[2]) : (nFamN3 k).Admissible :=
  nNielsenFacBlock_admissible (by rw [planeElemV_det]; exact isUnit_one)

theorem nFamN4_admissible (κ : ℤ_[2]ˣ) : (nFamN4 κ).Admissible :=
  nNielsenFacBlock_admissible (by rw [nPlaneDet_det]; exact κ.isUnit)

theorem nFamN5_admissible (p : ℤ_[2]) : (nFamN5 p).Admissible where
  det := by rw [nFamN5, Matrix.det_one]; exact isUnit_one
  couple_p := by simp [nFamN5]
  couple_q := by simp [nFamN5]

theorem nFamN6_admissible (q : ℤ_[2]) : (nFamN6 q).Admissible where
  det := by rw [nFamN6, Matrix.det_one]; exact isUnit_one
  couple_p := by simp [nFamN6]
  couple_q := by simp [nFamN6]

/-! ## `GL₂(ℤ₂)` in five elementary slots -/

/-- **Bounded elementary factorization of `GL₂(ℤ₂)`**: every matrix with unit determinant is
`F(w)·diag(δ, 1)·E(x)·F(y)·E(z)` with `δ` its determinant and `w ∈ {0, 1}`. This is the
bounded form of `nGL_factor` (`N.lean`): `ℤ₂` is local, so one of `c`, `c − a` is a unit
(`c` when `c` is, and otherwise `a` is, because `ad − bc` is), and a matrix with a unit `(1,0)`
entry is `diag(δ, 1)·E(x)·F(c)·E(z)` outright. -/
theorem nNielsenFac_gl2_factor (g : Matrix (Fin 2) (Fin 2) ℤ_[2]) (hg : IsUnit g.det) :
    ∃ (w x y z : ℤ_[2]), (w = 0 ∨ w = 1) ∧
      g = planeElemV w * nPlaneDet hg.unit * planeElemU x * planeElemV y * planeElemU z := by
  have hδ : ((hg.unit : ℤ_[2]ˣ) : ℤ_[2]) = g.det := hg.unit_spec
  have hδi : g.det * ((hg.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    calc g.det * ((hg.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2])
        = ((hg.unit : ℤ_[2]ˣ) : ℤ_[2]) * ((hg.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) := by rw [hδ]
      _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdet : g.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := Matrix.det_fin_two g
  -- the core case: a unit `(1,0)` entry
  have key : ∀ (c : ℤ_[2]ˣ) (a b d : ℤ_[2]),
      (a * d - b * (c : ℤ_[2]) = g.det) →
      !![a, b; (c : ℤ_[2]), d] = nPlaneDet hg.unit
        * planeElemU ((a - g.det) * ((hg.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((c⁻¹ : ℤ_[2]ˣ) : ℤ_[2]))
        * planeElemV (c : ℤ_[2]) * planeElemU ((d - 1) * ((c⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) := by
    intro c a b d hd
    have hci : (c : ℤ_[2]) * ((c⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [nPlaneDet, planeElemU, planeElemV, planeElemU, Matrix.mul_fin_two, Matrix.mul_fin_two,
      Matrix.mul_fin_two, hδ]
    refine Matrix.ext fun i k => ?_
    fin_cases i <;> fin_cases k <;> simp
    · linear_combination (-(a - g.det) * (c : ℤ_[2]) * ((c⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) * hδi
        + (-(a - g.det)) * hci
    · linear_combination (-((c⁻¹ : ℤ_[2]ˣ) : ℤ_[2])) * hd
        + (-(b + (a - g.det) * (d - 1) * ((c⁻¹ : ℤ_[2]ˣ) : ℤ_[2]))) * hci
        + (-((a - g.det) * (c : ℤ_[2]) * ((c⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((c⁻¹ : ℤ_[2]ˣ) : ℤ_[2])
          * (d - 1) + (a - g.det) * ((c⁻¹ : ℤ_[2]ˣ) : ℤ_[2]))) * hδi
    · linear_combination (-(d - 1)) * hci
  by_cases hc : IsUnit (g 1 0)
  · have hg' : g = !![g 0 0, g 0 1; g 1 0, g 1 1] :=
      Matrix.ext fun i k => by fin_cases i <;> fin_cases k <;> rfl
    have this := key hc.unit (g 0 0) (g 0 1) (g 1 1) (by rw [hc.unit_spec, hdet])
    rw [hc.unit_spec] at this
    refine ⟨0, (g 0 0 - g.det) * ((hg.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((hc.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]),
      g 1 0, (g 1 1 - 1) * ((hc.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]), Or.inl rfl, ?_⟩
    rw [planeElemV_zero, one_mul, ← this]
    exact hg'
  · -- `c` is not a unit, so `a` is, so `c − a` is; factor `F(−1)·g` instead
    have ha : IsUnit (g 0 0) := by
      have hsum : IsUnit (g 0 0 * g 1 1 + -(g 0 1 * g 1 0)) := by
        rw [← sub_eq_add_neg, ← hdet]; exact hg
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with h | h
      · exact isUnit_of_mul_isUnit_left h
      · exact absurd (isUnit_of_mul_isUnit_right ((IsUnit.neg_iff _).mp h)) hc
    have hca : IsUnit (g 1 0 - g 0 0) := by
      have h' : IsUnit ((g 0 0 - g 1 0) + g 1 0) := by rw [sub_add_cancel]; exact ha
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h' with h | h
      · rw [← neg_sub]; exact h.neg
      · exact absurd h hc
    have hg' : planeElemV (-1) * g = !![g 0 0, g 0 1; g 1 0 - g 0 0, g 1 1 - g 0 1] := by
      rw [planeElemV]
      refine Matrix.ext fun i k => ?_
      fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    have hfac : g = planeElemV 1 * (planeElemV (-1) * g) := by
      rw [← Matrix.mul_assoc, planeElemV_mul_planeElemV, add_neg_cancel, planeElemV_zero,
        Matrix.one_mul]
    have this := key hca.unit (g 0 0) (g 0 1) (g 1 1 - g 0 1)
      (by rw [hca.unit_spec, hdet]; ring)
    rw [hca.unit_spec] at this
    rw [hg', this] at hfac
    refine ⟨1, (g 0 0 - g.det) * ((hg.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((hca.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]),
      g 1 0 - g 0 0, (g 1 1 - g 0 1 - 1) * ((hca.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]), Or.inr rfl, ?_⟩
    refine hfac.trans ?_
    simp only [Matrix.mul_assoc]

/-! ## The factorization -/

private theorem nNielsenFac_nRed_val (a : ZMod 2) : nRed ((a.val : ℤ_[2])) = a := by
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) a with rfl | rfl
  · rw [show (((0 : ZMod 2).val : ℕ) : ℤ_[2]) = 0 by
      rw [show ((0 : ZMod 2).val) = 0 from rfl, Nat.cast_zero], map_zero]
  · rw [show (((1 : ZMod 2).val : ℕ) : ℤ_[2]) = 1 by
      rw [show ((1 : ZMod 2).val) = 1 from rfl, Nat.cast_one], map_one]

/-- **The two couplings are exactly the consistency of the `t`-slot**: under `det ḡ = 1` and
memo §3.3's two mod-2 couplings, the `t`-shifts that families N5 and N6 carry along recombine
into `(τ_σ, τ_{x₂})` on the nose. Finite check over the `2⁶` assignments. -/
private theorem nNielsenFac_couple (τσ τx p q g₁ g₂ h₁ h₂ : ZMod 2)
    (hdet : g₁ * h₂ + g₂ * h₁ = 1) (hp : p = τx * g₁ + τσ * g₂) (hq : q = τx * h₁ + τσ * h₂) :
    h₁ * p + g₁ * q = τσ ∧ h₂ * p + g₂ * q = τx := by
  subst hp hq
  revert τσ τx g₁ g₂ h₁ h₂
  decide

/-- **Completeness of the six Nielsen families** (memo §3.4, packet row MC-N). Every admissible
stabilizer parameter tuple `P` has its frame action equal to a composite of **eight** family
members in the fixed slot list

```
N2(z), N3(y), N2(x), N4(κ), N3(w), N5(p), N6(q), N1(k)      (leftmost applied first)
```

with `κ = det g` and `w ∈ {0, 1}` (both recorded in the statement), `(x, y, z)` the elementary
parameters of `nNielsenFac_gl2_factor`, `p, q` the parameters of `P` itself, and `k = τ + p̄·q̄`
(read in `ℤ₂` through `ZMod.val`). So seven slots carry a free 2-adic parameter and the eighth,
`N3(w)`, is a Boolean correction that is the identity when the `(1,0)` block entry is a unit.
The memo's recipe "kill the block by N2-N4, then `(p, q)` by N5/N6, then `τ` by N1" is followed
literally: the block is a matrix identity pushed through `nNielsenFacBlock_act_comp`, and the
`t`-slot closes because the two admissibility couplings say exactly that the `t`-shifts carried
by N5/N6 recombine to `(τ_σ, τ_{x₂})` (`nNielsenFac_couple`). Completely `α`-free, as the N
stabilizer is. -/
theorem nNielsen_factorization (P : NStabParam) (hP : P.Admissible) :
    ∃ (k q p w x y z : ℤ_[2]) (κ : ℤ_[2]ˣ), (w = 0 ∨ w = 1) ∧ (κ : ℤ_[2]) = P.g.det ∧
      P.act = (nFamN1 k).act ∘ (nFamN6 q).act ∘ (nFamN5 p).act ∘ (nFamN3 w).act ∘
        (nFamN4 κ).act ∘ (nFamN2 x).act ∘ (nFamN3 y).act ∘ (nFamN2 z).act := by
  obtain ⟨w, x, y, z, hw, hg⟩ := nNielsenFac_gl2_factor P.g hP.det
  set k : ℤ_[2] := (((P.tau + nRed P.p * nRed P.q).val : ℕ) : ℤ_[2]) with hk
  refine ⟨k, P.q, P.p, w, x, y, z, hP.det.unit, hw, hP.det.unit_spec, ?_⟩
  have hblock : (nFamN3 w).act ∘ (nFamN4 hP.det.unit).act ∘ (nFamN2 x).act ∘ (nFamN3 y).act ∘
      (nFamN2 z).act = (nNielsenFacBlock P.g).act := by
    simp only [Matrix.mul_assoc] at hg
    rw [nFamN3, nFamN4, nFamN2, nFamN3, nFamN2, nNielsenFacBlock_act_comp,
      nNielsenFacBlock_act_comp, nNielsenFacBlock_act_comp, nNielsenFacBlock_act_comp, ← hg]
  obtain ⟨hii, hiii⟩ := nNielsenFac_couple P.tauSigma P.tauX2 (nRed P.p) (nRed P.q)
    (nRed (P.g 0 0)) (nRed (P.g 0 1)) (nRed (P.g 1 0)) (nRed (P.g 1 1))
    ((nIsUnit_det_iff P.g).mp hP.det) hP.couple_p hP.couple_q
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [hblock]
  funext v
  obtain ⟨v1, a, b, c⟩ := v
  rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, nNielsenFacBlock_act,
    nFamN5_act, nFamN6_act, nFamN1_act, NStabParam.act_apply]
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ ?_))
  · show v1 + nRed a * P.tau + nRed b * P.tauSigma + nRed c * P.tauX2
      = v1 + nRed (b * P.g 1 0 + c * P.g 1 1) * nRed P.p
        + nRed (a * P.p + (b * P.g 0 0 + c * P.g 0 1)) * nRed P.q + nRed a * nRed k
    rw [hk, nNielsenFac_nRed_val]
    simp only [map_add, map_mul]
    linear_combination (-(nRed b)) * hii + (-(nRed c)) * hiii
      + (-(nRed a * nRed P.p * nRed P.q)) * h2
  · show a * P.p + b * P.g 0 0 + c * P.g 0 1 = a * P.p + (b * P.g 0 0 + c * P.g 0 1)
    ring
  · show a * P.q + b * P.g 1 0 + c * P.g 1 1 = a * P.q + (b * P.g 1 0 + c * P.g 1 1)
    ring


/-! ## The frame action on the actual rank-four N frame -/

/-- An arbitrary coordinate map transported to the rank-four full N frame `NFrameModel 0`; the
empty handle tail rides along untouched. It exists so that the composition calculus below is
definitional. -/
def nNielsenFacLift (F : NVec → NVec) (z : NFrameModel 0) : NFrameModel 0 :=
  ofAdd ((F (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).1,
    (F (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).2.1,
    (F (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).2.2.1,
    (F (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).2.2.2,
    z.toAdd.2.2.2.2)

theorem nNielsenFacLift_comp (F G : NVec → NVec) (z : NFrameModel 0) :
    nNielsenFacLift F (nNielsenFacLift G z) = nNielsenFacLift (F ∘ G) z := rfl

/-- `NStabParam.act` written on the rank-four full N frame model. -/
def nNielsenFacMap (P : NStabParam) : NFrameModel 0 → NFrameModel 0 := nNielsenFacLift P.act

theorem nNielsenFacMap_eq_lift (P : NStabParam) : nNielsenFacMap P = nNielsenFacLift P.act := rfl

theorem nNielsenFacMap_toAdd (P : NStabParam) (z : NFrameModel 0) :
    (nNielsenFacMap P z).toAdd =
      ((P.act (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).1,
        (P.act (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).2.1,
        (P.act (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).2.2.1,
        (P.act (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1)).2.2.2,
        z.toAdd.2.2.2.2) := rfl

theorem nNielsenFacMap_comp_of_act (P Q : NStabParam)
    (hPQ : ∀ v, P.act (Q.act v) = v) (z : NFrameModel 0) :
    nNielsenFacMap P (nNielsenFacMap Q z) = z := by
  rw [nNielsenFacMap_eq_lift, nNielsenFacMap_eq_lift, nNielsenFacLift_comp]
  have hid : P.act ∘ Q.act = id := funext hPQ
  rw [hid]
  rfl

theorem nNielsenFacMap_mul (P : NStabParam) (z w : NFrameModel 0) :
    nNielsenFacMap P (z * w) = nNielsenFacMap P z * nNielsenFacMap P w := by
  have hl : nNielsenFacMap P (z * w) = ofAdd
      (z.toAdd.1 + w.toAdd.1 + nRed (z.toAdd.2.1 + w.toAdd.2.1) * P.tau
          + nRed (z.toAdd.2.2.1 + w.toAdd.2.2.1) * P.tauSigma
          + nRed (z.toAdd.2.2.2.1 + w.toAdd.2.2.2.1) * P.tauX2,
       z.toAdd.2.1 + w.toAdd.2.1,
       (z.toAdd.2.1 + w.toAdd.2.1) * P.p + (z.toAdd.2.2.1 + w.toAdd.2.2.1) * P.g 0 0
         + (z.toAdd.2.2.2.1 + w.toAdd.2.2.2.1) * P.g 0 1,
       (z.toAdd.2.1 + w.toAdd.2.1) * P.q + (z.toAdd.2.2.1 + w.toAdd.2.2.1) * P.g 1 0
         + (z.toAdd.2.2.2.1 + w.toAdd.2.2.2.1) * P.g 1 1,
       z.toAdd.2.2.2.2 + w.toAdd.2.2.2.2) := rfl
  have hr : nNielsenFacMap P z * nNielsenFacMap P w = ofAdd
      ((z.toAdd.1 + nRed z.toAdd.2.1 * P.tau + nRed z.toAdd.2.2.1 * P.tauSigma
          + nRed z.toAdd.2.2.2.1 * P.tauX2)
        + (w.toAdd.1 + nRed w.toAdd.2.1 * P.tau + nRed w.toAdd.2.2.1 * P.tauSigma
          + nRed w.toAdd.2.2.2.1 * P.tauX2),
       z.toAdd.2.1 + w.toAdd.2.1,
       (z.toAdd.2.1 * P.p + z.toAdd.2.2.1 * P.g 0 0 + z.toAdd.2.2.2.1 * P.g 0 1)
         + (w.toAdd.2.1 * P.p + w.toAdd.2.2.1 * P.g 0 0 + w.toAdd.2.2.2.1 * P.g 0 1),
       (z.toAdd.2.1 * P.q + z.toAdd.2.2.1 * P.g 1 0 + z.toAdd.2.2.2.1 * P.g 1 1)
         + (w.toAdd.2.1 * P.q + w.toAdd.2.2.1 * P.g 1 0 + w.toAdd.2.2.2.1 * P.g 1 1),
       z.toAdd.2.2.2.2 + w.toAdd.2.2.2.2) := rfl
  rw [hl, hr, map_add, map_add, map_add]
  exact congrArg ofAdd (Prod.ext (by ring) (Prod.ext rfl (Prod.ext (by ring) (Prod.ext (by ring)
    rfl))))

theorem nNielsenFacMap_continuous (P : NStabParam) : Continuous (nNielsenFacMap P) := by
  have hred : Continuous nRed := GQ2.Dyadic.Instances.DNAutomorphismCup.continuous_nRed
  have hT : Continuous fun z : NFrameModel 0 => z.toAdd.1 :=
    continuous_fst.comp continuous_toAdd
  have hA : Continuous fun z : NFrameModel 0 => z.toAdd.2.1 :=
    (continuous_fst.comp continuous_snd).comp continuous_toAdd
  have hB : Continuous fun z : NFrameModel 0 => z.toAdd.2.2.1 :=
    ((continuous_fst.comp continuous_snd).comp continuous_snd).comp continuous_toAdd
  have hC : Continuous fun z : NFrameModel 0 => z.toAdd.2.2.2.1 :=
    ((continuous_fst.comp continuous_snd).comp (continuous_snd.comp continuous_snd)).comp
      continuous_toAdd
  have hE : Continuous fun z : NFrameModel 0 => z.toAdd.2.2.2.2 :=
    ((continuous_snd.comp continuous_snd).comp (continuous_snd.comp continuous_snd)).comp
      continuous_toAdd
  refine continuous_ofAdd.comp (Continuous.prodMk ?_ (Continuous.prodMk hA
    (Continuous.prodMk ?_ (Continuous.prodMk ?_ hE))))
  · exact ((hT.add ((hred.comp hA).mul continuous_const)).add
      ((hred.comp hB).mul continuous_const)).add ((hred.comp hC).mul continuous_const)
  · exact ((hA.mul continuous_const).add (hB.mul continuous_const)).add
      (hC.mul continuous_const)
  · exact ((hA.mul continuous_const).add (hB.mul continuous_const)).add
      (hC.mul continuous_const)

/-- A pair of mutually inverse stabilizer parameters gives a continuous automorphism of the
rank-four full N frame. -/
def nNielsenFacEquiv (P Q : NStabParam)
    (hPQ : ∀ v, P.act (Q.act v) = v) (hQP : ∀ v, Q.act (P.act v) = v) :
    ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0) where
  toFun := nNielsenFacMap P
  invFun := nNielsenFacMap Q
  left_inv := nNielsenFacMap_comp_of_act Q P hQP
  right_inv := nNielsenFacMap_comp_of_act P Q hPQ
  map_mul' := nNielsenFacMap_mul P
  continuous_toFun := nNielsenFacMap_continuous P
  continuous_invFun := nNielsenFacMap_continuous Q

@[simp] theorem nNielsenFacEquiv_apply (P Q : NStabParam)
    (hPQ : ∀ v, P.act (Q.act v) = v) (hQP : ∀ v, Q.act (P.act v) = v) (z : NFrameModel 0) :
    nNielsenFacEquiv P Q hPQ hQP z = nNielsenFacMap P z := rfl

/-! ## Orientation and cup: every parameter's frame action satisfies both hypotheses of
`nFullStabilizer_lift` -/

/-- The integral `x̄₁` coordinate is fixed on the nose by every parameter's frame action. -/
theorem nNielsenFacMap_coord_x1 (P : NStabParam) (z : NFrameModel 0) :
    (nNielsenFacMap P z).toAdd.2.1 = z.toAdd.2.1 := rfl

/-- **Orientation half.** Every parameter's frame action preserves the canonical N orientation,
because it fixes the integral `x̄₁` coordinate (`nFrameOrientation_preserved_iff`). -/
theorem nNielsenFac_orientation {alpha : ℕ} (ha : 2 ≤ alpha) (P Q : NStabParam)
    (hPQ : ∀ v, P.act (Q.act v) = v) (hQP : ∀ v, Q.act (P.act v) = v) (z : NFrameModel 0) :
    nFrameOrientation ha 0 (nNielsenFacEquiv P Q hPQ hQP z) = nFrameOrientation ha 0 z :=
  (nFrameOrientation_preserved_iff ha 0 (nNielsenFacEquiv P Q hPQ hQP)).mpr
    (fun w => nNielsenFacMap_coord_x1 P w) z

/-- The canonical marks of the rank-four N frame, in coordinates. -/
theorem nNielsenFac_mark_zero {alpha : ℕ} (ha : 2 ≤ alpha) :
    nFrameCanonicalMark ha 0 0 = ofAdd (1, 0, 0, 0, 0) :=
  nPhiHom_X0 ha 0

theorem nNielsenFac_mark_one {alpha : ℕ} (ha : 2 ≤ alpha) :
    nFrameCanonicalMark ha 0 1 = ofAdd (0, 1, 0, 0, 0) :=
  nPhiHom_X1 ha 0

theorem nNielsenFac_mark_two {alpha : ℕ} (ha : 2 ≤ alpha) :
    nFrameCanonicalMark ha 0 2 = ofAdd (0, 0, 1, 0, 0) :=
  nPhiHom_Sigma ha 0

theorem nNielsenFac_mark_three {alpha : ℕ} (ha : 2 ≤ alpha) :
    nFrameCanonicalMark ha 0 3 = ofAdd (0, 0, 0, 1, 0) :=
  nPhiHom_X2 ha 0

/-- The image of the `j`-th canonical mark under a parameter's frame action is the `j`-th column
of `NRows.col` at the parameter's rows, with an empty handle tail. -/
theorem nNielsenFacMap_mark {alpha : ℕ} (ha : 2 ≤ alpha) (P : NStabParam)
    (j : Fin (coreRank 0)) :
    nNielsenFacMap P (nFrameCanonicalMark ha 0 j)
      = ofAdd ((P.rows.col j).1, (P.rows.col j).2.1, (P.rows.col j).2.2.1, (P.rows.col j).2.2.2,
          0) := by
  have hj4 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by decide +revert
  have hpack : ∀ {u v : NVec}, u = v →
      (ofAdd (u.1, u.2.1, u.2.2.1, u.2.2.2, (0 : Fin (2 * 0) → ℤ_[2])) : NFrameModel 0)
        = ofAdd (v.1, v.2.1, v.2.2.1, v.2.2.2, 0) := fun h => by rw [h]
  rcases hj4 with rfl | rfl | rfl | rfl
  · rw [nNielsenFac_mark_zero]
    exact hpack (NStabParam.act_t P)
  · rw [nNielsenFac_mark_one]
    exact hpack (NStabParam.act_x1 P)
  · rw [nNielsenFac_mark_two]
    exact hpack (NStabParam.act_sigma P)
  · rw [nNielsenFac_mark_three]
    exact hpack (NStabParam.act_x2 P)

/-- **The reduced mod-two matrix of a parameter's frame action is `NRows.mat` at its rows**, in
N's own column convention. This is the bridge from `nNielsenGenMat` (W363) to `N.lean`. -/
theorem nNielsenFac_mat {alpha : ℕ} (ha : 2 ≤ alpha) (P Q : NStabParam)
    (hPQ : ∀ v, P.act (Q.act v) = v) (hQP : ∀ v, Q.act (P.act v) = v)
    (i j : Fin (coreRank 0)) :
    nNielsenGenMat ha (nNielsenFacEquiv P Q hPQ hQP) i j = P.rows.mat i j := by
  rw [nNielsenGenMat, nNielsenFacEquiv_apply, nNielsenFacMap_mark ha P j]
  have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide +revert
  rcases hi4 with rfl | rfl | rfl | rfl
  · rw [nNielsenGen_coord_zero]; rfl
  · rw [nNielsenGen_coord_one]; rfl
  · rw [nNielsenGen_coord_two]; rfl
  · rw [nNielsenGen_coord_three]; rfl

/-- **Cup half.** The frame action of every *admissible* parameter is a full semantic cup
isometry of the actual N frame, through W363's `nNielsenGen_cup_of_mat` and `N.lean`'s
`NStabParam.rows_isCupIsometry`. -/
theorem nNielsenFac_cupIsometry {alpha : ℕ} (ha : 2 ≤ alpha) (P Q : NStabParam)
    (hP : P.Admissible)
    (hPQ : ∀ v, P.act (Q.act v) = v) (hQP : ∀ v, Q.act (P.act v) = v) :
    NFrameCupIsometry ha (nNielsenFacEquiv P Q hPQ hQP) := by
  refine nNielsenGen_cup_of_mat ha _ fun i j => ?_
  rw [funext (nNielsenFac_mat ha P Q hPQ hQP i), funext (nNielsenFac_mat ha P Q hPQ hQP j)]
  exact NStabParam.rows_isCupIsometry hP i j

/-! ## The six families as continuous frame automorphisms -/

theorem nNielsenFacBlock_act_act (g₁ g₂ : Matrix (Fin 2) (Fin 2) ℤ_[2]) (v : NVec) :
    (nNielsenFacBlock g₁).act ((nNielsenFacBlock g₂).act v)
      = (nNielsenFacBlock (g₁ * g₂)).act v :=
  congrFun (nNielsenFacBlock_act_comp g₁ g₂) v

theorem nNielsenFac_N1_inv (k : ℤ_[2]) (v : NVec) :
    (nFamN1 k).act ((nFamN1 (-k)).act v) = v := by
  obtain ⟨v1, a, b, c⟩ := v
  rw [nFamN1_act, nFamN1_act, map_neg]
  exact Prod.ext (by ring) rfl

theorem nNielsenFac_N2_inv (k : ℤ_[2]) (v : NVec) :
    (nFamN2 k).act ((nFamN2 (-k)).act v) = v := by
  rw [nFamN2, nFamN2, nNielsenFacBlock_act_act, planeElemU_mul_planeElemU, add_neg_cancel,
    planeElemU_zero, nNielsenFacBlock_one_act]

theorem nNielsenFac_N3_inv (k : ℤ_[2]) (v : NVec) :
    (nFamN3 k).act ((nFamN3 (-k)).act v) = v := by
  rw [nFamN3, nFamN3, nNielsenFacBlock_act_act, planeElemV_mul_planeElemV, add_neg_cancel,
    planeElemV_zero, nNielsenFacBlock_one_act]

theorem nNielsenFac_N4_inv (κ : ℤ_[2]ˣ) (v : NVec) :
    (nFamN4 κ).act ((nFamN4 κ⁻¹).act v) = v := by
  rw [nFamN4, nFamN4, nNielsenFacBlock_act_act, nPlaneDet_mul, mul_inv_cancel, nPlaneDet_one,
    nNielsenFacBlock_one_act]

theorem nNielsenFac_N5_inv (p : ℤ_[2]) (v : NVec) :
    (nFamN5 p).act ((nFamN5 (-p)).act v) = v := by
  obtain ⟨v1, a, b, c⟩ := v
  rw [nFamN5_act, nFamN5_act, map_neg]
  exact Prod.ext (by ring) (Prod.ext rfl (Prod.ext (by ring) rfl))

theorem nNielsenFac_N6_inv (q : ℤ_[2]) (v : NVec) :
    (nFamN6 q).act ((nFamN6 (-q)).act v) = v := by
  obtain ⟨v1, a, b, c⟩ := v
  rw [nFamN6_act, nFamN6_act, map_neg]
  exact Prod.ext (by ring) (Prod.ext rfl (Prod.ext rfl (by ring)))

/-- Family **N1** `x₁ ↦ x₀^k·x₁` as a frame automorphism. -/
def nNielsenFacN1 (k : ℤ_[2]) : ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0) :=
  nNielsenFacEquiv (nFamN1 k) (nFamN1 (-k)) (nNielsenFac_N1_inv k)
    (fun v => by simpa only [neg_neg] using nNielsenFac_N1_inv (-k) v)

/-- Family **N2** `x₂ ↦ x₂·σ^k` as a frame automorphism. -/
def nNielsenFacN2 (k : ℤ_[2]) : ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0) :=
  nNielsenFacEquiv (nFamN2 k) (nFamN2 (-k)) (nNielsenFac_N2_inv k)
    (fun v => by simpa only [neg_neg] using nNielsenFac_N2_inv (-k) v)

/-- Family **N3** `σ ↦ σ·x₂^k` as a frame automorphism. -/
def nNielsenFacN3 (k : ℤ_[2]) : ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0) :=
  nNielsenFacEquiv (nFamN3 k) (nFamN3 (-k)) (nNielsenFac_N3_inv k)
    (fun v => by simpa only [neg_neg] using nNielsenFac_N3_inv (-k) v)

/-- Family **N4** `σ̄ ↦ κ·σ̄` as a frame automorphism. -/
def nNielsenFacN4 (κ : ℤ_[2]ˣ) : ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0) :=
  nNielsenFacEquiv (nFamN4 κ) (nFamN4 κ⁻¹) (nNielsenFac_N4_inv κ)
    (fun v => by simpa only [inv_inv] using nNielsenFac_N4_inv κ⁻¹ v)

/-- Family **N5** `x₁ ↦ x₁·σ^p` (with its coupled `x₂ ↦ x₀^p·x₂`) as a frame automorphism. -/
def nNielsenFacN5 (p : ℤ_[2]) : ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0) :=
  nNielsenFacEquiv (nFamN5 p) (nFamN5 (-p)) (nNielsenFac_N5_inv p)
    (fun v => by simpa only [neg_neg] using nNielsenFac_N5_inv (-p) v)

/-- Family **N6** `x₁ ↦ x₁·x₂^q` (with its coupled `σ ↦ x₀^q·σ`) as a frame automorphism. -/
def nNielsenFacN6 (q : ℤ_[2]) : ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0) :=
  nNielsenFacEquiv (nFamN6 q) (nFamN6 (-q)) (nNielsenFac_N6_inv q)
    (fun v => by simpa only [neg_neg] using nNielsenFac_N6_inv (-q) v)

/-! ## Composition: of frame automorphisms, and of their lifts -/

/-- `Psi` is an actual `chiN`-preserving continuous automorphism of the rank-four core inducing
`phi` on the full abelian frame, with the exact all-element commuting square. This is verbatim
the conclusion of `nFullStabilizer_lift` at `h = 0`. -/
def NNielsenFacLifts {alpha : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0)) : Prop :=
  ∃ Psi : ContinuousMulEquiv (DN alpha 0 : Type) (DN alpha 0 : Type),
    (∀ x, chiN alpha 0 (Psi x) = chiN alpha 0 x) ∧
    (∀ x, nPhiHom ha 0 (abMk (Psi x)) = phi (nPhiHom ha 0 (abMk x)))

/-- The identity frame automorphism lifts. -/
theorem nNielsenFacLifts_refl {alpha : ℕ} (ha : 2 ≤ alpha) :
    NNielsenFacLifts ha (ContinuousMulEquiv.refl (NFrameModel 0)) :=
  ⟨ContinuousMulEquiv.refl _, fun _ => rfl, fun _ => rfl⟩

/-- **The composite of the lifts is a lift of the composite.** -/
theorem nNielsenFacLifts_trans {alpha : ℕ} (ha : 2 ≤ alpha)
    {phi psi : ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0)}
    (h1 : NNielsenFacLifts ha phi) (h2 : NNielsenFacLifts ha psi) :
    NNielsenFacLifts ha (phi.trans psi) := by
  obtain ⟨P, hP1, hP2⟩ := h1
  obtain ⟨Q, hQ1, hQ2⟩ := h2
  refine ⟨P.trans Q, fun x => ?_, fun x => ?_⟩
  · exact (hQ1 (P x)).trans (hP1 x)
  · show nPhiHom ha 0 (abMk (Q (P x))) = psi (phi _)
    rw [hQ2 (P x), hP2 x]

/-- The composite of a finite list of frame automorphisms, leftmost applied first. -/
def nNielsenFacCompose (L : List (ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0))) :
    ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0) :=
  L.foldr (fun g e => g.trans e) (ContinuousMulEquiv.refl _)

theorem nNielsenFacLifts_compose {alpha : ℕ} (ha : 2 ≤ alpha)
    (L : List (ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0)))
    (h : ∀ g ∈ L, NNielsenFacLifts ha g) :
    NNielsenFacLifts ha (nNielsenFacCompose L) := by
  induction L with
  | nil => exact nNielsenFacLifts_refl ha
  | cons g L ih =>
      exact nNielsenFacLifts_trans ha (h g (List.mem_cons_self))
        (ih fun x hx => h x (List.mem_cons_of_mem g hx))

/-- Every frame automorphism built from an admissible parameter lifts: T1 fed to
`nFullStabilizer_lift`. -/
theorem nNielsenFacLifts_of_param {alpha : ℕ} (ha : 2 ≤ alpha) (P Q : NStabParam)
    (hP : P.Admissible)
    (hPQ : ∀ v, P.act (Q.act v) = v) (hQP : ∀ v, Q.act (P.act v) = v) :
    NNielsenFacLifts ha (nNielsenFacEquiv P Q hPQ hQP) :=
  nFullStabilizer_lift ha (nNielsenFacEquiv P Q hPQ hQP)
    (nNielsenFac_orientation ha P Q hPQ hQP) (nNielsenFac_cupIsometry ha P Q hP hPQ hQP)

/-- Each generator built from an admissible parameter preserves the orientation, is a cup
isometry, and lifts. -/
theorem nNielsenFac_props_of_param {alpha : ℕ} (ha : 2 ≤ alpha) (P Q : NStabParam)
    (hP : P.Admissible)
    (hPQ : ∀ v, P.act (Q.act v) = v) (hQP : ∀ v, Q.act (P.act v) = v) :
    (∀ z, nFrameOrientation ha 0 (nNielsenFacEquiv P Q hPQ hQP z) = nFrameOrientation ha 0 z) ∧
      NFrameCupIsometry ha (nNielsenFacEquiv P Q hPQ hQP) ∧
      NNielsenFacLifts ha (nNielsenFacEquiv P Q hPQ hQP) :=
  ⟨nNielsenFac_orientation ha P Q hPQ hQP, nNielsenFac_cupIsometry ha P Q hP hPQ hQP,
    nNielsenFacLifts_of_param ha P Q hP hPQ hQP⟩

/-! ## The packet's finite list -/

/-- **The finite list of Nielsen generators at N**, in the slot order
`N2(z), N3(y), N2(x), N4(κ), N3(w), N5(p), N6(q), N1(k)` (leftmost applied first): the block
first, then the two coupled mixes, then the torsion shift. -/
def nNielsenFacList (z y x : ℤ_[2]) (κ : ℤ_[2]ˣ) (w p q k : ℤ_[2]) :
    List (ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0)) :=
  [nNielsenFacN2 z, nNielsenFacN3 y, nNielsenFacN2 x, nNielsenFacN4 κ, nNielsenFacN3 w,
    nNielsenFacN5 p, nNielsenFacN6 q, nNielsenFacN1 k]

theorem nNielsenFacList_length (z y x : ℤ_[2]) (κ : ℤ_[2]ˣ) (w p q k : ℤ_[2]) :
    (nNielsenFacList z y x κ w p q k).length = 8 := rfl

theorem nNielsenFacCompose_list (z y x : ℤ_[2]) (κ : ℤ_[2]ˣ) (w p q k : ℤ_[2])
    (v : NFrameModel 0) :
    nNielsenFacCompose (nNielsenFacList z y x κ w p q k) v =
      nNielsenFacLift ((nFamN1 k).act ∘ (nFamN6 q).act ∘ (nFamN5 p).act ∘ (nFamN3 w).act ∘
        (nFamN4 κ).act ∘ (nFamN2 x).act ∘ (nFamN3 y).act ∘ (nFamN2 z).act) v := rfl

theorem nNielsenFacList_props {alpha : ℕ} (ha : 2 ≤ alpha) (z y x : ℤ_[2]) (κ : ℤ_[2]ˣ)
    (w p q k : ℤ_[2]) :
    ∀ g ∈ nNielsenFacList z y x κ w p q k,
      (∀ v, nFrameOrientation ha 0 (g v) = nFrameOrientation ha 0 v) ∧
        NFrameCupIsometry ha g ∧ NNielsenFacLifts ha g := by
  intro g hg
  simp only [nNielsenFacList, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact nNielsenFac_props_of_param ha _ _ (nFamN2_admissible z) _ _
  · exact nNielsenFac_props_of_param ha _ _ (nFamN3_admissible y) _ _
  · exact nNielsenFac_props_of_param ha _ _ (nFamN2_admissible x) _ _
  · exact nNielsenFac_props_of_param ha _ _ (nFamN4_admissible κ) _ _
  · exact nNielsenFac_props_of_param ha _ _ (nFamN3_admissible w) _ _
  · exact nNielsenFac_props_of_param ha _ _ (nFamN5_admissible p) _ _
  · exact nNielsenFac_props_of_param ha _ _ (nFamN6_admissible q) _ _
  · exact nNielsenFac_props_of_param ha _ _ (nFamN1_admissible k) _ _

/-- **The packet's MC-N finite-list artifact at the rank-four core** (`h = 0`, `alpha >= 2`).

For every admissible parameter `P : NStabParam`, equivalently (by `nStabilizer_classification`)
for every element of the Smith-Witt stabilizer of the rank-four N abelianization, there is an
explicit list of **eight** frame automorphisms, each one a member of memo §3.4's six Nielsen
families at an explicit parameter, such that

1. every member preserves the canonical orientation and the full mod-two cup form, and
   therefore lifts to an actual `chiN`-preserving continuous automorphism of `D_N` with the
   exact all-element commuting frame square;
2. the composite of the list is the frame action of `P`; and
3. the composite of the lifts is a lift of that composite.

The lifts in (1) are supplied by `nFullStabilizer_lift`, i.e. by the uniform filtered-correction
and compactness argument, **not** by an explicit generator-by-generator group-level
construction. -/
theorem nNielsenFac_finite_list {alpha : ℕ} (ha : 2 ≤ alpha) (P : NStabParam)
    (hP : P.Admissible) :
    ∃ (z y x : ℤ_[2]) (κ : ℤ_[2]ˣ) (w p q k : ℤ_[2]),
      (nNielsenFacList z y x κ w p q k).length = 8 ∧
      (∀ g ∈ nNielsenFacList z y x κ w p q k,
        (∀ v, nFrameOrientation ha 0 (g v) = nFrameOrientation ha 0 v) ∧
          NFrameCupIsometry ha g ∧ NNielsenFacLifts ha g) ∧
      (∀ v, nNielsenFacCompose (nNielsenFacList z y x κ w p q k) v = nNielsenFacMap P v) ∧
      NNielsenFacLifts ha (nNielsenFacCompose (nNielsenFacList z y x κ w p q k)) := by
  obtain ⟨k, q, p, w, x, y, z, κ, -, -, hfac⟩ := nNielsen_factorization P hP
  refine ⟨z, y, x, κ, w, p, q, k, nNielsenFacList_length _ _ _ _ _ _ _ _,
    nNielsenFacList_props ha _ _ _ _ _ _ _ _, fun v => ?_, ?_⟩
  · rw [nNielsenFacCompose_list, nNielsenFacMap_eq_lift, hfac]
  · exact nNielsenFacLifts_compose ha _
      (fun g hg => (nNielsenFacList_props ha _ _ _ _ _ _ _ _ g hg).2.2)

/-- **Every admissible rank-four stabilizer parameter is realized by an actual core
automorphism**, as the composite of the eight Nielsen generators' lifts. -/
theorem nNielsenFac_param_realized {alpha : ℕ} (ha : 2 ≤ alpha) (P : NStabParam)
    (hP : P.Admissible) :
    ∃ Psi : ContinuousMulEquiv (DN alpha 0 : Type) (DN alpha 0 : Type),
      (∀ x, chiN alpha 0 (Psi x) = chiN alpha 0 x) ∧
      (∀ x, nPhiHom ha 0 (abMk (Psi x)) = nNielsenFacMap P (nPhiHom ha 0 (abMk x))) := by
  obtain ⟨z, y, x, κ, w, p, q, k, _, _, hcomp, Psi, hchi, hsq⟩ := nNielsenFac_finite_list ha P hP
  exact ⟨Psi, hchi, fun u => (hsq u).trans (hcomp _)⟩

/-! ## Closing the quantifier against `nStabilizer_classification` -/

/-- The frame action of a parameter, packaged as a continuous hom. -/
def nNielsenFacHom (P : NStabParam) : ContinuousMonoidHom (NFrameModel 0) (NFrameModel 0) :=
  ⟨MonoidHom.mk' (nNielsenFacMap P) (nNielsenFacMap_mul P), nNielsenFacMap_continuous P⟩

/-- The canonical marks generate the full N frame topologically, so two continuous homs out of
it that agree on the marks agree. -/
theorem nNielsenFac_frame_hom_ext {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ)
    {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]
    (f g : ContinuousMonoidHom (NFrameModel h) X)
    (hgen : ∀ i, f (nFrameCanonicalMark ha h i) = g (nFrameCanonicalMark ha h i))
    (z : NFrameModel h) : f z = g z := by
  obtain ⟨x, rfl⟩ := freeNFrameProjection_surjective ha h z
  have he : f.comp (freeNFrameProjection ha h) = g.comp (freeNFrameProjection ha h) := by
    apply presPro2_hom_ext
    intro i
    change f (freeNFrameProjection ha h (freeTwoRankGen (coreRank h) i)) =
      g (freeNFrameProjection ha h (freeTwoRankGen (coreRank h) i))
    rw [freeNFrameProjection_gen]
    exact hgen i
  exact DFunLike.congr_fun he x

/-- **The rows of a continuous automorphism of the rank-four N frame**, in `N.lean`'s `NRows`
vocabulary: the four core coordinates of the images of the three non-torsion canonical marks.
The image of `t` is not data (`nFrameModel_map_t`), exactly as `NRows.col` assumes. -/
def nNielsenFacRows {alpha : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0)) : NRows where
  x1 := ((phi (nFrameCanonicalMark ha 0 1)).toAdd.1, (phi (nFrameCanonicalMark ha 0 1)).toAdd.2.1,
    (phi (nFrameCanonicalMark ha 0 1)).toAdd.2.2.1,
    (phi (nFrameCanonicalMark ha 0 1)).toAdd.2.2.2.1)
  sigma := ((phi (nFrameCanonicalMark ha 0 2)).toAdd.1,
    (phi (nFrameCanonicalMark ha 0 2)).toAdd.2.1,
    (phi (nFrameCanonicalMark ha 0 2)).toAdd.2.2.1,
    (phi (nFrameCanonicalMark ha 0 2)).toAdd.2.2.2.1)
  x2 := ((phi (nFrameCanonicalMark ha 0 3)).toAdd.1, (phi (nFrameCanonicalMark ha 0 3)).toAdd.2.1,
    (phi (nFrameCanonicalMark ha 0 3)).toAdd.2.2.1,
    (phi (nFrameCanonicalMark ha 0 3)).toAdd.2.2.2.1)

/-- Elements of the rank-four frame model are determined by their four core coordinates: the
handle tail is empty. -/
theorem nNielsenFac_ext_core (z w : NFrameModel 0) (h1 : z.toAdd.1 = w.toAdd.1)
    (h2 : z.toAdd.2.1 = w.toAdd.2.1) (h3 : z.toAdd.2.2.1 = w.toAdd.2.2.1)
    (h4 : z.toAdd.2.2.2.1 = w.toAdd.2.2.2.1) : z = w := by
  refine Multiplicative.toAdd.injective (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 (Prod.ext h4 ?_))))
  funext k
  exact absurd k.isLt (Nat.not_lt_zero _)

/-- **A frame automorphism whose rows are a parameter's rows is that parameter's frame
action.** This is the step from "for every admissible `P : NStabParam`" to "for every element
of the Smith-Witt stabilizer": `nStabilizer_classification` supplies the `P`, and this lemma
says the automorphism it classifies is exactly the one this file builds. It is proved by
hom-extensionality on `NFrameModel 0` against the three rows plus the automatic `t`-row
`nFrameModel_map_t`. -/
theorem nNielsenFac_frameAction_of_rows {alpha : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0)) (P : NStabParam)
    (hrows : P.rows = nNielsenFacRows ha phi) (z : NFrameModel 0) :
    phi z = nNielsenFacMap P z := by
  set f : ContinuousMonoidHom (NFrameModel 0) (NFrameModel 0) :=
    ⟨phi.toMulEquiv.toMonoidHom, phi.continuous_toFun⟩ with hf
  have hgen : ∀ i, f (nFrameCanonicalMark ha 0 i)
      = nNielsenFacHom P (nFrameCanonicalMark ha 0 i) := by
    have hi4 : ∀ i : Fin (coreRank 0), i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
    intro i
    change phi (nFrameCanonicalMark ha 0 i) = nNielsenFacMap P (nFrameCanonicalMark ha 0 i)
    rw [nNielsenFacMap_mark ha P i]
    rcases hi4 i with rfl | rfl | rfl | rfl
    · rw [nNielsenFac_mark_zero]
      exact nFrameModel_map_t phi.toMulEquiv
    · refine nNielsenFac_ext_core _ _ ?_ ?_ ?_ ?_ <;> (rw [hrows]; rfl)
    · refine nNielsenFac_ext_core _ _ ?_ ?_ ?_ ?_ <;> (rw [hrows]; rfl)
    · refine nNielsenFac_ext_core _ _ ?_ ?_ ?_ ?_ <;> (rw [hrows]; rfl)
  exact nNielsenFac_frame_hom_ext ha 0 f (nNielsenFacHom P) hgen z

/-- **The quantifier closure at the frame**: every continuous automorphism of the rank-four N
frame whose rows lie in the Smith-Witt stabilizer `IsNStab` is the composite of an explicit
eight-member list of Nielsen generators, each of which lifts, and it lifts itself. -/
theorem nNielsenFac_stabilizer_list {alpha : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0))
    (hphi : IsNStab alpha (nNielsenFacRows ha phi)) :
    ∃ (z y x : ℤ_[2]) (κ : ℤ_[2]ˣ) (w p q k : ℤ_[2]),
      (nNielsenFacList z y x κ w p q k).length = 8 ∧
      (∀ g ∈ nNielsenFacList z y x κ w p q k,
        (∀ v, nFrameOrientation ha 0 (g v) = nFrameOrientation ha 0 v) ∧
          NFrameCupIsometry ha g ∧ NNielsenFacLifts ha g) ∧
      (∀ v, nNielsenFacCompose (nNielsenFacList z y x κ w p q k) v = phi v) ∧
      NNielsenFacLifts ha phi := by
  obtain ⟨P, ⟨hP, hrows⟩, -⟩ := (nStabilizer_classification ha).mp hphi
  obtain ⟨z, y, x, κ, w, p, q, k, hlen, hprops, hcomp, Psi, hchi, hsq⟩ :=
    nNielsenFac_finite_list ha P hP
  have hphiP : ∀ v, phi v = nNielsenFacMap P v := nNielsenFac_frameAction_of_rows ha phi P hrows
  exact ⟨z, y, x, κ, w, p, q, k, hlen, hprops, fun v => (hcomp v).trans (hphiP v).symm,
    Psi, hchi, fun u => (hsq u).trans ((hcomp _).trans (hphiP _).symm)⟩

/-- A continuous automorphism of the rank-four N abelianization, transported to the canonical
frame `nFrameExists_phiEquiv`. -/
def nNielsenFacTransport {alpha : ℕ} (ha : 2 ≤ alpha)
    (xi : ContinuousMulEquiv (topAbelianization (DN alpha 0 : Type))
      (topAbelianization (DN alpha 0 : Type))) :
    ContinuousMulEquiv (NFrameModel 0) (NFrameModel 0) :=
  (nFrameExists_phiEquiv ha 0).symm.trans (xi.trans (nFrameExists_phiEquiv ha 0))

theorem nNielsenFacTransport_apply {alpha : ℕ} (ha : 2 ≤ alpha)
    (xi : ContinuousMulEquiv (topAbelianization (DN alpha 0 : Type))
      (topAbelianization (DN alpha 0 : Type))) (z : NFrameModel 0) :
    nNielsenFacTransport ha xi z = nPhiHom ha 0 (xi ((nFrameExists_phiEquiv ha 0).symm z)) := rfl

/-- The transported automorphism sends the `j`-th canonical mark to the frame image of `xi` at
the `j`-th marked generator: its rows are `xi`'s rows read in the canonical frame. -/
theorem nNielsenFacTransport_mark {alpha : ℕ} (ha : 2 ≤ alpha)
    (xi : ContinuousMulEquiv (topAbelianization (DN alpha 0 : Type))
      (topAbelianization (DN alpha 0 : Type))) (j : Fin (coreRank 0)) :
    nNielsenFacTransport ha xi (nFrameCanonicalMark ha 0 j)
      = nPhiHom ha 0 (xi (abMk (dnGen alpha 0 j))) := by
  rw [nNielsenFacTransport_apply]
  change nPhiHom ha 0 (xi ((nFrameExists_phiEquiv ha 0).symm
    (nFrameExists_phiEquiv ha 0 (abMk (dnGen alpha 0 j))))) = _
  rw [ContinuousMulEquiv.symm_apply_apply]

/-- **Every element of the Smith-Witt stabilizer of the rank-four N abelianization is induced
by an actual `chiN`-preserving continuous automorphism of `D_N`**, through the eight Nielsen
generators: `nStabilizer_classification` gives the parameter, `nNielsen_factorization` splits it
into the six families, each member lifts by `nFullStabilizer_lift`, and the composite of those
lifts is the automorphism produced here. The stabilizer clause is `IsNStab` on the rows of `xi`
read in the canonical frame (`nNielsenFacTransport_mark`). The conclusion is the exact square
`abMk (Psi x) = xi (abMk x)`, so `xi` really is the map induced by `Psi` on the topological
abelianization. -/
theorem nNielsenFac_stabilizer_induced {alpha : ℕ} (ha : 2 ≤ alpha)
    (xi : ContinuousMulEquiv (topAbelianization (DN alpha 0 : Type))
      (topAbelianization (DN alpha 0 : Type)))
    (hxi : IsNStab alpha (nNielsenFacRows ha (nNielsenFacTransport ha xi))) :
    ∃ Psi : ContinuousMulEquiv (DN alpha 0 : Type) (DN alpha 0 : Type),
      (∀ x, chiN alpha 0 (Psi x) = chiN alpha 0 x) ∧
      (∀ x, abMk (Psi x) = xi (abMk x)) := by
  obtain ⟨P, ⟨hP, hrows⟩, -⟩ := (nStabilizer_classification ha).mp hxi
  obtain ⟨Psi, hchi, hsq⟩ := nNielsenFac_param_realized ha P hP
  refine ⟨Psi, hchi, fun x => ?_⟩
  refine (nFrameExists_phiEquiv ha 0).injective ?_
  show nPhiHom ha 0 (abMk (Psi x)) = nPhiHom ha 0 (xi (abMk x))
  rw [hsq x, ← nNielsenFac_frameAction_of_rows ha _ P hrows, nNielsenFacTransport_apply]
  change nPhiHom ha 0 (xi ((nFrameExists_phiEquiv ha 0).symm
    (nFrameExists_phiEquiv ha 0 (abMk x)))) = _
  rw [ContinuousMulEquiv.symm_apply_apply]

/-! ## The per-family route: the same generators lift through the families' own constructions -/

/-- At handle rank zero, `NStabilizerFullRows.fullFrameMark` is the parameter's frame action on
the canonical marks: the two files' pictures of "the rows of `P` on the full frame" agree. -/
theorem nNielsenFac_fullFrameMark {alpha : ℕ} (ha : 2 ≤ alpha) (P : NStabParam)
    (i : Fin (coreRank 0)) :
    NStabilizerFullRows.fullFrameMark P 0 i = nNielsenFacMap P (nFrameCanonicalMark ha 0 i) := by
  rw [nNielsenFacMap_mark ha P i]
  have hi4 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide +revert
  have htail : (ofAdd (0, 0, 0, 0, fun k => toAdd (mHandleMark k (ofAdd (1 : ℤ_[2])) i)) :
      NFrameModel 0) = 1 := by
    show ofAdd _ = ofAdd ((0 : ZMod 2), (0 : ℤ_[2]), (0 : ℤ_[2]), (0 : ℤ_[2]),
      (0 : Fin (2 * 0) → ℤ_[2]))
    exact congrArg ofAdd (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl
      (funext fun k => absurd k.isLt (Nat.not_lt_zero _))))))
  rcases hi4 with rfl | rfl | rfl | rfl
  · rw [NStabilizerFullRows.fullFrameMark, coreMark_zero, htail, mul_one]; rfl
  · rw [NStabilizerFullRows.fullFrameMark, coreMark_one, htail, mul_one]; rfl
  · rw [NStabilizerFullRows.fullFrameMark, coreMark_two, htail, mul_one]; rfl
  · rw [NStabilizerFullRows.fullFrameMark, coreMark_three, htail, mul_one]; rfl

/-- **The per-family lift.** Every admissible parameter's frame action, in particular every
member of the eight-slot list, is also induced by the automorphism that
`nStabParam_fullFrame_lift_general` assembles from the six families' *own* constructions (N1, N2,
N3 the exact closed-form automorphisms `dnTauBEquiv`, `dnTauDEquiv`, `dnTauCEquiv`; N5, N6 the
core-mixing automorphisms behind `nMixPairHypothesis_coreMix`; N4 the N-plane scaling limit
`nPlaneScalingHypothesis_general`; then the exact N1 torsion adjustment `nTorsionAdjust`), with
the same exact all-element square. This route does
not go through the uniform full-frame compactness theorem `nFullStabilizer_lift`, so at N,
unlike at M, the finite list carries **two independent** lifts of each generator; note that the
N4 ingredient is itself a compactness limit of the N-plane stages, not a closed formula. -/
theorem nNielsenFacLifts_of_param_families {alpha : ℕ} (ha : 2 ≤ alpha) (P Q : NStabParam)
    (hP : P.Admissible)
    (hPQ : ∀ v, P.act (Q.act v) = v) (hQP : ∀ v, Q.act (P.act v) = v) :
    NNielsenFacLifts ha (nNielsenFacEquiv P Q hPQ hQP) := by
  obtain ⟨Psi, hchi, -, hmark⟩ := nStabParam_fullFrame_lift_general ha P hP
  refine ⟨Psi, hchi, ?_⟩
  let Ph : ContinuousMonoidHom (DN alpha 0 : Type) (DN alpha 0 : Type) :=
    ⟨Psi.toMonoidHom, Psi.continuous_toFun⟩
  have heq : (nCanonicalFrameHom ha 0).comp Ph
      = (nNielsenFacHom P).comp (nCanonicalFrameHom ha 0) := by
    apply dn_hom_ext
    intro i
    change nPhiHom ha 0 (abMk (Psi (dnGen alpha 0 i)))
      = nNielsenFacMap P (nPhiHom ha 0 (abMk (dnGen alpha 0 i)))
    rw [hmark i, nNielsenFac_fullFrameMark ha P i]
    rfl
  intro x
  exact DFunLike.congr_fun heq x

/-- The eight-member list, with every member lifted by the per-family route. -/
theorem nNielsenFacList_lifts_families {alpha : ℕ} (ha : 2 ≤ alpha) (z y x : ℤ_[2])
    (κ : ℤ_[2]ˣ) (w p q k : ℤ_[2]) :
    ∀ g ∈ nNielsenFacList z y x κ w p q k, NNielsenFacLifts ha g := by
  intro g hg
  simp only [nNielsenFacList, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact nNielsenFacLifts_of_param_families ha _ _ (nFamN2_admissible z) _ _
  · exact nNielsenFacLifts_of_param_families ha _ _ (nFamN3_admissible y) _ _
  · exact nNielsenFacLifts_of_param_families ha _ _ (nFamN2_admissible x) _ _
  · exact nNielsenFacLifts_of_param_families ha _ _ (nFamN4_admissible κ) _ _
  · exact nNielsenFacLifts_of_param_families ha _ _ (nFamN3_admissible w) _ _
  · exact nNielsenFacLifts_of_param_families ha _ _ (nFamN5_admissible p) _ _
  · exact nNielsenFacLifts_of_param_families ha _ _ (nFamN6_admissible q) _ _
  · exact nNielsenFacLifts_of_param_families ha _ _ (nFamN1_admissible k) _ _

/-! ## Stress pins

Instantiations of the statements above at concrete data, so that a later reshaping cannot
silently make them vacuous (the convention of `N.lean` §9). -/

section StressPins

/-- The identity parameter is admissible. -/
theorem nNielsenFac_id_admissible :
    NStabParam.Admissible ⟨0, 0, 0, 0, 0, (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])⟩ where
  det := by rw [Matrix.det_one]; exact isUnit_one
  couple_p := by simp
  couple_q := by simp

/-- The identity parameter factors through the eight slots. -/
example : ∃ (k q p w x y z : ℤ_[2]) (κ : ℤ_[2]ˣ), (w = 0 ∨ w = 1) ∧
    (κ : ℤ_[2]) = (1 : Matrix (Fin 2) (Fin 2) ℤ_[2]).det ∧
    (⟨0, 0, 0, 0, 0, 1⟩ : NStabParam).act = (nFamN1 k).act ∘ (nFamN6 q).act ∘ (nFamN5 p).act ∘
      (nFamN3 w).act ∘ (nFamN4 κ).act ∘ (nFamN2 x).act ∘ (nFamN3 y).act ∘ (nFamN2 z).act :=
  nNielsen_factorization ⟨0, 0, 0, 0, 0, 1⟩ nNielsenFac_id_admissible

/-- **The finite list at `alpha = 2`**, the smallest valid exponent, written out. -/
example (P : NStabParam) (hP : P.Admissible) :
    ∃ (z y x : ℤ_[2]) (κ : ℤ_[2]ˣ) (w p q k : ℤ_[2]),
      (nNielsenFacList z y x κ w p q k).length = 8 ∧
      (∀ g ∈ nNielsenFacList z y x κ w p q k,
        (∀ v, nFrameOrientation (by omega : 2 ≤ 2) 0 (g v)
            = nFrameOrientation (by omega : 2 ≤ 2) 0 v) ∧
          NFrameCupIsometry (by omega : 2 ≤ 2) g ∧ NNielsenFacLifts (by omega : 2 ≤ 2) g) ∧
      (∀ v, nNielsenFacCompose (nNielsenFacList z y x κ w p q k) v = nNielsenFacMap P v) ∧
      NNielsenFacLifts (by omega : 2 ≤ 2) (nNielsenFacCompose (nNielsenFacList z y x κ w p q k)) :=
  nNielsenFac_finite_list (by omega) P hP

/-- Family N5 at `p = 1` really moves the torsion slot of `x̄₂` (`x̄₂ ↦ t + x̄₂`): the coupled
`t`-shift is not preserving nothing. -/
example : (nFamN5 1).act ((0 : ZMod 2), 0, 0, 1) = ((1 : ZMod 2), 0, 0, 1) := by
  rw [nFamN5_act]; simp

private theorem nNielsenFac_nRed_two : nRed (2 : ℤ_[2]) = 0 := by
  rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num, map_natCast]
  decide

/-- And at `p = 2` it does not: the coupled `t`-shift is `p mod 2`. -/
example : (nFamN5 2).act ((0 : ZMod 2), 0, 0, 1) = ((0 : ZMod 2), 0, 0, 1) := by
  rw [nFamN5_act, nNielsenFac_nRed_two]; simp

private theorem nNielsenFac_det_one : IsUnit (1 : Matrix (Fin 2) (Fin 2) ℤ_[2]).det := by
  rw [Matrix.det_one]; exact isUnit_one

/-- The block factorization at the identity matrix, whose `(1,0)` entry is *not* a unit (the
branch of `nNielsenFac_gl2_factor` where the Boolean slot `N3(w)` does real work). -/
example : ∃ (w x y z : ℤ_[2]), (w = 0 ∨ w = 1) ∧
    (1 : Matrix (Fin 2) (Fin 2) ℤ_[2]) = planeElemV w * nPlaneDet nNielsenFac_det_one.unit
      * planeElemU x * planeElemV y * planeElemU z :=
  nNielsenFac_gl2_factor 1 nNielsenFac_det_one

end StressPins

#print axioms NStabParam.act
#print axioms NStabParam.act_apply
#print axioms NStabParam.act_t
#print axioms NStabParam.act_x1
#print axioms NStabParam.act_sigma
#print axioms NStabParam.act_x2
#print axioms nNielsenFacBlock
#print axioms nFamN1
#print axioms nFamN2
#print axioms nFamN3
#print axioms nFamN4
#print axioms nFamN5
#print axioms nFamN6
#print axioms nNielsenFacBlock_act
#print axioms nNielsenFacBlock_act_comp
#print axioms nNielsenFacBlock_one_act
#print axioms nFamN1_act
#print axioms nFamN2_act
#print axioms nFamN3_act
#print axioms nFamN4_act
#print axioms nFamN5_act
#print axioms nFamN6_act
#print axioms nNielsenFacBlock_admissible
#print axioms nFamN1_admissible
#print axioms nFamN2_admissible
#print axioms nFamN3_admissible
#print axioms nFamN4_admissible
#print axioms nFamN5_admissible
#print axioms nFamN6_admissible
#print axioms nNielsenFac_gl2_factor
#print axioms nNielsenFac_nRed_val
#print axioms nNielsenFac_couple
#print axioms nNielsen_factorization

#print axioms nNielsenFacLift
#print axioms nNielsenFacLift_comp
#print axioms nNielsenFacMap
#print axioms nNielsenFacMap_eq_lift
#print axioms nNielsenFacMap_toAdd
#print axioms nNielsenFacMap_comp_of_act
#print axioms nNielsenFacMap_mul
#print axioms nNielsenFacMap_continuous
#print axioms nNielsenFacEquiv
#print axioms nNielsenFacEquiv_apply
#print axioms nNielsenFacMap_coord_x1
#print axioms nNielsenFac_orientation
#print axioms nNielsenFac_mark_zero
#print axioms nNielsenFac_mark_one
#print axioms nNielsenFac_mark_two
#print axioms nNielsenFac_mark_three
#print axioms nNielsenFacMap_mark
#print axioms nNielsenFac_mat
#print axioms nNielsenFac_cupIsometry
#print axioms nNielsenFacBlock_act_act
#print axioms nNielsenFac_N1_inv
#print axioms nNielsenFac_N2_inv
#print axioms nNielsenFac_N3_inv
#print axioms nNielsenFac_N4_inv
#print axioms nNielsenFac_N5_inv
#print axioms nNielsenFac_N6_inv
#print axioms nNielsenFacN1
#print axioms nNielsenFacN2
#print axioms nNielsenFacN3
#print axioms nNielsenFacN4
#print axioms nNielsenFacN5
#print axioms nNielsenFacN6
#print axioms NNielsenFacLifts
#print axioms nNielsenFacLifts_refl
#print axioms nNielsenFacLifts_trans
#print axioms nNielsenFacCompose
#print axioms nNielsenFacLifts_compose
#print axioms nNielsenFacLifts_of_param
#print axioms nNielsenFac_props_of_param
#print axioms nNielsenFacList
#print axioms nNielsenFacList_length
#print axioms nNielsenFacCompose_list
#print axioms nNielsenFacList_props
#print axioms nNielsenFac_finite_list
#print axioms nNielsenFac_param_realized

#print axioms nNielsenFacHom
#print axioms nNielsenFac_frame_hom_ext
#print axioms nNielsenFacRows
#print axioms nNielsenFac_ext_core
#print axioms nNielsenFac_frameAction_of_rows
#print axioms nNielsenFac_stabilizer_list
#print axioms nNielsenFacTransport
#print axioms nNielsenFacTransport_apply
#print axioms nNielsenFacTransport_mark
#print axioms nNielsenFac_stabilizer_induced

#print axioms nNielsenFac_fullFrameMark
#print axioms nNielsenFacLifts_of_param_families
#print axioms nNielsenFacList_lifts_families

#print axioms nNielsenFac_id_admissible
#print axioms nNielsenFac_nRed_two
#print axioms nNielsenFac_det_one

end
end GQ2.Dyadic.MarkedCore
