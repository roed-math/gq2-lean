/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5.1
-/
import GQ2.Dyadic.MarkedCore.NNielsenGenerators

/-!
# The N frame-stabilizer factorization into the six Nielsen families

Wave 364, lane MC-N. Draft head; see the lane note `docs/dyadic/w364-nfactor-note.md`.
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
    (nNielsenFacBlock g).act (v1, a, b, c) = (v1, a, b * g 0 0 + c * g 0 1, b * g 1 0 + c * g 1 1) := by
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
    ∃ (w x y z : ℤ_[2]),
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
      g 1 0, (g 1 1 - 1) * ((hc.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]), ?_⟩
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
      g 1 0 - g 0 0, (g 1 1 - g 0 1 - 1) * ((hca.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]), ?_⟩
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

with `κ = det g`, `w ∈ {0, 1}`, `(x, y, z)` the elementary parameters of
`nNielsenFac_gl2_factor`, `p, q` the parameters of `P` itself, and `k = τ + p̄·q̄` (read in
`ℤ₂` through `ZMod.val`). The memo's recipe "kill the block by N2–N4, then `(p, q)` by N5/N6,
then `τ` by N1" is followed literally: the block is a matrix identity pushed through
`nNielsenFacBlock_act_comp`, and the `t`-slot closes because the two admissibility couplings
say exactly that the `t`-shifts carried by N5/N6 recombine to `(τ_σ, τ_{x₂})`
(`nNielsenFac_couple`). Completely `α`-free, as the N stabilizer is. -/
theorem nNielsen_factorization (P : NStabParam) (hP : P.Admissible) :
    ∃ (k q p w x y z : ℤ_[2]) (κ : ℤ_[2]ˣ),
      P.act = (nFamN1 k).act ∘ (nFamN6 q).act ∘ (nFamN5 p).act ∘ (nFamN3 w).act ∘
        (nFamN4 κ).act ∘ (nFamN2 x).act ∘ (nFamN3 y).act ∘ (nFamN2 z).act := by
  obtain ⟨w, x, y, z, hg⟩ := nNielsenFac_gl2_factor P.g hP.det
  set k : ℤ_[2] := (((P.tau + nRed P.p * nRed P.q).val : ℕ) : ℤ_[2]) with hk
  refine ⟨k, P.q, P.p, w, x, y, z, hP.det.unit, ?_⟩
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

end
end GQ2.Dyadic.MarkedCore
