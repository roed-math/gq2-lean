/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.KeystoneDelta
import GQ2.WordCoh2R

/-!
# The `ι_{Γ_R}`-computation rule

The `Γ_R` twin of `GQ2/IotaGammaA.lean`: the coboundary indicator `ι_Γ`
(`Phase140.iotaB`, the `Q⁰`-valuation) is computed, over the raw candidate carrier
`GR = F₄ ⧸ N_R`, by the **Roe word-relator obstruction** of the `WordCoh2R` degree-2
presentation comparison:

* `iotaB_eq_obsR` — `ι_{Γ_R} φ = obs_R φ` for every continuous 2-cocycle `φ`: both are
  `𝔽₂`-valued with the *same* vanishing locus (`iotaB_eq_zero_iff` vs `WordCoh2R.obs_ker_eq_B2_R`),
  hence equal.
* `iotaB_eq_levelFactor_obsR` — the evaluation form: `ι_{Γ_R} φ` is the (tame + Roe wild) relator
  obstruction `F.obs` of **any** finite `R`-admissible-level factorization `F` of the
  `(1,1)`-normalization of `φ` (`obsFun_eq_R` well-definedness).
* `QZero_eq_obsR` / `QZero_eq_levelFactor_obsR` — the same, specialized to the base determinant
  form: `Q⁰_{Γ_R,ρ'}(c)` is the Roe relator obstruction of any level factorization of the
  (normalized) graph pullback.

Everything is glue over proved technology: `iotaB`/`iotaB_eq_zero_iff` and
`graphPullback_mem_Z2_of_cocycle`/`QZero` are **generic in `Γ`** and reused verbatim; the only
`Γ_R`-specific inputs are `WordCoh2R.obs_ker_eq_B2_R` and `WordCoh2R.obsFun_eq_R`.
-/

namespace GQ2

namespace IotaGammaR

open SectionEight SectionEight.AffineTLift WordCohBridgeR WordCoh2R ContCoh

variable [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)]
variable (htriv : ∀ (x : GR) (m : ZMod 2), x • m = m)
include htriv

omit [ContinuousSMul GR (ZMod 2)] in
/-- **The `ι_{Γ_R}`-computation rule**: the coboundary indicator agrees with the Roe
word-relator obstruction on every continuous 2-cocycle — both are `𝔽₂`-valued with kernel
exactly `B²(Γ_R, 𝔽₂)`. -/
theorem iotaB_eq_obsR (φ : Z2 GR (ZMod 2)) :
    iotaB (φ : GR × GR → ZMod 2) = WordCoh2R.obs_R htriv φ := by
  have h2 : WordCoh2R.obs_R htriv φ = 0 ↔ (φ : GR × GR → ZMod 2) ∈ B2 GR (ZMod 2) := by
    rw [← AddMonoidHom.mem_ker, obs_ker_eq_B2_R htriv, AddSubgroup.mem_addSubgroupOf]
  exact (by decide : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b) _ _
    (iotaB_eq_zero_iff.trans h2.symm)

omit [ContinuousSMul GR (ZMod 2)] in
/-- **The evaluation form**: `ι_{Γ_R} φ` is the (tame + Roe wild) relator obstruction of *any*
finite `R`-admissible-level factorization of the `(1,1)`-normalization of `φ`. -/
theorem iotaB_eq_levelFactor_obsR (φ : Z2 GR (ZMod 2))
    (F : LevelFactorR (normalizeCochainR (φ : GR × GR → ZMod 2))) :
    iotaB (φ : GR × GR → ZMod 2) = F.obs :=
  (iotaB_eq_obsR htriv φ).trans (obsFun_eq_R htriv φ F)

section QZero

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
variable {ρM : ContinuousMonoidHom GR (Bg ⧸ D.M)}

omit [ContinuousSMul GR (ZMod 2)] in
/-- **`Q⁰` over `Γ_R` is the Roe word-relator obstruction**: the base determinant form evaluates
through `obs_R` at the graph pullback. -/
theorem QZero_eq_obsR (c : VCocycle DD ρM) :
    QZero DD ρM c
      = WordCoh2R.obs_R htriv ⟨graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c,
          graphPullback_mem_Z2_of_cocycle htriv c⟩ :=
  iotaB_eq_obsR htriv ⟨graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c,
    graphPullback_mem_Z2_of_cocycle htriv c⟩

omit [ContinuousSMul GR (ZMod 2)] in
/-- **The consumable form**: `Q⁰_{Γ_R,ρ'}(c)` is the (tame + Roe wild) relator obstruction of any
finite `R`-admissible-level factorization of the normalized graph pullback. -/
theorem QZero_eq_levelFactor_obsR (c : VCocycle DD ρM)
    (F : LevelFactorR (normalizeCochainR
      (graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c))) :
    QZero DD ρM c = F.obs :=
  (QZero_eq_obsR htriv c).trans
    (obsFun_eq_R htriv ⟨graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c,
      graphPullback_mem_Z2_of_cocycle htriv c⟩ F)

end QZero

end IotaGammaR

end GQ2
