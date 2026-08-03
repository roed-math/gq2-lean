/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import GQ2.Dyadic.PrincipalUnitCompletion

/-!
# Power cofinality for dyadic principal units

For a finite extension `K/ℚ₂`, every positive integer power map is locally invertible at `1`:
its strict derivative there is multiplication by that integer, hence is nonzero in characteristic
zero.  Applying the nonarchimedean inverse function theorem to the `2^k`-power map shows that a
sufficiently deep principal-unit subgroup consists of `2^k`-th powers from any prescribed
starting depth.  This proves the exact `DepthPowerCofinal` interface needed to rule out
discontinuous finite `2`-quotients.
-/

namespace GQ2.Dyadic

noncomputable section

open Filter Metric
open scoped Topology

local notation "ℚbar2" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚbar2}

/-- For a finite dyadic field, the depth filtration is cofinal with the images of all `2^k`
power maps.  The proof uses only local invertibility of `x ↦ x^(2^k)` at `1`, not a logarithm
or an assumed Hensel/power-surjectivity theorem. -/
theorem depthPowerCofinal_depthUnits [FiniteDimensional ℚ_[2] K]
    (FF : DyadicUnitFiltration K) (i : ℕ) : DepthPowerCofinal FF i := by
  intro k
  let πK : ↥K := ⟨FF.π, FF.hπ_mem⟩
  letI : NontriviallyNormedField ↥K := NontriviallyNormedField.ofNormNeOne
    ⟨πK, by intro h; exact FF.hπ_ne (congrArg Subtype.val h), ne_of_lt FF.hπ_lt⟩
  letI : CompleteSpace ↥K := FiniteDimensional.complete ℚ_[2] ↥K
  let n : ℕ := 2 ^ k
  let f : ↥K → ↥K := fun x ↦ x ^ n
  have hn : (n : ↥K) ≠ 0 := by
    exact_mod_cast (pow_ne_zero k two_ne_zero)
  have hf : HasStrictDerivAt f (n : ↥K) 1 := by
    simpa [f] using hasStrictDerivAt_pow n (1 : ↥K)
  let r : ℝ := ‖FF.π‖ ^ i
  have hrpos : 0 < r := pow_pos (norm_pos_iff.mpr FF.hπ_ne) i
  have hball : Metric.ball (1 : ↥K) r ∈ 𝓝 (1 : ↥K) :=
    Metric.ball_mem_nhds _ hrpos
  have himage0 : f '' Metric.ball (1 : ↥K) r ∈ 𝓝 (f 1) := by
    rw [← hf.map_nhds_eq hn]
    exact image_mem_map hball
  have himage : f '' Metric.ball (1 : ↥K) r ∈ 𝓝 (1 : ↥K) := by
    simpa [f] using himage0
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp himage
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hεpos FF.hπ_lt
  let j := i + m
  have hij : i ≤ j := Nat.le_add_right i m
  have hπnonneg : 0 ≤ ‖FF.π‖ := norm_nonneg _
  have hri : r ≤ 1 := pow_le_one₀ hπnonneg FF.hπ_lt.le
  have hjlt : ‖FF.π‖ ^ j < ε := by
    calc
      ‖FF.π‖ ^ j = ‖FF.π‖ ^ i * ‖FF.π‖ ^ m := by rw [show j = i + m from rfl, pow_add]
      _ = r * ‖FF.π‖ ^ m := by rfl
      _ ≤ 1 * ‖FF.π‖ ^ m :=
        mul_le_mul_of_nonneg_right hri (pow_nonneg hπnonneg m)
      _ = ‖FF.π‖ ^ m := one_mul _
      _ < ε := hm
  refine ⟨j, hij, ?_⟩
  intro u hu
  have hubound := ((mem_depthUnits K FF.π j u).mp hu).2
  have huball : ((u : ↥K)) ∈ Metric.ball (1 : ↥K) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hubound.trans_lt hjlt
  obtain ⟨x, hxball, hxu⟩ := hε huball
  have hxsub : ‖x - 1‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hxball
  have hxsubone : ‖x - 1‖ < 1 := hxsub.trans_le hri
  have hxnorm : ‖x‖ = 1 := by
    rw [show x = (x - 1) + 1 by ring,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (by rw [norm_one]; exact ne_of_lt hxsubone),
      norm_one, max_eq_right hxsubone.le]
  have hxne : x ≠ 0 := norm_pos_iff.mp (by rw [hxnorm]; exact zero_lt_one)
  let v : (↥K)ˣ := Units.mk0 x hxne
  have hvi : v ∈ depthUnits K FF.π i := by
    exact (mem_depthUnits K FF.π i v).mpr
      ⟨by simpa [v] using hxnorm, by simpa [v] using hxsub.le⟩
  refine ⟨v, hvi, ?_⟩
  apply Units.ext
  change x ^ (2 ^ k) = (u : ↥K)
  simpa [f, n] using hxu

/-- The depth `e+1` specialization used by the completion-torsion theorem. -/
theorem depthPowerCofinal_depthUnits_succ_e [FiniteDimensional ℚ_[2] K]
    (FF : DyadicUnitFiltration K) : DepthPowerCofinal FF (FF.e + 1) :=
  depthPowerCofinal_depthUnits FF (FF.e + 1)

/-- The abstract pro-`2` completion of `U^(e+1)` is torsion-free. -/
theorem isMulTorsionFree_proTwoCompletion_depthUnits_succ_e
    [FiniteDimensional ℚ_[2] K] (FF : DyadicUnitFiltration K) :
    IsMulTorsionFree (proPCompletion 2 ↥(depthUnits K FF.π (FF.e + 1))) :=
  isMulTorsionFree_proTwoCompletion_depthUnits_succ_e_of_powerCofinal FF
    (depthPowerCofinal_depthUnits_succ_e FF)

end

end GQ2.Dyadic
