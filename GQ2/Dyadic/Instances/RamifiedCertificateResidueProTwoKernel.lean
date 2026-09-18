/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.RamifiedCertificateResidueUnitReciprocity
import GQ2.ProfiniteTwoPrimary

/-!
# Unit-trivial pro-two characters and the marked unramified kernel

A continuous two-adic character that kills reciprocity units is a scalar multiple of the marked
unramified character. This kernel statement needs no normalization of the full Frobenius value.
-/

namespace GQ2.Dyadic
noncomputable section
open GQ2
local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  {R : LocalReciprocity}

/-- Every unit-trivial continuous two-adic character factors through the marked unramified
coordinate, with its uniformizer value as the scalar. -/
theorem markedRecip_twoAdic_character_eq
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (phi : ContinuousMonoidHom (GalKab K) (Multiplicative ℤ_[2]))
    (hunit : ∀ u : (↥K)ˣ, ‖((u : ↥K) : ℚ̄₂)‖ = 1 → phi (B.recip u) = 1)
    (g : GalKab K) :
    (phi g).toAdd = -(phi (B.recip (uniformizerK K FF))).toAdd * (B.nu_ur g).toAdd := by
  have heq : (fun a : GalKab K ↦ (phi a).toAdd) =
      fun a : GalKab K ↦ -(phi (B.recip (uniformizerK K FF))).toAdd * (B.nu_ur a).toAdd := by
    refine Continuous.ext_on B.denseRange_recip
      (continuous_toAdd.comp phi.continuous_toFun)
      (continuous_const.mul (continuous_toAdd.comp B.continuous_nu_ur)) ?_
    rintro _ ⟨x, rfl⟩
    dsimp only
    obtain ⟨u, n, hx, hu⟩ := exists_unit_zpow_decomp K FF x
    have hnu := B.nu_ur_recip_of_decomp x u (uniformizerK K FF) n hx hu
      (norm_uniformizerK_lt_one K FF) (uniformizerK_max K FF)
    rw [hnu, hx, map_mul, map_zpow, map_mul, map_zpow, hunit u hu, one_mul]
    change n • (phi (B.recip (uniformizerK K FF))).toAdd =
      -(phi (B.recip (uniformizerK K FF))).toAdd * ((-n : ℤ) : ℤ_[2])
    rw [zsmul_eq_mul]
    push_cast
    ring
  exact congrFun heq g

/-- Unit-trivial two-adic characters kill the marked unramified kernel; the Frobenius scalar
need not have been identified. -/
theorem markedRecip_twoAdic_character_eq_one_of_nu_eq_one
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    (phi : ContinuousMonoidHom (GalKab K) (Multiplicative ℤ_[2]))
    (hunit : ∀ u : (↥K)ˣ, ‖((u : ↥K) : ℚ̄₂)‖ = 1 → phi (B.recip u) = 1)
    {g : GalKab K} (hg : B.nu_ur g = 1) : phi g = 1 := by
  apply Multiplicative.toAdd.injective
  rw [markedRecip_twoAdic_character_eq B FF phi hunit g, hg]
  exact mul_zero _

/-- The marked unramified kernel is contained in the kernel of the two-primary projection of
the canonical residue coordinate. This is a kernel comparison, not a Frobenius normalization. -/
theorem absoluteResidueCoordinateKAb_proTwo_eq_one_of_nu_eq_one
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    {g : GalKab K} (hg : B.nu_ur g = 1) :
    maxProPMk 2 Zhat (absoluteResidueCoordinateKAb (K := K) g) = 1 := by
  let phi : ContinuousMonoidHom (GalKab K) (Multiplicative ℤ_[2]) :=
    (ztwoIota : ContinuousMonoidHom Ztwo (Multiplicative ℤ_[2])).comp
      ((maxProPMk 2 Zhat).comp (absoluteResidueCoordinateKAb (K := K)))
  have hunit : ∀ u : (↥K)ˣ, ‖((u : ↥K) : ℚ̄₂)‖ = 1 → phi (B.recip u) = 1 := by
    intro u hu
    change ztwoIota (maxProPMk 2 Zhat
      (absoluteResidueCoordinateKAb (K := K) (B.recip u))) = 1
    rw [absoluteResidueUnitReciprocity_of_norm_reciprocity B FF u hu, map_one]
    exact map_one ztwoIota
  have h := markedRecip_twoAdic_character_eq_one_of_nu_eq_one B FF phi hunit hg
  exact ztwoIota.injective (h.trans (map_one ztwoIota).symm)

/-- Any pro-two subgroup on which the marked unramified character vanishes acts trivially on
the canonical absolute residue field. -/
theorem proTwo_le_absoluteInertia_of_nu_eq_one
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (W : Subgroup (GalK K)) (hclosed : IsClosed (W : Set (GalK K)))
    (hpro : IsProP 2 W) (hnu : ∀ g : W, B.nu_ur (toAbK K g.val) = 1) :
    W ≤ absoluteInertiaK (K := K) := by
  letI : CommGroup Zhat :=
    { (inferInstance : Group Zhat) with mul_comm := Words.Mpc.zhat_mul_comm }
  letI : CompactSpace W := isCompact_iff_compactSpace.mp hclosed.isCompact
  let incl : ContinuousMonoidHom W (GalK K) := ⟨W.subtype, continuous_subtype_val⟩
  let phi := (absoluteResidueCoordinateK (K := K)).comp incl
  intro g hg
  rw [← absoluteResidueCoordinateK_ker]
  change absoluteResidueCoordinateK (K := K) g = 1
  apply eq_one_of_omegaTwo_fixed_of_maxProTwo_eq_one
  · have h := congrArg phi (zpowHat_omega2_eq_self hpro (⟨g, hg⟩ : W))
    rw [map_zpowHat] at h
    exact h
  · rw [← absoluteResidueCoordinateKAb_toAbK]
    exact absoluteResidueCoordinateKAb_proTwo_eq_one_of_nu_eq_one B FF (hnu ⟨g, hg⟩)

#print axioms markedRecip_twoAdic_character_eq
#print axioms markedRecip_twoAdic_character_eq_one_of_nu_eq_one
#print axioms absoluteResidueCoordinateKAb_proTwo_eq_one_of_nu_eq_one
#print axioms proTwo_le_absoluteInertia_of_nu_eq_one

end
end GQ2.Dyadic
