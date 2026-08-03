/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Analysis.Normed.Module.FiniteDimension
import GQ2.Dyadic.ResidueLocalFieldBridge

/-!
# The extension-level ramification/inertia interface

`ResidueLocalFieldBridge` identifies the spectral residue field used by the dyadic development
with the residue field of the norm valuation ring.  This file makes the next extension-level step.

For a finite intermediate field `K / ℚ₂`, the norm valuation of `K` is proved to extend the norm
valuation of `ℚ₂`.  Consequently Mathlib supplies the algebra of their valuation rings.  This
algebra is finite: after choosing a `ℚ₂`-basis of `K`, continuity of its coordinate map uniformly
bounds the coordinates of norm-integer elements; multiplication by one sufficiently small
nonzero scalar embeds the target integer ring into a finite free module over the base integer
ring.  Its rank is therefore `[K : ℚ₂]`, and the prime over the base maximal ideal is automatically
unique: finiteness gives integrality, and every such prime is maximal, hence is the unique maximal
ideal of the local target ring.

This reduces the fundamental identity to one genuinely extension-level input which the current
Mathlib local-field API does not supply: identification of Mathlib's ring-theoretic
`ramificationIdx'` with `FF.e`.

Flatness is derived: the base norm valuation ring is identified with `ℤ₂`, hence is a DVR, while
`Valuation.HasExtension` supplies torsion-freeness of the target; torsion-free modules over a
Dedekind domain are flat.  The inertia-degree comparison is also derived from the two residue
cardinalities and `Module.natCard_eq_pow_finrank`.  Under the remaining input,
`Ideal.sum_ramification_inertia_eq_finrank` has a one-term sum and proves
`[K : ℚ₂] = FF.e * FF.f`.
-/

namespace GQ2.Dyadic.SpectralLocalField

open scoped NNReal NormedField

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable section

/-- The norm valuation ring of the dyadic base field. -/
abbrev BaseInteger := (NormedField.valuation (K := ℚ_[2])).integer

/-- The norm valuation ring of a spectral intermediate field. -/
abbrev ExtensionInteger (K : IntermediateField ℚ_[2] ℚ̄₂) :=
  (NormedField.valuation (K := K)).integer

/-- The norm valuation ring of `ℚ₂` is the usual ring `ℤ₂`. -/
def baseIntegerEquivPadicInt : BaseInteger ≃+* ℤ_[2] where
  toFun x := ⟨x, by
    have hx := x.2
    change ‖(x : ℚ_[2])‖₊ ≤ 1 at hx
    exact_mod_cast hx⟩
  invFun x := ⟨x, by
    change ‖(x : ℚ_[2])‖₊ ≤ 1
    have hx := x.2
    change ‖(x : ℚ_[2])‖ ≤ 1 at hx
    exact_mod_cast hx⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The base norm valuation ring is a DVR, transported from `ℤ₂`. -/
theorem baseInteger_isDiscreteValuationRing : IsDiscreteValuationRing BaseInteger :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    baseIntegerEquivPadicInt.symm

/-- The equivalence with `ℤ₂` carries the maximal ideal of the base norm valuation ring to the
maximal ideal of `ℤ₂`. -/
theorem baseInteger_map_maximalIdeal :
    Ideal.map baseIntegerEquivPadicInt.toRingHom
        (IsLocalRing.maximalIdeal BaseInteger) =
      IsLocalRing.maximalIdeal ℤ_[2] := by
  apply IsLocalRing.eq_maximalIdeal
  exact (IsLocalRing.maximalIdeal.isMaximal BaseInteger).map_bijective
    baseIntegerEquivPadicInt.toRingHom baseIntegerEquivPadicInt.bijective

/-- The residue field of the base norm valuation ring is `ZMod 2`. -/
def baseIntegerResidueEquivZMod :
    IsLocalRing.ResidueField BaseInteger ≃+* ZMod 2 :=
  (Ideal.quotientEquiv
    (IsLocalRing.maximalIdeal BaseInteger)
    (IsLocalRing.maximalIdeal ℤ_[2])
    baseIntegerEquivPadicInt baseInteger_map_maximalIdeal.symm).trans
      PadicInt.residueField

/-- The base norm valuation ring has residue cardinality two. -/
theorem baseInteger_residue_card :
    Nat.card (IsLocalRing.ResidueField BaseInteger) = 2 := by
  rw [Nat.card_congr baseIntegerResidueEquivZMod.toEquiv, Nat.card_zmod]

/-- The inherited norm on an intermediate field extends the norm on `ℚ₂`, in Mathlib's
valuation-extension sense.  This is the canonical source of the valuation-ring algebra used
below. -/
theorem normValuation_hasExtension (K : IntermediateField ℚ_[2] ℚ̄₂) :
    (NormedField.valuation (K := ℚ_[2])).HasExtension
      (NormedField.valuation (K := K)) := by
  constructor
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  simp only [Valuation.comap_apply, NormedField.valuation_apply]
  have hnorm : ‖(algebraMap ℚ_[2] K x : K)‖₊ = ‖x‖₊ := nnnorm_algebraMap' K x
  rw [hnorm]

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]

/-- The norm valuation ring of a finite extension of `ℚ₂` is finite over the base norm valuation
ring.

The proof is a direct bounded-coordinate argument, avoiding an integral-closure finiteness API.
Choose a `ℚ₂`-basis of `K`.  Its continuous coordinate equivalence has an operator-norm bound on
the unit ball.  After multiplication by a sufficiently small nonzero `c : ℚ₂`, every coordinate
of every norm-integer element lies in `BaseInteger`.  The resulting `BaseInteger`-linear map into
the finite free coordinate module is injective.  Since `BaseInteger` is a DVR, hence noetherian,
its submodule is finite. -/
theorem integer_finite :
    letI := normValuation_hasExtension K
    Module.Finite BaseInteger (ExtensionInteger K) := by
  letI := normValuation_hasExtension K
  letI : IsDiscreteValuationRing BaseInteger := baseInteger_isDiscreteValuationRing
  letI : IsNoetherianRing BaseInteger := inferInstance
  let b := Module.Basis.ofVectorSpace ℚ_[2] K
  let R : ℝ := max ‖b.equivFunL.toContinuousLinearMap‖ 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨c : ℚ_[2], hcpos, hcR⟩ := NormedField.exists_norm_lt ℚ_[2] (inv_pos.mpr hR)
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
  let coord : ExtensionInteger K →
      Module.Basis.ofVectorSpaceIndex ℚ_[2] K → BaseInteger := fun x i =>
    ⟨c * b.equivFun (x : K) i, by
      change ‖c * b.equivFun (x : K) i‖₊ ≤ 1
      rw [← NNReal.coe_le_coe]
      push_cast
      have hxnorm : ‖(x : K)‖ ≤ 1 := by
        have hxnn : ‖(x : K)‖₊ ≤ 1 := x.2
        exact_mod_cast hxnn
      have hrepr : ‖b.equivFun (x : K) i‖ ≤ R := by
        calc
          ‖b.equivFun (x : K) i‖ ≤ ‖b.equivFunL (x : K)‖ := norm_le_pi_norm _ _
          _ ≤ ‖b.equivFunL.toContinuousLinearMap‖ * ‖(x : K)‖ :=
            b.equivFunL.toContinuousLinearMap.le_opNorm _
          _ ≤ ‖b.equivFunL.toContinuousLinearMap‖ * 1 := by gcongr
          _ = ‖b.equivFunL.toContinuousLinearMap‖ := mul_one _
          _ ≤ R := le_max_left _ _
      exact le_of_lt <| calc
        ‖c * b.equivFun (x : K) i‖ = ‖c‖ * ‖b.equivFun (x : K) i‖ := norm_mul _ _
        _ ≤ ‖c‖ * R := mul_le_mul_of_nonneg_left hrepr (norm_nonneg _)
        _ < R⁻¹ * R := mul_lt_mul_of_pos_right hcR hR
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hR)⟩
  let f : ExtensionInteger K →ₗ[BaseInteger]
      (Module.Basis.ofVectorSpaceIndex ℚ_[2] K → BaseInteger) :=
    { toFun := coord
      map_add' := by
        intro x y
        funext i
        apply Subtype.ext
        simp [coord, b, map_add, mul_add]
      map_smul' := by
        intro r x
        funext i
        apply Subtype.ext
        change c * b.equivFun ((r : ℚ_[2]) • (x : K)) i =
          (r : ℚ_[2]) * (c * b.equivFun (x : K) i)
        rw [map_smul]
        simp only [Pi.smul_apply]
        change c * ((r : ℚ_[2]) * b.equivFun (x : K) i) =
          (r : ℚ_[2]) * (c * b.equivFun (x : K) i)
        ring }
  apply Module.Finite.of_injective f
  intro x y hxy
  apply Subtype.ext
  apply b.equivFun.injective
  funext i
  apply mul_left_cancel₀ hc0
  have hi := congrFun hxy i
  exact congrArg Subtype.val hi

/-- The ring-theoretic rank of the extension of norm valuation rings is the field degree.  The
proof uses that both valuation rings have their ambient fields as fraction fields. -/
theorem integer_finrank_eq_field_finrank :
    letI := normValuation_hasExtension K
    Module.finrank BaseInteger (ExtensionInteger K) = Module.finrank ℚ_[2] K := by
  letI := normValuation_hasExtension K
  letI := integer_finite K
  exact (Algebra.IsAlgebraic.finrank_of_isFractionRing
    BaseInteger ℚ_[2] (ExtensionInteger K) K).symm

/-- The norm valuation-ring extension is automatically flat.  The extension relation gives
torsion-freeness, and the base ring is a DVR (hence a Dedekind domain). -/
theorem integer_flat :
    letI := normValuation_hasExtension K
    Module.Flat BaseInteger (ExtensionInteger K) := by
  letI := normValuation_hasExtension K
  letI : IsDiscreteValuationRing BaseInteger := baseInteger_isDiscreteValuationRing
  letI : IsDedekindDomain BaseInteger := inferInstance
  infer_instance

/-- The norm valuation-ring extension identifies Mathlib's ring-theoretic inertia degree with the
filtration residue degree `FF.f`.  This uses the already-proved target residue
cardinality `2 ^ FF.f` and the base residue cardinality `2`. -/
theorem integer_inertiaDeg_eq_filtration_f
    (FF : GQ2.DyadicUnitFiltration K) :
    letI := normValuation_hasExtension K
    (IsLocalRing.maximalIdeal (ExtensionInteger K)).inertiaDeg' BaseInteger = FF.f := by
  letI := normValuation_hasExtension K
  letI := integer_finite K
  let p := IsLocalRing.maximalIdeal BaseInteger
  let q := IsLocalRing.maximalIdeal (ExtensionInteger K)
  letI : p.IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
  letI : q.IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
  letI : q.LiesOver p := inferInstance
  letI : Field (BaseInteger ⧸ p) := Ideal.Quotient.field p
  letI : Field (ExtensionInteger K ⧸ q) := Ideal.Quotient.field q
  rw [← Ideal.inertiaDeg_eq_inertiaDeg' p q, Ideal.inertiaDeg_algebraMap]
  apply Nat.pow_right_injective (le_refl 2)
  have hcard := Module.natCard_eq_pow_finrank
    (K := BaseInteger ⧸ p) (V := ExtensionInteger K ⧸ q)
  change Nat.card (IsLocalRing.ResidueField (ExtensionInteger K)) =
    Nat.card (IsLocalRing.ResidueField BaseInteger) ^
      Module.finrank (BaseInteger ⧸ p) (ExtensionInteger K ⧸ q) at hcard
  rw [baseInteger_residue_card] at hcard
  exact hcard.symm.trans (normInteger_residueField_card_eq_pow_f K FF)

/-- The maximal ideal of the target norm valuation ring is the unique prime over the maximal ideal
of the base.  Thus prime uniqueness is a theorem here, not an extra field of the conditional
package. -/
@[implicit_reducible]
def uniquePrimesOverMaximal :
    letI := normValuation_hasExtension K
    Unique ((IsLocalRing.maximalIdeal BaseInteger).primesOver (ExtensionInteger K)) := by
  letI := normValuation_hasExtension K
  letI := integer_finite K
  letI : Algebra.IsIntegral BaseInteger (ExtensionInteger K) :=
    Algebra.IsIntegral.of_finite BaseInteger (ExtensionInteger K)
  let p := IsLocalRing.maximalIdeal BaseInteger
  let q := IsLocalRing.maximalIdeal (ExtensionInteger K)
  letI : q.IsPrime := (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  letI : q.LiesOver p := inferInstance
  exact
    { default := Ideal.primesOver.mk p q
      uniq := fun Q => SetCoe.ext (IsLocalRing.eq_maximalIdeal (I := Q.1) inferInstance) }

/-- The exact remaining extension-level data needed by the ramification/inertia sum theorem.

The valuation-ring algebra, finiteness, flatness, the unique prime over the base maximal ideal, and
the inertia-degree comparison are already derived; the package retains only the ramification-index
comparison with the dyadic filtration parameter. -/
structure RamificationInertiaCompatibility (FF : GQ2.DyadicUnitFiltration K) : Prop where
  ramificationIdx_eq :
    letI := normValuation_hasExtension K
    (IsLocalRing.maximalIdeal (ExtensionInteger K)).ramificationIdx' BaseInteger = FF.e

namespace RamificationInertiaCompatibility

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
variable {FF : GQ2.DyadicUnitFiltration K}

/-- The one-prime specialization of Mathlib's sum formula at the norm valuation rings. -/
theorem integer_finrank_eq_ramification_mul_inertia
    : letI := normValuation_hasExtension K
    Module.finrank BaseInteger (ExtensionInteger K) =
      (IsLocalRing.maximalIdeal (ExtensionInteger K)).ramificationIdx' BaseInteger *
        (IsLocalRing.maximalIdeal (ExtensionInteger K)).inertiaDeg' BaseInteger := by
  letI := normValuation_hasExtension K
  letI := integer_finite K
  letI : Module.Flat BaseInteger (ExtensionInteger K) := integer_flat K
  letI : Unique ((IsLocalRing.maximalIdeal BaseInteger).primesOver (ExtensionInteger K)) :=
    uniquePrimesOverMaximal K
  letI : Fintype ((IsLocalRing.maximalIdeal BaseInteger).primesOver (ExtensionInteger K)) :=
    Fintype.ofFinite _
  have hsum := Ideal.sum_ramification_inertia_eq_finrank
    (IsLocalRing.maximalIdeal BaseInteger) (ExtensionInteger K)
  rw [Fintype.sum_unique] at hsum
  change
    (IsLocalRing.maximalIdeal (ExtensionInteger K)).ramificationIdx' BaseInteger *
      (IsLocalRing.maximalIdeal (ExtensionInteger K)).inertiaDeg' BaseInteger =
        Module.finrank BaseInteger (ExtensionInteger K) at hsum
  exact hsum.symm

/-- **Conditional arbitrary-`K` fundamental identity.**  The ramification-index comparison implies
the degree formula used by the corrected field selector. -/
theorem field_finrank_eq_e_mul_f
    (C : RamificationInertiaCompatibility K FF) :
    Module.finrank ℚ_[2] K = FF.e * FF.f := by
  rw [← integer_finrank_eq_field_finrank K,
    integer_finrank_eq_ramification_mul_inertia (K := K),
    C.ramificationIdx_eq,
    integer_inertiaDeg_eq_filtration_f K FF]

/-- Regression: the compatibility package feeds the existing arbitrary-field parameter
constructor without any additional degree or divisibility hypothesis. -/
def finiteDyadicParameters
    (C : RamificationInertiaCompatibility K FF) :
    GQ2.Dyadic.FiniteDyadicParameters K FF :=
  GQ2.Dyadic.FiniteDyadicParameters.ofFundamentalIdentity FF
    (field_finrank_eq_e_mul_f C)

/-- Focused regression: the constructor obtained from the extension-level package has the field
degree, ramification index, residue degree, and residue cardinality expected by the corrected
selector. -/
theorem finiteDyadicParameters_regression
    (C : RamificationInertiaCompatibility K FF) :
    (finiteDyadicParameters C).params.n = Module.finrank ℚ_[2] K ∧
      (finiteDyadicParameters C).params.e = FF.e ∧
      (finiteDyadicParameters C).params.f = FF.f ∧
      (finiteDyadicParameters C).params.qK = GQ2.Dyadic.qOf K FF := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  exact (GQ2.Dyadic.FiniteDyadicParameters.params_e_eq_iff_fundamentalIdentity
    (finiteDyadicParameters C)).2 (field_finrank_eq_e_mul_f C)

end RamificationInertiaCompatibility

end

end GQ2.Dyadic.SpectralLocalField
