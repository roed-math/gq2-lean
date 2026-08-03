/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.NumberTheory.Padics.RingHoms
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

The ramification-index comparison is also proved here.  The local-field API makes the integer
ring of the valuative relation a DVR; since `valuativeRel K` was defined from the norm valuation,
an identity-on-elements ring equivalence transports this result to `ExtensionInteger K`.  The
filtration uniformizer then generates its maximal ideal, and
`FF.he : ‖2‖ = ‖π‖ ^ FF.e` gives the exact factorization
`map 𝔪_ℚ₂ = 𝔪_K ^ FF.e`.  Mathlib's `Ideal.ramificationIdx_spec` and
`Ideal.ramificationIdx_eq_ramificationIdx'` identify the ring-theoretic index with `FF.e`.

Flatness is derived: the base norm valuation ring is identified with `ℤ₂`, hence is a DVR, while
`Valuation.HasExtension` supplies torsion-freeness of the target; torsion-free modules over a
Dedekind domain are flat.  The inertia-degree comparison is also derived from the two residue
cardinalities and `Module.natCard_eq_pow_finrank`.
`Ideal.sum_ramification_inertia_eq_finrank` then has a one-term sum and proves
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

/-! ## The norm valuation ring is a DVR -/

/-- The integer ring of the valuative relation represented by the norm is canonically the norm
valuation ring itself.  Both maps are the identity on the underlying field element. -/
def valuativeIntegerEquivNormInteger :
    letI : ValuativeRel K := valuativeRel K
    (ValuativeRel.valuation K).integer ≃+* ExtensionInteger K := by
  letI : ValuativeRel K := valuativeRel K
  letI : (NormedField.valuation (K := K)).Compatible :=
    Valuation.Compatible.ofValuation _
  let hEq := ValuativeRel.isEquiv (ValuativeRel.valuation K)
    (NormedField.valuation (K := K))
  apply RingEquiv.subringCongr
  ext x
  rw [(ValuativeRel.valuation K).mem_integer_iff,
    (NormedField.valuation (K := K)).mem_integer_iff]
  simpa only [map_one] using hEq x 1

/-- The norm valuation ring of a finite spectral intermediate field is a DVR. -/
theorem extensionInteger_isDiscreteValuationRing :
    IsDiscreteValuationRing (ExtensionInteger K) := by
  letI : ValuativeRel K := valuativeRel K
  letI : IsNonarchimedeanLocalField K := isNonarchimedeanLocalField K
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (valuativeIntegerEquivNormInteger K)

/-! ## The filtration uniformizer and maximal-ideal factorization -/

/-- The uniformizer supplied by the dyadic unit filtration, regarded as an element of the norm
valuation ring. -/
def filtrationUniformizerInteger (FF : GQ2.DyadicUnitFiltration K) : ExtensionInteger K :=
  ⟨⟨FF.π, FF.hπ_mem⟩, by
    change ‖FF.π‖₊ ≤ 1
    exact_mod_cast FF.hπ_lt.le⟩

@[simp]
theorem filtrationUniformizerInteger_coe (FF : GQ2.DyadicUnitFiltration K) :
    ((filtrationUniformizerInteger K FF : ExtensionInteger K) : K) =
      ⟨FF.π, FF.hπ_mem⟩ := rfl

/-- The filtration uniformizer generates the maximal ideal of the norm valuation ring. -/
theorem extensionInteger_maximalIdeal_eq_span
    (FF : GQ2.DyadicUnitFiltration K) :
    IsLocalRing.maximalIdeal (ExtensionInteger K) =
      Ideal.span {filtrationUniformizerInteger K FF} := by
  ext x
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  have hspan := Valuation.integer.coe_span_singleton_eq_setOf_le_v_coe
    (filtrationUniformizerInteger K FF)
  rw [Set.ext_iff] at hspan
  change ‖(x : K)‖₊ < 1 ↔ x ∈
    (↑(Ideal.span {filtrationUniformizerInteger K FF}) : Set (ExtensionInteger K))
  rw [hspan x]
  change ‖(x : K)‖₊ < 1 ↔ ‖(x : K)‖₊ ≤ ‖FF.π‖₊
  constructor
  · intro hx
    exact_mod_cast FF.hπ_max ((x : K) : ℚ̄₂) x.1.2 (by exact_mod_cast hx)
  · intro hx
    exact hx.trans_lt (by exact_mod_cast FF.hπ_lt)

/-- The maximal ideal of the base norm valuation ring is generated by `2`. -/
theorem baseInteger_maximalIdeal_eq_span_two :
    IsLocalRing.maximalIdeal BaseInteger = Ideal.span {(2 : BaseInteger)} := by
  have hinj : Function.Injective
      (fun I : Ideal BaseInteger ↦ I.map baseIntegerEquivPadicInt.toRingHom) := by
    intro I J h
    have h' := congrArg
      (fun H : Ideal ℤ_[2] ↦ H.map baseIntegerEquivPadicInt.symm.toRingHom) h
    simpa using h'
  apply hinj
  change Ideal.map baseIntegerEquivPadicInt.toRingHom
      (IsLocalRing.maximalIdeal BaseInteger) =
    Ideal.map baseIntegerEquivPadicInt.toRingHom (Ideal.span {(2 : BaseInteger)})
  rw [baseInteger_map_maximalIdeal, PadicInt.maximalIdeal_eq_span_p, Ideal.map_span,
    Set.image_singleton]
  congr 2

/-- In the target norm valuation ring, the image of `2` and the `FF.e`-th power of the
filtration uniformizer generate the same principal ideal. -/
theorem span_two_eq_span_filtrationUniformizer_pow
    (FF : GQ2.DyadicUnitFiltration K) :
    letI := normValuation_hasExtension K
    Ideal.span {algebraMap BaseInteger (ExtensionInteger K) (2 : BaseInteger)} =
      Ideal.span {(filtrationUniformizerInteger K FF) ^ FF.e} := by
  letI := normValuation_hasExtension K
  ext x
  have htwo := Valuation.integer.coe_span_singleton_eq_setOf_le_v_coe
    (algebraMap BaseInteger (ExtensionInteger K) (2 : BaseInteger))
  have hpi := Valuation.integer.coe_span_singleton_eq_setOf_le_v_coe
    ((filtrationUniformizerInteger K FF) ^ FF.e)
  rw [Set.ext_iff] at htwo hpi
  change x ∈ (↑(Ideal.span
      {algebraMap BaseInteger (ExtensionInteger K) (2 : BaseInteger)}) :
        Set (ExtensionInteger K)) ↔
    x ∈ (↑(Ideal.span {(filtrationUniformizerInteger K FF) ^ FF.e}) :
      Set (ExtensionInteger K))
  rw [htwo x, hpi x]
  change ‖(x : K)‖₊ ≤ ‖(2 : K)‖₊ ↔ ‖(x : K)‖₊ ≤ ‖FF.π ^ FF.e‖₊
  have heq : ‖(2 : K)‖₊ = ‖FF.π ^ FF.e‖₊ := by
    apply NNReal.eq
    change ‖(2 : ℚ̄₂)‖ = ‖FF.π ^ FF.e‖
    simpa only [norm_pow] using FF.he
  rw [heq]

/-- The exact maximal-ideal factorization measured by the filtration ramification index. -/
theorem map_baseInteger_maximalIdeal_eq_pow_extensionInteger_maximalIdeal
    (FF : GQ2.DyadicUnitFiltration K) :
    letI := normValuation_hasExtension K
    Ideal.map (algebraMap BaseInteger (ExtensionInteger K))
        (IsLocalRing.maximalIdeal BaseInteger) =
      IsLocalRing.maximalIdeal (ExtensionInteger K) ^ FF.e := by
  letI := normValuation_hasExtension K
  rw [baseInteger_maximalIdeal_eq_span_two,
    extensionInteger_maximalIdeal_eq_span K FF, Ideal.span_singleton_pow]
  simpa only [Ideal.map_span, Set.image_singleton] using
    span_two_eq_span_filtrationUniformizer_pow K FF

/-- Consecutive powers at the filtration exponent are distinct. -/
theorem extensionInteger_maximalIdeal_pow_not_le_succ
    (FF : GQ2.DyadicUnitFiltration K) :
    ¬ IsLocalRing.maximalIdeal (ExtensionInteger K) ^ FF.e ≤
      IsLocalRing.maximalIdeal (ExtensionInteger K) ^ (FF.e + 1) := by
  intro hle
  have hmem : (filtrationUniformizerInteger K FF) ^ FF.e ∈
      IsLocalRing.maximalIdeal (ExtensionInteger K) ^ (FF.e + 1) := by
    apply hle
    rw [extensionInteger_maximalIdeal_eq_span K FF, Ideal.span_singleton_pow]
    exact Submodule.mem_span_singleton_self _
  rw [extensionInteger_maximalIdeal_eq_span K FF, Ideal.span_singleton_pow] at hmem
  have hspan := Valuation.integer.coe_span_singleton_eq_setOf_le_v_coe
    ((filtrationUniformizerInteger K FF) ^ (FF.e + 1))
  rw [Set.ext_iff] at hspan
  change (filtrationUniformizerInteger K FF) ^ FF.e ∈
    (↑(Ideal.span {(filtrationUniformizerInteger K FF) ^ (FF.e + 1)}) :
      Set (ExtensionInteger K)) at hmem
  rw [hspan ((filtrationUniformizerInteger K FF) ^ FF.e)] at hmem
  change ‖FF.π ^ FF.e‖₊ ≤ ‖FF.π ^ (FF.e + 1)‖₊ at hmem
  have hlt : ‖FF.π ^ (FF.e + 1)‖ < ‖FF.π ^ FF.e‖ := by
    rw [norm_pow, norm_pow, pow_succ]
    exact mul_lt_of_lt_one_right (pow_pos (norm_pos_iff.mpr FF.hπ_ne) _) FF.hπ_lt
  exact (not_le_of_gt (by exact_mod_cast hlt)) hmem

/-- Mathlib's original Dedekind-domain ramification index is the filtration exponent `FF.e`. -/
theorem integer_ramificationIdx_eq_filtration_e
    (FF : GQ2.DyadicUnitFiltration K) :
    letI := normValuation_hasExtension K
    Ideal.ramificationIdx (IsLocalRing.maximalIdeal BaseInteger)
      (IsLocalRing.maximalIdeal (ExtensionInteger K)) = FF.e := by
  letI := normValuation_hasExtension K
  apply Ideal.ramificationIdx_spec
  · exact (map_baseInteger_maximalIdeal_eq_pow_extensionInteger_maximalIdeal K FF).le
  · rw [map_baseInteger_maximalIdeal_eq_pow_extensionInteger_maximalIdeal K FF]
    exact extensionInteger_maximalIdeal_pow_not_le_succ K FF

/-- Mathlib's localized-length ramification index is the filtration exponent `FF.e`. -/
theorem integer_ramificationIdx'_eq_filtration_e
    (FF : GQ2.DyadicUnitFiltration K) :
    letI := normValuation_hasExtension K
    (IsLocalRing.maximalIdeal (ExtensionInteger K)).ramificationIdx' BaseInteger = FF.e := by
  letI := normValuation_hasExtension K
  letI : IsDiscreteValuationRing BaseInteger := baseInteger_isDiscreteValuationRing
  letI : IsDiscreteValuationRing (ExtensionInteger K) :=
    extensionInteger_isDiscreteValuationRing K
  rw [← Ideal.ramificationIdx_eq_ramificationIdx'
    (IsLocalRing.maximalIdeal BaseInteger)
    (IsLocalRing.maximalIdeal (ExtensionInteger K))
    (IsDiscreteValuationRing.not_a_field BaseInteger)]
  exact integer_ramificationIdx_eq_filtration_e K FF

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

/-- **Arbitrary-`K` fundamental identity.**  The field degree is the product of the filtration
ramification and residue degrees. -/
theorem field_finrank_eq_e_mul_f :
    Module.finrank ℚ_[2] K = FF.e * FF.f := by
  rw [← integer_finrank_eq_field_finrank K,
    integer_finrank_eq_ramification_mul_inertia (K := K),
    integer_ramificationIdx'_eq_filtration_e K FF,
    integer_inertiaDeg_eq_filtration_f K FF]

/-- The extension arithmetic feeds the existing arbitrary-field parameter constructor without any
additional degree or divisibility hypothesis. -/
def finiteDyadicParameters :
    GQ2.Dyadic.FiniteDyadicParameters K FF :=
  GQ2.Dyadic.FiniteDyadicParameters.ofFundamentalIdentity FF
    field_finrank_eq_e_mul_f

/-- Focused regression: the constructor obtained from the extension-level package has the field
degree, ramification index, residue degree, and residue cardinality expected by the corrected
selector. -/
theorem finiteDyadicParameters_regression
    (FF : GQ2.DyadicUnitFiltration K) :
    (finiteDyadicParameters (FF := FF)).params.n = Module.finrank ℚ_[2] K ∧
      (finiteDyadicParameters (FF := FF)).params.e = FF.e ∧
      (finiteDyadicParameters (FF := FF)).params.f = FF.f ∧
      (finiteDyadicParameters (FF := FF)).params.qK = GQ2.Dyadic.qOf K FF := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  exact (GQ2.Dyadic.FiniteDyadicParameters.params_e_eq_iff_fundamentalIdentity
    (finiteDyadicParameters (FF := FF))).2 field_finrank_eq_e_mul_f

end

end GQ2.Dyadic.SpectralLocalField
