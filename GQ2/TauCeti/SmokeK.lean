/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5.5
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.FiniteExtension
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Cyclotomic
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Unramified
public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
public import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic
public import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
public import TauCeti.NumberTheory.LocalField.NormalizedValuation
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.RootsOfUnity.Unramified
public import TauCeti.NumberTheory.LocalField.Tame.Geometric
public import TauCeti.NumberTheory.LocalField.Tame.Quotient
public import TauCeti.NumberTheory.LocalField.Unramified.Basic
public import TauCeti.NumberTheory.LocalField.Unramified.Coordinate
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Cyclotomic
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.SeparableClosure
public import TauCeti.NumberTheory.LocalField.WildInertia
public import TauCeti.NumberTheory.LocalField.WorkedExamples.CyclotomicEight.Basic
public import TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.NegOne.Ramification
public import TauCeti.RingTheory.Norm.Units
public import TauCeti.Topology.Algebra.Group.ClosedSubgroup
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Presentation.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Basic
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import GQ2.TauCeti.GaloisDict
public import GQ2.TauCeti.B5
public import GQ2.TauCeti.B10
public import GQ2.TauCeti.ProPDict
public import GQ2.Dyadic.MarkedRecipBundle
public import GQ2.Dyadic.OrientedTameBundle
public import GQ2.UnitFiltrationCounts
public import GQ2.TraceForm
public import GQ2.Foundations.TauCetiInstance

/-!
# Tau Ceti smoke import for the two `K`-level inputs (dyadic campaign, ticket T2)

Pins, at Tau Ceti `706344c35` / Mathlib `cfc55fc58`, every Tau Ceti declaration named in the
recon memo `docs/dyadic/tauceti-discharge-recon.md` for **B5-K** (`MarkedRecip`) and **B10-K**
(`OrientedTameQuotientK`), by `#check`ing it under its full name (section `Signatures`), and
instantiates each at a finite `↥K ⊆ ℚ̄₂` under A1's `letI` package (section `AtK`), with
`example`s recording which instances synthesize and which must be supplied (negative results
are pinned with `fail_if_success`).  Nothing here is imported by the library.  The complete
scratch terms for both inputs are in `docs/dyadic/tauceti-t2-evidence/` (`full/b5k_b10k.lean`).

Tau Ceti names are written fully qualified and `TauCeti` is never opened.
-/

noncomputable section

namespace GQ2.TauCetiBridge

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

open ValuativeRel

/-- A1's local-field package on `↥K`: `letI`/`haveI` of `valuativeRel`, `localTopology`,
`isNonarchimedeanLocalField` around a term. -/
local macro "pkgK " K:term:max t:term:max : term =>
  `(letI := valuativeRel $K; letI := localTopology $K; haveI := isNonarchimedeanLocalField $K; $t)

/-! ## Signatures (verbatim `#check` output is quoted in the memo) -/

section Signatures

/-! ### A1-K: local-field package, bridge, `G_K^{ab}` -/

#check @TauCeti.finiteIntermediateFieldValuativeRel
#check @TauCeti.finiteIntermediateFieldTopology
#check @TauCeti.finiteIntermediateField_valuativeExtension
#check @TauCeti.finiteIntermediateField_isValuativeTopology
#check @TauCeti.finiteIntermediateField_isNonarchimedeanLocalField
#check @TauCeti.vle_iff_algebraicExtensionNormedField_norm_le
#check @TauCeti.algebraicExtensionNormedField_norm_le_norm_iff
#check @TauCeti.algebraicExtensionValuativeRel_vle_iff
#check @Padic.normalizedAbsoluteValue_eq_nnnorm
#check @TauCeti.normalizedAbsoluteValue_le_normalizedAbsoluteValue_iff
#check @TauCeti.normalizedValuation
#check @TauCeti.normalizedValuation_eq_one_iff
#check @TauCeti.toAdd_normalizedValuation_le_iff_valuation_le
#check @TauCeti.normalizedValuation_surjective
#check @TauCeti.normalizedValuation_irreducible
#check @IsValuativeTopology.of_mem_nhds_zero_iff_vle
#check @IsValuativeTopology.mem_nhds_iff
#check @ContinuousMulEquiv.topologicalAbelianizationCongr
#check @ContinuousMulEquiv.topologicalAbelianizationCongr_mk
#check @Valuation.Integer.not_isUnit_iff_valuation_lt_one
#check @GQ2.UnitFiltrationCounts.residueField_card_eq_pow_f
#check @GQ2.UnitFiltrationCounts.card_gradeZero
#check @GQ2.TauCetiBridge.absGalEquivFixing
#check @GQ2.TauCetiBridge.coe_absGalEquivFixing_apply
#check @GQ2.TauCetiBridge.fixingEquivAbsGal_apply
#check @GQ2.TauCetiBridge.fixingEquivAbsGal_mem_galoisSubgroup_quadExt_iff
#check @GQ2.TauCetiBridge.sepClosureEquiv_algebraMap
#check @GQ2.TauCetiBridge.sepClosureEquiv_layerEmb
#check @GQ2.TauCetiBridge.compactSpace_fixingSubgroup

/-! ### B5-K: reciprocity map, norm functoriality, unramified coordinate -/

#check @TauCeti.ClassFieldTheory.artinMap
#check @TauCeti.ClassFieldTheory.continuous_artinMap
#check @TauCeti.ClassFieldTheory.denseRange_artinMap
#check @TauCeti.ClassFieldTheory.artinMap_norm
#check @TauCeti.Algebra.normUnits
#check @TauCeti.Algebra.coe_normUnits
#check @TauCeti.unramifiedCoordinate
#check @TauCeti.unramifiedCoordinate_mk
#check @TauCeti.unramifiedCoordinate_mk_eq_one_iff
#check @TauCeti.ker_unramifiedCoordinate
#check @TauCeti.unramifiedCoordinate_surjective
#check @TauCeti.ClassFieldTheory.unramifiedCoordinate_artinMap
#check @TauCeti.zHat.lift
#check @TauCeti.zHat.lift_ofInt
#check @TauCeti.zHat.lift_gen
#check @GQ2.TauCetiBridge.localReciprocity_tauceti_recip
#check @GQ2.TauCetiBridge.chiCycAb_artinMap_uniformizer

/-! ### B5-K, the level `r` (Q1) -/

#check @PadicInt.ideal_eq_span_pow_p
#check @PadicInt.denseRange_intCast
#check @TauCeti.abelianizedLocalCyclotomicCharacter
#check @TauCeti.abelianizedLocalCyclotomicCharacter_mk
#check @TauCeti.localCyclotomicCharacter_absoluteGaloisGroupExtend
#check @TauCeti.ClassFieldTheory.abelianizedLocalCyclotomicCharacter_artinMap
#check @TauCeti.ClassFieldTheory.abelianizedLocalCyclotomicCharacter_artinMap_norm
#check @TauCeti.localCyclotomicCharacter_eq_one_of_mem_inertiaSubgroup
#check @TauCeti.DyadicCyclotomicEight.isTotallyRamified
#check @TauCeti.DyadicCyclotomicEight.ramificationIndex_eq_four
#check @TauCeti.DyadicSqrtNegOne.ramificationIndex_eq_two
#check @TauCeti.localRootOfUnityOrder_two_of_isUnramified

/-! ### B5-K, `ki_unramified` (Q2) -/

#check @TauCeti.inertiaSubgroup
#check @TauCeti.mem_inertiaSubgroup_iff
#check @TauCeti.inertiaSubgroup_le_fixingSubgroup_iff
#check @TauCeti.map_inertiaSubgroup_absoluteGaloisGroupRestrictEquiv
#check @TauCeti.map_inertiaSubgroup_le_fixingSubgroup_iff
#check @TauCeti.IsUnramified
#check @TauCeti.isUnramified_iff_ramificationIndex_eq_one
#check @TauCeti.isUnramified_iff_normalizedValuation_comp_unitsMap_surjective
#check @TauCeti.isUnramified_iff_normalizedValuation_algebraMap
#check @TauCeti.galoisSubgroup_toSubgroup
#check @TauCeti.maximalUnramifiedExtension
#check @IntermediateField.le_maximalUnramifiedExtension_iff
#check @cyclotomicCharacter.spec

/-! ### B10-K: wild inertia, tame quotient, geometric Iwasawa presentation -/

#check @TauCeti.wildInertiaSubgroup
#check @TauCeti.isClosed_wildInertiaSubgroup
#check @TauCeti.wildInertiaSubgroup_normal
#check @TauCeti.isProP_wildInertiaSubgroup
#check @TauCeti.FinitePadicExtension
#check @TauCeti.FinitePadicExtension.ofInstances
#check @TauCeti.charP_residueField
#check @TauCeti.isProP_iff
#check @TauCeti.IsProP.of_surjective
#check @GQ2.TauCetiBridge.isProP_iff_tauCeti
#check @ContinuousMulEquiv.quotientCongr
#check @ContinuousMulEquiv.quotientCongr_symm_mk
#check @TauCeti.tameQuotient
#check @TauCeti.toTameQuotient_apply
#check @TauCeti.tameQuotientToZHat_toTameQuotient
#check @TauCeti.exists_isArithFrobeniusLift
#check @TauCeti.exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top
#check @TauCeti.IwasawaGroupGeometric
#check @TauCeti.iwasawaRelatorGeometric_def
#check @TauCeti.inv_iwasawaSigmaGeometric_mul_iwasawaTauGeometric_mul
#check @TauCeti.iwasawaCoordinateGeometric
#check @TauCeti.iwasawaCoordinateGeometric_iwasawaSigmaGeometric
#check @TauCeti.iwasawaCoordinateGeometric_iwasawaTauGeometric
#check @TauCeti.tameQuotientGeometricEquiv
#check @TauCeti.iwasawaCoordinateGeometric_tameQuotientGeometricEquiv
#check @TauCeti.presentedProfiniteGroup.lift
#check @TauCeti.presentedProfiniteGroup.lift_of
#check @TauCeti.presentedProfiniteGroup.hom_ext_of
#check @TauCeti.freeProfiniteGroup.lift
#check @TauCeti.freeProfiniteGroup.lift_of
#check @GQ2.TauCetiBridge.iwasawaGeometricEquivTtame
#check @GQ2.TauCetiBridge.nuT_iwasawaGeometricToTtame
#check @GQ2.Dyadic.Tq
#check @GQ2.Dyadic.nuTq
#check @GQ2.Dyadic.tame_relation_q
#check @GQ2.Dyadic.qOf
#check @GQ2.Dyadic.uniformizerK_max

end Signatures

/-! ## Instantiation at a finite `↥K` under A1's package -/

section AtK

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]

/-! ### The package itself -/

/-- `IsNonarchimedeanLocalField ↥K` after the two `letI`s (A1). -/
example : @IsNonarchimedeanLocalField K _ (valuativeRel K) (localTopology K) :=
  isNonarchimedeanLocalField K

/-- Under the package, the local topology wins over the global subspace topology. -/
example : pkgK K ((inferInstance : TopologicalSpace K) = localTopology K) := pkgK K rfl

/-- `Algebra.IsAlgebraic ℚ₂ ↥K` synthesizes (needed by the bridge). -/
example : pkgK K (Algebra.IsAlgebraic ℚ_[2] K) := pkgK K inferInstance

/-- `ValuativeExtension ℚ₂ ↥K` does **not** synthesize from the package: supply A1's
`valuativeExtension K`. -/
example : pkgK K (ValuativeExtension ℚ_[2] K) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  fail_if_success exact inferInstance
  exact valuativeExtension K

/-- With `valuativeExtension K` in context, `FinitePadicExtension ↥K 2` synthesizes
(`ofInstances`). -/
example : pkgK K (haveI := valuativeExtension K; TauCeti.FinitePadicExtension K 2) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  haveI := valuativeExtension K
  exact inferInstance

/-- `CharP 𝓀[↥K] 2` does **not** synthesize: supply `TauCeti.charP_residueField K 2`. -/
example : pkgK K (CharP 𝓀[K] 2) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  haveI := valuativeExtension K
  fail_if_success exact inferInstance
  exact TauCeti.charP_residueField K 2

/-- The two topologies on `↥K` are not definitionally equal (`rfl` fails); the A1-K lemma
`localTopology_eq` (prototype `bridge/bridge.lean`) proves them equal. -/
example : True := by
  fail_if_success (have : localTopology K = (inferInstance : TopologicalSpace K) := rfl)
  trivial

/-- `CompactSpace (GalK K)` is not found (A1's instance is on the `Kummer.GaloisGroup` path);
supply `compactSpace_fixingSubgroup K` (the same term, by defeq). -/
example : CompactSpace (Dyadic.GalK K) := by
  fail_if_success exact inferInstance
  exact compactSpace_fixingSubgroup K

/-- ... and then `CompactSpace (GalKab K)` is `Quotient.compactSpace`. -/
example : CompactSpace (Dyadic.GalKab K) :=
  haveI : CompactSpace (Dyadic.GalK K) := compactSpace_fixingSubgroup K
  Quotient.compactSpace

/-- gq2's `GalK K` and A1's `↥K.fixingSubgroup` are the same type (two instance paths): the
identity is a `ContinuousMulEquiv`. -/
example : Dyadic.GalK K ≃ₜ* ↥(K.fixingSubgroup : Subgroup (GQ2.Kummer.GaloisGroup ℚ_[2])) :=
  ContinuousMulEquiv.refl _

/-- `GQ2.localReciprocity` is not exposed outside `GQ2/Foundations/TauCetiInstance.lean`: its
identification with `localReciprocity_tauceti` is not `rfl` here (C1' must place the K-level
same-name `def`s in that file). -/
example : True := by
  fail_if_success (have : GQ2.localReciprocity = localReciprocity_tauceti := rfl)
  trivial

/-! ### B5-K -/

example : pkgK K (Kˣ →* Field.absoluteGaloisGroupAbelianization K) :=
  pkgK K (TauCeti.ClassFieldTheory.artinMap K)

example : pkgK K (Continuous (TauCeti.ClassFieldTheory.artinMap K)) :=
  pkgK K (TauCeti.ClassFieldTheory.continuous_artinMap K)

example : pkgK K (DenseRange (TauCeti.ClassFieldTheory.artinMap K)) :=
  pkgK K (TauCeti.ClassFieldTheory.denseRange_artinMap K)

/-- `abEquivK`: `G_K^{ab}` (gq2) `≃ₜ* G_{↥K}^{ab}` (Tau Ceti). -/
example : Dyadic.GalKab K ≃ₜ* Field.absoluteGaloisGroupAbelianization K :=
  (((ContinuousMulEquiv.refl _ : Dyadic.GalK K ≃ₜ*
      ↥(K.fixingSubgroup : Subgroup (GQ2.Kummer.GaloisGroup ℚ_[2])))).trans
    (absGalEquivFixing K).symm).topologicalAbelianizationCongr

/-- Norm functoriality at `(ℚ₂, ↥K)`, with `ValuativeExtension ℚ₂ ↥K` supplied. -/
example (x : Kˣ) (τ : Field.absoluteGaloisGroup K)
    (hτ : pkgK K ((τ : Field.absoluteGaloisGroupAbelianization K) =
      TauCeti.ClassFieldTheory.artinMap K x)) :
    (TauCeti.absoluteGaloisGroupExtend ℚ_[2] K (sepEmb K) τ :
        Field.absoluteGaloisGroupAbelianization ℚ_[2]) =
      TauCeti.ClassFieldTheory.artinMap ℚ_[2] (TauCeti.Algebra.normUnits ℚ_[2] x) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  haveI := valuativeExtension K
  exact TauCeti.ClassFieldTheory.artinMap_norm (K := ℚ_[2]) K (sepEmb K) x τ hτ

/-- gq2's `normUnitsK` is Tau Ceti's `Algebra.normUnits` (not `rfl`: not exposed). -/
example (x : Kˣ) : Dyadic.normUnitsK K x = TauCeti.Algebra.normUnits ℚ_[2] x :=
  Units.ext (by rw [Dyadic.normUnitsK_val, TauCeti.Algebra.coe_normUnits])

example (x : Kˣ) : pkgK K (TauCeti.unramifiedCoordinate K (TauCeti.ClassFieldTheory.artinMap K x) =
    TauCeti.zHat.ofInt (TauCeti.normalizedValuation K x)) :=
  pkgK K (TauCeti.ClassFieldTheory.unramifiedCoordinate_artinMap K x)

example : pkgK K (Function.Surjective (TauCeti.normalizedValuation K)) :=
  pkgK K TauCeti.normalizedValuation_surjective

/-! ### Q2 at `↥K`: inertia, its fixed fields, `IsUnramified` -/

example (σ : Field.absoluteGaloisGroup K) : pkgK K
    (TauCeti.unramifiedCoordinate K (σ : Field.absoluteGaloisGroupAbelianization K) = 1 ↔
      σ ∈ TauCeti.inertiaSubgroup K) :=
  pkgK K (TauCeti.unramifiedCoordinate_mk_eq_one_iff σ)

/-- The inertia criterion at a finite subextension `E` of `↥K`'s separable closure, with Tau
Ceti's package on `↥E` supplied from the package on `↥K`. -/
example (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] : pkgK K
    (letI := TauCeti.finiteIntermediateFieldValuativeRel K (SeparableClosure K) E
     letI := TauCeti.finiteIntermediateFieldTopology K (SeparableClosure K) E
     haveI := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) E
     haveI := TauCeti.finiteIntermediateField_valuativeExtension K (SeparableClosure K) E
     ((TauCeti.inertiaSubgroup K).map (TauCeti.absoluteGaloisGroupRestrictEquiv K).toMonoidHom ≤
        E.fixingSubgroup ↔ TauCeti.IsUnramified K E)) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  letI := TauCeti.finiteIntermediateFieldValuativeRel K (SeparableClosure K) E
  letI := TauCeti.finiteIntermediateFieldTopology K (SeparableClosure K) E
  haveI := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) E
  haveI := TauCeti.finiteIntermediateField_valuativeExtension K (SeparableClosure K) E
  exact TauCeti.map_inertiaSubgroup_le_fixingSubgroup_iff E

/-- `FiniteDimensional ↥K (quadExt K δi)` is not found by instance search; it is B9's
`finiteDimensional_quadExt` at `d = -1`. -/
example (δi : ℚ̄₂) (hδi : δi ^ 2 = -1) : FiniteDimensional K (quadExt K δi) := by
  fail_if_success exact inferInstance
  exact finiteDimensional_quadExt K (-1) (by rw [hδi]; simp)

/-- B9's layer embedding gives the `K(δi)` layer as a subextension of `↥K`'s separable closure,
and A1's stabilizer criterion applies at `δ = δi`. -/
example (δi : ℚ̄₂) [FiniteDimensional K (quadExt K δi)] (g : K.fixingSubgroup) :
    fixingEquivAbsGal K g ∈
        TauCeti.galoisSubgroup K (quadExt K δi) (layerEmb K (quadExt K δi)) ↔
      (g : GQ2.Kummer.GaloisGroup ℚ_[2]) • δi = δi :=
  fixingEquivAbsGal_mem_galoisSubgroup_quadExt_iff K δi g

/-! ### B10-K -/

example : pkgK K (Subgroup (Field.absoluteGaloisGroup K)) := pkgK K (TauCeti.wildInertiaSubgroup K)

/-- `(wildInertiaSubgroup ↥K).Normal` synthesizes under the package. -/
example : pkgK K ((TauCeti.wildInertiaSubgroup K).Normal) := pkgK K inferInstance

example : pkgK K (IsClosed (TauCeti.wildInertiaSubgroup K : Set (Field.absoluteGaloisGroup K))) :=
  pkgK K (TauCeti.isClosed_wildInertiaSubgroup K)

/-- Pro-2 wild inertia at `↥K`, with `ValuativeExtension` and `CharP 𝓀[↥K] 2` supplied. -/
example : pkgK K (TauCeti.IsProP 2 (TauCeti.wildInertiaSubgroup K)) := by
  letI := valuativeRel K
  letI := localTopology K
  haveI := isNonarchimedeanLocalField K
  haveI := valuativeExtension K
  haveI := TauCeti.charP_residueField K 2
  exact TauCeti.isProP_wildInertiaSubgroup K 2

example : pkgK K (∃ σ : Field.absoluteGaloisGroup K, TauCeti.IsArithFrobeniusLift K σ) :=
  pkgK K (TauCeti.exists_isArithFrobeniusLift K)

example : pkgK K (∃ τ : TauCeti.inertiaSubgroup K,
    (Subgroup.zpowers (TauCeti.inertiaTameCharacter K τ)).topologicalClosure = ⊤) :=
  pkgK K (TauCeti.exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top K)

example : pkgK K (TauCeti.tameQuotient K ≃ₜ* TauCeti.IwasawaGroupGeometric K) :=
  pkgK K (TauCeti.tameQuotientGeometricEquiv
    (Classical.choose_spec (TauCeti.exists_isArithFrobeniusLift K))
    (Classical.choose (TauCeti.exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top K))
    (Classical.choose_spec
      (TauCeti.exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top K)))

/-- The relator of `IwasawaGroupGeometric ↥K` is at `q = #𝓀[↥K]`. -/
example : pkgK K (TauCeti.iwasawaRelatorGeometric K =
    (TauCeti.freeProfiniteGroup.of (ULift.up 0))⁻¹ * TauCeti.freeProfiniteGroup.of (ULift.up 1) *
      TauCeti.freeProfiniteGroup.of (ULift.up 0) *
        (TauCeti.freeProfiniteGroup.of (ULift.up 1) ^ Nat.card 𝓀[K])⁻¹) :=
  pkgK K (TauCeti.iwasawaRelatorGeometric_def K)

/-- gq2's intrinsic residue field of `↥K` has `2 ^ FF.f` elements (public; Q3). -/
example (FF : DyadicUnitFiltration K) :
    Nat.card (UnitFiltrationCounts.ResidueField K) = 2 ^ FF.f :=
  UnitFiltrationCounts.residueField_card_eq_pow_f K FF

end AtK

end GQ2.TauCetiBridge

end
