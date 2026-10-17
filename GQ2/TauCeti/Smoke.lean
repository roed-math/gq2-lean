/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5.5
-/
module

public import TauCeti.Algebra.Module.ZMod.Dual
public import TauCeti.Algebra.Module.ZMod.SMulCommClass
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Orientation
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Extension
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.ProP
public import TauCeti.FieldTheory.GaloisCohomology.Corestriction.Basic
public import TauCeti.FieldTheory.GaloisCohomology.EvensNorm
public import TauCeti.FieldTheory.GaloisCohomology.Kummer
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Basic
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.CupNorm
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.KummerCharacter
public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Transfer
public import TauCeti.FieldTheory.GaloisCohomology.Restriction
public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Basic
public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Class
public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.QuadraticExtension
public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Transfer
public import TauCeti.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Descent
public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.RootsOfUnity
public import TauCeti.NumberTheory.ClassFieldTheory.FiniteCohomology.DegreeTwo
public import TauCeti.NumberTheory.ClassFieldTheory.Formation.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Cyclotomic
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Explicit
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.Perfect
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Duality.RootsOfUnity
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Shapiro
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Theorem
public import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Reciprocity
public import TauCeti.NumberTheory.ClassFieldTheory.Local.Unramified
public import TauCeti.NumberTheory.ClassFieldTheory.LocalExistence.ArtinMap
public import TauCeti.NumberTheory.ClassFieldTheory.MuNRep
public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
public import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
public import TauCeti.NumberTheory.LocalField.Generation.AbsoluteGaloisGroup
public import TauCeti.NumberTheory.LocalField.NormalizedValuation
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.ProP.RatPadic
public import TauCeti.NumberTheory.LocalField.Tame.Geometric
public import TauCeti.NumberTheory.LocalField.Tame.Quotient
public import TauCeti.NumberTheory.LocalField.Unramified.Coordinate
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic
public import TauCeti.NumberTheory.LocalField.WildInertia
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ContinuousCohomologyIso
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.TrivialF2
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Cohomology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Comparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.RestrictScalars
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2.Inhomogeneous
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Class
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Cochain
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Corestriction
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Identities
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.IndexTwoNorm
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Naturality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
public import TauCeti.RepresentationTheory.Homological.ContCohomology.RestrictScalars
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialF2.Character
public import TauCeti.RingTheory.Henselian.Basic
public import TauCeti.RingTheory.Norm.Units
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
public import TauCeti.Topology.Algebra.Group.ClosedSubgroup
public import TauCeti.Topology.Algebra.Group.ContinuousAut.Basic
public import TauCeti.Topology.Algebra.Group.Generation
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.D0.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.D0.Invariants
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Orientation
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Dyadic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
public import TauCeti.Topology.Algebra.Group.Profinite.MaximalProP
public import TauCeti.Topology.Algebra.Group.Profinite.Presentation.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicPow
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicUnits
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Component
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Decomposition
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.PadicInt
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Pow
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Ring
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.ZMod
public import TauCeti.Topology.Instances.ZMod
public import GQ2.Cohomology
public import GQ2.CupProduct
public import GQ2.Demushkin
public import GQ2.EvensKahn
public import GQ2.Foundations.LiteratureInputs
public import GQ2.Orientation
public import GQ2.PeripheralAction
public import GQ2.ProfinitePresentation
public import GQ2.Reciprocity
public import GQ2.Statement
public import GQ2.TameQuotient
public import GQ2.TateDuality
public import GQ2.TraceForm

/-!
# Tau Ceti smoke import (ticket T2)

Pins, at Tau Ceti `706344c35` / Mathlib `cfc55fc58`, every Tau Ceti declaration named in
`docs/orchestration/tauceti-proof-plan.md` §3 (plus the better routes found by the T2 recon), by
`#check`ing each under its full name, and records the definitional-equality facts the adapter
tickets rely on as `example`s. The recon memo `docs/orchestration/tauceti-t2-recon.md` explains
every entry. Nothing here is imported by the library; build it with `lake build GQ2.TauCeti.Smoke`
(with the Tau Ceti cache variables set, see the memo).

Both libraries define `IsProP`, `D0`/`d0A`/…, `kummerClass`, `H0`/`H1`/`H2`, `Zhat`/`zHat`, so
Tau Ceti names are written fully qualified and `TauCeti` is never opened. Each lane is a
`section`, so its local instances, notations and options stay local to it.
-/

section Lane_galois

/-! # T2 smoke fragment: lanes A1, B1, B11a (lane id `galois`) -/

/-! ## A1 -/

#check @TauCeti.AbsoluteGaloisGroup
#check @TauCeti.absoluteGaloisGroupRestrictEquiv
#check @TauCeti.absoluteGaloisGroupRestrictEquiv_apply
#check @TauCeti.coe_absoluteGaloisGroupRestrictEquiv_apply
#check @TauCeti.absoluteGaloisGroupRestrictEquiv_symm_apply_coe
#check @TauCeti.separableClosureRingEquiv
#check @TauCeti.separableClosureRingEquiv_algebraMap
#check @TauCeti.galoisSubgroup
#check @TauCeti.galoisSubgroup_toSubgroup
#check @TauCeti.mem_galoisSubgroup_iff
#check @TauCeti.galoisSubgroup_index
#check @TauCeti.galoisSubgroupEquiv
#check @TauCeti.absoluteGaloisGroupExtend
#check @TauCeti.absoluteGaloisGroupRestrictEquiv_absoluteGaloisGroupExtend
#check @TauCeti.absoluteGaloisGroupExtend_apply_separableClosureRingEquiv
#check @TauCeti.mem_range_absoluteGaloisGroupExtend_iff
#check @TauCeti.absoluteGaloisGroupExtendEquiv
#check @TauCeti.coe_absoluteGaloisGroupExtendEquiv_apply
#check @TauCeti.absoluteGaloisGroupRestrictSubgroupEquiv
#check @TauCeti.coe_absoluteGaloisGroupRestrictSubgroupEquiv_apply
#check @TauCeti.ClassFieldTheory.shapiroFieldEmbedding
#check @TauCeti.ClassFieldTheory.range_absoluteGaloisGroupExtend_shapiroFieldEmbedding
#check @TauCeti.finiteIntermediateFieldValuativeRel
#check @TauCeti.finiteIntermediateFieldTopology
#check @TauCeti.finiteIntermediateField_isNonarchimedeanLocalField
#check @TauCeti.finiteIntermediateField_valuativeExtension
#check @TauCeti.FinitePadicExtension
#check @TauCeti.FinitePadicExtension.ofInstances
#check @TauCeti.valuativeExtension_self
#check @TauCeti.localCyclotomicCharacter
#check @TauCeti.localCyclotomicCharacter_apply
#check @TauCeti.continuousLocalCyclotomicCharacter
#check @TauCeti.abelianizedLocalCyclotomicCharacter
#check @TauCeti.abelianizedLocalCyclotomicCharacter_mk

/-- `GQ2.Kummer.GaloisGroup ℚ_[2]` (an abbrev for `ℚ̄₂ ≃ₐ[ℚ₂] ℚ̄₂`) is `AbsGalQ2` by `rfl`
(Mathlib's `Field.absoluteGaloisGroup` is an exposed, but not reducible, `def`). -/
example : GQ2.Kummer.GaloisGroup ℚ_[2] = GQ2.AbsGalQ2 := rfl
example : (inferInstance : TopologicalSpace (GQ2.Kummer.GaloisGroup ℚ_[2])) =
    (inferInstance : TopologicalSpace GQ2.AbsGalQ2) := rfl
example : (inferInstance : Group (GQ2.Kummer.GaloisGroup ℚ_[2])) =
    (inferInstance : Group GQ2.AbsGalQ2) := rfl

/-- `GQ2.chiCyc` is Tau Ceti's local cyclotomic character.  Not `rfl` in a `module` file
(`TauCeti.localCyclotomicCharacter` is not exposed); `rfl` does work from a plain-import file. -/
example : GQ2.chiCyc = TauCeti.localCyclotomicCharacter 2 ℚ_[2] :=
  MonoidHom.ext fun σ => (TauCeti.localCyclotomicCharacter_apply 2 ℚ_[2] σ).symm

/-- The same on the abelianization (`GQ2.AbsGalQ2ab` is Mathlib's, as is Tau Ceti's domain). -/
example (x : GQ2.AbsGalQ2ab) :
    GQ2.chiCycAb x = TauCeti.abelianizedLocalCyclotomicCharacter 2 ℚ_[2] x := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [TauCeti.abelianizedLocalCyclotomicCharacter_mk]
    exact (TauCeti.localCyclotomicCharacter_apply 2 ℚ_[2] g).symm

-- Not checked here: with this import set (it contains
-- `TauCeti.NumberTheory.LocalField.Generation.AbsoluteGaloisGroup`, whose closure includes
-- `TauCeti.NumberTheory.LocalField.ClassModule`), `Module.IsTorsionFree ℚ_[2] (AlgebraicClosure ℚ_[2])`,
-- hence `IsAlgClosure`/`Normal`/`IsGalois ℚ_[2] ℚ̄₂` and `CompactSpace Gal(ℚ̄₂/ℚ₂)`, time out in
-- instance search.  `CompactSpace ↥k.fixingSubgroup` is proved in `a1_b11a_prototype.lean`.

-- `LocallyCompactSpace (TauCeti.AbsoluteGaloisGroup ↥k)` exceeds the default
-- `synthInstance.maxHeartbeats` (times out at `R1Space`); it succeeds with a larger budget.
set_option synthInstance.maxHeartbeats 200000 in
example (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) :
    LocallyCompactSpace (TauCeti.AbsoluteGaloisGroup k) := inferInstance

/-- `FinitePadicExtension`'s bundled algebra is the existing one at `ℚ_[2]`. -/
example : (TauCeti.FinitePadicExtension.toAlgebra ℚ_[2] 2 : Algebra ℚ_[2] ℚ_[2]) =
    Algebra.id ℚ_[2] := rfl

/-- The instance package on a finite `k`, installed locally, reaches `FinitePadicExtension k 2`;
the bundled algebra is the intermediate-field algebra; the local topology wins over the global
subspace topology coming from `PadicAlgCl`. -/
example (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k] :
    TauCeti.IsTopologicallyFinitelyGenerated (Field.absoluteGaloisGroup k) := by
  let _ := TauCeti.finiteIntermediateFieldValuativeRel ℚ_[2] (AlgebraicClosure ℚ_[2]) k
  let _ := TauCeti.finiteIntermediateFieldTopology ℚ_[2] (AlgebraicClosure ℚ_[2]) k
  have := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField ℚ_[2]
    (AlgebraicClosure ℚ_[2]) k
  have := TauCeti.finiteIntermediateField_valuativeExtension ℚ_[2] (AlgebraicClosure ℚ_[2]) k
  have _hF : TauCeti.FinitePadicExtension k 2 := inferInstance
  have _hA : (TauCeti.FinitePadicExtension.toAlgebra k 2 : Algebra ℚ_[2] k) =
      (inferInstance : Algebra ℚ_[2] k) := rfl
  have _hT : (inferInstance : TopologicalSpace k) =
      TauCeti.finiteIntermediateFieldTopology ℚ_[2] (AlgebraicClosure ℚ_[2]) k := rfl
  exact TauCeti.isTopologicallyFinitelyGenerated_absoluteGaloisGroup 2 k

/-! ## B1 -/

#check @TauCeti.isTopologicallyFinitelyGenerated_absoluteGaloisGroup
#check @TauCeti.IsTopologicallyFinitelyGenerated
#check @TauCeti.isTopologicallyFinitelyGenerated_iff

/-- B1 at `K = ℚ_[2]`: every instance argument is found automatically. -/
example : ∃ s : Finset GQ2.AbsGalQ2,
    (Subgroup.closure (s : Set GQ2.AbsGalQ2)).topologicalClosure = ⊤ :=
  TauCeti.isTopologicallyFinitelyGenerated_iff.mp
    (TauCeti.isTopologicallyFinitelyGenerated_absoluteGaloisGroup 2 ℚ_[2])

/-! ## B11a -/

#check @TauCeti.cup_kummerClass_eq_zero_iff
#check @TauCeti.kummerClass
#check @TauCeti.kummerClass_eq_homClass
#check @TauCeti.kummerClass_eq_kummerCocycleModTwoClass_of_sq_eq
#check @TauCeti.trivialF2
#check @TauCeti.trivialF2Equiv
#check @TauCeti.trivialF2TopPairing
#check @TauCeti.trivialF2TopPairing_cup_one_one_explicitH1
#check @TauCeti.trivialF2Map
#check @TauCeti.trivialF2Map_cup
#check @TauCeti.trivialF2Iso
#check @TauCeti.trivialF2Iso_hom
#check @TauCeti.galoisF2Iso
#check @TauCeti.galoisF2Iso_inv
#check @TauCeti.galoisF2Iso_inv_cup
#check @TauCeti.galoisF2Iso_inv_kummerClass
#check @TauCeti.galoisKummerCharacter
#check @TauCeti.toAdd_galoisKummerCharacter
#check @TauCeti.rootSign_of_apply_eq
#check @TauCeti.rootSign_of_apply_ne
#check @TauCeti.ContCohomology.homClass
#check @TauCeti.ContCohomology.homClass_def
#check @TauCeti.ContCohomology.homClass_inj
#check @TauCeti.ContCohomology.trivialF2Map_homClass
#check @TauCeti.ContCohomology.evensHomCocycle
#check @TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology
#check @TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology

/-- `(2 : ↥k)` is not invertible by instance search; supply it. -/
noncomputable example (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) :
    Invertible (2 : k) :=
  invertibleOfNonzero two_ne_zero

/-- The right-hand sides of Tau Ceti's cup-norm theorem and of the gq2 B11a field agree
on the nose at `K = ↥k`. -/
example (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) (a b : (↥k)ˣ) :
    letI : Invertible (2 : k) := invertibleOfNonzero two_ne_zero
    ((TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup k)).cup 1 1
        (TauCeti.kummerClass a) (TauCeti.kummerClass b) = 0 ↔
      ∃ x y : ↥k, (b : ↥k) = x ^ 2 - (a : ↥k) * y ^ 2) :=
  TauCeti.cup_kummerClass_eq_zero_iff a b

end Lane_galois


section Lane_cohom

/-! ## A2 -/
#check @TauCeti.ContCohomology.C1
#check @TauCeti.ContCohomology.C2
#check @TauCeti.ContCohomology.d0
#check @TauCeti.ContCohomology.d1
#check @TauCeti.ContCohomology.d2
#check @TauCeti.ContCohomology.Z1
#check @TauCeti.ContCohomology.Z2
#check @TauCeti.ContCohomology.B1
#check @TauCeti.ContCohomology.B2
#check @TauCeti.ContCohomology.H0
#check @TauCeti.ContCohomology.H1
#check @TauCeti.ContCohomology.H2
#check @TauCeti.ContCohomology.H1pi
#check @TauCeti.ContCohomology.H2pi
#check @TauCeti.ContCohomology.mem_C1_iff
#check @TauCeti.ContCohomology.mem_Z1_iff
#check @TauCeti.ContCohomology.mem_Z2_iff
#check @TauCeti.ContCohomology.mem_B1_iff
#check @TauCeti.ContCohomology.mem_B2_iff
#check @TauCeti.ContCohomology.d1_apply
#check @TauCeti.ContCohomology.H1pi_eq_iff
#check @continuousCohomology
#check @TauCeti.ofDiscreteModule
#check @TauCeti.ofDiscreteModule_V
#check @TauCeti.ofDiscreteModule_ρ_apply_apply
#check @TopRep.distribMulAction
#check @TauCeti.ContCohomology.explicitH0IsoContinuousCohomology
#check @TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology
#check @TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology_apply
#check @TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology_map
#check @TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology
#check @TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology_apply
#check @TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology_map
#check @TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv
#check @TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete
#check @TopRep.explicitH2AddEquivContinuousCohomologyOfDiscrete
#check @TauCeti.ContCohomology.explicitMap1
#check @TauCeti.ContCohomology.explicitMap2
#check @TauCeti.ContCohomology.explicitMap1Equiv
#check @TauCeti.ContCohomology.explicitMap2Equiv
#check @TauCeti.ContCohomology.explicitRes1
#check @TauCeti.ContCohomology.explicitRes2
#check @TauCeti.ContCohomology.explicitCoeff1
#check @TauCeti.ContCohomology.explicitCoeff2
#check @TauCeti.ContCohomology.explicitCup11
#check @TauCeti.ContCohomology.explicitCup02
#check @TauCeti.ContCohomology.explicitCup20
#check @TauCeti.ContCohomology.explicitCup11_mk
#check @TauCeti.ContCohomology.explicitAddEquiv_cup11
#check @TauCeti.ContCohomology.explicitAddEquiv_cup02
#check @TauCeti.ContCohomology.explicitAddEquiv_cup20
#check @TauCeti.ContCohomology.explicitMap2_explicitCup11
#check @TauCeti.trivialF2
#check @TauCeti.trivialF2_V
#check @TauCeti.trivialF2Equiv
#check @TauCeti.trivialF2_ρ_apply_apply
#check @TauCeti.trivialF2Pairing
#check @TauCeti.ofDiscreteModule_trivialF2
#check @TauCeti.isSmoothDiscrete_trivialF2
#check @TauCeti.TopPairing.cup
#check @TauCeti.trivialF2TopPairing
#check @TauCeti.trivialF2TopPairing_cup_one_one_explicitH1
#check @TauCeti.trivialF2TopPairing_cup_one_one_explicitH1_subgroup
#check @TauCeti.trivialF2TopPairing_cup_comm
#check @TauCeti.cohomF2
#check @TauCeti.trivialF2ResMap
#check @TauCeti.trivialF2ResMap_explicitH1AddEquivContinuousCohomology
#check @TauCeti.absoluteGaloisGroupRestrictEquiv
#check @TauCeti.kummerClass
#check @TauCeti.kummerCocycleModTwo
#check @TauCeti.kummerCocycleModTwo_apply
#check @TauCeti.kummerCocycleModTwoClass
#check @TauCeti.kummerClass_eq_kummerCocycleModTwoClass_of_sq_eq

/-! ## B7 -/
#check @TauCeti.ClassFieldTheory.GalRep
#check @TauCeti.IsSmoothDiscrete
#check @TauCeti.ofDiscreteModule_isSmoothDiscrete
#check @TauCeti.isSmoothDiscrete_iff_continuousSMul
#check @TauCeti.IsSmoothDiscrete.continuousSMul
#check @TauCeti.ClassFieldTheory.eulerCharacteristic_mixed
#check @TauCeti.ClassFieldTheory.finite_H
#check @TauCeti.FinitePadicExtension
#check @TauCeti.FinitePadicExtension.ofInstances
#check @TauCeti.ZMod.smulCommClass'
#check @TauCeti.ZMod.continuousSMul_of_discreteTopology
#check @AddCommGroup.zmodModule
#check @TauCeti.instCompactSpaceAbsoluteGaloisGroup_tauCeti
#check @TauCeti.IsAdicComplete.henselianLocalRing

/-! ## A2: definitional-equality pins

`GQ2.ContCoh.H0 = TauCeti.ContCohomology.H0` holds by `rfl` in a `module` file. The analogous
`rfl` for `C1`, `C2`, `d0`, `d1`, `d2`, `Z1`, `Z2`, `B1`, `B2` (hence `H1`, `H2`, `res1`/`explicitRes1`,
`cup11`/`explicitCup11`) fails here: those Tau Ceti bodies are not `@[expose]`d. They do hold by
`rfl` in a non-`module` file or after `import all TauCeti.…LowDegree` (see the recon memo). -/
section A2Pins
variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

example : GQ2.ContCoh.H0 G M = TauCeti.ContCohomology.H0 G M := rfl

example : GQ2.Kummer.GaloisGroup ℚ_[2] = GQ2.AbsGalQ2 := rfl
example : GQ2.AbsGalQ2 = Field.absoluteGaloisGroup ℚ_[2] := rfl
end A2Pins

/-! ## B7: packaging pins -/
section B7Pins
variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction GQ2.AbsGalQ2 M] [ContinuousSMul GQ2.AbsGalQ2 M] [Finite M]

/-- `M` as a `ZMod (Nat.card M)`-module (Lagrange). -/
@[instance_reducible] private noncomputable def smokeZModModule : Module (ZMod (Nat.card M)) M :=
  haveI : NeZero (Nat.card M) := ⟨Nat.card_pos.ne'⟩
  AddCommGroup.zmodModule fun _ => card_nsmul_eq_zero'

attribute [local instance] smokeZModModule

/-- The coefficient object of B7. -/
private noncomputable def smokeGalRep : TauCeti.ClassFieldTheory.GalRep (Nat.card M) ℚ_[2] :=
  TauCeti.ofDiscreteModule (ZMod (Nat.card M)) (Field.absoluteGaloisGroup ℚ_[2]) M

example : (smokeGalRep M).V = M := rfl

example : (TopRep.distribMulAction (smokeGalRep M) : DistribMulAction GQ2.AbsGalQ2 M) =
    (inferInstance : DistribMulAction GQ2.AbsGalQ2 M) := rfl

example : TauCeti.IsSmoothDiscrete (ZMod (Nat.card M)) (smokeGalRep M) :=
  TauCeti.ofDiscreteModule_isSmoothDiscrete _ _ M

example : TauCeti.FinitePadicExtension.toAlgebra ℚ_[2] 2 = Algebra.id ℚ_[2] := rfl

attribute [-instance] TauCeti.IsAdicComplete.henselianLocalRing in
example : @Module.finrank ℚ_[2] ℚ_[2] _ _
    (@Algebra.toModule _ _ _ _ (TauCeti.FinitePadicExtension.toAlgebra ℚ_[2] 2)) = 1 :=
  Module.finrank_self ℚ_[2]
end B7Pins

end Lane_cohom


section Lane_prop

/-! ## P1 -/

universe u

-- (1) the free profinite groups are the same object (Tau Ceti's is an exposed `abbrev`,
-- gq2's an `@[expose]` def), hence also the same carrier.  `TauCeti.freeProfiniteGroup.of` is
-- not exposed, so `GQ2.FreeProfiniteGroup.of x = TauCeti.freeProfiniteGroup.of x` is *not* `rfl`
-- in a `module` file (use `fromFreeGroup_of` + `coe_fromFreeGroup`, then `rfl`).
example (X : Type u) : GQ2.FreeProfiniteGroup X = TauCeti.freeProfiniteGroup X := rfl
example (X : Type u) :
    (GQ2.FreeProfiniteGroup X : Type u) = (TauCeti.freeProfiniteGroup X : Type u) := rfl
example {X : Type u} (x : X) :
    GQ2.FreeProfiniteGroup.of x = TauCeti.freeProfiniteGroup.of x := by
  rw [← TauCeti.freeProfiniteGroup.fromFreeGroup_of, TauCeti.freeProfiniteGroup.coe_fromFreeGroup]
  rfl
-- the free pro-p group on gq2's free profinite group, and gq2's presentation carrier
example : TauCeti.maximalProPQuotient 2 (GQ2.FreeProfiniteGroup (Fin 2)) =
    TauCeti.freeProP 2 (Fin 2) := rfl
example {X : Type u} (rels : Set (GQ2.FreeProfiniteGroup X)) :
    (GQ2.profinitePresentation rels : Type u) = TauCeti.presentedProfiniteGroup X rels := rfl
-- (2) `TauCeti.IsProP` and `TauCeti.proPKernel` are not exposed: `Iff.rfl`/`rfl` fail here;
-- the propositional bridges below are the adapter's route.
example (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] :
    GQ2.IsProP p G ↔ TauCeti.IsProP p G := TauCeti.isProP_iff.symm
example (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] :
    GQ2.proPKernel p G = TauCeti.proPKernel p G := by
  ext x
  rw [TauCeti.mem_proPKernel_iff, GQ2.proPKernel, Subgroup.mem_iInf]
  exact ⟨fun h U hU => h ⟨U, hU⟩, fun h U => h U.1 U.2⟩

-- pro-p predicate
#check @TauCeti.IsProP
#check @TauCeti.isProP_iff
-- pro-p kernel and maximal pro-p quotient
#check @TauCeti.proPKernel
#check @TauCeti.mem_proPKernel_iff
#check @TauCeti.proPKernel_le
#check @TauCeti.isClosed_proPKernel
#check @TauCeti.maximalProPQuotient
#check @TauCeti.maximalProPQuotient.mk
#check @TauCeti.maximalProPQuotient.mk_apply
#check @TauCeti.maximalProPQuotient.mk_surjective
#check @TauCeti.maximalProPQuotient.continuous_mk
#check @TauCeti.maximalProPQuotient.lift
#check @TauCeti.maximalProPQuotient.lift_mk
#check @TauCeti.maximalProPQuotient.continuous_lift
#check @TauCeti.maximalProPQuotient.congr
#check @TauCeti.isProP_maximalProPQuotient
#check @TauCeti.existsUnique_continuousMonoidHom_maximalProPQuotient
#check @ContinuousMulEquiv.quotientCongr
#check @ContinuousMulEquiv.quotientCongr_mk
#check @TauCeti.absoluteGaloisGroupProP
-- free profinite group
#check @TauCeti.freeProfiniteGroup
#check @TauCeti.freeProfiniteGroup.fromFreeGroup
#check @TauCeti.freeProfiniteGroup.of
#check @TauCeti.freeProfiniteGroup.fromFreeGroup_of
#check @TauCeti.freeProfiniteGroup.coe_fromFreeGroup
#check @TauCeti.freeProfiniteGroup.lift
#check @TauCeti.freeProfiniteGroup.lift_of
#check @TauCeti.freeProfiniteGroup.hom_ext
#check @TauCeti.freeProfiniteGroup.existsUnique_continuousMulEquiv
-- free pro-p group
#check @TauCeti.freeProP
#check @TauCeti.freeProP.fromFreeProfiniteGroup
#check @TauCeti.freeProP.fromFreeProfiniteGroup_apply
#check @TauCeti.freeProP.of
#check @TauCeti.freeProP.fromFreeProfiniteGroup_of
#check @TauCeti.freeProP.fromFreeProfiniteGroup_surjective
#check @TauCeti.isProP_freeProP
-- presentations
#check @TauCeti.presentedProfiniteGroup
#check @TauCeti.presentedProfiniteGroup.mk
#check @TauCeti.presentedProfiniteGroup.mk_apply
#check @TauCeti.presentedProfiniteGroup.mk_surjective
#check @TauCeti.presentedProfiniteGroup.mk_relator
#check @TauCeti.presentedProfiniteGroup.of
#check @TauCeti.presentedProfiniteGroup.lift
#check @TauCeti.presentedProfiniteGroup.congr
#check @TauCeti.presentedProfiniteGroup.toPresentedProP
#check @TauCeti.presentedProfiniteGroup.toPresentedProP_mk
#check @TauCeti.presentedProfiniteGroup.toPresentedProP_surjective
#check @TauCeti.presentedProP
#check @TauCeti.presentedProP.mk
#check @TauCeti.presentedProP.mk_apply
#check @TauCeti.presentedProP.mk_surjective
#check @TauCeti.presentedProP.of
#check @TauCeti.presentedProP.isProP
#check @TauCeti.presentedProP.lift
#check @TauCeti.presentedProP.lift_mk
#check @TauCeti.presentedProP.congr
#check @TauCeti.presentedProP.congrOfClosureEq
#check @TauCeti.d0Relator
#check @TauCeti.d0Relator_def
#check @TauCeti.demushkinD0
-- ℤ̂
#check @TauCeti.zHat
#check @TauCeti.zHat.ofInt
#check @TauCeti.zHat.coe_ofInt
#check @TauCeti.zHat.gen
#check @TauCeti.zHat.ofInt_ofAdd
#check @TauCeti.zHat.lift
#check @TauCeti.zHat.lift_ofInt
#check @TauCeti.zHat.lift_gen
#check @TauCeti.zHat.hom_ext
#check @TauCeti.zHat.map_lift
#check @TauCeti.zHat.toZMod
#check @TauCeti.zHat.lift_ofAdd_one_apply
#check @TauCeti.zHat.ext_of_toZMod
#check @TauCeti.zHat.instCommRing
#check @TauCeti.zHat.ofMul_ofInt
-- ℤ₂-component and the decomposition
#check @TauCeti.zHat.maximalProPQuotientEquivPadicInt
#check @TauCeti.zHat.maximalProPQuotientEquivPadicInt_mk
#check @TauCeti.zHat.component
#check @TauCeti.zHat.toZModPow_component
#check @TauCeti.zHat.component_apply
#check @TauCeti.zHat.lift_ofAdd_one_padicInt_apply
#check @TauCeti.zHat.continuous_component
#check @TauCeti.zHat.component_surjective
#check @TauCeti.zHat.maximalProPQuotientEquivPadicInt_mk_eq_component
#check @TauCeti.zHat.ringEquivPiPadicInt
#check @TauCeti.zHat.ringEquivPiPadicInt_apply
#check @TauCeti.zHat.component_ringEquivPiPadicInt_symm
#check @TauCeti.zHat.continuous_ringEquivPiPadicInt
#check @TauCeti.zHat.continuous_ringEquivPiPadicInt_symm
#check @TauCeti.zHat.ext_of_component
#check @TauCeti.zHat.exists_forall_component_eq
#check @TauCeti.zHat.idem
#check @TauCeti.zHat.component_idem
#check @TauCeti.zHat.component_idem_self
#check @TauCeti.zHat.component_idem_of_ne
-- p-adic powers
#check @TauCeti.IsProP.padicPow
#check @TauCeti.IsProP.mk_padicPow
#check @TauCeti.IsProP.padicPow_natCast
#check @TauCeti.IsProP.padicPow_intCast
#check @TauCeti.IsProP.continuous_padicPow
#check @TauCeti.IsProP.eq_padicPow_of_continuous
#check @TauCeti.IsProP.map_padicPow
#check @TauCeti.IsProP.conj_padicPow
#check @TauCeti.zpowHat
#check @TauCeti.zpowHat_eq_padicPow_component

/-! ## B8 -/

#check @TauCeti.ContinuousAut
#check @TauCeti.Peripheral.basis
#check @TauCeti.Peripheral.basis_apply
#check @TauCeti.Peripheral.map_basis
#check @TauCeti.Peripheral.periphP
#check @TauCeti.Peripheral.periphT
#check @TauCeti.Peripheral.periphC
#check @TauCeti.Peripheral.periphP_eq_basis
#check @TauCeti.Peripheral.periphT_eq_basis
#check @TauCeti.Peripheral.periphC_def
#check @TauCeti.Peripheral.periphP_mul_periphT_mul_periphC
#check @TauCeti.Peripheral.exists_peripheralPowerAutomorphism_two

end Lane_prop


section Lane_tate

/-! ## B6 -/

/-! ### Tau Ceti: the duality statements and their objects -/
#check @TauCeti.ClassFieldTheory.tateDualityPairing_perfect_mixed
#check @TauCeti.ClassFieldTheory.tateDualityPairing_perfect
#check @TauCeti.ClassFieldTheory.tateDualityPairing_flip_perfect
#check @TauCeti.ClassFieldTheory.tateDualityPairing
#check @TauCeti.ClassFieldTheory.tateDualityPairing_def
#check @TauCeti.ClassFieldTheory.h2MuEquivZMod_mixed
#check @TauCeti.ClassFieldTheory.h2MuEquivZMod
#check @TauCeti.ClassFieldTheory.tateDual
#check @TauCeti.ClassFieldTheory.tateDualEquiv
#check @TauCeti.ClassFieldTheory.tateDualEquiv_ρ_apply
#check @TauCeti.ClassFieldTheory.tateEvaluationPairing
#check @TauCeti.ClassFieldTheory.instFiniteTateDual
#check @TauCeti.ClassFieldTheory.muNRep
#check @TauCeti.ClassFieldTheory.GalRep
#check @TauCeti.ClassFieldTheory.kummerCoeffEquivMuNRep
#check @TauCeti.ClassFieldTheory.kummerCoeffEquivMuNRep_smul
#check @TauCeti.ClassFieldTheory.isSmoothDiscrete_muNRep
#check @TauCeti.ClassFieldTheory.muNRepToTateDual
#check @TauCeti.KummerCoeff
#check @TauCeti.ofDiscreteModule
#check @TauCeti.ofDiscreteModule_isSmoothDiscrete
#check @TauCeti.IsSmoothDiscrete
#check @TauCeti.ClassFieldTheory.finite_H
#check @TauCeti.natCard_addMonoidHom_zmod
#check @TauCeti.forall_eq_zero_and_exists_eq_of_bijective_flip
#check @Function.Injective.bijective_of_nat_card_le

/-! ### Tau Ceti: explicit-cocycle bridges (for comparing with gq2 `cup02/cup11/cup20`) -/
#check @TauCeti.ClassFieldTheory.tateDualityPairing_eq_explicitDualityPairing02
#check @TauCeti.ClassFieldTheory.tateDualityPairing_eq_explicitDualityPairing11
#check @TauCeti.ClassFieldTheory.tateDualityPairing_eq_explicitDualityPairing20
#check @TauCeti.TopPairing.cup_one_one_explicitH1AddEquivContinuousCohomologyOfDiscrete
#check @TauCeti.TopPairing.cup_zero_two_ofDiscreteModuleRestrictScalarsInt
#check @TauCeti.TopPairing.cup_two_zero_ofDiscreteModuleRestrictScalarsInt
#check @TauCeti.ContCohomology.explicitAddEquiv_cup02
#check @TauCeti.ContCohomology.explicitAddEquiv_cup20
#check @TauCeti.ContCohomology.explicitMap1Equiv
#check @TauCeti.ContCohomology.explicitMap2Equiv
#check @TauCeti.ContCohomology.explicitMap0_bijective
#check @TauCeti.ContCohomology.explicitMap2_explicitCup02
#check @TauCeti.ContCohomology.explicitMap2_explicitCup11
#check @TauCeti.ContCohomology.explicitMap2_explicitCup20

/-! ### Tau Ceti: finite extensions inside `G_F`, and the `μₙ` transport -/
#check @TauCeti.ClassFieldTheory.range_absoluteGaloisGroupExtend_shapiroFieldEmbedding
#check @TauCeti.ClassFieldTheory.index_eq_finrank_of_range_absoluteGaloisGroupExtend_eq_comap
#check @TauCeti.ClassFieldTheory.fixingSubgroup_shapiroField
#check @TauCeti.ClassFieldTheory.shapiroFieldEmbedding
#check @TauCeti.absoluteGaloisGroupExtend
#check @TauCeti.absoluteGaloisGroupExtendEquiv
#check @TauCeti.coe_absoluteGaloisGroupExtendEquiv_apply
#check @TauCeti.mem_range_absoluteGaloisGroupExtend_iff
#check @TauCeti.index_range_absoluteGaloisGroupExtend
#check @TauCeti.absoluteGaloisGroupRestrictEquiv_absoluteGaloisGroupExtend
#check @TauCeti.galoisSubgroup
#check @TauCeti.mem_galoisSubgroup_iff
#check @TauCeti.toSubgroup_eq_fixingSubgroup_of_fixedField_eq
#check @TauCeti.finiteDimensional_fixedField_toSubgroup
#check @TauCeti.absoluteGaloisGroupRestrictEquiv
#check @TauCeti.coe_absoluteGaloisGroupRestrictEquiv_apply
#check @TauCeti.kummerCoeffMap
#check @TauCeti.kummerCoeffMap_smul
#check @TauCeti.finiteIntermediateFieldValuativeRel
#check @TauCeti.finiteIntermediateFieldTopology
#check @TauCeti.finiteIntermediateField_isNonarchimedeanLocalField
#check @ContinuousMonoidHom.equivRangeOfIsEmbedding
#check @ContinuousMonoidHom.equivRangeOfIsEmbedding_apply

/-! ### Mathlib: infinite Galois correspondence (Q4) -/
#check @InfiniteGalois.fixingSubgroup_fixedField
#check @InfiniteGalois.fixedField_fixingSubgroup
#check @InfiniteGalois.isOpen_iff_finite
#check @IntermediateField.finrank_eq_fixingSubgroup_index
#check @Subgroup.isClosed_of_isOpen
#check @AlgebraicClosure.instIsAlgClosure
#check @IsAlgClosure.isGalois

/-! ### gq2 -/
#check @GQ2.TateDualityG
#check @GQ2.IsLocalDualizingGroup
#check @GQ2.MuN
#check @GQ2.MuDual
#check @GQ2.muDualPairing
#check @GQ2.muDualPairing_equivariant
#check @GQ2.nsmul_muN_eq_zero

/-! ### Definitional pins (all succeed; `muNRep` and `tateDual` are *not* exposed, so their
carriers are reached only through `kummerCoeffEquivMuNRep` / `tateDualEquiv`) -/
example (n : ℕ) (F : Type) [Field F] :
    TauCeti.KummerCoeff F n = Additive (rootsOfUnity n (SeparableClosure F)) := rfl
example (n : ℕ) : GQ2.MuN n = Additive (rootsOfUnity n (AlgebraicClosure ℚ_[2])) := rfl
example : GQ2.AbsGalQ2 = Field.absoluteGaloisGroup ℚ_[2] := rfl
example (n : ℕ) (M : Type) [AddCommGroup M] : GQ2.MuDual n M = (M →+ GQ2.MuN n) := rfl
example (n : ℕ) [NeZero n] (G : Type) [Group G] [TopologicalSpace G] (M : Type) [AddCommGroup M]
    [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M] :
    (TauCeti.ofDiscreteModule (ZMod n) G M).V = M := rfl
example (G : Type) [Group G] [TopologicalSpace G] (n : ℕ) [NeZero n]
    [DistribMulAction G (GQ2.MuN n)] :
    GQ2.IsLocalDualizingGroup G n ↔
      ∃ ι : G →* GQ2.AbsGalQ2, Topology.IsOpenEmbedding ι ∧ (ι.range).FiniteIndex ∧
        ∀ (g : G) (x : GQ2.MuN n), g • x = ι g • x := Iff.rfl

end Lane_tate


section Lane_sw

set_option synthInstance.maxHeartbeats 400000

open CategoryTheory

/-! ## B9 -/

-- the two headline identities (plan §3)
#check @TauCeti.sw1Class_formClass_traceTransfer_smul_sq
#check @TauCeti.sw2Class_formClass_traceTransfer_smul_sq
-- the same identities on diagonal presentations (the shape gq2's `swOne`/`swTwo` need)
#check @TauCeti.sw1_eq_add_galoisCor_of_equivalent_traceTransfer
#check @TauCeti.sw2_eq_add_galoisEvens_add_cup_of_equivalent_traceTransfer
-- Stiefel-Whitney classes
#check @TauCeti.sw1
#check @TauCeti.sw2
#check @TauCeti.sw1_fin_two
#check @TauCeti.sw2_fin_two
#check @TauCeti.sw1Class
#check @TauCeti.sw2Class
#check @TauCeti.sw1Class_formClass
#check @TauCeti.sw2Class_formClass
-- regular form classes
#check @TauCeti.RegularFormPresentation
#check @TauCeti.RegularFormClass
#check @TauCeti.formClass
#check @TauCeti.formClass_mk
#check @TauCeti.RegularFormClass.liftDiagonal
#check @TauCeti.exists_presentedForm_equivalent
-- trace transfer (root namespace `QuadraticMap`, defined by Tau Ceti)
#check @QuadraticMap.traceTransfer
#check @QuadraticMap.traceTransfer_apply
#check @QuadraticMap.traceTransfer_sq
#check @QuadraticMap.nondegenerate_traceTransfer_iff
#check @QuadraticMap.nondegenerate_smul_sq
-- corestriction, Evens norm, open subgroup
#check @TauCeti.galoisSubgroup
#check @TauCeti.galoisSubgroup_index
#check @TauCeti.mem_galoisSubgroup_iff_apply_eq_of_finrank_eq_two
#check @TauCeti.galoisF2Iso
#check @TauCeti.galoisCor
#check @TauCeti.galoisCor_def
#check @TauCeti.galoisCor_kummerClass
#check @TauCeti.galoisEvens
#check @TauCeti.galoisEvens_def
#check @TauCeti.galoisCor_embedding_independent
#check @TauCeti.galoisEvens_embedding_independent
#check @TauCeti.ContCohomology.evensNormIndexTwo
#check @TauCeti.ContCohomology.evensNormIndexTwo_homClass
#check @TauCeti.ContCohomology.graphClass
#check @TauCeti.ContCohomology.graphClass_eq_evensGraphCochainClass
#check @TauCeti.ContCohomology.graphClass_eq_cochainClass
#check @TauCeti.ContCohomology.evensGraphCochainClass_def
#check @TauCeti.ContCohomology.evensGraphCocycle
#check @TauCeti.ContCohomology.evensGraphCochain
#check @TauCeti.ContCohomology.evensB1
#check @TauCeti.ContCohomology.evensBs
#check @TauCeti.ContCohomology.evensExtend
#check @TauCeti.ContCohomology.evensCorCochain
#check @TauCeti.ContCohomology.evensCorCocycle
#check @TauCeti.ContCohomology.evensGraphCochain_comap
#check @TauCeti.ContCohomology.trivialF2Map_graphClass
#check @TauCeti.ContCohomology.trivialF2Map_evensNormIndexTwo
#check @TauCeti.ContCohomology.evensB1_comap
#check @TauCeti.ContCohomology.evensBs_comap
#check @TauCeti.ContCohomology.evensB1_of_mem
#check @TauCeti.ContCohomology.evensB1_of_notMem
#check @TauCeti.ContCohomology.evensBs_apply
#check @TauCeti.ContCohomology.evensExtend_of_mem
#check @TauCeti.ContCohomology.evensExtend_of_notMem
#check @TauCeti.ContCohomology.evensCorCochain_apply
#check @TauCeti.ContCohomology.evensGraphCochain_of_mem
#check @TauCeti.ContCohomology.evensGraphCochain_of_notMem
#check @TauCeti.ContCohomology.evensGraphCochainClass
#check @TauCeti.isSmoothDiscrete_trivialF2
#check @TauCeti.ContCohomology.homClass
#check @TauCeti.ContCohomology.homClass_eq_evensHomCocycleAmbient
#check @TauCeti.ContCohomology.explicitCor1_evensHomCocycleAmbient
#check @TauCeti.trivialF2CorMap
#check @TauCeti.trivialF2CorMap_explicitH1AddEquivContinuousCohomology
-- Kummer classes and characters
#check @TauCeti.kummerClass
#check @TauCeti.rootSign
#check @TauCeti.galoisKummerCharacter
#check @TauCeti.galoisF2Iso_inv_kummerClass
#check @TauCeti.cup_kummerClass_eq_zero_iff
-- the identification of separable closures that `σ` and the A1 group isomorphism must share
#check @TauCeti.separableClosureRingEquiv
#check @TauCeti.separableClosureRingEquiv_symm_apply_eq_algebraMap
#check @TauCeti.absoluteGaloisGroupEquivFixingSubgroup
#check @TauCeti.absoluteGaloisGroupEquivFixingSubgroup_apply
#check @TauCeti.galoisSubgroupEquiv
-- cup product and its commutativity
#check @TauCeti.trivialF2TopPairing
#check @TauCeti.trivialF2TopPairing_cup_comm
#check @TauCeti.ContCohomology.cup11_homClass

-- gq2 side
#check @GQ2.swOne
#check @GQ2.swTwo
#check @GQ2.diagForm
#check @GQ2.IsDiagonalization
#check @GQ2.exists_isDiagonalization
#check @GQ2.traceFormOne
#check @GQ2.traceFormTwisted
#check @GQ2.traceFormOne_isDiagonalization
#check @GQ2.quadExt
#check @GQ2.finiteDimensional_quadExt
#check @GQ2.corFun
#check @GQ2.corH1
#check @GQ2.evensAux
#check @GQ2.bS
#check @GQ2.evensNormFun
#check @GQ2.evensNormH2
#check @GQ2.kummerClassK

section B9Examples

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

attribute [local instance] TopRep.distribMulAction

/-- the local instance every Tau Ceti `Evens` file declares; the adapter needs it too -/
local instance continuousSMul_trivialF2_b9 (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : ContinuousSMul G (TauCeti.trivialF2 G).V :=
  (TauCeti.isSmoothDiscrete_trivialF2 G).continuousSMul

-- `traceFormOne k δ = Tr_*⟨1⟩`: not `rfl` (`QuadraticMap.traceTransfer` is not exposed), but
-- one lemma.
example (k : IntermediateField ℚ_[2] ℚ̄₂) (δ : ℚ̄₂) :
    GQ2.traceFormOne k δ = QuadraticMap.traceTransfer ↥k
      (QuadraticMap.sq (R := ↥(GQ2.quadExt k δ)) (A := ↥(GQ2.quadExt k δ))) :=
  QuadraticMap.traceTransfer_sq.symm

-- `traceFormTwisted k δ a = Tr_*⟨a⟩`: `Tr(a*z*z)` against `Tr(a*(z*z))`, by `ext` + `mul_assoc`.
example (k : IntermediateField ℚ_[2] ℚ̄₂) (δ : ℚ̄₂) (a : ↥(GQ2.quadExt k δ)) :
    GQ2.traceFormTwisted k δ a = QuadraticMap.traceTransfer ↥k
      (a • QuadraticMap.sq (R := ↥(GQ2.quadExt k δ)) (A := ↥(GQ2.quadExt k δ))) := by
  ext z
  rw [GQ2.traceFormTwisted_apply, QuadraticMap.traceTransfer_apply, smul_apply,
    QuadraticMap.sq_apply, smul_eq_mul, mul_assoc]

-- Tau Ceti side, Evens norm: `N^Ev((a))` is the class of the explicit graph cocycle of the
-- Kummer character of `a` on `galoisSubgroup K L σ`, at every `s ∉ G_L`.
example {K L : Type} [Field K] [Field L] [Invertible (2 : L)] [Algebra K L]
    [FiniteDimensional K L] (σ : L →ₐ[K] SeparableClosure K)
    (hL : Module.finrank K L = 2) (a : Lˣ) (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L))
    (s : TauCeti.AbsoluteGaloisGroup K) (hs : s ∉ TauCeti.galoisSubgroup K L σ) :
    TauCeti.galoisEvens K L σ hL (TauCeti.kummerClass a) =
      TauCeti.ContCohomology.evensGraphCochainClass (TauCeti.galoisSubgroup K L σ) s
        (TauCeti.galoisKummerCharacter σ a r hr) ((TauCeti.galoisSubgroup_index K L σ).trans hL) hs
        (TauCeti.continuous_galoisKummerCharacter σ a r hr) := by
  rw [TauCeti.galoisEvens_def, TauCeti.galoisF2Iso_inv_kummerClass σ a r hr,
    TauCeti.ContCohomology.evensNormIndexTwo_homClass,
    TauCeti.ContCohomology.graphClass_eq_evensGraphCochainClass _ _ s hs]

-- Tau Ceti side, corestriction: `cor (a)` is the explicit class of the Shapiro-sum cocycle
-- `b₁ + b_s` of the Kummer character, at every `s ∉ G_L`.
example {K L : Type} [Field K] [Invertible (2 : K)] [Field L] [Invertible (2 : L)] [Algebra K L]
    [FiniteDimensional K L] (σ : L →ₐ[K] SeparableClosure K)
    (hL : Module.finrank K L = 2) (a : Lˣ) (r : SeparableClosure K) (hr : r ^ 2 = σ (a : L))
    (s : TauCeti.AbsoluteGaloisGroup K) (hs : s ∉ TauCeti.galoisSubgroup K L σ) :
    TauCeti.galoisCor K L σ 1 (TauCeti.kummerClass a) =
      (eqToHom (congrArg (continuousCohomology 1)
          (TauCeti.ofDiscreteModule_trivialF2 (TauCeti.AbsoluteGaloisGroup K)))).hom
        (TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology
          (TauCeti.AbsoluteGaloisGroup K)
          (TauCeti.trivialF2 (TauCeti.AbsoluteGaloisGroup K)).V
          (TauCeti.ContCohomology.evensCorCocycle (TauCeti.galoisSubgroup K L σ) s
            (TauCeti.galoisKummerCharacter σ a r hr)
            ((TauCeti.galoisSubgroup_index K L σ).trans hL) hs
            (TauCeti.continuous_galoisKummerCharacter σ a r hr))) := by
  rw [TauCeti.galoisCor_def, ConcreteCategory.comp_apply,
    TauCeti.galoisF2Iso_inv_kummerClass σ a r hr,
    TauCeti.ContCohomology.homClass_eq_evensHomCocycleAmbient,
    TauCeti.trivialF2CorMap_explicitH1AddEquivContinuousCohomology,
    TauCeti.ContCohomology.explicitCor1_evensHomCocycleAmbient _
      ((TauCeti.galoisSubgroup_index K L σ).trans hL) s hs]

-- gq2's Shapiro components and two-point graph cocycle (eqs. (97)-(98)) are Tau Ceti's,
-- pointwise, once `α : U → 𝔽₂` is read as `α' : U →* Multiplicative (ZMod 2)`.
example {G : Type} [Group G] (U : Subgroup G) (s : G) (α : U → ZMod 2)
    (α' : U →* Multiplicative (ZMod 2)) (hα' : ∀ u, Multiplicative.toAdd (α' u) = α u) :
    GQ2.corFun U s α = TauCeti.ContCohomology.evensCorCochain U s α' ∧
      GQ2.evensNormFun U s α = TauCeti.ContCohomology.evensGraphCochain U s α' := by
  open TauCeti.ContCohomology in
  have hb1 : ∀ x, GQ2.evensAux U s α x = evensB1 U s α' x := by
    intro x
    by_cases hx : x ∈ U
    · rw [GQ2.evensAux_of_mem α hx, evensB1_of_mem hx, evensExtend_of_mem hx, hα']
    · rw [evensB1_of_notMem hx]
      by_cases hxs : x * s ∈ U
      · rw [GQ2.evensAux, dite_eq_right hx, dite_eq_left hxs, evensExtend_of_mem hxs, hα']
      · rw [GQ2.evensAux, dite_eq_right hx, dite_eq_right hxs, evensExtend_of_notMem hxs]
  have hbs : ∀ x, GQ2.bS U s α x = evensBs U s α' x := fun x => by
    rw [evensBs_apply, ← hb1]; rfl
  refine ⟨funext fun x => by rw [evensCorCochain_apply, GQ2.corFun, hb1, hbs], ?_⟩
  funext ⟨γ, η⟩
  by_cases hγ : γ ∈ U
  · rw [evensGraphCochain_of_mem hγ, GQ2.evensNormFun, ite_eq_left hγ, hb1, hbs]
  · rw [evensGraphCochain_of_notMem hγ, GQ2.evensNormFun, ite_eq_right hγ, hb1, hb1, hbs]

-- The Tau Ceti diagonal-presentation identities, at `K = ↥k`, `L = ↥(quadExt k δ)` and any
-- `σ`, on gq2 diagonalizations `Tr_*⟨1⟩ ≃ ⟨x, y⟩`, `Tr_*⟨a⟩ ≃ ⟨x', y'⟩`. Note `simp only`, not
-- `rw`, on the degree-2 equation: `rw [sw2_fin_two] at e2` times out (whnf, 200000 heartbeats).
example (k : IntermediateField ℚ_[2] ℚ̄₂) {δ : ℚ̄₂} [FiniteDimensional ↥k ↥(GQ2.quadExt k δ)]
    (hdeg : Module.finrank ↥k ↥(GQ2.quadExt k δ) = 2) (a : (↥(GQ2.quadExt k δ))ˣ)
    (σ : ↥(GQ2.quadExt k δ) →ₐ[↥k] SeparableClosure ↥k) (x y x' y' : (↥k)ˣ)
    (h1 : GQ2.IsDiagonalization k (GQ2.traceFormOne k δ) x y)
    (ha : GQ2.IsDiagonalization k (GQ2.traceFormTwisted k δ ↑a) x' y') :
    TauCeti.kummerClass x' + TauCeti.kummerClass y' =
        TauCeti.kummerClass x + TauCeti.kummerClass y +
          TauCeti.galoisCor ↥k ↥(GQ2.quadExt k δ) σ 1 (TauCeti.kummerClass a) ∧
      (TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
          (TauCeti.kummerClass x') (TauCeti.kummerClass y') =
        (TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
            (TauCeti.kummerClass x) (TauCeti.kummerClass y) +
          TauCeti.galoisEvens ↥k ↥(GQ2.quadExt k δ) σ hdeg (TauCeti.kummerClass a) +
          (TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
            (TauCeti.kummerClass x + TauCeti.kummerClass y)
            (TauCeti.galoisCor ↥k ↥(GQ2.quadExt k δ) σ 1 (TauCeti.kummerClass a)) := by
  have hd : ∀ u v : (↥k)ˣ, GQ2.diagForm k u v =
      QuadraticMap.weightedSumSquares ↥k fun i => ((![u, v] i : (↥k)ˣ) : ↥k) := fun u v => by
    ext w
    simp [GQ2.diagForm, QuadraticMap.weightedSumSquares_apply, Units.smul_def]
  have hw : ∀ (V : Type) [AddCommGroup V] [Module ↥k V] (Q : QuadraticForm ↥k V) (u v : (↥k)ˣ),
      GQ2.IsDiagonalization k Q u v →
        Q.Equivalent (QuadraticMap.weightedSumSquares ↥k fun i => ((![u, v] i : (↥k)ˣ) : ↥k)) := by
    intro V _ _ Q u v h
    rwa [GQ2.IsDiagonalization, hd] at h
  have heq1 : GQ2.traceFormOne k δ = QuadraticMap.traceTransfer ↥k
      (QuadraticMap.sq (R := ↥(GQ2.quadExt k δ)) (A := ↥(GQ2.quadExt k δ))) :=
    QuadraticMap.traceTransfer_sq.symm
  have heqa : GQ2.traceFormTwisted k δ ↑a = QuadraticMap.traceTransfer ↥k
      ((a : ↥(GQ2.quadExt k δ)) •
        QuadraticMap.sq (R := ↥(GQ2.quadExt k δ)) (A := ↥(GQ2.quadExt k δ))) := by
    ext z
    rw [GQ2.traceFormTwisted_apply, QuadraticMap.traceTransfer_apply, smul_apply,
      QuadraticMap.sq_apply, smul_eq_mul, mul_assoc]
  have h1' := hw _ _ _ _ h1
  have ha' := hw _ _ _ _ ha
  rw [heq1] at h1'
  rw [heqa] at ha'
  have e1 := TauCeti.sw1_eq_add_galoisCor_of_equivalent_traceTransfer σ a h1' ha'
  have e2 := TauCeti.sw2_eq_add_galoisEvens_add_cup_of_equivalent_traceTransfer σ hdeg a h1' ha'
  have hs2 : ∀ u v : (↥k)ˣ, TauCeti.sw2 ![u, v] =
      (TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
        (TauCeti.kummerClass u) (TauCeti.kummerClass v) := fun u v => TauCeti.sw2_fin_two _
  have hs1 : ∀ u v : (↥k)ˣ, TauCeti.sw1 ![u, v] = TauCeti.kummerClass u + TauCeti.kummerClass v :=
    fun u v => TauCeti.sw1_fin_two _
  simp only [hs1] at e1
  simp only [hs2, hs1] at e2
  exact ⟨e1, e2⟩

end B9Examples

end Lane_sw


section Lane_recip

/-! ## B5 -/

-- the absolute Artin map and its three topological properties
#check @TauCeti.ClassFieldTheory.artinMap
#check @TauCeti.ClassFieldTheory.continuous_artinMap
#check @TauCeti.ClassFieldTheory.denseRange_artinMap
#check @TauCeti.ClassFieldTheory.injective_artinMap
-- unramified coordinate and its normalization by the valuation
#check @TauCeti.unramifiedCoordinate
#check @TauCeti.unramifiedCoordinate_mk
#check @TauCeti.unramifiedCoordinate_surjective
#check @TauCeti.ClassFieldTheory.unramifiedCoordinate_artinMap
#check @TauCeti.normalizedValuation
#check @Padic.toAdd_normalizedValuation_eq_valuation
#check @TauCeti.Padic.isUniformizer_natCast_self
-- ℤ̂ → ℤ₂ reduction
#check @TauCeti.zHat.lift
#check @TauCeti.zHat.lift_ofInt
#check @TauCeti.zHat.lift_gen
#check @TauCeti.zHat.lift_ofAdd_one_padicInt_apply
#check @TauCeti.zHat.component_surjective
-- finite-layer reciprocity
#check @TauCeti.ClassFieldTheory.localArtinEquiv
#check @TauCeti.ClassFieldTheory.localArtinMap
#check @TauCeti.ClassFieldTheory.localArtinMap_eq_zero_iff
#check @TauCeti.ClassFieldTheory.ker_localArtinMap
#check @TauCeti.ClassFieldTheory.surjective_localArtinMap
#check @TauCeti.ClassFieldTheory.artinMap_restrict
#check @TauCeti.ClassFieldTheory.mem_normGroup_of_mk_eq_artinMap_of_fixes
#check @TauCeti.ClassFieldTheory.ClassFormation.artinMap
#check @TauCeti.ClassFieldTheory.ClassFormation.ker_artinMap
#check @TauCeti.normGroup
#check @TauCeti.mem_normGroup_iff
#check @TauCeti.absoluteGaloisGroupRestrictEquiv
#check @TauCeti.coe_absoluteGaloisGroupRestrictEquiv_apply
-- cyclotomic normalization
#check @TauCeti.localCyclotomicCharacter
#check @TauCeti.localCyclotomicCharacter_apply
#check @TauCeti.abelianizedLocalCyclotomicCharacter
#check @TauCeti.abelianizedLocalCyclotomicCharacter_mk
#check @TauCeti.ClassFieldTheory.localCyclotomicCharacter_artinMap_unit
#check @TauCeti.ClassFieldTheory.localCyclotomicCharacter_artinMap_padic
#check @TauCeti.ClassFieldTheory.localCyclotomicCharacter_artinMap_padic_uniformizer

-- The Artin map's target is literally gq2's `AbsGalQ2ab`.
example : GQ2.AbsGalQ2ab = Field.absoluteGaloisGroupAbelianization ℚ_[2] := rfl
-- gq2's abelianization map is Tau Ceti's coercion into `G^ab`.
example (g : GQ2.AbsGalQ2) :
    GQ2.toAb g = (g : Field.absoluteGaloisGroupAbelianization ℚ_[2]) := rfl
-- gq2's `unitEmbed` is the embedding in `localCyclotomicCharacter_artinMap_padic`.
example (u : ℤ_[2]ˣ) :
    GQ2.unitEmbed u = Units.map (algebraMap ℤ_[2] ℚ_[2]).toMonoidHom u := rfl
-- gq2's `uniformizer` is the one in `localCyclotomicCharacter_artinMap_padic_uniformizer`.
example : GQ2.uniformizer =
    Units.mk0 ((2 : ℕ) : ℚ_[2]) (Nat.cast_ne_zero.2 (Fact.out : Nat.Prime 2).ne_zero) := rfl
-- Instance agreement: Tau Ceti's continuity/density proofs typecheck at gq2's field types.
example : Continuous (TauCeti.ClassFieldTheory.artinMap ℚ_[2] : ℚ_[2]ˣ →* GQ2.AbsGalQ2ab) :=
  TauCeti.ClassFieldTheory.continuous_artinMap ℚ_[2]
example : DenseRange (TauCeti.ClassFieldTheory.artinMap ℚ_[2] : ℚ_[2]ˣ →* GQ2.AbsGalQ2ab) :=
  TauCeti.ClassFieldTheory.denseRange_artinMap ℚ_[2]

/-! ## B10 -/

#check @TauCeti.wildInertiaSubgroup
#check @TauCeti.isClosed_wildInertiaSubgroup
#check @TauCeti.wildInertiaSubgroup_normal
#check @TauCeti.isProP_wildInertiaSubgroup
#check @TauCeti.charP_residueField
#check @TauCeti.isProP_iff
#check @TauCeti.tameQuotient
#check @TauCeti.toTameQuotient
#check @TauCeti.toTameQuotient_apply
#check @TauCeti.tameQuotientToZHat_toTameQuotient
#check @TauCeti.tameQuotientGeometricEquiv
#check @TauCeti.IwasawaGroupGeometric
#check @TauCeti.iwasawaRelatorGeometric_def
#check @TauCeti.iwasawaSigmaGeometric
#check @TauCeti.iwasawaTauGeometric
#check @TauCeti.inv_iwasawaSigmaGeometric_mul_iwasawaTauGeometric_mul
#check @TauCeti.iwasawaCoordinateGeometric
#check @TauCeti.iwasawaCoordinateGeometric_iwasawaSigmaGeometric
#check @TauCeti.iwasawaCoordinateGeometric_iwasawaTauGeometric
#check @TauCeti.iwasawaCoordinateGeometric_tameQuotientGeometricEquiv
#check @TauCeti.tameQuotientGeometricEquiv_toTameQuotient_frobenius
#check @TauCeti.IsArithFrobeniusLift
#check @TauCeti.exists_isArithFrobeniusLift
#check @TauCeti.exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top
#check @TauCeti.ClassFieldTheory.isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer
#check @TauCeti.ClassFieldTheory.mem_inertiaSubgroup_of_mk_eq_artinMap
#check @Padic.natCard_residueField
#check @TauCeti.presentedProfiniteGroup.lift
#check @TauCeti.presentedProfiniteGroup.lift_of
#check @TauCeti.presentedProfiniteGroup.hom_ext_of
#check @TauCeti.freeProfiniteGroup.lift
#check @TauCeti.freeProfiniteGroup.lift_of

-- gq2's `AbsGalQ2 ⧸ W` at `W = wildInertiaSubgroup ℚ_[2]` is Tau Ceti's `tameQuotient ℚ_[2]`.
example : (GQ2.AbsGalQ2 ⧸ TauCeti.wildInertiaSubgroup ℚ_[2]) = TauCeti.tameQuotient ℚ_[2] := rfl
-- The Frobenius lift and the tame generator exist at `ℚ_[2]` with all instances inferred.
example : ∃ σ : Field.absoluteGaloisGroup ℚ_[2], TauCeti.IsArithFrobeniusLift ℚ_[2] σ :=
  TauCeti.exists_isArithFrobeniusLift ℚ_[2]
example : ∃ τ : TauCeti.inertiaSubgroup ℚ_[2],
    (Subgroup.zpowers (TauCeti.inertiaTameCharacter ℚ_[2] τ)).topologicalClosure = ⊤ :=
  TauCeti.exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top ℚ_[2]

end Lane_recip


section Lane_orient

/-! ## B3c: the dyadic orientation -/

-- the marked theorem and its unmarked corollary
set_option pp.funBinderTypes true in
#check @TauCeti.absoluteGaloisGroupProP_two_ratPadic_marked
#check @TauCeti.absoluteGaloisGroupProP_two_ratPadic
#check @TauCeti.ratPadicTwo_hasPrimitiveRoot

-- `G_K(p)`
#check @TauCeti.absoluteGaloisGroupProP
#check @TauCeti.absoluteGaloisGroupProPQuotientMap
#check @TauCeti.isProP_absoluteGaloisGroupProP

-- the cyclotomic character and its descent
#check @TauCeti.localCyclotomicCharacter
#check @TauCeti.localCyclotomicCharacter_apply
#check @TauCeti.localCyclotomicCharacter_continuous
#check @TauCeti.continuousLocalCyclotomicCharacter
#check @TauCeti.continuousLocalCyclotomicCharacter_apply
#check @TauCeti.proPKernel_le_ker_localCyclotomicCharacter
#check @TauCeti.cyclotomicOrientation
#check @TauCeti.cyclotomicOrientation_mk
#check @TauCeti.cyclotomicOrientation_comp_absoluteGaloisGroupProPQuotientMap
#check @TauCeti.cyclotomicOrientation_range

-- `D₀`, its relator and generators
#check @TauCeti.d0Relator
#check @TauCeti.d0Relator_def
#check @TauCeti.d0Relator_eq_demushkinWordTwoOdd
#check @TauCeti.demushkinD0
#check @TauCeti.d0A
#check @TauCeti.d0S
#check @TauCeti.d0Y
#check @TauCeti.d0_relation
#check @TauCeti.d0Lift
#check @TauCeti.d0Lift_d0A
#check @TauCeti.d0Lift_d0S
#check @TauCeti.d0Lift_d0Y
#check @TauCeti.d0_hom_ext
#check @TauCeti.isProP_demushkinD0
#check @TauCeti.d0_topologicallyGenerates

-- the standard orientation and its values (T2 item 5)
#check @TauCeti.isUnit_neg_three
#check @TauCeti.negThreeUnit
#check @TauCeti.negThreeUnit_coe
#check @TauCeti.negThreeUnit_inv_mul_one_sub_two_pow_two
#check @TauCeti.standardD0Orientation_relator
#check @TauCeti.standardD0Orientation
#check @TauCeti.standardD0Orientation_d0A
#check @TauCeti.standardD0Orientation_d0S
#check @TauCeti.standardD0Orientation_d0Y
#check @TauCeti.standardD0Orientation_surjective
#check @TauCeti.range_standardD0Orientation
#check @TauCeti.standardD0Orientation_unique

-- `D0/Invariants.lean` (canonical-character identification; not needed by the adapter)
#check @TauCeti.isDemushkin_demushkinD0
#check @TauCeti.hasPrescriptionProperty_standardD0Orientation
#check @TauCeti.demushkinCharacter_demushkinD0

-- support used by the adapter sketch
#check @TauCeti.IsProP
#check @TauCeti.isProP_iff
#check @TauCeti.isProP_units_padicInt_two
#check @TauCeti.proPKernel
#check @TauCeti.mem_proPKernel_iff
#check @TauCeti.maximalProPQuotient
#check @TauCeti.isProP_maximalProPQuotient
#check @TauCeti.freeProP
#check @TauCeti.freeProP.of
#check @TauCeti.presentedProP
#check @TauCeti.presentedProP.of

/-! ### B3c pins -/

-- Same commutator convention on both sides: `[x,y] = x⁻¹y⁻¹xy`.
example {G : Type*} [Group G] (x y : G) : GQ2.commP x y = x⁻¹ * y⁻¹ * x * y := rfl

-- gq2's relator unfolds to Tau Ceti's word (same generator order `A, S, Y = of 0, 1, 2`, `Fin 3`),
-- but in `GQ2.FreeProfiniteGroup (Fin 3)` rather than `TauCeti.freeProP 2 (Fin 3)`.
example : GQ2.d0Relator = GQ2.FreeProfiniteGroup.of 0 ^ 2 * GQ2.FreeProfiniteGroup.of 1 ^ 4 *
    ((GQ2.FreeProfiniteGroup.of 1)⁻¹ * (GQ2.FreeProfiniteGroup.of 2)⁻¹ *
      GQ2.FreeProfiniteGroup.of 1 * GQ2.FreeProfiniteGroup.of 2) := rfl

-- gq2's `d0_relation` is literally the hypothesis of `TauCeti.d0Lift`.
example : GQ2.d0A ^ 2 * GQ2.d0S ^ 4 * (GQ2.d0S⁻¹ * GQ2.d0Y⁻¹ * GQ2.d0S * GQ2.d0Y) = 1 :=
  GQ2.d0_relation

-- `chiCyc` agrees pointwise with Tau Ceti's character through the stated `_apply` lemma
-- (a bare `rfl` for `GQ2.chiCyc = TauCeti.localCyclotomicCharacter 2 ℚ_[2]` fails: not exposed).
example (g : GQ2.AbsGalQ2) : GQ2.chiCyc g = TauCeti.localCyclotomicCharacter 2 ℚ_[2] g :=
  (TauCeti.localCyclotomicCharacter_apply 2 ℚ_[2] g).symm

-- gq2's `(-3)`-quantified value against Tau Ceti's `negThreeUnit`.
example (y : ℤ_[2]ˣ) (hy : (y : ℤ_[2]) = -3) : y = TauCeti.negThreeUnit :=
  Units.ext (by rw [hy, TauCeti.negThreeUnit_coe])

-- `IsProP`: not `Iff.rfl` (Tau Ceti's body is not exposed), but one rewrite.
example (p : ℕ) (P : Type*) [Group P] [TopologicalSpace P] :
    GQ2.IsProP p P ↔ TauCeti.IsProP p P := by
  rw [TauCeti.isProP_iff]; rfl

-- `proPKernel`: not `rfl` (not exposed), but `ext` through `TauCeti.mem_proPKernel_iff`.
example (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] :
    GQ2.proPKernel p G = TauCeti.proPKernel p G := by
  ext x
  rw [TauCeti.mem_proPKernel_iff, GQ2.proPKernel, Subgroup.mem_iInf]
  exact ⟨fun h U hU => h ⟨U, hU⟩, fun h U => h U.1 U.2⟩

end Lane_orient
