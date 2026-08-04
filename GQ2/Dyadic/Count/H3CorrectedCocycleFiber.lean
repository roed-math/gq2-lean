/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3RelationCharacterTransition
import GQ2.Dyadic.Count.H3SqReconstructionJointLiftCapstone

/-!
# Corrected finite cocycle fibers and their strictification obstruction

Literal compatibility of the universal relation-word output is false.  The corrected finite
fiber retains a chosen bar representative and compares adjacent levels modulo the universal
Fox kernel, with the explicit normalized-section relation cell on the right-hand side.

For one transition we package the remaining discrepancy as a linear map into the universal
Fox kernel.  Absorbing the relation cell and this kernel defect into an actual target bar input
is equivalent to vanishing of the original target-bar cokernel class.  Thus corrected fibers
remove the terminal contradiction and compose, but strictification to the raw compatible
family required by the present capstone is still a genuine finite affine/cokernel problem.
The joint one-relator lift is chosen only after that raw family, so its extra freedom does not
change this strictification equation.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh GQ2.FoxH
open GQ2.Dyadic.SqCore

private abbrev SqCorrectedInputThree (h : ℕ)
    (V : OpenNormalSubgroup (DSq h : Type)) :=
  FiniteModTwoBarCochainThree ((DSq h : Type) ⧸ V.toSubgroup)

/-! ## Corrected finite fibers -/

/-- A finite cocycle-cancelling output together with a specified bar-two representative.
Keeping the representative is necessary because the explicit section correction is evaluated
on its bar boundary. -/
structure SqCorrectedUniversalCocycleOutputFiber
    (h : ℕ) (V U : OpenNormalSubgroup (DSq h : Type)) where
  point : SqUniversalCocycleOutputFiber h V U
  barChain : SqCorrectedInputThree h V →ₗ[ZMod 2]
    FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)
  output_eq : point.output =
    (sqOpenQuotientBarToUniversalRelationTwo h U).comp barChain

/-- Choose a bar representative from the existential field of an ordinary finite fiber. -/
noncomputable def SqCorrectedUniversalCocycleOutputFiber.ofFiber
    {h : ℕ} {V U : OpenNormalSubgroup (DSq h : Type)}
    (x : SqUniversalCocycleOutputFiber h V U) :
    SqCorrectedUniversalCocycleOutputFiber h V U where
  point := x
  barChain := Classical.choose x.bar_representable
  output_eq := Classical.choose_spec x.bar_representable

/-- Every ordinary local fiber therefore has a corrected representative. -/
theorem nonempty_sqCorrectedUniversalCocycleOutputFiber_of_fiber
    {h : ℕ} {V U : OpenNormalSubgroup (DSq h : Type)}
    (x : SqUniversalCocycleOutputFiber h V U) :
    Nonempty (SqCorrectedUniversalCocycleOutputFiber h V U) :=
  ⟨SqCorrectedUniversalCocycleOutputFiber.ofFiber x⟩

@[ext] theorem SqCorrectedUniversalCocycleOutputFiber.ext
    {h : ℕ} {V U : OpenNormalSubgroup (DSq h : Type)}
    {x y : SqCorrectedUniversalCocycleOutputFiber h V U}
    (hpoint : x.point = y.point) (hbar : x.barChain = y.barChain) : x = y := by
  cases x
  cases y
  cases hpoint
  cases hbar
  rfl

/-- The corrected fiber remains finite after retaining a bar representative: it embeds in the
product of the old finite fiber and the finite space of linear bar-chain choices. -/
noncomputable instance SqCorrectedUniversalCocycleOutputFiber.instFinite
    (h : ℕ) (V U : OpenNormalSubgroup (DSq h : Type)) :
    Finite (SqCorrectedUniversalCocycleOutputFiber h V U) := by
  classical
  letI : Finite ((DSq h : Type) ⧸ V.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen V.toSubgroup V.isOpen'
  letI : Finite ((DSq h : Type) ⧸ U.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen'
  letI : Fintype ((DSq h : Type) ⧸ V.toSubgroup) := Fintype.ofFinite _
  letI : Fintype ((DSq h : Type) ⧸ U.toSubgroup) := Fintype.ofFinite _
  letI : Fintype (SqCorrectedInputThree h V) := Fintype.ofFinite _
  letI : Fintype
      (FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)) :=
    Finsupp.fintype
  letI : Finite (SqCorrectedInputThree h V →ₗ[ZMod 2]
      FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)) :=
    Finite.of_injective
      (fun f : SqCorrectedInputThree h V →ₗ[ZMod 2]
          FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup) =>
        (f : SqCorrectedInputThree h V →
          FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)))
      LinearMap.coe_injective
  let representative (x : SqCorrectedUniversalCocycleOutputFiber h V U) :=
    (x.point, x.barChain)
  apply Finite.of_injective representative
  intro x y hxy
  apply SqCorrectedUniversalCocycleOutputFiber.ext
  · simpa [representative] using congrArg Prod.fst hxy
  · simpa [representative] using congrArg Prod.snd hxy

/-- Corrected compatibility of two local fibers across a quotient transition.  The transported
finer output plus the chosen coarser output equals the explicit relation cell modulo the
universal Fox kernel. -/
def SqCorrectedUniversalCocycleOutputTransitionRel
    (h : ℕ) {V U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U')
    (x : SqCorrectedUniversalCocycleOutputFiber h V U)
    (y : SqCorrectedUniversalCocycleOutputFiber h V U') : Prop :=
  ∀ c : SqCorrectedInputThree h V,
    SqUniversalRelationFoxEquivalent h U'
      (sqUniversalRelationModuleTransition h hUU' (x.point.output c) +
        y.point.output c)
      (sqUniversalSectionRefinementCorrection h hUU'
        (finiteModTwoBarBoundaryTwo (x.barChain c)))

/-- A corrected compatible cocycle-cancelling family.  Its level objects retain all local
Fox-zero and cancellation fields of the old finite fibers; only transition compatibility is
weakened to the proved relation-cell/Fox-kernel law. -/
structure SqCorrectedCompatibleUniversalCocycleCancellingSyzygyAt
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type)) where
  level : ∀ U : OpenNormalSubgroup (DSq h : Type),
    SqCorrectedUniversalCocycleOutputFiber h V U
  compatible : ∀ {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U'),
    SqCorrectedUniversalCocycleOutputTransitionRel h hUU' (level U) (level U')

/-- A strictification of a corrected family to the literal compatible object consumed by the
current capstone.  The raw coordinates are allowed to change inside the universal Fox kernel,
which is precisely the freedom retained by corrected compatibility. -/
structure SqCorrectedCompatibleUniversalCocycleCancellingSyzygyAt.RawStrictification
    {h : ℕ} {V : OpenNormalSubgroup (DSq h : Type)}
    (C : SqCorrectedCompatibleUniversalCocycleCancellingSyzygyAt h V) where
  raw : SqCompatibleUniversalCocycleCancellingSyzygyAt h V
  foxEquivalent : ∀ (U : OpenNormalSubgroup (DSq h : Type))
    (c : SqCorrectedInputThree h V),
    SqUniversalRelationFoxEquivalent h U
      (raw.universalSyzygy.coordinate U c) ((C.level U).point.output c)

/-! ## The universal Fox-kernel defect -/

/-- The relation-cell correction as a linear function of the source bar-two input. -/
def sqUniversalBarInputRelationCellCorrectionTwo
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U') :
    FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup) →ₗ[ZMod 2]
      RegularModTwoRelationModule
        ((DSq h : Type) ⧸ U'.toSubgroup)
        (FreeRelationKernel (sqOpenQuotientMarking h U')) :=
  (sqUniversalSectionRefinementCorrection h hUU').comp
    finiteModTwoBarBoundaryTwo

@[simp] theorem sqUniversalBarInputRelationCellCorrectionTwo_apply
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U')
    (b : FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)) :
    sqUniversalBarInputRelationCellCorrectionTwo h hUU' b =
      sqUniversalSectionRefinementCorrection h hUU'
        (finiteModTwoBarBoundaryTwo b) :=
  rfl

/-- After adjoining the explicit relation cell, the remaining failure of raw compatibility.
It is linear in the finite bar input. -/
def sqUniversalBarInputCorrectedKernelDefect
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U') :
    FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup) →ₗ[ZMod 2]
      RegularModTwoRelationModule
        ((DSq h : Type) ⧸ U'.toSubgroup)
        (FreeRelationKernel (sqOpenQuotientMarking h U')) :=
  (sqUniversalRelationModuleTransition h hUU').comp
      (sqOpenQuotientBarToUniversalRelationTwo h U) +
    (sqOpenQuotientBarToUniversalRelationTwo h U').comp
      (finiteModTwoBarMapTwo (openNormalQuotientProj hUU')) +
    sqUniversalBarInputRelationCellCorrectionTwo h hUU'

@[simp] theorem sqUniversalBarInputCorrectedKernelDefect_apply
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U')
    (b : FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)) :
    sqUniversalBarInputCorrectedKernelDefect h hUU' b =
      sqUniversalRelationModuleTransition h hUU'
          (sqOpenQuotientBarToUniversalRelationTwo h U b) +
        sqOpenQuotientBarToUniversalRelationTwo h U'
          (finiteModTwoBarMapTwo (openNormalQuotientProj hUU') b) +
        sqUniversalSectionRefinementCorrection h hUU'
          (finiteModTwoBarBoundaryTwo b) :=
  rfl

/-- The corrected discrepancy lands in the universal Fox kernel unconditionally. -/
theorem sqUniversalBarInputCorrectedKernelDefect_mem_ker
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U')
    (b : FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)) :
    sqUniversalBarInputCorrectedKernelDefect h hUU' b ∈
      LinearMap.ker ((finiteUniversalRelationFoxBoundary
        (sqOpenQuotientMarking h U')).map) := by
  rw [LinearMap.mem_ker, sqUniversalBarInputCorrectedKernelDefect_apply,
    map_add, map_add, sqUniversalBarInput_correctedTransition_fox]
  exact ZModModule.add_self _

/-- Exact raw decomposition: transported output equals canonical target output, relation cell,
and the residual Fox-kernel defect. -/
theorem sqUniversalBarInput_eq_target_add_relationCell_add_kernelDefect
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U')
    (b : FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)) :
    sqUniversalRelationModuleTransition h hUU'
        (sqOpenQuotientBarToUniversalRelationTwo h U b) =
      sqOpenQuotientBarToUniversalRelationTwo h U'
          (finiteModTwoBarMapTwo (openNormalQuotientProj hUU') b) +
        sqUniversalBarInputRelationCellCorrectionTwo h hUU' b +
        sqUniversalBarInputCorrectedKernelDefect h hUU' b := by
  rw [sqUniversalBarInputCorrectedKernelDefect_apply]
  rw [sqUniversalBarInputRelationCellCorrectionTwo_apply]
  let A := sqUniversalRelationModuleTransition h hUU'
    (sqOpenQuotientBarToUniversalRelationTwo h U b)
  let B := sqOpenQuotientBarToUniversalRelationTwo h U'
    (finiteModTwoBarMapTwo (openNormalQuotientProj hUU') b)
  let C := sqUniversalSectionRefinementCorrection h hUU'
    (finiteModTwoBarBoundaryTwo b)
  change A = B + C + (A + B + C)
  symm
  calc
    B + C + (A + B + C) = (B + B) + (C + C) + A := by abel
    _ = _ := by rw [ZModModule.add_self, ZModModule.add_self]; simp

/-! ## The finite affine strictification problem -/

/-- The canonical corrected transition strictifies precisely when its relation-cell plus
Fox-kernel defect can be represented by an additional target bar-two input. -/
def SqUniversalBarInputCorrectedStrictifiableAt
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U')
    (b : FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)) : Prop :=
  ∃ a : FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U'.toSubgroup),
    sqOpenQuotientBarToUniversalRelationTwo h U' a =
      sqUniversalBarInputRelationCellCorrectionTwo h hUU' b +
        sqUniversalBarInputCorrectedKernelDefect h hUU' b

/-- Exact affine characterization: absorbing the correction is equivalent to the original
transported raw output belonging to the target bar range. -/
theorem sqUniversalBarInputCorrectedStrictifiableAt_iff_mem_range
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U')
    (b : FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)) :
    SqUniversalBarInputCorrectedStrictifiableAt h hUU' b ↔
      sqUniversalRelationModuleTransition h hUU'
          (sqOpenQuotientBarToUniversalRelationTwo h U b) ∈
        LinearMap.range (sqOpenQuotientBarToUniversalRelationTwo h U') := by
  let b₀ := finiteModTwoBarMapTwo (openNormalQuotientProj hUU') b
  let A := sqUniversalRelationModuleTransition h hUU'
    (sqOpenQuotientBarToUniversalRelationTwo h U b)
  let C := sqUniversalBarInputRelationCellCorrectionTwo h hUU' b +
    sqUniversalBarInputCorrectedKernelDefect h hUU' b
  have hdecomp : A = sqOpenQuotientBarToUniversalRelationTwo h U' b₀ + C := by
    simpa only [A, b₀, C, add_assoc] using
      sqUniversalBarInput_eq_target_add_relationCell_add_kernelDefect h hUU' b
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨b₀ + a, ?_⟩
    change sqOpenQuotientBarToUniversalRelationTwo h U' (b₀ + a) = A
    rw [map_add, ha]
    exact hdecomp.symm
  · rintro ⟨a, ha⟩
    refine ⟨a + b₀, ?_⟩
    change sqOpenQuotientBarToUniversalRelationTwo h U' (a + b₀) = C
    rw [map_add, ha]
    change A + sqOpenQuotientBarToUniversalRelationTwo h U' b₀ = C
    rw [hdecomp]
    rw [add_assoc, add_comm C, ← add_assoc, ZModModule.add_self, zero_add]

/-- Cokernel form of the same finite affine obstruction. -/
theorem sqUniversalBarInputCorrectedStrictifiableAt_iff_obstruction_eq_zero
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U')
    (b : FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)) :
    SqUniversalBarInputCorrectedStrictifiableAt h hUU' b ↔
      sqUniversalBarInputTransitionCokernelObstruction h hUU' b = 0 := by
  rw [sqUniversalBarInputCorrectedStrictifiableAt_iff_mem_range]
  change _ ∈ LinearMap.range (sqOpenQuotientBarToUniversalRelationTwo h U') ↔
    (LinearMap.range (sqOpenQuotientBarToUniversalRelationTwo h U')).mkQ _ = 0
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  rfl

/-- The corrected affine obstruction is literally the old cokernel class: the new relation
cell exposes why transport fails, but the joint one-relator variables occur too late to erase
the need for raw bar-range strictification. -/
theorem sqCorrectedStrictificationObstruction_eq_literalObstruction
    (h : ℕ) {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U')
    (b : FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)) :
    (LinearMap.range (sqOpenQuotientBarToUniversalRelationTwo h U')).mkQ
        (sqUniversalBarInputRelationCellCorrectionTwo h hUU' b +
          sqUniversalBarInputCorrectedKernelDefect h hUU' b) =
      sqUniversalBarInputTransitionCokernelObstruction h hUU' b := by
  have hdecomp :=
    sqUniversalBarInput_eq_target_add_relationCell_add_kernelDefect h hUU' b
  let R := sqOpenQuotientBarToUniversalRelationTwo h U'
  let A := sqUniversalRelationModuleTransition h hUU'
    (sqOpenQuotientBarToUniversalRelationTwo h U b)
  let C := sqUniversalBarInputRelationCellCorrectionTwo h hUU' b +
    sqUniversalBarInputCorrectedKernelDefect h hUU' b
  change (LinearMap.range R).mkQ C = (LinearMap.range R).mkQ A
  have hdecomp' : A = R (finiteModTwoBarMapTwo
      (openNormalQuotientProj hUU') b) + C := by
    simpa only [A, R, C, add_assoc] using hdecomp
  have hzero : (LinearMap.range R).mkQ
      (R (finiteModTwoBarMapTwo (openNormalQuotientProj hUU') b)) = 0 := by
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact LinearMap.mem_range_self R _
  calc
    (LinearMap.range R).mkQ C =
        0 + (LinearMap.range R).mkQ C := by rw [zero_add]
    _ = (LinearMap.range R).mkQ
          (R (finiteModTwoBarMapTwo (openNormalQuotientProj hUU') b)) +
        (LinearMap.range R).mkQ C := by rw [hzero]
    _ = (LinearMap.range R).mkQ
          (R (finiteModTwoBarMapTwo (openNormalQuotientProj hUU') b) + C) := by
      exact ((LinearMap.range R).mkQ.map_add
        (R (finiteModTwoBarMapTwo (openNormalQuotientProj hUU') b)) C).symm
    _ = (LinearMap.range R).mkQ A := congrArg _ hdecomp'.symm

/-! ## Interface with the joint one-relator capstone -/

/-- The joint one-relator lift cannot be chosen until a corrected family has first been
strictified to the literal compatible universal syzygy expected by the capstone.  This adapter
makes that dependency explicit: the lift and its generator table are indexed by `T.raw`, not by
the merely Fox-equivalent corrected family. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_correctedStrictifications
    (h : ℕ)
    (H : SqCompletedMonomialPBWKernelIdentityAll h)
    (C : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqCorrectedCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (T : ∀ V : OpenNormalSubgroup (DSq h : Type),
      (C V).RawStrictification)
    (L : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqCompatibleUniversalBarRelationLiftAt (T V).raw.universalSyzygy)
    (hgenerators : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteInputRelationReconstructionGeneratorSystemAt
        (T V).raw.degreeThreeComparison (L V)) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) :=
  GQ2.ContCoh.finiteElementaryH2RightExactSupply_DSq_of_compatibleLiftReconstructionGenerators
    h H (fun V ↦ (T V).raw) L hgenerators

/-- Preferred corrected-fiber endpoint.  Once the corrected family is strictly represented,
the one-relator lift may still be chosen jointly with its reconstruction table; it need not be
fixed before strictification. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_correctedJointLiftSystems
    (h : ℕ)
    (H : SqCompletedMonomialPBWKernelIdentityAll h)
    (C : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqCorrectedCompatibleUniversalCocycleCancellingSyzygyAt h V)
    (T : ∀ V : OpenNormalSubgroup (DSq h : Type),
      (C V).RawStrictification)
    (hjoint : ∀ V : OpenNormalSubgroup (DSq h : Type),
      SqFiniteInputRelationReconstructionJointLiftSystemAt
        (T V).raw.degreeThreeComparison
        (T V).raw.universalSyzygy.relationLiftOfSqPresentation) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) :=
  GQ2.ContCoh.finiteElementaryH2RightExactSupply_DSq_of_jointReconstructionLiftSystems
    h H (fun V ↦ (T V).raw) hjoint

/-! ## Terminal regression -/

/-- Corrected finite transition data and its Fox-kernel defect exist everywhere, including the
terminal direction, although universal strictifiability would recover the refuted literal
range condition. -/
theorem sqCorrectedCocycleFiber_strictification_regression (h : ℕ) :
    (∀ {U U' : OpenNormalSubgroup (DSq h : Type)} (hUU' : U ≤ U')
      (b : FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ U.toSubgroup)),
      sqUniversalBarInputCorrectedKernelDefect h hUU' b ∈
        LinearMap.ker ((finiteUniversalRelationFoxBoundary
          (sqOpenQuotientMarking h U')).map)) ∧
      ¬ SqUniversalBarInputTransitionEventuallyRange h :=
  ⟨fun hUU' b ↦ sqUniversalBarInputCorrectedKernelDefect_mem_ker h hUU' b,
    not_sqUniversalBarInputTransitionEventuallyRange h⟩

#print axioms sqUniversalBarInputCorrectedKernelDefect_mem_ker
#print axioms sqUniversalBarInputCorrectedStrictifiableAt_iff_obstruction_eq_zero
#print axioms finiteElementaryH2RightExactSupply_DSq_of_correctedStrictifications
#print axioms finiteElementaryH2RightExactSupply_DSq_of_correctedJointLiftSystems
#print axioms sqCorrectedCocycleFiber_strictification_regression

end

end GQ2.Dyadic.Count
