/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3SqTateDualityCapstone
import GQ2.Dyadic.Count.H2MaxProTwoRightExactTransport
import GQ2.Dyadic.Instances.GammaLH2RightExact
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStage

/-!
# Field-presentation boundary for square-core H² right exactness

An improved presentation identifies `DSq h` with the maximal pro-two quotient of a local
Galois group, not with the local Galois group itself.  Local Tate duality gives finite-elementary
H² right exactness on `GalK K`; this file isolates the additional comparison needed to descend
that result to `maxProPQuotient 2 (GalK K)` and then transports it across the presentation.

The sharp missing comparison is surjectivity of H² inflation on each source coefficient and
injectivity on each target coefficient, uniformly over finite elementary compatible modules.
Bijectivity is exposed as a convenient one-premise package.  No H³ object or new axiom is
introduced.
-/

set_option autoImplicit false

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.ContCoh
open GQ2.Dyadic GQ2.Dyadic.SqCore

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable local instance absGalQ2_compactSpace_fieldPresentation :
    CompactSpace AbsGalQ2 := by
  change CompactSpace (AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2])
  infer_instance

noncomputable local instance absGalQ2_totallyDisconnectedSpace_fieldPresentation :
    TotallyDisconnectedSpace AbsGalQ2 := by
  change TotallyDisconnectedSpace (AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2])
  infer_instance

/- `GalK K` is an open, hence closed, subgroup of the compact absolute Galois group.  The
general instance is developed in `KSupply`; keeping this proof local avoids importing that
downstream supply package merely to form the maximal pro-two quotient. -/
local instance compactSpace_galK_fieldPresentation
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K] :
    CompactSpace (GalK K) :=
  isCompact_iff_compactSpace.mp
    (Subgroup.isClosed_of_isOpen _ (isOpen_fixingSubgroup K)).isCompact

local instance totallyDisconnectedSpace_galK_fieldPresentation
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K] :
    TotallyDisconnectedSpace (GalK K) := inferInstance

/-! ## The exact local-field comparison boundary -/

/-- The finite-elementary H² tail on the maximal pro-two local Galois group.  This is the
field-side statement that an equivalence with `DSq h` can honestly transport. -/
abbrev GalKMaxProTwoH2RightExactSupply
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K] : Prop :=
  FiniteElementaryH2RightExactSupply (maxProPQuotient 2 (GalK K))

/-- The source-coefficient half of the uniform H² comparison needed to descend B6. -/
abbrev GalKMaxProTwoFiniteElementaryH2InflationSurjective
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K] : Prop :=
  FiniteElementaryH2InflationSurjective (maxProPMk 2 (GalK K))

/-- The target-coefficient half of the uniform H² comparison needed to descend B6. -/
abbrev GalKMaxProTwoFiniteElementaryH2InflationInjective
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K] : Prop :=
  FiniteElementaryH2InflationInjective (maxProPMk 2 (GalK K))

/-- A convenient uniform H² inflation-bijectivity package for the maximal pro-two quotient. -/
abbrev GalKMaxProTwoFiniteElementaryH2InflationBijective
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K] : Prop :=
  FiniteElementaryH2InflationBijective (maxProPMk 2 (GalK K))

/-- B6 on the local Galois group, source-coefficient surjectivity, and target-coefficient
injectivity of H² inflation supply right exactness on its maximal pro-two quotient. -/
theorem galKMaxProTwoH2RightExactSupply_of_B6_and_inflation_surjective_injective
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (hsurj : GalKMaxProTwoFiniteElementaryH2InflationSurjective K)
    (hinj : GalKMaxProTwoFiniteElementaryH2InflationInjective K) :
    GalKMaxProTwoH2RightExactSupply K :=
  finiteElementaryH2RightExactSupply_of_inflation_surjective_injective
    (maxProPMk 2 (GalK K)) (galKH2RightExactSupply_of_B6 K) hsurj hinj

/-- Bijective finite-elementary H² inflation is the clean uniform package of the two exact
directions needed by the preceding theorem. -/
theorem galKMaxProTwoH2RightExactSupply_of_B6_and_inflation_bijective
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (hinf : GalKMaxProTwoFiniteElementaryH2InflationBijective K) :
    GalKMaxProTwoH2RightExactSupply K :=
  galKMaxProTwoH2RightExactSupply_of_B6_and_inflation_surjective_injective
    K hinf.surjective hinf.injective

/-! ## Transport across the improved presentation -/

/-- A topological presentation equivalence transports the exact field-side H² tail to the
improved square core. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_equiv_maxProTwoGalK
    {h : ℕ} (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (e : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (hK : GalKMaxProTwoH2RightExactSupply K) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) :=
  finiteTwoH2RightExactSupply_congr e hK

/-- Oriented spelling matching the output of the variable-rank field-presentation campaign. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_orientedFieldPresentation
    {h : ℕ} (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (e : OrientedContinuousMulEquiv (chiSq h) (chiCycKTwo (K := K)))
    (hK : GalKMaxProTwoH2RightExactSupply K) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) :=
  finiteElementaryH2RightExactSupply_DSq_of_equiv_maxProTwoGalK K e.1 hK

/-- Sharp oriented reduction: the field presentation, source-surjective H² inflation, and
target-injective H² inflation turn B6 into square-core right exactness. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_orientedFieldPresentation_B6_of_inflation_surjective_injective
    {h : ℕ} (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (e : OrientedContinuousMulEquiv (chiSq h) (chiCycKTwo (K := K)))
    (hsurj : GalKMaxProTwoFiniteElementaryH2InflationSurjective K)
    (hinj : GalKMaxProTwoFiniteElementaryH2InflationInjective K) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) :=
  finiteElementaryH2RightExactSupply_DSq_of_orientedFieldPresentation K e
    (galKMaxProTwoH2RightExactSupply_of_B6_and_inflation_surjective_injective K hsurj hinj)

/-- Convenient packaged reduction: an oriented field presentation and uniform bijectivity of
finite-elementary H² inflation turn B6 into square-core right exactness. -/
theorem finiteElementaryH2RightExactSupply_DSq_of_orientedFieldPresentation_B6
    {h : ℕ} (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (e : OrientedContinuousMulEquiv (chiSq h) (chiCycKTwo (K := K)))
    (hinf : GalKMaxProTwoFiniteElementaryH2InflationBijective K) :
    FiniteElementaryH2RightExactSupply (DSq h : Type) :=
  finiteElementaryH2RightExactSupply_DSq_of_orientedFieldPresentation_B6_of_inflation_surjective_injective
    K e hinf.surjective hinf.injective

/-- Sharp application to the existing GammaL capstone.  Beyond B6, it exposes both directional
finite-elementary inflation hypotheses and the independently isolated Sylow-kernel residual
package. -/
noncomputable def tateDualityG_of_orientedFieldPresentation_B6_of_inflation_surjective_injective
    {h q : ℕ} (hq2 : 2 ≤ q) (hqe : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (e : OrientedContinuousMulEquiv (chiSq h) (chiCycKTwo (K := K)))
    (hsurj : GalKMaxProTwoFiniteElementaryH2InflationSurjective K)
    (hinj : GalKMaxProTwoFiniteElementaryH2InflationInjective K)
    (R : GammaLSylowPreimageKernelH2AndCoreEqualitySupply h q) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_sqCoreAndSylowKernelResiduals hq2 hqe R
    (finiteElementaryH2RightExactSupply_DSq_of_orientedFieldPresentation_B6_of_inflation_surjective_injective
      K e hsurj hinj)

/-- Packaged-bijectivity application to the existing GammaL capstone. -/
noncomputable def tateDualityG_of_orientedFieldPresentation_B6
    {h q : ℕ} (hq2 : 2 ≤ q) (hqe : Even q)
    [DistribMulAction (gamma h q : Type) (MuN 2)]
    [ContinuousSMul (gamma h q : Type) (MuN 2)]
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (e : OrientedContinuousMulEquiv (chiSq h) (chiCycKTwo (K := K)))
    (hinf : GalKMaxProTwoFiniteElementaryH2InflationBijective K)
    (R : GammaLSylowPreimageKernelH2AndCoreEqualitySupply h q) :
    TateDualityG (gamma h q : Type) 2 :=
  tateDualityG_of_orientedFieldPresentation_B6_of_inflation_surjective_injective
    hq2 hqe K e hinf.surjective hinf.injective R

#print axioms galKMaxProTwoH2RightExactSupply_of_B6_and_inflation_surjective_injective
#print axioms finiteElementaryH2RightExactSupply_DSq_of_orientedFieldPresentation_B6_of_inflation_surjective_injective
#print axioms tateDualityG_of_orientedFieldPresentation_B6_of_inflation_surjective_injective

end

end GQ2.Dyadic.LSquare
