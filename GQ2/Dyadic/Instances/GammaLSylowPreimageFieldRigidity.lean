/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.DemushkinEpimorphismRigidity
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteDegreeThree

/-!
# Field-facing rigidity for the improved square presentation

This module bypasses every higher lower-two-central cardinal comparison.  A forward map from
the literal improved square presentation is already an epimorphism.  The source and target are
positive equal-rank Demushkin pro-two groups, so the generic low-degree rigidity theorem reduces
injectivity to exactly two inputs:

* `H1H2InflationDetectsInvariantKernelCharacters`;
* `InvariantKernelCharacterSupply`.

The resulting equivalence is built from the original forward map.  Consequently the improved
constructor table and all five cyclotomic orientation rows are preserved definitionally.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.ContCoh

section GeneralTarget

variable {h : ℕ} {G : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {chiG : ContinuousMonoidHom G ℤ_[2]ˣ}

local instance rigidityScalarActionG : DistribMulAction G (ZMod 2) :=
  scalarActionZmodTwo G
local instance rigidityContinuousScalarG : ContinuousSMul G (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul G

/-- The generic field-facing bypass.  The forward presentation map is bijective once the
target is Demushkin of the literal improved rank and the two invariant-kernel-character
boundary inputs are supplied.  No lower-series or Jennings hypothesis occurs. -/
theorem SqCyclotomicForwardGeneratorData.forward_bijective_of_kernelCharacterBoundary
    (D : SqCyclotomicForwardGeneratorData h chiG)
    (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = SqCore.sqRank h)
    (hdetect : H1H2InflationDetectsInvariantKernelCharacters (D.forward hD.isProP))
    (hsupply : InvariantKernelCharacterSupply (D.forward hD.isProP)) :
    Function.Bijective (D.forward hD.isProP) := by
  apply demushkinEpimorphism_bijective_of_kernelCharacterBoundary
    (D.forward hD.isProP) (D.forward_surjective hD.isProP)
    (isDemushkin_DSq h) hD
  · rw [demushkinRank_DSq, hrank]
  · rw [demushkinRank_DSq]
    simp only [SqCore.sqRank]
    omega
  · exact hdetect
  · exact hsupply

/-- The bijective forward map, bundled as a topological group equivalence. -/
noncomputable def SqCyclotomicForwardGeneratorData.forwardContinuousMulEquiv_of_kernelCharacterBoundary
    (D : SqCyclotomicForwardGeneratorData h chiG)
    (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = SqCore.sqRank h)
    (hdetect : H1H2InflationDetectsInvariantKernelCharacters (D.forward hD.isProP))
    (hsupply : InvariantKernelCharacterSupply (D.forward hD.isProP)) :
    ContinuousMulEquiv (SqCore.DSq h : Type) G :=
  continuousMulEquivOfBijective (D.forward hD.isProP)
    (D.forward_bijective_of_kernelCharacterBoundary hD hrank hdetect hsupply)

/-- The bundled equivalence has exactly the original forward homomorphism as its forward map. -/
@[simp] theorem SqCyclotomicForwardGeneratorData.forwardContinuousMulEquiv_of_kernelCharacterBoundary_apply
    (D : SqCyclotomicForwardGeneratorData h chiG)
    (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = SqCore.sqRank h)
    (hdetect : H1H2InflationDetectsInvariantKernelCharacters (D.forward hD.isProP))
    (hsupply : InvariantKernelCharacterSupply (D.forward hD.isProP))
    (x : SqCore.DSq h) :
    D.forwardContinuousMulEquiv_of_kernelCharacterBoundary
        hD hrank hdetect hsupply x = D.forward hD.isProP x :=
  rfl

/-- Oriented form of the rigidity bypass.  The proof reuses the five rows stored in `D`, so
the improved constructor table is not reconstructed or weakened. -/
noncomputable def SqCyclotomicForwardGeneratorData.orientedEquiv_of_kernelCharacterBoundary
    (D : SqCyclotomicForwardGeneratorData h chiG)
    (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = SqCore.sqRank h)
    (hdetect : H1H2InflationDetectsInvariantKernelCharacters (D.forward hD.isProP))
    (hsupply : InvariantKernelCharacterSupply (D.forward hD.isProP)) :
    OrientedContinuousMulEquiv (SqCore.chiSq h) chiG := by
  let e := D.forwardContinuousMulEquiv_of_kernelCharacterBoundary
    hD hrank hdetect hsupply
  apply orientedEquivSq_of_values chiG e
  · change chiG (D.forward hD.isProP (SqCore.dsqSigma h)) = GQ2.Roe.SvalUnit
    rw [SqCore.dsqSigma, D.forward_gen]
    exact D.sigma
  · change chiG (D.forward hD.isProP (SqCore.dsqX0 h)) = GQ2.Roe.rootXUnit
    rw [SqCore.dsqX0, D.forward_gen]
    exact D.x0
  · change chiG (D.forward hD.isProP (SqCore.dsqX1 h)) = GQ2.Roe.YvalUnit
    rw [SqCore.dsqX1, D.forward_gen]
    exact D.x1
  · intro j
    change chiG (D.forward hD.isProP
      (SqCore.sqGen h (SqCore.sqHandleIdxU j))) = 1
    rw [D.forward_gen]
    exact D.handleU j
  · intro j
    change chiG (D.forward hD.isProP
      (SqCore.sqGen h (SqCore.sqHandleIdxV j))) = 1
    rw [D.forward_gen]
    exact D.handleV j

end GeneralTarget

/-! ## Odd-degree dyadic specialization -/

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

section OddDegreeField

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

local instance fieldRigidityScalarAction :
    DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _
local instance fieldRigidityContinuousScalar :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

omit [T2Space (GalK K)] in
/-- For an odd-degree dyadic field, the standard handle count has literal improved rank equal
to the Demushkin rank of its maximal pro-two Galois group. -/
theorem demushkinRank_maxProTwoGalK_eq_sqRank_half_pred
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    demushkinRank 2 (maxProPQuotient 2 (GalK K)) =
      SqCore.sqRank ((Module.finrank ℚ_[2] K - 1) / 2) := by
  rw [demushkinRank_maxProTwoGalK (K := K)]
  obtain ⟨m, hm⟩ := hodd
  rw [hm]
  simp only [SqCore.sqRank]
  omega

/-- Odd-degree field specialization of forward-map bijectivity.  Its only unproved inputs are
the two generic kernel-character boundary statements for this particular forward epimorphism. -/
theorem SqCyclotomicForwardGeneratorData.forward_bijective_oddDegree_of_kernelCharacterBoundary
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (D : SqCyclotomicForwardGeneratorData
      ((Module.finrank ℚ_[2] K - 1) / 2) (chiCycKTwo (K := K)))
    (hdetect : H1H2InflationDetectsInvariantKernelCharacters
      (D.forward isProP_maxProPQuotient))
    (hsupply : InvariantKernelCharacterSupply
      (D.forward isProP_maxProPQuotient)) :
    Function.Bijective (D.forward isProP_maxProPQuotient) := by
  exact D.forward_bijective_of_kernelCharacterBoundary
    (isDemushkin_maxProTwoGalK (K := K))
    (demushkinRank_maxProTwoGalK_eq_sqRank_half_pred (K := K) hodd)
    hdetect hsupply

/-- The corresponding odd-degree field equivalence, with forward map equal to `D.forward`. -/
noncomputable def SqCyclotomicForwardGeneratorData.forwardContinuousMulEquiv_oddDegree_of_kernelCharacterBoundary
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (D : SqCyclotomicForwardGeneratorData
      ((Module.finrank ℚ_[2] K - 1) / 2) (chiCycKTwo (K := K)))
    (hdetect : H1H2InflationDetectsInvariantKernelCharacters
      (D.forward isProP_maxProPQuotient))
    (hsupply : InvariantKernelCharacterSupply
      (D.forward isProP_maxProPQuotient)) :
    ContinuousMulEquiv
      (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type)
      (maxProPQuotient 2 (GalK K)) :=
  D.forwardContinuousMulEquiv_of_kernelCharacterBoundary
    (isDemushkin_maxProTwoGalK (K := K))
    (demushkinRank_maxProTwoGalK_eq_sqRank_half_pred (K := K) hodd)
    hdetect hsupply

/-- The odd-degree field equivalence with the improved square orientation attached. -/
noncomputable def SqCyclotomicForwardGeneratorData.orientedEquiv_oddDegree_of_kernelCharacterBoundary
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (D : SqCyclotomicForwardGeneratorData
      ((Module.finrank ℚ_[2] K - 1) / 2) (chiCycKTwo (K := K)))
    (hdetect : H1H2InflationDetectsInvariantKernelCharacters
      (D.forward isProP_maxProPQuotient))
    (hsupply : InvariantKernelCharacterSupply
      (D.forward isProP_maxProPQuotient)) :
    OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (chiCycKTwo (K := K)) :=
  D.orientedEquiv_of_kernelCharacterBoundary
    (isDemushkin_maxProTwoGalK (K := K))
    (demushkinRank_maxProTwoGalK_eq_sqRank_half_pred (K := K) hodd)
    hdetect hsupply

#print axioms SqCyclotomicForwardGeneratorData.forward_bijective_of_kernelCharacterBoundary
#print axioms SqCyclotomicForwardGeneratorData.orientedEquiv_of_kernelCharacterBoundary
#print axioms demushkinRank_maxProTwoGalK_eq_sqRank_half_pred
#print axioms SqCyclotomicForwardGeneratorData.forward_bijective_oddDegree_of_kernelCharacterBoundary
#print axioms SqCyclotomicForwardGeneratorData.orientedEquiv_oddDegree_of_kernelCharacterBoundary

end OddDegreeField

end

end GQ2.Dyadic.LSquare
