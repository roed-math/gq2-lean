/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.DemushkinEpimorphismRigidity
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteDegreeThree
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteHilbertTail
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteSharpInflationKernelBoundary

/-!
# Field-facing rigidity for the improved square presentation

This module bypasses every higher lower-two-central cardinal comparison.  A forward map from
the literal improved square presentation is already an epimorphism.  The source and target are
positive equal-rank Demushkin pro-two groups, so the generic low-degree rigidity theorem reduces
injectivity without any further field-facing hypothesis.  The invariant kernel character and
the continuous five-term detection argument are constructed automatically.

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
target is Demushkin of the literal improved rank.  No kernel-boundary, lower-series, or Jennings
hypothesis occurs. -/
theorem SqCyclotomicForwardGeneratorData.forward_bijective
    (D : SqCyclotomicForwardGeneratorData h chiG)
    (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = SqCore.sqRank h) :
    Function.Bijective (D.forward hD.isProP) := by
  apply demushkinEpimorphism_bijective
    (D.forward hD.isProP) (D.forward_surjective hD.isProP)
    (isDemushkin_DSq h) hD
  · rw [demushkinRank_DSq, hrank]
  · rw [demushkinRank_DSq]
    simp only [SqCore.sqRank]
    omega

/-- The bijective forward map, bundled as a topological group equivalence. -/
noncomputable def SqCyclotomicForwardGeneratorData.forwardContinuousMulEquiv
    (D : SqCyclotomicForwardGeneratorData h chiG)
    (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = SqCore.sqRank h) :
    ContinuousMulEquiv (SqCore.DSq h : Type) G :=
  continuousMulEquivOfBijective (D.forward hD.isProP)
    (D.forward_bijective hD hrank)

/-- The bundled equivalence has exactly the original forward homomorphism as its forward map. -/
@[simp] theorem SqCyclotomicForwardGeneratorData.forwardContinuousMulEquiv_apply
    (D : SqCyclotomicForwardGeneratorData h chiG)
    (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = SqCore.sqRank h)
    (x : SqCore.DSq h) :
    D.forwardContinuousMulEquiv hD hrank x = D.forward hD.isProP x :=
  rfl

/-- Oriented form of the rigidity bypass.  The proof reuses the five rows stored in `D`, so
the improved constructor table is not reconstructed or weakened. -/
noncomputable def SqCyclotomicForwardGeneratorData.orientedEquiv
    (D : SqCyclotomicForwardGeneratorData h chiG)
    (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = SqCore.sqRank h) :
    OrientedContinuousMulEquiv (SqCore.chiSq h) chiG := by
  let e := D.forwardContinuousMulEquiv hD hrank
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

/-! The former one- and two-input boundary APIs remain available for downstream compatibility.
Their boundary arguments are no longer used. -/

@[deprecated SqCyclotomicForwardGeneratorData.forward_bijective (since := "2026-08-04")]
theorem SqCyclotomicForwardGeneratorData.forward_bijective_of_fiveTermKernelDetection
    (D : SqCyclotomicForwardGeneratorData h chiG)
    (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = SqCore.sqRank h)
    (_hdetect : H1H2InflationDetectsInvariantKernelCharacters (D.forward hD.isProP)) :
    Function.Bijective (D.forward hD.isProP) :=
  D.forward_bijective hD hrank

@[deprecated SqCyclotomicForwardGeneratorData.forwardContinuousMulEquiv
    (since := "2026-08-04")]
noncomputable def SqCyclotomicForwardGeneratorData.forwardContinuousMulEquiv_of_fiveTermKernelDetection
    (D : SqCyclotomicForwardGeneratorData h chiG)
    (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = SqCore.sqRank h)
    (_hdetect : H1H2InflationDetectsInvariantKernelCharacters (D.forward hD.isProP)) :
    ContinuousMulEquiv (SqCore.DSq h : Type) G :=
  D.forwardContinuousMulEquiv hD hrank

@[deprecated SqCyclotomicForwardGeneratorData.forwardContinuousMulEquiv_apply
    (since := "2026-08-04")]
theorem SqCyclotomicForwardGeneratorData.forwardContinuousMulEquiv_of_fiveTermKernelDetection_apply
    (D : SqCyclotomicForwardGeneratorData h chiG)
    (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = SqCore.sqRank h)
    (hdetect : H1H2InflationDetectsInvariantKernelCharacters (D.forward hD.isProP))
    (x : SqCore.DSq h) :
    D.forwardContinuousMulEquiv_of_fiveTermKernelDetection
        hD hrank hdetect x = D.forward hD.isProP x :=
  rfl

@[deprecated SqCyclotomicForwardGeneratorData.orientedEquiv (since := "2026-08-04")]
noncomputable def SqCyclotomicForwardGeneratorData.orientedEquiv_of_fiveTermKernelDetection
    (D : SqCyclotomicForwardGeneratorData h chiG)
    (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = SqCore.sqRank h)
    (_hdetect : H1H2InflationDetectsInvariantKernelCharacters (D.forward hD.isProP)) :
    OrientedContinuousMulEquiv (SqCore.chiSq h) chiG :=
  D.orientedEquiv hD hrank

@[deprecated SqCyclotomicForwardGeneratorData.forward_bijective
    (since := "2026-08-04")]
theorem SqCyclotomicForwardGeneratorData.forward_bijective_of_kernelCharacterBoundary
    (D : SqCyclotomicForwardGeneratorData h chiG)
    (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = SqCore.sqRank h)
    (_hdetect : H1H2InflationDetectsInvariantKernelCharacters (D.forward hD.isProP))
    (_hsupply : InvariantKernelCharacterSupply (D.forward hD.isProP)) :
    Function.Bijective (D.forward hD.isProP) :=
  D.forward_bijective hD hrank

@[deprecated SqCyclotomicForwardGeneratorData.forwardContinuousMulEquiv
    (since := "2026-08-04")]
noncomputable def SqCyclotomicForwardGeneratorData.forwardContinuousMulEquiv_of_kernelCharacterBoundary
    (D : SqCyclotomicForwardGeneratorData h chiG)
    (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = SqCore.sqRank h)
    (_hdetect : H1H2InflationDetectsInvariantKernelCharacters (D.forward hD.isProP))
    (_hsupply : InvariantKernelCharacterSupply (D.forward hD.isProP)) :
    ContinuousMulEquiv (SqCore.DSq h : Type) G :=
  D.forwardContinuousMulEquiv hD hrank

@[deprecated SqCyclotomicForwardGeneratorData.forwardContinuousMulEquiv_apply
    (since := "2026-08-04")]
theorem SqCyclotomicForwardGeneratorData.forwardContinuousMulEquiv_of_kernelCharacterBoundary_apply
    (D : SqCyclotomicForwardGeneratorData h chiG)
    (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = SqCore.sqRank h)
    (hdetect : H1H2InflationDetectsInvariantKernelCharacters (D.forward hD.isProP))
    (hsupply : InvariantKernelCharacterSupply (D.forward hD.isProP))
    (x : SqCore.DSq h) :
    D.forwardContinuousMulEquiv_of_kernelCharacterBoundary
        hD hrank hdetect hsupply x = D.forward hD.isProP x :=
  rfl

@[deprecated SqCyclotomicForwardGeneratorData.orientedEquiv
    (since := "2026-08-04")]
noncomputable def SqCyclotomicForwardGeneratorData.orientedEquiv_of_kernelCharacterBoundary
    (D : SqCyclotomicForwardGeneratorData h chiG)
    (hD : IsDemushkin 2 G)
    (hrank : demushkinRank 2 G = SqCore.sqRank h)
    (_hdetect : H1H2InflationDetectsInvariantKernelCharacters (D.forward hD.isProP))
    (_hsupply : InvariantKernelCharacterSupply (D.forward hD.isProP)) :
    OrientedContinuousMulEquiv (SqCore.chiSq h) chiG :=
  D.orientedEquiv hD hrank

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

/-- Unconditional odd-degree field specialization of forward-map bijectivity. -/
theorem SqCyclotomicForwardGeneratorData.forward_bijective_oddDegree
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (D : SqCyclotomicForwardGeneratorData
      ((Module.finrank ℚ_[2] K - 1) / 2) (chiCycKTwo (K := K))) :
    Function.Bijective (D.forward isProP_maxProPQuotient) := by
  exact D.forward_bijective
    (isDemushkin_maxProTwoGalK (K := K))
    (demushkinRank_maxProTwoGalK_eq_sqRank_half_pred (K := K) hodd)

/-- The corresponding odd-degree field equivalence, with forward map equal to `D.forward`. -/
noncomputable def SqCyclotomicForwardGeneratorData.forwardContinuousMulEquiv_oddDegree
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (D : SqCyclotomicForwardGeneratorData
      ((Module.finrank ℚ_[2] K - 1) / 2) (chiCycKTwo (K := K))) :
    ContinuousMulEquiv
      (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type)
      (maxProPQuotient 2 (GalK K)) :=
  D.forwardContinuousMulEquiv
    (isDemushkin_maxProTwoGalK (K := K))
    (demushkinRank_maxProTwoGalK_eq_sqRank_half_pred (K := K) hodd)

/-- The odd-degree field equivalence with the improved square orientation attached. -/
noncomputable def SqCyclotomicForwardGeneratorData.orientedEquiv_oddDegree
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (D : SqCyclotomicForwardGeneratorData
      ((Module.finrank ℚ_[2] K - 1) / 2) (chiCycKTwo (K := K))) :
    OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (chiCycKTwo (K := K)) :=
  D.orientedEquiv
    (isDemushkin_maxProTwoGalK (K := K))
    (demushkinRank_maxProTwoGalK_eq_sqRank_half_pred (K := K) hodd)

omit [T2Space (GalK K)] in
/-- A finite-level assembly may hand rigidity merely a nonempty forward-generator package.
The resulting oriented equivalence uses that package's original forward map and hence preserves
the three core constructor rows and both handle rows. -/
theorem nonempty_orientedEquiv_oddDegree_of_forwardGeneratorData
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (hdata : Nonempty (SqCyclotomicForwardGeneratorData
      ((Module.finrank ℚ_[2] K - 1) / 2) (chiCycKTwo (K := K)))) :
    Nonempty (OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (chiCycKTwo (K := K))) :=
  hdata.map fun D => D.orientedEquiv_oddDegree hodd

/-! ## Forward stage capstones

These capstones compose the corrected stage induction with finite-level König assembly and
Demushkin rigidity.  In particular, no reverse finite-quotient map, lower-series cardinality
comparison, Jennings formula, or Hilbert-tail premise remains in their signatures. -/

/-- The most direct corrected-forward capstone.  One exact level-three stage and actual-defect
reachability at every subsequent stage produce the odd-degree oriented presentation. -/
theorem nonempty_orientedEquiv_oddDegree_of_stageBase_and_corrections
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (base : SqCyclotomicStageTuple K
      ((Module.finrank ℚ_[2] K - 1) / 2) 3)
    (Hcorr : ∀ (k : ℕ), 3 ≤ k →
      ∀ T : SqCyclotomicStageTuple K
        ((Module.finrank ℚ_[2] K - 1) / 2) k,
        SqCyclotomicStageTuple.DefectReachable T) :
    Nonempty (OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (chiCycKTwo (K := K))) := by
  apply nonempty_orientedEquiv_oddDegree_of_forwardGeneratorData hodd
  apply forwardGeneratorData_of_finiteLevel _
  intro U
  exact SqCyclotomicStageTuple.finiteLevelEpiData_nonempty_of_base_and_corrections
    _ base (maxProTwoGalK_isTopologicallyFinGen K) Hcorr U

/-- The concrete actual-defect interface is enough for the direct capstone.  Sharp exact fibre
lifting is supplied by odd-degree marked reciprocity, so it is not an additional open premise.

The bundle `B` is the caller's own: `oddDegreeGalKSq_sharpExactLevelFibreLiftSupply` is generic
in it, so the axiom `markedRecipAt` (B5-K) is never summoned here. -/
theorem nonempty_orientedEquiv_oddDegree_of_stageBase_and_actualDefectSupply
    {Rec : LocalReciprocity} (B : MarkedRecip Rec K)
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (base : SqCyclotomicStageTuple K
      ((Module.finrank ℚ_[2] K - 1) / 2) 3)
    (Hactual : ∀ (k : ℕ) (hk : 3 ≤ k)
      (T : SqCyclotomicStageTuple K
        ((Module.finrank ℚ_[2] K - 1) / 2) k),
      Nonempty (SqCyclotomicStageTuple.CoreHandleSharpActualDefectSupply T hk)) :
    Nonempty (OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (chiCycKTwo (K := K))) := by
  apply nonempty_orientedEquiv_oddDegree_of_stageBase_and_corrections hodd base
  intro k hk T
  obtain ⟨S⟩ := Hactual k hk T
  exact S.toDefectReachable
    (SqCyclotomicStageTuple.oddDegreeGalKSq_sharpExactLevelFibreLiftSupply B hodd)

/-- Chain-level form of the remaining arithmetic boundary.  It suffices, at every stage, to
choose one sharp-admissible affine base whose residual is annihilated by normalized primitives
of the relevant inflation-kernel cocycles.  Transgression duality converts this statement to
literal bracket-span membership and hence to the actual-defect correction used above. -/
theorem nonempty_orientedEquiv_oddDegree_of_stageBase_and_primitiveResidualVanishing
    {Rec : LocalReciprocity} (B : MarkedRecip Rec K)
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (base : SqCyclotomicStageTuple K
      ((Module.finrank ℚ_[2] K - 1) / 2) 3)
    (Hprimitive : ∀ (k : ℕ) (hk : 3 ≤ k)
      (T : SqCyclotomicStageTuple K
        ((Module.finrank ℚ_[2] K - 1) / 2) k),
      ∃ W : SqCyclotomicStageTuple.SharpAdmissibleCorrection T (by omega),
        SqCyclotomicStageTuple.SharpCyclotomicInflationPrimitiveResidualVanishing
          T hk W (maxProTwoGalK_isTopologicallyFinGen K)) :
    Nonempty (OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (chiCycKTwo (K := K))) := by
  apply nonempty_orientedEquiv_oddDegree_of_stageBase_and_actualDefectSupply B hodd base
  intro k hk T
  obtain ⟨W, hprimitive⟩ := Hprimitive k hk T
  have hcompat :=
    SqCyclotomicStageTuple.sharpCyclotomicInflationKernelResidualCompatibility_of_primitiveVanishing
      W (maxProTwoGalK_isTopologicallyFinGen K) hprimitive
  have hmem :=
    (SqCyclotomicStageTuple.sharpCyclotomicInflationKernelResidualCompatibility_iff_mem_bracketSpan
      W (maxProTwoGalK_isTopologicallyFinGen K)).mp hcompat
  exact
    (SqCyclotomicStageTuple.nonempty_coreHandleSharpActualDefectSupply_iff_mem_bracketSpan
      W).mpr hmem

/-! Deprecated odd-degree adapters for the former boundary arguments. -/

@[deprecated SqCyclotomicForwardGeneratorData.forward_bijective_oddDegree
    (since := "2026-08-04")]
theorem SqCyclotomicForwardGeneratorData.forward_bijective_oddDegree_of_fiveTermKernelDetection
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (D : SqCyclotomicForwardGeneratorData
      ((Module.finrank ℚ_[2] K - 1) / 2) (chiCycKTwo (K := K)))
    (_hdetect : H1H2InflationDetectsInvariantKernelCharacters
      (D.forward isProP_maxProPQuotient)) :
    Function.Bijective (D.forward isProP_maxProPQuotient) :=
  D.forward_bijective_oddDegree hodd

@[deprecated SqCyclotomicForwardGeneratorData.forwardContinuousMulEquiv_oddDegree
    (since := "2026-08-04")]
noncomputable def SqCyclotomicForwardGeneratorData.forwardContinuousMulEquiv_oddDegree_of_fiveTermKernelDetection
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (D : SqCyclotomicForwardGeneratorData
      ((Module.finrank ℚ_[2] K - 1) / 2) (chiCycKTwo (K := K)))
    (_hdetect : H1H2InflationDetectsInvariantKernelCharacters
      (D.forward isProP_maxProPQuotient)) :
    ContinuousMulEquiv
      (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type)
      (maxProPQuotient 2 (GalK K)) :=
  D.forwardContinuousMulEquiv_oddDegree hodd

@[deprecated SqCyclotomicForwardGeneratorData.orientedEquiv_oddDegree
    (since := "2026-08-04")]
noncomputable def SqCyclotomicForwardGeneratorData.orientedEquiv_oddDegree_of_fiveTermKernelDetection
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (D : SqCyclotomicForwardGeneratorData
      ((Module.finrank ℚ_[2] K - 1) / 2) (chiCycKTwo (K := K)))
    (_hdetect : H1H2InflationDetectsInvariantKernelCharacters
      (D.forward isProP_maxProPQuotient)) :
    OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (chiCycKTwo (K := K)) :=
  D.orientedEquiv_oddDegree hodd

@[deprecated SqCyclotomicForwardGeneratorData.forward_bijective_oddDegree
    (since := "2026-08-04")]
theorem SqCyclotomicForwardGeneratorData.forward_bijective_oddDegree_of_kernelCharacterBoundary
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (D : SqCyclotomicForwardGeneratorData
      ((Module.finrank ℚ_[2] K - 1) / 2) (chiCycKTwo (K := K)))
    (_hdetect : H1H2InflationDetectsInvariantKernelCharacters
      (D.forward isProP_maxProPQuotient))
    (_hsupply : InvariantKernelCharacterSupply
      (D.forward isProP_maxProPQuotient)) :
    Function.Bijective (D.forward isProP_maxProPQuotient) :=
  D.forward_bijective_oddDegree hodd

@[deprecated
    SqCyclotomicForwardGeneratorData.forwardContinuousMulEquiv_oddDegree
    (since := "2026-08-04")]
noncomputable def SqCyclotomicForwardGeneratorData.forwardContinuousMulEquiv_oddDegree_of_kernelCharacterBoundary
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (D : SqCyclotomicForwardGeneratorData
      ((Module.finrank ℚ_[2] K - 1) / 2) (chiCycKTwo (K := K)))
    (_hdetect : H1H2InflationDetectsInvariantKernelCharacters
      (D.forward isProP_maxProPQuotient))
    (_hsupply : InvariantKernelCharacterSupply
      (D.forward isProP_maxProPQuotient)) :
    ContinuousMulEquiv
      (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type)
      (maxProPQuotient 2 (GalK K)) :=
  D.forwardContinuousMulEquiv_oddDegree hodd

@[deprecated SqCyclotomicForwardGeneratorData.orientedEquiv_oddDegree
    (since := "2026-08-04")]
noncomputable def SqCyclotomicForwardGeneratorData.orientedEquiv_oddDegree_of_kernelCharacterBoundary
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (D : SqCyclotomicForwardGeneratorData
      ((Module.finrank ℚ_[2] K - 1) / 2) (chiCycKTwo (K := K)))
    (_hdetect : H1H2InflationDetectsInvariantKernelCharacters
      (D.forward isProP_maxProPQuotient))
    (_hsupply : InvariantKernelCharacterSupply
      (D.forward isProP_maxProPQuotient)) :
    OrientedContinuousMulEquiv
      (SqCore.chiSq ((Module.finrank ℚ_[2] K - 1) / 2))
      (chiCycKTwo (K := K)) :=
  D.orientedEquiv_oddDegree hodd

#print axioms SqCyclotomicForwardGeneratorData.forward_bijective
#print axioms SqCyclotomicForwardGeneratorData.orientedEquiv
#print axioms demushkinRank_maxProTwoGalK_eq_sqRank_half_pred
#print axioms SqCyclotomicForwardGeneratorData.forward_bijective_oddDegree
#print axioms SqCyclotomicForwardGeneratorData.orientedEquiv_oddDegree
#print axioms nonempty_orientedEquiv_oddDegree_of_forwardGeneratorData
#print axioms nonempty_orientedEquiv_oddDegree_of_stageBase_and_corrections
#print axioms nonempty_orientedEquiv_oddDegree_of_stageBase_and_actualDefectSupply
#print axioms nonempty_orientedEquiv_oddDegree_of_stageBase_and_primitiveResidualVanishing

end OddDegreeField

end

end GQ2.Dyadic.LSquare
