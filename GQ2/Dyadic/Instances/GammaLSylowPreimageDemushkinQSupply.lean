/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.DemushkinQRamifiedI
import GQ2.Dyadic.OddDegreeRamifiedI
import GQ2.Dyadic.ProTwoCompletionDecomposition
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldCore
import GQ2.Foundations.Axioms

/-!
# Supplying the odd-degree field `q = 2` input

This adapter connects the ramified-`i` torsion calculation to the field-model route for
variable GammaL Sylow cores.  Odd degree supplies ramification of `K(i)/K` internally, and
`ProTwoCompletionDecomposition` proves unconditionally that every torsion point in the pro-`2`
completion of `K×` comes from a field root.  Its single remaining premise is therefore exactly
injectivity of the canonical completed reciprocity map.

There is no separate reciprocity field in the package: `localReciprocity` and
`markedRecipAt K` are the repository's canonical APIs.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The only remaining field-specific input to the odd-degree `q = 2` calculation:
injectivity of the completed canonical reciprocity map
`(K×)^(2) → G_K(2)^ab`.

Ramification of `K(i)/K` and generation of source torsion by field roots are theorems, not
fields of this structure. -/
structure GalKCompletedReciprocityInjectivityData
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] where
  completedReciprocityInjective :
    Function.Injective (proTwoReciprocityToTopAb (markedRecipAt K))

/-- The uniform arithmetic supply sufficient for the odd-degree field theorem `q = 2`:
completed canonical reciprocity is injective for every odd-degree dyadic field. -/
def OddDegreeGalKCompletedReciprocityInjectivitySupply : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
    Odd (Module.finrank ℚ_[2] K) →
      Nonempty (GalKCompletedReciprocityInjectivityData K)

/-- **Pointwise end-to-end odd-degree adapter.**  Once completed reciprocity is injective,
the Demushkin invariant is `q = 2`.  The source torsion theorem and ramification of `K(i)/K`
are discharged by the repository. -/
theorem demushkinQ_maxProTwoGalK_eq_two_of_odd_completedReciprocityInjective
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (hrecip : Function.Injective
      (proTwoReciprocityToTopAb (markedRecipAt K))) :
    demushkinQ (maxProPQuotient 2 (GalK K)) = 2 :=
  demushkinQ_maxProTwoGalK_eq_two_of_completion
    (markedRecipAt K) hodd (ramifiedIData_of_odd_finrank K hodd) hrecip
      (GQ2.Dyadic.proTwoCompletionTorsionGeneratedByFieldRoots (K := K))

/-- Uniform end-to-end adapter from the sole remaining completed-reciprocity premise to the
field theorem consumed by the variable GammaL Sylow-core route. -/
theorem oddDegreeGalKDemushkinQTwo_of_completedReciprocityInjectivitySupply
    (hSupply : OddDegreeGalKCompletedReciprocityInjectivitySupply) :
    OddDegreeGalKDemushkinQTwo := by
  intro K _ _ _ _ hodd
  obtain ⟨hData⟩ := hSupply K hodd
  exact demushkinQ_maxProTwoGalK_eq_two_of_odd_completedReciprocityInjective
    K hodd hData.completedReciprocityInjective

/-- Compatibility name for the former torsion-generation package.  The package now contains
only completed-reciprocity injectivity. -/
abbrev GalKTorsionGenerationData := GalKCompletedReciprocityInjectivityData

/-- Compatibility name for the former torsion-generation supply. -/
abbrev OddDegreeGalKTorsionGenerationSupply :=
  OddDegreeGalKCompletedReciprocityInjectivitySupply

/-- Compatibility theorem for the former torsion-generation name. -/
theorem oddDegreeGalKDemushkinQTwo_of_torsionGenerationSupply
    (hSupply : OddDegreeGalKTorsionGenerationSupply) :
    OddDegreeGalKDemushkinQTwo :=
  oddDegreeGalKDemushkinQTwo_of_completedReciprocityInjectivitySupply hSupply

/-- Compatibility name for the earlier two-input adapter; ramification and source torsion are
now proved rather than supplied. -/
abbrev GalKRamifiedITorsionData := GalKCompletedReciprocityInjectivityData

/-- Compatibility name for the earlier uniform supply. -/
abbrev OddDegreeGalKRamifiedITorsionSupply :=
  OddDegreeGalKCompletedReciprocityInjectivitySupply

/-- Compatibility wrapper for the earlier theorem name. -/
theorem oddDegreeGalKDemushkinQTwo_of_ramifiedITorsionSupply
    (hSupply : OddDegreeGalKRamifiedITorsionSupply) :
    OddDegreeGalKDemushkinQTwo :=
  oddDegreeGalKDemushkinQTwo_of_torsionGenerationSupply hSupply

#print axioms oddDegreeGalKDemushkinQTwo_of_torsionGenerationSupply
#print axioms demushkinQ_maxProTwoGalK_eq_two_of_odd_completedReciprocityInjective
#print axioms oddDegreeGalKDemushkinQTwo_of_completedReciprocityInjectivitySupply

end

end GQ2.Dyadic.LSquare
