/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.DemushkinQRamifiedI
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldCore
import GQ2.Foundations.Axioms

/-!
# Supplying the odd-degree field `q = 2` input

This adapter connects the ramified-`i` torsion calculation to the field-model route for
variable GammaL Sylow cores.  Its single uniform premise packages, for every odd-degree finite
dyadic field `K`, both ramification of `K(i)/K` and the exact remaining torsion-surjectivity
statement for the canonical marked reciprocity map.

There is no separate reciprocity field in the package: `localReciprocity` and
`markedRecipAt K` are the repository's canonical APIs.  Thus the only genuinely variable data
left in the supply are the ramified-`i` witness and the torsion calculation.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The two field-specific inputs to the odd-degree `q = 2` calculation, using the
repository's canonical marked reciprocity map. -/
structure GalKRamifiedITorsionData
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] where
  ramifiedI : RamifiedIData K
  torsionGenerated :
    MaxProTwoAbTorsionGeneratedByFieldRoots (markedRecipAt K)

/-- The uniform arithmetic supply sufficient for the odd-degree field theorem `q = 2`.

For each odd-degree `K`, the supply gives a ramification witness for `K(i)/K` and says that
every torsion class in `Gal(K)(2)^ab` is the image of a 2-primary field root under the
canonical marked reciprocity map. -/
def OddDegreeGalKRamifiedITorsionSupply : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
    Odd (Module.finrank ℚ_[2] K) →
      Nonempty (GalKRamifiedITorsionData K)

/-- The ramified-`i` torsion supply discharges the `OddDegreeGalKDemushkinQTwo` premise used
by the GammaL field-core reduction. -/
theorem oddDegreeGalKDemushkinQTwo_of_ramifiedITorsionSupply
    (hSupply : OddDegreeGalKRamifiedITorsionSupply) :
    OddDegreeGalKDemushkinQTwo := by
  intro K _ _ _ _ hodd
  obtain ⟨hData⟩ := hSupply K hodd
  exact demushkinQ_maxProTwoGalK_eq_two_of_odd_ramifiedI
    (markedRecipAt K) hodd hData.ramifiedI hData.torsionGenerated

#print axioms oddDegreeGalKDemushkinQTwo_of_ramifiedITorsionSupply

end

end GQ2.Dyadic.LSquare
