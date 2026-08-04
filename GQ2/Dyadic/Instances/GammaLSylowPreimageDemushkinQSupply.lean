/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.DemushkinQRamifiedI
import GQ2.Dyadic.OddDegreeRamifiedI
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldCore
import GQ2.Foundations.Axioms

/-!
# Supplying the odd-degree field `q = 2` input

This adapter connects the ramified-`i` torsion calculation to the field-model route for
variable GammaL Sylow cores.  Odd degree now supplies ramification of `K(i)/K` internally, so
its single uniform premise packages only the exact remaining torsion-surjectivity statement
for the canonical marked reciprocity map.

There is no separate reciprocity field in the package: `localReciprocity` and
`markedRecipAt K` are the repository's canonical APIs.  Thus the only genuinely variable data
left in the supply is the torsion calculation.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The remaining field-specific input to the odd-degree `q = 2` calculation, using the
repository's canonical marked reciprocity map.  Ramification of `K(i)/K` follows from odd
degree and is not data in this structure. -/
structure GalKTorsionGenerationData
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] where
  torsionGenerated :
    MaxProTwoAbTorsionGeneratedByFieldRoots (markedRecipAt K)

/-- The uniform arithmetic supply sufficient for the odd-degree field theorem `q = 2`: every
torsion class in `Gal(K)(2)^ab` is the image of a 2-primary field root under canonical marked
reciprocity. -/
def OddDegreeGalKTorsionGenerationSupply : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)],
    Odd (Module.finrank ℚ_[2] K) →
      Nonempty (GalKTorsionGenerationData K)

/-- Torsion generation is now the only supplied arithmetic premise: odd degree constructs the
ramified-`i` witness used by the Demushkin-q calculation. -/
theorem oddDegreeGalKDemushkinQTwo_of_torsionGenerationSupply
    (hSupply : OddDegreeGalKTorsionGenerationSupply) :
    OddDegreeGalKDemushkinQTwo := by
  intro K _ _ _ _ hodd
  obtain ⟨hData⟩ := hSupply K hodd
  exact demushkinQ_maxProTwoGalK_eq_two_of_odd_ramifiedI
    (markedRecipAt K) hodd (ramifiedIData_of_odd_finrank K hodd) hData.torsionGenerated

/-- Compatibility name for the earlier two-input adapter; its ramification component is now
proved rather than supplied. -/
abbrev GalKRamifiedITorsionData := GalKTorsionGenerationData

/-- Compatibility name for the earlier uniform supply. -/
abbrev OddDegreeGalKRamifiedITorsionSupply := OddDegreeGalKTorsionGenerationSupply

/-- Compatibility wrapper for the earlier theorem name. -/
theorem oddDegreeGalKDemushkinQTwo_of_ramifiedITorsionSupply
    (hSupply : OddDegreeGalKRamifiedITorsionSupply) :
    OddDegreeGalKDemushkinQTwo :=
  oddDegreeGalKDemushkinQTwo_of_torsionGenerationSupply hSupply

#print axioms oddDegreeGalKDemushkinQTwo_of_torsionGenerationSupply

end

end GQ2.Dyadic.LSquare
